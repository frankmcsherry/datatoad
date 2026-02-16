use std::fs::File;
use std::io::{BufReader, BufRead};
use std::collections::BTreeMap;

use datatoad::{parse, types};

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {

    use timely_communication::Config;

    // Extract configurations and free arguments.
    let (config, mut free) = {
        let args = std::env::args();
        let mut opts = getopts::Options::new();
        Config::install_options(&mut opts);
        let matches = opts.parse(args).map_err(|e| e.to_string()).unwrap();
        (Config::from_matches(&matches).unwrap(), matches.free)
    };

    free.remove(0); // remove binary

    // Start multiple workers.
    // Worker 0 will listen for input and broadcast to all workers.
    // All workers then respond to each input synchronously.
    // TODO: A future version should have one command stream, rather than workers that need the same inputs.
    let guards = timely_communication::initialize(config, move |allocator| {

        let mut state = types::State::default();
        let mut timer = std::time::Instant::now();
        let mut bytes = BTreeMap::default();

        state.comms = allocator.into();

        // Command-line arguments are treated as files to execute.
        for filename in free.iter() { exec_file(filename.as_str(), &mut state, &mut bytes, &mut timer); }

        let mut done = false;
        while !done {

            use std::rc::Rc;
            use columnar::{Index, Push};
            use datatoad::facts::{FactLSM, Lists, Terms, trie::Layer};

            let mut command = FactLSM::default();

            if state.comms.index() == 0 {

                use std::io::Write;
                println!();
                print!("> ");
                let _ = std::io::stdout().flush();

                let mut text = String::new();
                if let Ok(size) = std::io::stdin().read_line(&mut text) {
                    // Handle EOF.
                    if size == 0 || text == ".quit" { }
                    else {
                        let mut list: Lists<Terms> = Default::default();
                        list.push([text.as_bytes()]);
                        command.push(vec![Rc::new(Layer { list })].try_into().unwrap());
                    }
                }

            }

            state.comms.broadcast(&mut command);
            if let Some(command) = command.flatten() {
                let text = str::from_utf8(command.borrow()[0].get(0).get(0).as_slice()).unwrap();
                handle_command(text, &mut state, &mut bytes, &mut timer);
            }
            else { done = true; }
        }

    });

    // computation runs until guards are joined or dropped.
    if let Ok(guards) = guards { for _guard in guards.join() { } }
    else { println!("error in computation"); }

}

fn handle_command(text: &str, state: &mut types::State, bytes: &mut BTreeMap<Vec<u8>, usize>, timer: &mut std::time::Instant) {

    if let Some(parsed) = parse::datalog(text) {
        state.extend(parsed);
        state.update();
    }

    else {
        let mut words = text.split_whitespace();
        if let Some(word) = words.next() {
            match word {
                ".exec" => { for filename in words { exec_file(filename, state, bytes, timer); } }
                ".list" => { state.facts.list() }
                ".flow" => {

                    let args: Result<[_;2],_> = words.take(2).collect::<Vec<_>>().try_into();
                    if let Ok(args) = args {
                        flow_log::load_rows(args[0], args[1], state);
                        state.update();
                    }
                    else { println!(".flow command requires arguments: <name> <file>"); }
                }
                ".load" => {

                    use std::io::{BufRead, BufReader};
                    use std::fs::File;

                    let args: Result<[_;3],_> = words.take(3).collect::<Vec<_>>().try_into();
                    if let Ok(args) = args {
                        let name = args[0].to_string();
                        let pattern = args[1];
                        let filename = args[2];

                        if let Ok(regex) = regex::Regex::new(pattern) {
                            let names = regex.capture_names().map(|x| x.to_owned()).collect::<Vec<_>>();
                            if let Ok(file) = File::open(filename) {
                                let mut file = BufReader::new(file);
                                use columnar::Push;
                                use datatoad::facts::{Forest, Terms};
                                let arity = names.len()-1;
                                let atom = crate::types::Atom { name, anti: false, terms: vec![crate::types::Term::Lit(vec![]); arity] };
                                let mut columns = vec![Terms::default(); arity];
                                let mut readline = String::default();
                                while file.read_line(&mut readline).unwrap() > 0 {
                                    let line = readline.trim();
                                    if let Some(captures) = regex.captures(line) {
                                        for ((term, name), col) in captures.iter().zip(names.iter()).skip(1).zip(columns.iter_mut()) {
                                            let term = term.unwrap().as_str();
                                            if name.map(|x| x.starts_with("u32_")).unwrap_or(false) {
                                                col.push(&term.parse::<u32>().unwrap().to_be_bytes());
                                            }
                                            else if name.map(|x| x.starts_with("h32_")).unwrap_or(false) {
                                                if !bytes.contains_key(term.as_bytes()) { bytes.insert(term.as_bytes().to_vec(), bytes.len()); }
                                                col.push(&(*bytes.get(term.as_bytes()).unwrap() as u32).to_be_bytes());
                                            }
                                            else {
                                                col.push(term.as_bytes());
                                            }
                                        }
                                    }
                                    else { println!("Regex missed line: {:?}", line); }
                                    readline.clear();
                                    use columnar::Len;
                                    if columns[0].len() > 100_000_000 {
                                        // Pass ownership of columns so the method can drop them as they are processed.
                                        state.extend_facts(&atom, Forest::from_columns(columns).unwrap().into());
                                        columns = vec![Terms::default(); arity];
                                    }
                                }
                                state.extend_facts(&atom, Forest::from_columns(columns).unwrap().into());
                                state.update();
                            }
                            else { println!("file not found: {:?}", filename); }
                        }
                        else { println!("invalid regex: {:?}", pattern); }
                    }
                    else { println!(".load command requires arguments: <name> <patt> <file>"); }
                }
                ".note" => { }
                ".prof" => {
                    for (rule, durs) in state.rules.iter() {
                        println!("{:>10}ms {}", durs.iter().sum::<std::time::Duration>().as_millis(), rule);
                    }
                }
                ".quit" => { std::process::exit(0); }
                ".save" => { println!("unimplemented: {:?}", word); }
                ".time" => {
                    println!("time:\t{:?}\t{:?}", timer.elapsed(), words.collect::<Vec<_>>());
                    *timer = std::time::Instant::now();
                }
                ".wipe" => { state.facts = Default::default(); state.rules = Default::default(); *bytes = Default::default(); }
                _ => { println!("Parse failure: {:?}", text); }
            }
        }
    }
}

fn exec_file(filename: &str, state: &mut types::State, bytes: &mut BTreeMap<Vec<u8>, usize>, timer: &mut std::time::Instant) {
    if let Ok(file) = File::open(filename) {
        let file = BufReader::new(file);
        for readline in file.lines() {
            handle_command(readline.expect("Read error").as_str(), state, bytes, timer);
        }
    }
}

/// Specialized logic to load FlowLog evaluation files, which are unsigned 32bit integers as CSVs.
mod flow_log {

    /// Column-oriented loading; usually slower than row-oriented loading for homogenous rows.
    #[allow(unused)]
    fn load_cols(name: &str, filename: &str, state: &mut datatoad::types::State) {

        if let Ok(file) = std::fs::File::open(filename) {

            let file = std::io::BufReader::new(file);
            let mut reader = simd_csv::ZeroCopyReaderBuilder::default().has_headers(false).from_reader(file);
            if let Some(record) = reader.read_byte_record().unwrap() {

                use columnar::Push;
                use datatoad::facts::{Forest, Terms};
                let mut columns = Vec::default();
                for term in record.iter() {
                    let mut terms = Terms::default();
                    let num = term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32));
                    terms.push(&num.to_be_bytes());
                    columns.push(terms);
                }

                let atom = crate::types::Atom { name: name.to_string(), anti: false, terms: vec![crate::types::Term::Lit(vec![]); columns.len()] };

                while let Some(record) = reader.read_byte_record().unwrap() {
                    for (term, col) in record.iter().zip(columns.iter_mut()) {
                        let num = term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32));
                        col.push(&num.to_be_bytes());
                    }
                    use columnar::Len;
                    if columns[0].len() > 100_000_000 {
                        // Pass ownership of columns so the method can drop them as they are processed.
                        let arity = columns.len();
                        state.extend_facts(&atom, Forest::from_columns(columns).unwrap().into());
                        columns = vec![Terms::default(); arity];
                    }
                }
                state.extend_facts(&atom, Forest::from_columns(columns).unwrap().into());
            }
        }
        else { println!("file not found: {:?}", filename); }
    }

    /// Row-oriented loading; usually faster than column-oriented loading, as the rows have a common column type.
    pub fn load_rows(name: &str, filename: &str, state: &mut datatoad::types::State) {

        if let Ok(file) = std::fs::File::open(filename) {

            let file = std::io::BufReader::new(file);
            let mut reader = simd_csv::ZeroCopyReaderBuilder::default().has_headers(false).from_reader(file);
            if let Some(record) = reader.read_byte_record().unwrap() {
                let first = record.iter().flat_map(|term| term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32)).to_be_bytes()).collect::<Vec<_>>();
                let atom = crate::types::Atom { name: name.to_string(), anti: false, terms: vec![crate::types::Term::Lit(vec![]); first.len()/4] };
                let data = match first.len()/4 {
                    0 => { to_facts::<_, 0>(reader, first) },
                    1 => { to_facts::<_, 4>(reader, first) },
                    2 => { to_facts::<_, 8>(reader, first) },
                    3 => { to_facts::<_,12>(reader, first) },
                    4 => { to_facts::<_,16>(reader, first) },
                    5 => { to_facts::<_,20>(reader, first) },
                    6 => { to_facts::<_,24>(reader, first) },
                    7 => { to_facts::<_,28>(reader, first) },
                    8 => { to_facts::<_,32>(reader, first) },
                    9 => { to_facts::<_,36>(reader, first) },
                    _ => { unimplemented!("too many columns! (use `load_cols`)") }
                };
                state.extend_facts(&atom, data);
            }
        }
        else { println!("file not found: {:?}", filename); }
    }

    use datatoad::facts::{FactLSM, Forest, Lists, Terms, trie::Layer};
    use datatoad::facts::radix_sort::{lsb_paged, PageBuilder};

    /// Converts a CSV reader into a collection of facts, provided `KW` the bytes per whole record.
    fn to_facts<R: std::io::Read, const KW: usize>(mut reader: simd_csv::ZeroCopyReader<R>, bytes: Vec<u8>) -> FactLSM<Forest<Terms>> {
        let mut array: [u8; KW] = bytes.try_into().unwrap();
        let mut builder = PageBuilder::<[u8;KW], KW>::new(1024);
        let mut counter = 0;
        let mut result = FactLSM::default();
        builder.push(array);
        counter += 1;
        while let Some(record) = reader.read_byte_record().unwrap() {

            let mut iter = record.iter();
            for index in 0 .. KW/4 {
                let next = iter.next().unwrap().iter().fold(0u32, |n,b| n*10 + ((b-48) as u32)).to_be_bytes();
                array[4*index .. 4*index+4].copy_from_slice(&next);
            }
            builder.push(array);
            counter += 1;

            if counter * KW >= 4_000_000_000 {
                let (mut data, diff) = builder.done();
                builder = PageBuilder::<[u8;KW], KW>::new(1024);
                lsb_paged(&mut data, &diff[..]);
                let iter = data.into_iter().flat_map(|page| page);
                if let Some(layers) = build(iter) {
                    result.push(layers.into_iter().map(|l| std::rc::Rc::new(Layer { list: l }) ).collect::<Vec<_>>().try_into().unwrap());
                }
                counter = 0;
            }
        }

        let (mut data, diff) = builder.done();
        lsb_paged(&mut data, &diff[..]);
        let iter = data.into_iter().flat_map(|page| page);
        if let Some(layers) = build(iter) {
            result.push(layers.into_iter().map(|l| std::rc::Rc::new(Layer { list: l }) ).collect::<Vec<_>>().try_into().unwrap());
        }

        result
    }

    /// Constructs a list of layers corresponding to `KW/4` columns of `[u8;4]` terms.
    ///
    /// Returns `None` only when the iterator is empty.
    fn build<const KW: usize>(mut iter: impl Iterator<Item=[u8;KW]>) -> Option<Vec<Lists<Terms>>> {

        use columnar::{Len, Push};

        if let Some(row) = iter.next() {
            let mut columns: Vec<Lists<Terms>> = vec![Default::default(); KW/4];
            let cols = row.as_chunks::<4>().0;
            for col in 0 .. KW/4 { columns[col].values.push(cols[col]); }
            let mut prev = row;
            for row in iter {
                let cols = row.as_chunks::<4>().0;
                let pos = prev.as_chunks::<4>().0.iter().zip(cols.iter()).position(|(p,r)| p != r).unwrap_or(KW/4);
                for col in (pos .. KW/4).skip(1) { let len = columns[col].values.len() as u64; columns[col].bounds.push(len); }
                for col in pos .. KW/4 { columns[col].values.push(cols[col]); }
                prev = row;
            }

            for col in 0 .. KW/4 { let len = columns[col].values.len() as u64; columns[col].bounds.push(len); }
            Some(columns)
        }
        else { None }
    }
}
