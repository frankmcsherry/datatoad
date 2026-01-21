use std::fs::File;
use std::io::{BufReader, BufRead};
use std::collections::BTreeMap;

use datatoad::{parse, types};

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {

    let mut state = types::State::default();
    let mut timer = std::time::Instant::now();
    let mut bytes = BTreeMap::default();

    // Command-line arguments are treated as files to execute.
    for filename in std::env::args().skip(1) {
        println!("> .exec {}", filename);
        exec_file(filename.as_str(), &mut state, &mut bytes, &mut timer);
        println!("{:?}", timer.elapsed());
        println!();
    }

    use std::io::Write;
    println!();
    print!("> ");
    let _ = std::io::stdout().flush();

    let mut text = String::new();
    while let Ok(size) = std::io::stdin().read_line(&mut text) {
        // Handle EOF.
        if size == 0 { break; }

        handle_command(text.as_str(), &mut state, &mut bytes, &mut timer);

        println!();
        print!("> ");
        let _ = std::io::stdout().flush();
        text.clear();
    }
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
                        flow_log::load_rows(args[0], args[1], &mut state.facts);
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
                                        state.facts.entry(&atom).extend(Forest::from_columns(columns));
                                        columns = vec![Terms::default(); arity];
                                    }
                                }
                                state.facts.entry(&atom).extend(Forest::from_columns(columns));
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
                ".wipe" => { *state = Default::default(); *bytes = Default::default(); }
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
    fn load_cols(name: &str, filename: &str, facts: &mut datatoad::facts::Relations) {

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
                        facts.entry(&atom).extend(Forest::from_columns(columns));
                        columns = vec![Terms::default(); arity];
                    }
                }
                facts.entry(&atom).extend(Forest::from_columns(columns));
            }
        }
        else { println!("file not found: {:?}", filename); }
    }

    /// Row-oriented loading; usually faster than column-oriented loading, as the rows have a common column type.
    pub fn load_rows(name: &str, filename: &str, facts: &mut datatoad::facts::Relations) {

        if let Ok(file) = std::fs::File::open(filename) {

            let file = std::io::BufReader::new(file);
            let mut reader = simd_csv::ZeroCopyReaderBuilder::default().has_headers(false).from_reader(file);
            if let Some(record) = reader.read_byte_record().unwrap() {
                let arity = record.len();
                let mut bytes = Vec::default();
                for term in record.iter() {
                    let num = term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32));
                    bytes.extend(num.to_be_bytes());
                }

                let atom = crate::types::Atom { name: name.to_string(), anti: false, terms: vec![crate::types::Term::Lit(vec![]); arity] };

                while let Some(record) = reader.read_byte_record().unwrap() {
                    for term in record.iter() {
                        let num = term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32));
                        bytes.extend(num.to_be_bytes());
                    }
                    if bytes.len() >= 4_000_000_000 {
                        facts.entry(&atom).extend([to_forest(&mut bytes, arity)]);
                        bytes.clear();
                    }
                }

                facts.entry(&atom).extend([to_forest(&mut bytes, arity)]);
            }
        }
        else { println!("file not found: {:?}", filename); }
    }

    use datatoad::facts::{Forest, Lists, Terms, trie::Layer};

    /// Extracts a forest over `[u8;4]` values from bytes and a row arity.
    ///
    /// Only specialized up through arity nine; greater arities cause a panic.
    fn to_forest(bytes: &mut [u8], arity: usize) -> Forest<Terms> {
        let layers = match arity {
            0 => { flow_sort::< 0>(bytes) },
            1 => { flow_sort::< 4>(bytes) },
            2 => { flow_sort::< 8>(bytes) },
            3 => { flow_sort::<12>(bytes) },
            4 => { flow_sort::<16>(bytes) },
            5 => { flow_sort::<20>(bytes) },
            6 => { flow_sort::<24>(bytes) },
            7 => { flow_sort::<28>(bytes) },
            8 => { flow_sort::<32>(bytes) },
            9 => { flow_sort::<36>(bytes) },
            _ => { unimplemented!("Too many columns") }
        }.unwrap();
        layers.into_iter().map(|l| std::rc::Rc::new(Layer { list: l }) ).collect::<Vec<_>>().try_into().unwrap()
    }

    /// Takes bytes blocked as `KW` bytes of `[u8;4]` values for each row, and builds layers.
    fn flow_sort<const KW: usize>(entries: &mut [u8]) -> Option<Vec<Lists<Terms>>> {

        use datatoad::facts::radix_sort;
        use columnar::{Push, Len};

        radix_sort::lsb_range(entries.as_chunks_mut::<KW>().0, 0, KW);

        let mut iter = entries.as_chunks_mut::<4>().0.chunks(KW/4);
        if let Some(row) = iter.next() {
            let mut columns: Vec<Lists<Terms>> = vec![Default::default(); KW/4];
            for col in 0 .. KW/4 { columns[col].values.push(row[col]); }
            let mut prev = row;
            for row in iter {
                let pos = prev.iter().zip(row.iter()).position(|(p,r)| p != r).unwrap_or(KW/4);
                for col in (pos .. KW/4).skip(1) { let len = columns[col].values.len() as u64; columns[col].bounds.push(len); }
                for col in pos .. KW/4 { columns[col].values.push(row[col]); }
                prev = row;
            }

            for col in 0 .. KW/4 { let len = columns[col].values.len() as u64; columns[col].bounds.push(len); }
            Some(columns)
        }
        else { None }
    }
}
