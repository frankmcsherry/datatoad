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
    while let Ok(_size) = std::io::stdin().read_line(&mut text) {

        handle_command(text.as_str(), &mut state, &mut bytes, &mut timer);

        println!("{:?}", timer.elapsed());
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

                    use std::io::{BufRead, BufReader};
                    use std::fs::File;

                    let args: Result<[_;2],_> = words.take(2).collect::<Vec<_>>().try_into();
                    if let Ok(args) = args {
                        let name = args[0].to_string();
                        let filename = args[1];
                        if let Ok(file) = File::open(filename) {
                            let mut file = BufReader::new(file);
                            use columnar::Push;
                            use datatoad::facts::{Forest, Terms};
                            let mut readline = String::default();
                            if file.read_line(&mut readline).unwrap() > 0 {
                                let mut columns = Vec::default();
                                let line = readline.trim();
                                for term in line.split(',') {
                                    let mut terms = Terms::default();
                                    terms.push(&term.parse::<u32>().unwrap().to_be_bytes());
                                    columns.push(terms);
                                }
                                readline.clear();

                                let atom = crate::types::Atom { name, anti: false, terms: vec![crate::types::Term::Lit(vec![]); columns.len()] };

                                while file.read_line(&mut readline).unwrap() > 0 {
                                    let line = readline.trim();
                                    for (term, col) in line.split(',').zip(columns.iter_mut()) {
                                        col.push(&term.parse::<u32>().unwrap().to_be_bytes());
                                    }
                                    readline.clear();
                                    use columnar::Len;
                                    if columns[0].len() > 100_000_000 {
                                        // Pass ownership of columns so the method can drop them as they are processed.
                                        let arity = columns.len();
                                        state.facts.entry(&atom).extend(Forest::from_columns(columns));
                                        columns = vec![Terms::default(); arity];
                                    }
                                }
                                state.facts.entry(&atom).extend(Forest::from_columns(columns));
                                state.update();
                            }
                        }
                        else { println!("file not found: {:?}", filename); }
                    }
                    else { println!(".flow command requires arguments: <name> <patt> <file>"); }
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
