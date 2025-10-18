use datatoad::{parse, types};

fn main() {

    let mut state = types::State::default();

    use std::io::Write;
    println!();
    print!("> ");
    let _ = std::io::stdout().flush();

    let mut text = String::new();
    while let Ok(_size) = std::io::stdin().read_line(&mut text) {

        let timer = std::time::Instant::now();

        if let Some(parsed) = parse::datalog(&text) {
            state.extend(parsed);
            state.update();
        }

        else {
            let mut words = text.split_whitespace();
            if let Some(word) = words.next() {
                match word {
                    ".list" => { state.facts.list() }
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
                                    let file = BufReader::new(file);
                                    use columnar::{Container, Push};
                                    use datatoad::facts::{Forest, Terms};
                                    let mut columns = vec![Terms::default(); names.len()-1];
                                    for readline in file.lines() {
                                        let line = readline.expect("read error");
                                        if let Some(captures) = regex.captures(&line) {
                                            for ((term, name), col) in captures.iter().zip(names.iter()).skip(1).zip(columns.iter_mut()) {
                                                let term = term.unwrap().as_str();
                                                if name.map(|x| x.starts_with("u32")).unwrap_or(false) {
                                                    col.push(&term.parse::<u32>().unwrap().to_be_bytes());
                                                }
                                                else {
                                                    col.push(term.as_bytes());
                                                }
                                            }
                                        }
                                    }
                                    let trie = Forest::from_columns(&columns.iter().map(|c| c.borrow()).collect::<Vec<_>>()[..]);
                                    state.facts.entry(name).extend([trie]);
                                    state.update();
                                }
                                else { println!("file not found: {:?}", filename); }
                            }
                            else { println!("invalid regex: {:?}", pattern); }
                        }
                        else { println!(".load command requires arguments: <name> <patt> <file>"); }
                    }
                    ".save" => { println!("unimplemnted: {:?}", word); }
                    _ => {
                        println!("Parse failure: {:?}", text);
                    }
                }
            }
        }

        println!("{:?}", timer.elapsed());

        println!();
        print!("> ");
        let _ = std::io::stdout().flush();
        text.clear();
    }

}
