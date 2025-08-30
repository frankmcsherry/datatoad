use datatoad::{facts, parse, types};
use datatoad::facts::FactCollection;

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
                    // ".show" => {
                    //     use columnar::Index;
                    //     for name in words {
                    //         if let Some(found) = state.facts.get(name) {
                    //             println!();
                    //             let mut temp = found.stable.contents().flat_map(|i| i.borrow().into_index_iter().take(10)).collect::<Vec<_>>();
                    //             temp.sort();
                    //             for item in temp.iter().take(10) {
                    //                 print!("\t(");
                    //                 for coord in item.into_iter() {
                    //                     print!("{:?},", str::from_utf8(coord.as_slice()).unwrap());
                    //                 }
                    //                 println!(")");
                    //             }
                    //             if found.len() > 10 {
                    //                 println!("\t .. ({:?} more)", found.len() - 10);
                    //             }
                    //         }
                    //     }
                    // }
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
                                let mut builder = facts::FactBuilder::<FactCollection>::default();
                                if let Ok(file) = File::open(filename) {
                                    let file = BufReader::new(file);
                                    let mut terms = datatoad::facts::Terms::default();
                                    for readline in file.lines() {
                                        let line = readline.expect("read error");
                                        if let Some(captures) = regex.captures(&line) {
                                            use columnar::{Container, Index, Push, Clear};
                                            terms.clear();
                                            for (term, name) in captures.iter().zip(names.iter()).skip(1) {
                                                let term = term.unwrap().as_str();
                                                if name.map(|x| x.starts_with("u32")).unwrap_or(false) {
                                                    let u = term.parse::<u32>().unwrap();
                                                    let bytes = [
                                                        (u >> 24) as u8,
                                                        (u >> 16) as u8,
                                                        (u >>  8) as u8,
                                                        (u >>  0) as u8,
                                                    ];
                                                    terms.push(&bytes);
                                                }
                                                else {
                                                    terms.push(term.as_bytes());
                                                }
                                            }
                                            builder.push(terms.borrow().into_index_iter());
                                        }
                                    }
                                    state.facts.entry(name).add_set(builder.finish());
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
