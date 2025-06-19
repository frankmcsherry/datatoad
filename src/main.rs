use std::collections::BTreeMap;

use datatoad::{facts, parse, types};

fn main() {

    let mut state = types::State::default();

    for filename in std::env::args().skip(1) {

        // Read input data from a handy file.
        use std::fs::File;
        use std::io::{BufRead, BufReader};

        let mut dict: BTreeMap<String, facts::FactBuilder> = BTreeMap::default();
        let file = BufReader::new(File::open(filename).unwrap());
        for readline in file.lines() {
            let line = readline.expect("read error");
            if !line.is_empty() && !line.starts_with('#') {
                let mut elts = line.split_whitespace().rev();
                if let Some(name) = elts.next() {
                    dict.entry(name.to_string())
                        .or_default()
                        .push(elts.rev().map(|x| x.as_bytes()));
                }
            }
        }
        for (name, facts) in dict { state.facts.entry(name).or_default().add_set(facts); }
    }
    state.update();

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
                    ".list" => {
                        for (name, facts) in state.facts.iter() {
                            println!("\t{}:\t{:?}", name, facts.len());
                        }
                    }
                    ".show" => {
                        use columnar::Index;
                        for name in words {
                            if let Some(found) = state.facts.get(name) {
                                println!();
                                let mut temp = found.stable.layers.iter().flat_map(|i| i.borrow().into_index_iter().take(10)).collect::<Vec<_>>();
                                temp.sort();
                                for item in temp.iter().take(10) {
                                    print!("\t(");
                                    for coord in (*item).into_index_iter() {
                                        print!("{:?},", str::from_utf8(coord.as_slice()).unwrap());
                                    }
                                    println!(")");
                                }
                                if found.len() > 10 {
                                    println!("\t .. ({:?} more)", found.len() - 10);
                                }
                            }
                        }
                    }
                    ".load" => { println!("unimplemnted: {:?}", word); }
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
