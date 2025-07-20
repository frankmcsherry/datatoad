use std::collections::BTreeMap;

use datatoad::{facts, parse, types};
use datatoad::facts::FactCollection;

fn main() {

    let mut state = types::State::default();

    for filename in std::env::args().skip(1) {

        // Read input data from a handy file.
        use std::fs::File;
        use std::io::{BufRead, BufReader};
        let mut dict: BTreeMap<String, facts::FactBuilder<FactCollection>> = BTreeMap::default();
        let file = BufReader::new(File::open(filename).unwrap());
        for readline in file.lines() {
            let line = readline.expect("read error");
            if !line.is_empty() && !line.starts_with('#') {
                let mut elts = line.split_whitespace().rev();
                if let Some(name) = elts.next() {
                    let items = elts.rev().map(|x| x.parse::<u32>().unwrap()).map(|u| { vec![
                        (u >> 24) as u8,
                        (u >> 16) as u8,
                        (u >>  8) as u8,
                        (u >>  0) as u8,
                    ] }).collect::<Vec<_>>();
                    dict.entry(name.to_string())
                        .or_default()
                        .push(&items);
                }
            }
        }
        for (name, facts) in dict { state.facts.entry(name).or_default().add_set(facts.finish()); }
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
                    // ".test" => {
                    //     for name in words {
                    //         if let Some(found) = state.facts.get(name) {
                    //             println!("Found {:?}", name);
                    //             for list in found.stable.contents() {
                    //                 use std::fmt::Write;
                    //                 use columnar::{Container, Index, Len, AsBytes};
                    //                 use datatoad::facts::forests::Forest;
                    //                 use datatoad::facts::{Facts, Sorted};

                    //                 let timer = std::time::Instant::now();
                    //                 let mut text = String::default();

                    //                 let list = list.borrow();

                    //                 let _test = <Facts as Sorted>::merge::<true>(list, list);
                    //                 println!("{:?}\tmerged (old)", timer.elapsed());

                    //                 let forest = Forest::<Terms>::form(list.into_index_iter());
                    //                 write!(&mut text, "Layer sizes: {:?}", list.len()).unwrap();
                    //                 for layer in forest.layers.iter().rev() {
                    //                     use columnar::Len;
                    //                     write!(&mut text, " -> {:?}", layer.list.len()).unwrap();
                    //                 }
                    //                 println!("{:?}\t{}", timer.elapsed(), text);
                    //                 text.clear();

                    //                 let mut total = 0;
                    //                 list.as_bytes().for_each(|(_,s)| { write!(&mut text, " {:?}", s.len()).unwrap(); total += s.len() });
                    //                 println!("{:?}\told bytes: {:?}:\t{}", timer.elapsed(), total, text);
                    //                 text.clear();

                    //                 let mut total = 0;
                    //                 forest.layers
                    //                       .iter()
                    //                       .for_each(|layer| layer.list.borrow()
                    //                             .as_bytes()
                    //                             .for_each(|(_,s)| { write!(&mut text, " {:?}", s.len()).unwrap(); total += s.len()}));
                    //                 println!("{:?}\tnew bytes: {:?}:\t{}", timer.elapsed(), total, text);
                    //                 text.clear();

                    //                 let forest2 = forest.union(&forest);
                    //                 println!("{:?}\tmerged (new) {} -> {}", timer.elapsed(), forest.len(), forest2.len());

                    //                 let forest3 = forest.minus(&forest);
                    //                 println!("{:?}\texcept (new) {} -> {}", timer.elapsed(), forest.len(), forest3.len());
                    //             }
                    //         }
                    //     }
                    // }
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
