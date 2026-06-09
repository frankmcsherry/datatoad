use std::fs::File;
use std::io::{BufReader, BufRead};
use std::collections::BTreeMap;

use datatoad::{parse, types};

#[cfg(feature = "mimalloc")]
use mimalloc::MiMalloc;

#[cfg(feature = "mimalloc")]
#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

/// Snapshot of process memory stats from mimalloc's `mi_process_info`.
#[cfg(feature = "mimalloc")]
struct HeapInfo { rss: usize, peak_rss: usize, commit: usize, peak_commit: usize }

#[cfg(feature = "mimalloc")]
fn heap_info() -> HeapInfo {
    let mut v = [0usize; 8];
    // SAFETY: `mi_process_info` writes to eight `usize` out-parameters and
    // performs no other observable effects.
    unsafe {
        libmimalloc_sys::mi_process_info(
            &mut v[0], &mut v[1], &mut v[2],
            &mut v[3], &mut v[4], &mut v[5], &mut v[6], &mut v[7],
        );
    }
    HeapInfo { rss: v[3], peak_rss: v[4], commit: v[5], peak_commit: v[6] }
}

#[cfg(feature = "mimalloc")]
fn fmt_bytes(n: usize) -> String {
    // mimalloc tracks `current_commit` as a signed delta (commits minus
    // purges to the OS) and stores it in a usize; if it goes negative it
    // wraps near usize::MAX. Reinterpret as isize so negatives print as
    // signed values instead of nonsense like "16777215.99TiB".
    const UNITS: [&str; 5] = ["B", "KiB", "MiB", "GiB", "TiB"];
    let signed = n as isize;
    let mag = signed.unsigned_abs();
    let mut x = mag as f64;
    let mut u = 0;
    while x >= 1024.0 && u + 1 < UNITS.len() { x /= 1024.0; u += 1; }
    let sign = if signed < 0 { "-" } else { "" };
    if u == 0 { format!("{}{}B", sign, mag) } else { format!("{}{:.2}{}", sign, x, UNITS[u]) }
}

fn main() {

    use timely_communication::Config;

    // Extract configurations and free arguments.
    let (config, mem_budget, mut free) = {
        let args = std::env::args();
        let mut opts = getopts::Options::new();
        Config::install_options(&mut opts);
        opts.optopt("m", "memory", "cluster-wide memory budget for in-flight tuples (e.g. 200M, 1G, 200000000); default 200M", "BYTES");
        let matches = opts.parse(args).map_err(|e| e.to_string()).unwrap();
        let config = Config::from_matches(&matches).unwrap();
        let mem_budget = matches.opt_str("m")
            .or_else(|| std::env::var("DATATOAD_MEMORY").ok())
            .map(|s| parse_byte_size(&s).expect("invalid -m/DATATOAD_MEMORY value"))
            .unwrap_or(datatoad::comms::DEFAULT_MEM_BUDGET);
        (config, mem_budget, matches.free)
    };

    free.remove(0); // remove binary

    // Start multiple workers. Worker 0 owns the input stream and broadcasts
    // each command line to every worker; non-zero workers receive and execute,
    // but don't read files or stdin themselves. Driver-level commands (`.exec`,
    // `.quit`) are handled by worker 0 inside `next_command_line` and never
    // reach `handle_command`; everything else is broadcast verbatim.
    timely_communication::initialize(config, move |allocator| {

        let mut state = types::State::default();
        let mut timer = std::time::Instant::now();
        let mut bytes = BTreeMap::default();

        state.comms = allocator.into();
        state.comms.set_mem_budget(mem_budget);

        // Worker 0's command stack; initially .exec <file> for each command line argument.
        let mut cmd_stack: Vec<String> = Vec::new();
        if state.comms.index() == 0 {
            cmd_stack.extend(free.iter().rev().map(|f| format!(".exec {}", f)));
        }

        let mut done = false;
        while !done {

            use std::rc::Rc;
            use columnar::{Index, Push};
            use datatoad::facts::{FactLSM, Lists, Terms, trie::Layer};

            let mut command = FactLSM::default();

            if state.comms.index() == 0 {
                if let Some(text) = next_command_line(&mut cmd_stack) {
                    let mut list: Lists<Terms> = Default::default();
                    list.push([text.as_bytes()]);
                    command.push(vec![Rc::new(Layer { list })].try_into().unwrap());
                }
                // None → leave `command` empty → broadcast tells workers to stop.
            }

            state.comms.broadcast(&mut command);
            if let Some(command) = command.flatten() {
                let text = str::from_utf8(command.borrow()[0].get(0).get(0).as_slice()).unwrap();
                handle_command(text, &mut state, &mut bytes, &mut timer);
            }
            else { done = true; }
        }

        // `.test` all_reduces fact counts internally, so every worker ends
        // with the same `state.test_failures` value. Worker 0 panics if any
        // failed; the unwind drops the comms layer cleanly, peers see EOF
        // and finish normally, and the panic propagates through guards' Drop.
        if state.comms.index() == 0 && state.test_failures > 0 {
            panic!("{} .test assertion(s) failed", state.test_failures);
        }
    }).unwrap();
}

/// Pull the next command line from worker 0's command stack.
///
/// Driver-level directives (`.exec`, `.help`, `.quit`) are interpreted here and consumed without
/// surfacing to the engine. EOF on a source pops it; an empty stack returns `None`,
/// signaling the worker loop to broadcast "no more commands".
fn next_command_line(cmd_stack: &mut Vec<String>) -> Option<String> {

    // Loop, because .exec of an empty file could result in an empty queue.
    loop {
        // If no pending commands, read one from the console.
        if cmd_stack.is_empty() {
            use std::io::Write;
            println!();
            print!("> ");
            let _ = std::io::stdout().flush();
            let mut text = String::new();
            match std::io::stdin().read_line(&mut text) {
                Ok(0) | Err(_) => { return None; },
                Ok(_) => cmd_stack.push(text.trim_end().to_string()),
            }
        }

        let text = cmd_stack.pop().unwrap();
        let mut words = text.split_whitespace();
        match words.next() {
            Some(".quit") => { cmd_stack.clear(); return None; }
            Some(".exec") => {
                // Read each file in order, record their lines.
                let new_cmds: Vec<String> = words.flat_map(|filename| BufReader::new(File::open(filename).unwrap()).lines()).flatten().collect();
                cmd_stack.extend(new_cmds.into_iter().rev());
            }
            Some(".help") => { print_help(); }
            _ => return Some(text),
        }
    }
}

/// Print a summary of available directives.
fn print_help() {
    println!("Datatoad directives:");
    println!("  .decl name(_, ...) [view]   declare a relation's arity (and optional flags)");
    println!("  .exec <file> [<file> ...]   queue commands from one or more script files");
    println!("  .flow <name> <file>         load a FlowLog-format relation from <file>");
    println!("  .heap [tag ...]             print resident/peak memory usage");
    println!("  .help                       show this message");
    println!("  .list                       list all known relations and their sizes");
    println!("  .load <name> <regex> <file> ingest <file>, extracting fields via named captures");
    println!("  .note ...                   no-op; comment line");
    println!("  .plan <rule>                show the planner's stage-by-stage breakdown for <rule>");
    println!("  .prof                       print per-rule (and per-seed) accumulated runtime");
    println!("  .quit                       exit datatoad");
    println!("  .sync                       cluster-wide barrier (no-op single-process)");
    println!("  .test <relation> <count>    assert global row count; nonzero exit on mismatch");
    println!("  .time [tag ...]             print elapsed since previous .time and reset");
    println!("  .wipe                       clear all facts, rules, and declarations");
    println!("Datalog rules and facts are entered directly, e.g. `foo(x) :- bar(x).`");
}

/// Commands executed symmetrically by all workers.
fn handle_command(text: &str, state: &mut types::State, bytes: &mut BTreeMap<Vec<u8>, usize>, timer: &mut std::time::Instant) {

    if let Some(parsed) = parse::datalog(text) {
        state.extend(parsed);
        state.update();
    }

    else {
        let mut words = text.split_whitespace();
        if let Some(word) = words.next() {
            match word {
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
                                let thresh = state.comms.thresh();
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
                                    if columns[0].len() > thresh {
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
                ".plan" => {
                    // Parse the remainder of the line as a Datalog rule and print
                    // the planner's stage-by-stage breakdown for each seed atom.
                    // Does not execute the rule or mutate state.
                    let rest = text.trim_start().strip_prefix(".plan").unwrap_or("").trim_start();
                    match parse::datalog(rest) {
                        Some(rules) if rules.len() == 1 => {
                            let rule = &rules[0];
                            let head = &rule.head[..];
                            let body = &rule.body[..];
                            let seed_atoms: Vec<usize> = (0..body.len()).collect();
                            let (plans, _loads) = datatoad::rules::plan::plan_rule(head, body, &seed_atoms, &state.decls);
                            for (seed_idx, plan) in plans.iter() {
                                println!("plan seed #{} {}:", seed_idx, body[*seed_idx]);
                                for (i, (atoms, terms, target)) in plan.iter().enumerate() {
                                    let atom_descrs: Vec<String> = atoms.iter()
                                        .map(|a| format!("#{} {}", a, body[*a]))
                                        .collect();
                                    let intro: Vec<&str> = terms.iter().map(|s| s.as_str()).collect();
                                    let tgt: Vec<&str> = target.iter().map(|s| s.as_str()).collect();
                                    println!("  stage {}: atoms=[{}] introduce={{{}}} target=[{}]",
                                             i, atom_descrs.join(", "), intro.join(", "), tgt.join(", "));
                                }
                            }
                        }
                        Some(rules) => println!(".plan expected exactly one rule, got {}", rules.len()),
                        None => println!(".plan: could not parse rule from {:?}", rest),
                    }
                }
                ".prof" => {
                    // For each rule, total = sum across all calls and seeds.
                    // Per-seed = sum across calls grouped by body-atom index (the
                    // seed_idx carried alongside each duration).
                    use std::collections::BTreeMap;
                    for (rule, calls) in state.rules.iter() {
                        let total: std::time::Duration =
                            calls.iter().flat_map(|c| c.iter()).map(|(_, d)| *d).sum();
                        println!("{:>10}ms {}", total.as_millis(), rule);
                        let mut per_seed: BTreeMap<usize, std::time::Duration> = BTreeMap::new();
                        for call in calls.iter() {
                            for (idx, d) in call.iter() {
                                *per_seed.entry(*idx).or_default() += *d;
                            }
                        }
                        if per_seed.len() > 1 {
                            for (idx, d) in per_seed.iter() {
                                let atom_descr = rule.body.get(*idx)
                                    .map(|a| format!("{}", a))
                                    .unwrap_or_else(|| format!("#{}", idx));
                                println!("{:>10}ms   seed #{} {}", d.as_millis(), idx, atom_descr);
                            }
                        }
                    }
                }
                ".test" => {
                    // `.test <rel> <count>` — assert that relation's globally-summed
                    // row count equals `<count>`. Failures are tallied on `state` and
                    // surfaced at `.quit` (nonzero exit). Only worker 0 prints.
                    let args: Vec<&str> = words.collect();
                    if args.len() != 2 {
                        if state.comms.index() == 0 {
                            println!(".test command requires arguments: <relation> <expected_count>");
                        }
                        state.test_failures += 1;
                    } else {
                        let name = args[0];
                        let expected: u64 = match args[1].parse() {
                            Ok(n) => n,
                            Err(_) => {
                                if state.comms.index() == 0 {
                                    println!(".test: expected_count must be an integer, got {:?}", args[1]);
                                }
                                state.test_failures += 1;
                                return;
                            }
                        };
                        let local = state.facts.get(name).map(|f| f.len() as u64).unwrap_or(0);
                        let actual = state.comms.all_reduce_sum(local);
                        if state.facts.get(name).is_none() {
                            if state.comms.index() == 0 {
                                println!(".test FAIL {}: relation does not exist", name);
                            }
                            state.test_failures += 1;
                        } else if actual == expected {
                            if state.comms.index() == 0 {
                                println!(".test ok   {}: {}", name, actual);
                            }
                        } else {
                            if state.comms.index() == 0 {
                                println!(".test FAIL {}: expected {}, got {}", name, expected, actual);
                            }
                            state.test_failures += 1;
                        }
                    }
                }
                ".save" => { println!("unimplemented: {:?}", word); }
                ".sync" => {
                    // Cluster-wide barrier: broadcast an empty FactLSM so every
                    // peer waits to receive from every other peer. No-op in
                    // single-process mode (peers() == 1). Useful at the top of
                    // a script before the first `.time` measurement, to absorb
                    // ssh/startup skew across processes.
                    let mut empty = datatoad::facts::FactLSM::default();
                    state.comms.broadcast(&mut empty);
                }
                ".time" => {
                    println!(".time\t{:?}\t{:?}", timer.elapsed(), words.collect::<Vec<_>>());
                    *timer = std::time::Instant::now();
                }
                ".heap" => {
                    #[cfg(feature = "mimalloc")]
                    {
                        let h = heap_info();
                        println!(
                            ".heap\trss={} peak_rss={} commit={} peak_commit={}\t{:?}",
                            fmt_bytes(h.rss), fmt_bytes(h.peak_rss),
                            fmt_bytes(h.commit), fmt_bytes(h.peak_commit),
                            words.collect::<Vec<_>>(),
                        );
                    }
                    #[cfg(not(feature = "mimalloc"))]
                    println!(".heap\tunavailable (built without mimalloc)\t{:?}", words.collect::<Vec<_>>());
                }
                ".decl" => {
                    // `.decl name(_, _, ...) [flags]` declares a relation's arity and any
                    // attribute flags (currently just `view`). If the name has already
                    // been seen (explicitly or implicitly) the arity must match, and any
                    // explicit prior declaration cannot be reissued with conflicting flags.
                    let rest: String = words.collect::<Vec<_>>().join(" ");
                    match parse_decl(rest.as_str()) {
                        Some((name, arity, flags)) => {
                            let view = flags.iter().any(|f| f == "view");
                            for flag in flags.iter() {
                                if flag != "view" {
                                    println!(".decl: unknown flag `{}` (known flags: view)", flag);
                                    return;
                                }
                            }
                            match state.decls.get(&name) {
                                Some(prior) if prior.arity != arity => {
                                    println!(
                                        ".decl: name `{}` already used with arity {}; cannot redeclare with arity {}.",
                                        name, prior.arity, arity
                                    );
                                }
                                Some(prior) if prior.explicit && (prior.view != view) => {
                                    println!(
                                        ".decl: name `{}` already declared; cannot reissue with conflicting flags.",
                                        name
                                    );
                                }
                                _ => {
                                    state.decls.insert(
                                        name,
                                        types::RelationDecl { arity, explicit: true, view },
                                    );
                                }
                            }
                        }
                        None => { println!(".decl requires `.decl name(_, _, ...) [flags]`"); }
                    }
                }
                ".wipe" => { state.facts = Default::default(); state.rules = Default::default(); state.decls = Default::default(); *bytes = Default::default(); }
                _ => { println!("Parse failure: {:?}", text); }
            }
        }
    }
}

/// Parses a `.decl` directive's argument: `name(_, _, ...) [flags]` (with optional
/// trailing `.`), returning `(name, arity, flags)`. Arity is the number of
/// comma-separated placeholders; flags are space-separated tokens after the closing
/// paren. An empty argument list `name()` yields arity 0.
fn parse_decl(text: &str) -> Option<(String, usize, Vec<String>)> {
    let trimmed = text.trim().trim_end_matches('.').trim();
    let lparen = trimmed.find('(')?;
    let rparen = trimmed.rfind(')')?;
    if rparen < lparen { return None; }
    let name = trimmed[..lparen].trim().to_string();
    if name.is_empty() { return None; }
    let inside = trimmed[lparen + 1..rparen].trim();
    let arity = if inside.is_empty() { 0 } else { inside.split(',').count() };
    let flags = trimmed[rparen + 1..]
        .split_whitespace()
        .map(|s| s.to_string())
        .collect();
    Some((name, arity, flags))
}

/// Parses a byte-size string: accepts trailing `K`/`M`/`G` (decimal, base 1000)
/// or a raw integer. Whitespace around the value and unit is allowed.
fn parse_byte_size(s: &str) -> Option<usize> {
    let s = s.trim();
    let (digits, mult) = if let Some(rest) = s.strip_suffix(['G', 'g']) { (rest, 1_000_000_000) }
                         else if let Some(rest) = s.strip_suffix(['M', 'm']) { (rest, 1_000_000) }
                         else if let Some(rest) = s.strip_suffix(['K', 'k']) { (rest, 1_000) }
                         else { (s, 1) };
    digits.trim().parse::<usize>().ok().map(|n| n * mult)
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

                let thresh = state.comms.thresh();
                while let Some(record) = reader.read_byte_record().unwrap() {
                    for (term, col) in record.iter().zip(columns.iter_mut()) {
                        let num = term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32));
                        col.push(&num.to_be_bytes());
                    }
                    use columnar::Len;
                    if columns[0].len() > thresh {
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

        let index = state.comms.index();
        let peers = state.comms.peers();

        if let Ok(file) = std::fs::File::open(filename) {

            let file = std::io::BufReader::new(file);
            let mut reader = simd_csv::ZeroCopyReaderBuilder::default().has_headers(false).from_reader(file);
            if let Some(record) = reader.read_byte_record().unwrap() {
                let first = record.iter().flat_map(|term| term.iter().fold(0u32, |n,b| n*10 + ((b-48) as u32)).to_be_bytes()).collect::<Vec<_>>();
                for _ in 0 .. index { reader.read_byte_record().unwrap(); }
                let atom = crate::types::Atom { name: name.to_string(), anti: false, terms: vec![crate::types::Term::Lit(vec![]); first.len()/4] };
                let data = match first.len()/4 {
                    0 => { to_facts::<_, 0>(reader, first, peers) },
                    1 => { to_facts::<_, 4>(reader, first, peers) },
                    2 => { to_facts::<_, 8>(reader, first, peers) },
                    3 => { to_facts::<_,12>(reader, first, peers) },
                    4 => { to_facts::<_,16>(reader, first, peers) },
                    5 => { to_facts::<_,20>(reader, first, peers) },
                    6 => { to_facts::<_,24>(reader, first, peers) },
                    7 => { to_facts::<_,28>(reader, first, peers) },
                    8 => { to_facts::<_,32>(reader, first, peers) },
                    9 => { to_facts::<_,36>(reader, first, peers) },
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
    fn to_facts<R: std::io::Read, const KW: usize>(mut reader: simd_csv::ZeroCopyReader<R>, bytes: Vec<u8>, step: usize) -> FactLSM<Forest<Terms>> {
        let mut array: [u8; KW] = bytes.try_into().unwrap();
        let mut builder = PageBuilder::<[u8;KW], KW>::default();
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
                builder = PageBuilder::<[u8;KW], KW>::default();
                lsb_paged::<_, 1024>(&mut data, &diff[..]);
                let iter = data.into_iter().flat_map(|page| page);
                if let Some(layers) = build(iter) {
                    result.push(layers.into_iter().map(|l| std::rc::Rc::new(Layer { list: l }) ).collect::<Vec<_>>().try_into().unwrap());
                }
                counter = 0;
            }

            for _ in 0 .. step-1 { reader.read_byte_record().unwrap(); }
        }

        let (mut data, diff) = builder.done();
        lsb_paged::<_, 1024>(&mut data, &diff[..]);
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
