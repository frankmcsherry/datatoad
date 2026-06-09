//! WASI *reactor* front-end for datatoad.
//!
//! Unlike the CLI binary (a run-to-completion *command* that owns stdin/files),
//! this is a reactor: it exports `alloc`/`eval`, keeps one `State` alive in
//! linear memory across calls, and lets a host (a browser WASI shim, or
//! wasmtime) drive an interactive, *incremental* session — each `eval` extends
//! the same fixpoint rather than recomputing from scratch.
//!
//! All engine output goes to `stdout` (fd 1) via the existing `println!`s; the
//! host captures fd 1 and displays it. We do not marshal output across the ABI.
//!
//! Input crosses the ABI as a UTF-8 byte buffer: the host calls `alloc(len)` to
//! reserve space in linear memory, writes the line there, then calls
//! `eval(ptr, len)`.

use std::cell::RefCell;
use std::io::Write;
use std::time::Instant;

use datatoad::{parse, types};

thread_local! {
    static STATE: RefCell<types::State> = RefCell::new(types::State::default());
    // `.time` reports elapsed since the previous `.time`; the reactor must hold
    // the timer across calls, where the CLI kept it as a `main` local.
    static TIMER: RefCell<Instant> = RefCell::new(Instant::now());
}

/// Reserve `len` bytes in linear memory and hand the host a pointer to write
/// into. Ownership passes to the host until it calls `eval`, which reclaims it.
#[unsafe(no_mangle)]
pub extern "C" fn alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len);
    let ptr = buf.as_mut_ptr();
    std::mem::forget(buf);
    ptr
}

/// Execute one command line. Reconstructs (and frees) the buffer from `alloc`,
/// dispatches it against the persistent `State`, and flushes stdout so the host
/// sees this call's output before `eval` returns.
///
/// # Safety
/// `ptr`/`len` must name a buffer previously returned by `alloc(len)` and not
/// yet passed to `eval`. The host upholds this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn eval(ptr: *mut u8, len: usize) {
    let bytes = unsafe { Vec::from_raw_parts(ptr, len, len) };
    let line = String::from_utf8_lossy(&bytes).into_owned();
    STATE.with(|state| dispatch(&mut state.borrow_mut(), line.trim()));
    let _ = std::io::stdout().flush();
}

/// Command dispatch: a focused subset of the CLI's `handle_command`, covering
/// what the talk demos need. Rules and facts go through the parser; directives
/// are matched by leading token. `.plan`/`.prof` read in-memory state and so
/// port cleanly; `.heap`/`.load`/`.flow` stay CLI-only (mimalloc / real files).
fn dispatch(state: &mut types::State, text: &str) {
    if let Some(parsed) = parse::datalog(text) {
        state.extend(parsed);
        state.update();
        return;
    }

    let mut words = text.split_whitespace();
    match words.next() {
        None => {}
        Some(".list") => state.facts.list(),
        Some(".note") => {}
        Some(".plan") => {
            // Parse the remainder as a rule and print the planner's stage-by-stage
            // breakdown for each seed atom. Does not execute or mutate state.
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
        Some(".prof") => {
            // Per rule, total = sum across all calls and seeds; per-seed = sum
            // across calls grouped by body-atom index. Durations are collected
            // by `state.update()`, so they accrue the same way in the browser.
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
        Some(".time") => {
            TIMER.with(|t| {
                let mut t = t.borrow_mut();
                println!(".time\t{:?}\t{:?}", t.elapsed(), words.collect::<Vec<_>>());
                *t = Instant::now();
            });
        }
        Some(".wipe") => { *state = types::State::default(); }
        Some(other) => println!("unsupported in web demo: {:?}", other),
    }
}
