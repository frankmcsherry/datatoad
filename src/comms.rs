use std::rc::Rc;
use std::cell::RefCell;

use timely_communication::{allocator::Allocator, Bytesable};
use crate::facts::{FactLSM, Forest, Lists, Terms};
use crate::facts::trie::Layer;

/// Cluster-wide default budget (bytes) for in-flight intermediate tuples.
/// Per-peer slice is `mem_budget / peers()`. See `Comms::thresh`.
pub const DEFAULT_MEM_BUDGET: usize = 200_000_000;

pub struct Comms {
    /// If set, communication infrastructure.
    pub ether: Option<Rc<RefCell<Allocator>>>,
    /// An incrementing channel identifier.
    count: usize,
    /// Cluster-wide budget for in-flight intermediate tuples (bytes).
    /// Configurable via `-m`/`--memory` CLI flag or `DATATOAD_MEMORY` env var.
    mem_budget: usize,
}

impl Default for Comms {
    fn default() -> Self {
        Self { ether: None, count: 0, mem_budget: DEFAULT_MEM_BUDGET }
    }
}

impl Comms {

    pub fn index(&self) -> usize { self.ether.as_ref().map(|e| e.borrow().index()).unwrap_or(0) }
    pub fn peers(&self) -> usize { self.ether.as_ref().map(|e| e.borrow().peers()).unwrap_or(1) }

    /// Cluster-wide budget for in-flight intermediate tuples (bytes).
    pub fn mem_budget(&self) -> usize { self.mem_budget }
    /// Per-peer slice of the cluster-wide budget. The constant most call sites want.
    pub fn thresh(&self) -> usize { self.mem_budget / self.peers() }
    /// Set the cluster-wide memory budget. Typically called once at startup.
    pub fn set_mem_budget(&mut self, budget: usize) { self.mem_budget = budget; }

    pub fn next_id(&self) -> usize { self.count }

    pub fn conduit(&mut self) -> Conduit {
        let budget = self.mem_budget;
        let comms = self.ether.as_mut().map(|comms| {
            let (sends, recv) = comms.borrow_mut().allocate(self.count);
            self.count += 1;
            let count = sends.len();
            Channel { comms: comms.clone(), sends, recv, count, done: false }
        });
        Conduit { comms, facts: FactLSM::default(), mem_budget: budget }
    }

    /// Drains a set of active indices, broadcasts, and refills with the union across all workers.
    pub fn active_set(&mut self, indices: &mut std::collections::BTreeSet<usize>) {
        use columnar::Push;
        let mut facts = FactLSM::default();
        if !indices.is_empty() {
            let mut column = Terms::default();
            for index in indices.iter() {
                // Encode width-independently as `u64`: `usize::to_be_bytes` is 8
                // bytes on 64-bit targets but 4 on wasm32, and the decode below
                // matches on `len() == 8`. A bare `usize` here silently drops
                // every index on wasm32, collapsing the fixpoint to one round.
                column.push(&(*index as u64).to_be_bytes().to_vec());
            }
            if let Some(forest) = Forest::from_columns(vec![column]) {
                facts.extend([forest]);
            }
        }
        indices.clear();
        self.broadcast(&mut facts);
        if let Some(flat) = facts.flatten() {
            for i in 0 .. flat.layer(0).list.borrow().values.len() {
                let bytes = flat.layer(0).list.borrow().values.get(i).as_slice();
                if bytes.len() == 8 {
                    indices.insert(u64::from_be_bytes(bytes.try_into().unwrap()) as usize);
                }
            }
        }
    }

    /// Broadcasts facts to all workers.
    pub fn broadcast(&mut self, facts: &mut FactLSM<Forest<Terms>>) {
        if let Some(comms) = self.ether.as_mut() {
            let mut comms = comms.borrow_mut();
            let (senders, mut receiver) = comms.allocate(self.count);
            let mut countdown = senders.len();
            self.count += 1;
            if let Some(fact) = facts.flatten() {
                for mut sender in senders { sender.send(FactMessage { facts: Some((0 .. fact.arity()).map(|i| fact.layer(i).list.clone()).collect::<Vec<_>>()) } ); }
            }
            else {
                for mut sender in senders { sender.send(FactMessage { facts: None } ); }
            }

            while countdown > 0 {
                comms.receive();
                while let Some(message) = receiver.recv() { if let Some(fact) = message.facts { facts.push(fact.into_iter().map(|list| std::rc::Rc::new(Layer { list })).collect::<Vec<_>>().try_into().unwrap()); } countdown -= 1; }
                comms.release();
            }
        }
    }

    /// Logical-OR across peers: `true` if any worker passes `true`.
    pub fn any(&mut self, local: bool) -> bool {
        if self.peers() == 1 { return local; }
        self.all_reduce_sum(local as u64) > 0
    }

    /// Logical-AND across peers: `true` only if every worker passes `true`.
    pub fn all(&mut self, local: bool) -> bool {
        if self.peers() == 1 { return local; }
        self.all_reduce_sum((!local) as u64) == 0
    }

    /// All-reduce sum across peers. Returns the same value on every peer.
    ///
    /// Each contribution is tagged with the sender's index so that workers
    /// reporting the same `value` produce distinct rows after broadcast.
    /// Without the tag, `flatten()` (which unions / deduplicates) would
    /// collapse equal contributions and silently undercount the sum.
    pub fn all_reduce_sum(&mut self, value: u64) -> u64 {
        if self.peers() == 1 { return value; }
        use columnar::Push;
        let mut facts = FactLSM::default();
        let mut column = Terms::default();
        let mut buf = [0u8; 16];
        buf[..8].copy_from_slice(&(self.index() as u64).to_be_bytes());
        buf[8..].copy_from_slice(&value.to_be_bytes());
        column.push(&buf.to_vec());
        if let Some(forest) = Forest::from_columns(vec![column]) { facts.extend([forest]); }
        self.broadcast(&mut facts);
        let mut total: u64 = 0;
        if let Some(flat) = facts.flatten() {
            for i in 0 .. flat.layer(0).list.borrow().values.len() {
                let bytes = flat.layer(0).list.borrow().values.get(i).as_slice();
                if bytes.len() == 16 {
                    total += u64::from_be_bytes(bytes[8..].try_into().unwrap());
                }
            }
        }
        total
    }

    /// Exchanges facts among all workers.
    pub fn exchange(&mut self, facts: &mut FactLSM<Forest<Terms>>) {
        // Single-worker: nothing to shuffle, facts already local.
        if self.peers() == 1 { return; }
        let mut conduit = self.conduit();
        conduit.extend(facts);
        *facts = conduit.finish();
    }
}

impl From<Allocator> for Comms {
    fn from(comm: Allocator) -> Self {
        Self { ether: Some(Rc::new(RefCell::new(comm))), count: 0, mem_budget: DEFAULT_MEM_BUDGET }
    }
}

use timely_communication::{Push, Pull};

pub struct Channel {
    comms: Rc<RefCell<Allocator>>,
    sends: Vec<Box<dyn Push<FactMessage>>>,
    recv: Box<dyn Pull<FactMessage>>,
    count: usize,
    done: bool,
}

impl Channel {
    fn close(&mut self) { if !self.done {
        for sender in self.sends.iter_mut() { sender.send(FactMessage { facts: None } ); }
        self.done = true;
    }}
    /// Extracts all remaining facts
    fn complete(mut self) -> FactLSM<Forest<Terms>> {
        self.close();
        let mut facts = FactLSM::default();
        while self.count > 0 { let mut temp = FactLSM::default(); self.exchange(&mut temp); facts.extend(temp); }
        facts
    }
    /// Exchanges facts with other participants, drawing from and refilling `facts`.
    fn exchange(&mut self, facts: &mut FactLSM<Forest<Terms>>) {

        if self.done && !facts.is_empty() { panic!("Exchanging on a sealed channel"); }

        let mut comms = self.comms.borrow_mut();

        // TODO: put self-sends back in to `facts`.
        if let Some(facts) = facts.flatten() {
            let mut bools: std::collections::VecDeque<bool> = Default::default();
            for (index, sender) in self.sends.iter_mut().enumerate() {
                bools.extend((0 .. facts.layer(0).list.borrow().values.len()).map(|i| (*facts.layer(0).list.borrow().values.get(i).as_slice().last().unwrap() as usize) % comms.peers() == index));
                if let Some(facts) = facts.clone().retain_core(1, bools.clone()).flatten() {
                    let layers = (0 .. facts.arity()).map(|i| facts.layer(i).clone()).collect::<Vec<_>>();
                    drop(facts);
                    let message = FactMessage { facts: Some(layers.into_iter().map(|l| Rc::unwrap_or_clone(l).list).collect::<Vec<_>>()) };
                    sender.send(message);
                }
                bools.clear();
            }
        }

        comms.receive();

        // Receive data first, to allow early consolidation.
        while let Some(message) = self.recv.recv() {
            if let Some(fact) = message.facts {
                facts.push(fact.into_iter().map(|list| std::rc::Rc::new(Layer { list })).collect::<Vec<_>>().try_into().unwrap());
            }
            else { self.count -= 1; }
        }

        comms.release();
    }
}

/// A destination for data that wrangles sharding and consolidation.
///
/// Internally, a communication protocol with other peers relies on each eventually sending an empty `FactMessage`.
/// Once as many of these have been received as there are peers, the exchange is complete.
pub struct Conduit {
    /// Communication infrastructure.
    comms: Option<Channel>,
    facts: FactLSM<Forest<Terms>>,
    /// Snapshot of the cluster-wide budget at allocation time.
    mem_budget: usize,
}

impl Conduit {
    /// The number of peers backing the conduit.
    pub fn peers(&self) -> usize { self.comms.as_ref().map(|c| c.comms.borrow().peers()).unwrap_or(1) }
    /// Per-peer slice of the cluster-wide budget. Mirrors `Comms::thresh`.
    pub fn thresh(&self) -> usize { self.mem_budget / self.peers() }
    /// Supplies facts to the conduit, which are exchanged and then collected.
    pub fn extend(&mut self, facts: &mut FactLSM<Forest<Terms>>) {
        if let Some(channel) = self.comms.as_mut() { channel.exchange(facts); }
        self.facts.extend(std::mem::take(facts));
    }
    pub fn close(&mut self) { if let Some(channel) = self.comms.as_mut() { channel.close(); } }
    /// Finalizes the facts awaiting receipt from all other participants.
    pub fn finish(mut self) -> FactLSM<Forest<Terms>> {
        if let Some(channel) = self.comms { self.facts.extend(channel.complete()); }
        self.facts
    }
}

/// An optional list of non-empty columns.
///
/// The encoding is first the number of columns plus one, with zero indicating `None`.
/// The columns are then appended.
struct FactMessage { facts: Option<Vec<columnar::bytes::stash::Stash<Lists<Terms>, timely_bytes::arc::Bytes>>> }

use columnar::{Index, Len, bytes::{indexed, stash::Stash}};

impl Bytesable for FactMessage {
    fn from_bytes(mut bytes: timely_bytes::arc::Bytes) -> Self {
        let count: u64 = u64::from_be_bytes(bytes[..8].try_into().unwrap());
        bytes.extract_to(8);
        if count > 0 {
            let mut columns = Vec::with_capacity(count as usize - 1);
            for _ in 1 .. count {
                let stash: Stash<Lists<Terms>, timely_bytes::arc::Bytes> = Stash::try_from_bytes(bytes.clone()).unwrap();
                let length = stash.length_in_bytes();
                let _ = bytes.extract_to(length);
                columns.push(stash);
            }
            FactMessage { facts: Some(columns) }
        }
        else { FactMessage { facts: None } }
    }
    fn length_in_bytes(&self) -> usize {
        if let Some(columns) = self.facts.as_ref() { 8 + columns.iter().map(|c| indexed::length_in_bytes(&c.borrow())).sum::<usize>() }
        else { 8 }
    }
    fn into_bytes<W: ::std::io::Write>(&self, mut writer: &mut W) {
        if let Some(columns) = self.facts.as_ref() {
            let count: u64 = 1 + columns.len() as u64;
            writer.write_all(&count.to_be_bytes()).unwrap();
            for column in columns.iter() {
                indexed::write(&mut writer, &column.borrow()).unwrap();
            }
        }
        else { writer.write_all(&0u64.to_be_bytes()).unwrap(); }
    }
}
