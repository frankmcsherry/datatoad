use std::rc::Rc;
use std::cell::RefCell;

use timely_communication::{Allocate, allocator::Generic, Bytesable};
use crate::facts::{FactLSM, Forest, Lists, Terms};
use crate::facts::trie::Layer;

#[derive(Default)]
pub struct Comms {
    /// If set, communication infrastructure.
    pub ether: Option<Rc<RefCell<Generic>>>,
    /// An incrementing channel identifier.
    count: usize,
}

impl Comms {

    pub fn index(&self) -> usize { self.ether.as_ref().map(|e| e.borrow().index()).unwrap_or(0) }
    pub fn peers(&self) -> usize { self.ether.as_ref().map(|e| e.borrow().peers()).unwrap_or(1) }

    pub fn next_id(&self) -> usize { self.count }

    pub fn conduit(&mut self) -> Conduit {
        let comms = self.ether.as_mut().map(|comms| {
            let (sends, recv) = comms.borrow_mut().allocate(self.count);
            self.count += 1;
            let count = sends.len();
            Channel { comms: comms.clone(), sends, recv, count }
        });
        Conduit { comms, facts: FactLSM::default() }
    }

    /// Commits a bit, and returns the union across all workers.
    pub fn any(&mut self, bit: bool) -> bool {
        let mut facts = FactLSM::default();
        if bit { facts.extend([vec![].try_into().unwrap()]); }
        self.broadcast(&mut facts);
        facts.flatten().is_some()
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
                while let Some(message) = receiver.recv() { if let Some(fact) = message.facts { facts.push(fact.into_iter().map(|l| std::rc::Rc::new(Layer { list: l })).collect::<Vec<_>>().try_into().unwrap()); } countdown -= 1; }
                comms.release();
            }
        }
    }

    /// Exchanges facts among all workers.
    pub fn exchange(&mut self, facts: &mut FactLSM<Forest<Terms>>) {
        let mut conduit = self.conduit();
        conduit.extend(facts);
        *facts = conduit.finish();
    }
}

impl From<Generic> for Comms {
    fn from(comm: Generic) -> Self { Self { ether: Some(Rc::new(RefCell::new(comm))), count: 0 } }
}

use timely_communication::{Push, Pull};

pub struct Channel {
    comms: Rc<RefCell<Generic>>,
    sends: Vec<Box<dyn Push<FactMessage>>>,
    recv: Box<dyn Pull<FactMessage>>,
    count: usize,
}

impl Channel {
    /// Extracts all remaining facts
    fn complete(mut self) -> FactLSM<Forest<Terms>> {
        for sender in self.sends.iter_mut() { sender.send(FactMessage { facts: None } ); }
        let mut facts = FactLSM::default();
        while self.count > 0 { let mut temp = FactLSM::default(); self.exchange(&mut temp); facts.extend(temp); }
        facts
    }
    /// Exchanges facts with other participants, drawing from and refilling `facts`.
    fn exchange(&mut self, facts: &mut FactLSM<Forest<Terms>>) {

        let mut comms = self.comms.borrow_mut();

        // TODO: put self-sends back in to `facts`.
        if let Some(facts) = facts.flatten() {
            let mut bools: std::collections::VecDeque<bool> = Default::default();
            for (index, sender) in self.sends.iter_mut().enumerate() {
                bools.extend((0 .. facts.layer(0).list.values.len()).map(|i| (*facts.layer(0).list.values.borrow().get(i).as_slice().last().unwrap() as usize) % comms.peers() == index));
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
                facts.push(fact.into_iter().map(|l| std::rc::Rc::new(Layer { list: l })).collect::<Vec<_>>().try_into().unwrap());
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
}

impl Conduit {
    /// Supplies facts to the conduit, which are exchanged and then collected.
    pub fn extend(&mut self, facts: &mut FactLSM<Forest<Terms>>) {
        if let Some(channel) = self.comms.as_mut() { channel.exchange(facts); }
        self.facts.extend(std::mem::take(facts));
    }
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
struct FactMessage { facts: Option<Vec<Lists<Terms>>> }

use columnar::{Borrow, Container, Index, Len, bytes::{EncodeDecode, Indexed, stash::Stash}};

impl Bytesable for FactMessage {
    fn from_bytes(mut bytes: timely_bytes::arc::Bytes) -> Self {
        let count: u64 = u64::from_be_bytes(bytes[..8].try_into().unwrap());
        bytes.extract_to(8);
        if count > 0 {
            let mut columns = Vec::with_capacity(count as usize - 1);
            for _ in 1 .. count {
                let stash: Stash<Lists<Terms>, timely_bytes::arc::Bytes> = bytes.clone().into();
                let length = Indexed::length_in_bytes(&stash.borrow());
                let _ = bytes.extract_to(length);
                let mut column: Lists<Terms> = Default::default();
                column.extend_from_self(stash.borrow(), 0 .. stash.len());
                columns.push(column);
            }
            FactMessage { facts: Some(columns) }
        }
        else { FactMessage { facts: None } }
    }
    fn length_in_bytes(&self) -> usize {
        if let Some(columns) = self.facts.as_ref() { 8 + columns.iter().map(|c| Indexed::length_in_bytes(&c.borrow())).sum::<usize>() }
        else { 8 }
    }
    fn into_bytes<W: ::std::io::Write>(&self, mut writer: &mut W) {
        if let Some(columns) = self.facts.as_ref() {
            let count: u64 = 1 + columns.len() as u64;
            writer.write_all(&count.to_be_bytes()).unwrap();
            for column in columns.iter() {
                Indexed::write(&mut writer, &column.borrow()).unwrap();
            }
        }
        else { writer.write_all(&0u64.to_be_bytes()).unwrap(); }
    }
}
