//! Methods and types to support parsing Datalog rules.

use std::iter::Peekable;
use crate::types::{Rule, Atom, Term};

/// Attempt to parse `text` as a sequence of Datalog rules.
pub fn datalog(text: &str) -> Option<Vec<Rule>> {
    parse(tokenize(text)?)
}

/// Text translated to a sequence of tokens.
#[derive(Debug, PartialEq)]
enum Token {
    Period,
    Comma,
    LParen,
    RParen,
    Turnstile,
    Question,
    Text(String),
}

fn tokenize(text: &str) -> Option<Vec<Token>> {

    let mut text = text.replace(":-", "←");
    text.retain(|c| !c.is_whitespace());

    let mut result = Vec::new();

    let pattern = ['.', ',', '(', ')', '←', '?'];
    for token in text.split_inclusive(&pattern) {
        let mut split = token.split(&pattern);
        let prev = split.next().unwrap();
        if !prev.is_empty() {
            result.push(Token::Text(prev.to_owned()));
        }
        let next = token.chars().next_back().unwrap();
        result.push (
            match next {
                '.' => Token::Period,
                ',' => Token::Comma,
                '(' => Token::LParen,
                ')' => Token::RParen,
                '←' => Token::Turnstile,
                '?' => Token::Question,
                _ => { None? }
            }
        );
    }

    Some(result)
}

fn parse(tokens: Vec<Token>) -> Option<Vec<Rule>> {
    let mut tokens = tokens.into_iter().peekable();
    let mut rules = Vec::new();
    while tokens.len() > 0 {
        rules.push(parse_rule(&mut tokens)?);
    }

    Some(rules)
}

fn parse_rule<I: Iterator<Item=Token>>(tokens: &mut Peekable<I>) -> Option<Rule> {
    let mut head = Vec::new();
    while &Token::Turnstile != tokens.peek()? {
        if &Token::Comma == tokens.peek()? { tokens.next(); }
        head.push(parse_atom(tokens)?);
    }
    let Token::Turnstile = tokens.next()? else { None? };
    let mut body = Vec::new();
    while &Token::Period != tokens.peek()? {
        if &Token::Comma == tokens.peek()? { tokens.next(); }
        body.push(parse_atom(tokens)?);
    }
    let Token::Period = tokens.next()? else { None? };

    Some(Rule { head, body })
}

fn parse_atom<I: Iterator<Item=Token>>(tokens: &mut Peekable<I>) -> Option<Atom> {
    let Token::Text(name) = tokens.next()? else { None? };
    let Token::LParen     = tokens.next()? else { None? };

    let mut terms = Vec::new();
    terms.push(parse_term(tokens)?);
    while let Token::Comma = tokens.peek()? {
        tokens.next();
        terms.push(parse_term(tokens)?);
    }
    let Token::RParen     = tokens.next()? else { None? };

    // Names starting with an `!` indicate an antijoin, which suppresses records that match.
    let (anti, name) = name.strip_prefix("!").map(|n| (true, n)).unwrap_or((false, name.as_str()));
    if anti { panic!("antijoins ('!') not correctly supported yet"); }

    Some(Atom { name: name.to_owned(), anti, terms })
}

fn parse_term<I: Iterator<Item=Token>>(tokens: &mut Peekable<I>) -> Option<Term> {
    if let Token::Question = tokens.peek()? {
        tokens.next()?;
        let Token::Text(term) = tokens.next()? else { None? };
        Some(Term::Var(term.clone()))
    }
    else {
        let Token::Text(term) = tokens.next()? else { None? };
        Some(Term::Lit(term.clone()))
    }
}
