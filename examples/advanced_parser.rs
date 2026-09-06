//! Advanced Parser Library - Type-safe DSL Engine
//!
//! This example demonstrates how to build a parser combinator library
//! using Rustica's Choice abstraction.

use rustica::datatypes::choice::Choice;
use rustica::prelude::*;
use std::fmt::{Debug, Display};
use std::rc::Rc;

/// Parse error with location information
#[derive(Clone, Debug, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
    pub expected: Option<String>,
    pub found: Option<String>,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Parse error at position {}: {}",
            self.position, self.message
        )?;
        if let Some(ref exp) = self.expected {
            write!(f, " (expected: {})", exp)?;
        }
        if let Some(ref found) = self.found {
            write!(f, " (found: {})", found)?;
        }
        Ok(())
    }
}

impl ParseError {
    pub fn new(message: impl Into<String>, position: usize) -> Self {
        ParseError {
            message: message.into(),
            position,
            expected: None,
            found: None,
        }
    }
}

type ParseFn<I, O> = Rc<dyn Fn(&[I]) -> Option<Choice<(O, &[I])>>>;

pub struct Parser<I, O>
where
    I: Clone + Debug,
    O: Clone + Debug,
{
    parse_fn: ParseFn<I, O>,
}

impl<I, O> Clone for Parser<I, O>
where
    I: Clone + Debug,
    O: Clone + Debug,
{
    fn clone(&self) -> Self {
        Parser {
            parse_fn: self.parse_fn.clone(),
        }
    }
}

impl<I, O> Parser<I, O>
where
    I: Clone + Debug + PartialEq + 'static,
    O: Clone + Debug + Send + Sync + 'static,
{
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&[I]) -> Option<Choice<(O, &[I])>> + 'static,
    {
        Parser {
            parse_fn: Rc::new(f),
        }
    }

    pub fn parse<'a>(&self, input: &'a [I]) -> Option<Choice<(O, &'a [I])>> {
        (self.parse_fn)(input)
    }

    pub fn or<P: Into<Parser<I, O>>>(self, other: P) -> Parser<I, O> {
        let other = other.into();
        Parser::new(move |input| match (self.parse(input), other.parse(input)) {
            (Some(a), Some(b)) => Some(a.combine(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        })
    }

    pub fn and_then<B, F>(self, f: F) -> Parser<I, B>
    where
        F: Fn(O) -> Parser<I, B> + 'static,
        B: Clone + Debug + Send + Sync + 'static,
    {
        Parser::new(move |input| {
            let results = self.parse(input)?;
            let mut all_results = Vec::new();
            for (result, remaining) in results.into_iter() {
                if let Some(next_choices) = f(result).parse(remaining) {
                    all_results.extend(next_choices);
                }
            }
            Choice::of_many(all_results)
        })
    }

    pub fn map<B, F>(self, f: F) -> Parser<I, B>
    where
        F: Fn(O) -> B + 'static,
        B: Clone + Debug + Send + Sync + 'static,
    {
        Parser::new(move |input| {
            let results = self.parse(input)?;
            let mapped = results.fmap(|(res, rem)| (f(res), rem));
            Some(mapped)
        })
    }

    pub fn many(self) -> Parser<I, Vec<O>> {
        Parser::new(move |input| {
            let mut results = Vec::new();
            let mut current_input = input;

            while let Some(choice) = self.parse(current_input) {
                let (result, remaining) = choice.into_iter().next().unwrap();
                results.push(result);
                current_input = remaining;
            }

            Some(Choice::single((results, current_input)))
        })
    }

    pub fn many1(self) -> Parser<I, Vec<O>> {
        let parser_clone = self.clone();
        self.and_then(move |first| {
            parser_clone.clone().many().map(move |mut rest| {
                let mut result = vec![first.clone()];
                result.append(&mut rest);
                result
            })
        })
    }

    pub fn optional(self) -> Parser<I, Option<O>> {
        Parser::new(move |input| match self.parse(input) {
            Some(choice) => {
                let (result, remaining) = choice.into_iter().next().unwrap();
                Some(Choice::single((Some(result), remaining)))
            },
            None => Some(Choice::single((None, input))),
        })
    }

    pub fn sep_by<S>(self, separator: Parser<I, S>) -> Parser<I, Vec<O>>
    where
        S: Clone + Debug + Send + Sync + 'static,
    {
        let parser_clone = self.clone();
        self.and_then(move |first| {
            let sep_clone = separator.clone();
            let parser_clone2 = parser_clone.clone();
            sep_clone
                .and_then(move |_| parser_clone2.clone())
                .many()
                .map(move |mut rest| {
                    let mut result = vec![first.clone()];
                    result.append(&mut rest);
                    result
                })
        })
        .or(Parser::new(|input| Some(Choice::single((vec![], input)))))
    }

    pub fn between<L, R, Open, Close>(
        open: Open, close: Close, content: Parser<I, O>,
    ) -> Parser<I, O>
    where
        Open: Into<Parser<I, L>>,
        Close: Into<Parser<I, R>>,
        L: Clone + Debug + Send + Sync + 'static,
        R: Clone + Debug + Send + Sync + 'static,
    {
        let open_parser = open.into();
        let close_parser = close.into();

        open_parser
            .and_then(move |_| content.clone())
            .and_then(move |result| close_parser.clone().map(move |_| result.clone()))
    }
}

pub fn item<I>(expected: I) -> Parser<I, I>
where
    I: Clone + Debug + PartialEq + Send + Sync + 'static,
{
    Parser::new(move |input: &[I]| {
        if let Some((first, rest)) = input.split_first() {
            if *first == expected {
                Some(Choice::single((first.clone(), rest)))
            } else {
                None
            }
        } else {
            None
        }
    })
}

pub fn satisfy<I, F>(predicate: F) -> Parser<I, I>
where
    I: Clone + Debug + PartialEq + Send + Sync + 'static,
    F: Fn(&I) -> bool + 'static,
{
    Parser::new(move |input: &[I]| {
        if let Some((first, rest)) = input.split_first() {
            if predicate(first) {
                Some(Choice::single((first.clone(), rest)))
            } else {
                None
            }
        } else {
            None
        }
    })
}

pub fn sequence<I>(expected: Vec<I>) -> Parser<I, Vec<I>>
where
    I: Clone + Debug + PartialEq + Send + Sync + 'static,
{
    Parser::new(move |input: &[I]| {
        if input.len() >= expected.len() && input[..expected.len()] == expected[..] {
            Some(Choice::single((expected.clone(), &input[expected.len()..])))
        } else {
            None
        }
    })
}

#[derive(Clone, Debug, PartialEq)]
pub enum SqlQuery {
    Select {
        columns: Vec<String>,
        table: String,
        where_clause: Option<WhereClause>,
    },
    Insert {
        table: String,
        values: Vec<String>,
    },
    Update {
        table: String,
        set_clause: String,
        where_clause: Option<WhereClause>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub struct WhereClause {
    pub conditions: Vec<Condition>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Condition {
    pub field: String,
    pub operator: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SelectClause {
    pub columns: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FromClause {
    pub table: String,
}

fn whitespace() -> Parser<char, Vec<char>> {
    satisfy(|c: &char| c.is_whitespace()).many()
}

fn word() -> Parser<char, String> {
    satisfy(|c: &char| c.is_alphanumeric() || *c == '_')
        .many1()
        .map(|chars| chars.into_iter().collect())
}

fn keyword(kw: &'static str) -> Parser<char, String> {
    Parser::new(move |input: &[char]| {
        if input.len() < kw.len() {
            return None;
        }

        let matches = kw
            .chars()
            .zip(input.iter())
            .all(|(expected, actual)| expected.eq_ignore_ascii_case(actual));

        if matches {
            Some(Choice::single((kw.to_string(), &input[kw.len()..])))
        } else {
            None
        }
    })
}

fn select_parser() -> Parser<char, SelectClause> {
    keyword("SELECT").and_then(|_| whitespace()).and_then(|_| {
        word()
            .and_then(|first_col| {
                item(',')
                    .and_then(|_| whitespace())
                    .and_then(|_| word())
                    .many()
                    .map(move |rest_cols| {
                        let mut columns = vec![first_col.clone()];
                        columns.extend(rest_cols);
                        SelectClause { columns }
                    })
            })
            .or(word().map(|col| SelectClause { columns: vec![col] }))
    })
}

fn from_parser() -> Parser<char, FromClause> {
    whitespace()
        .and_then(|_| keyword("FROM"))
        .and_then(|_| whitespace())
        .and_then(|_| word())
        .map(|table| FromClause { table })
}

fn operator_parser() -> Parser<char, String> {
    sequence(vec!['!', '='])
        .map(|_| "!=".to_string())
        .or(item('=').map(|_| "=".to_string()))
        .or(item('<').map(|_| "<".to_string()))
        .or(item('>').map(|_| ">".to_string()))
}

fn condition_parser() -> Parser<char, Condition> {
    word().and_then(|field| {
        let field_clone = field;
        whitespace()
            .and_then(|_| operator_parser())
            .and_then(move |operator| {
                let field_clone2 = field_clone.clone();
                let operator_clone = operator;
                whitespace()
                    .and_then(|_| word())
                    .map(move |value| Condition {
                        field: field_clone2.clone(),
                        operator: operator_clone.clone(),
                        value,
                    })
            })
    })
}

fn where_parser() -> Parser<char, WhereClause> {
    whitespace()
        .and_then(|_| keyword("WHERE"))
        .and_then(|_| whitespace())
        .and_then(|_| {
            condition_parser()
                .sep_by(
                    whitespace()
                        .and_then(|_| keyword("AND"))
                        .and_then(|_| whitespace()),
                )
                .map(|conditions| WhereClause { conditions })
        })
}

fn insert_parser() -> Parser<char, SqlQuery> {
    keyword("INSERT")
        .and_then(|_| whitespace())
        .and_then(|_| keyword("INTO"))
        .and_then(|_| whitespace())
        .and_then(|_| word())
        .and_then(|table| {
            whitespace()
                .and_then(|_| keyword("VALUES"))
                .and_then(|_| whitespace())
                .and_then(|_| word())
                .map(move |value| SqlQuery::Insert {
                    table: table.clone(),
                    values: vec![value],
                })
        })
}

fn update_parser() -> Parser<char, SqlQuery> {
    keyword("UPDATE")
        .and_then(|_| whitespace())
        .and_then(|_| word())
        .and_then(|table| {
            let table_clone = table;
            whitespace()
                .and_then(|_| keyword("SET"))
                .and_then(|_| whitespace())
                .and_then(|_| word())
                .and_then(move |set_clause| {
                    let table_clone2 = table_clone.clone();
                    let set_clause_clone = set_clause;
                    where_parser()
                        .optional()
                        .map(move |where_clause| SqlQuery::Update {
                            table: table_clone2.clone(),
                            set_clause: set_clause_clone.clone(),
                            where_clause,
                        })
                })
        })
}

pub fn sql_query_parser() -> Parser<char, SqlQuery> {
    select_parser()
        .and_then(|select_clause| {
            let columns_clone = select_clause.columns;
            from_parser().and_then(move |from_clause| {
                let columns_clone2 = columns_clone.clone();
                let table_clone = from_clause.table;
                where_parser()
                    .optional()
                    .map(move |where_clause| SqlQuery::Select {
                        columns: columns_clone2.clone(),
                        table: table_clone.clone(),
                        where_clause,
                    })
            })
        })
        .or(insert_parser())
        .or(update_parser())
}

pub fn parser_examples() {
    println!("=== Advanced Parser Library Examples ===\n");

    let input = ['h', 'e', 'l', 'l', 'o'];
    let parser = item('h');
    match parser.parse(&input).and_then(|c| c.into_iter().next()) {
        Some((result, remaining)) => {
            println!("   Parsed: {:?}, Remaining: {:?}", result, remaining);
        },
        None => println!("   Parse failed"),
    }

    let parser = item('x').or(item('h'));
    match parser.parse(&input).and_then(|c| c.into_iter().next()) {
        Some((result, remaining)) => {
            println!("   Parsed: {:?}, Remaining: {:?}", result, remaining);
        },
        None => println!("   Parse failed"),
    }

    let hello_parser = sequence(vec!['h', 'e', 'l', 'l', 'o']);
    match hello_parser
        .parse(&input)
        .and_then(|c| c.into_iter().next())
    {
        Some((result, remaining)) => {
            println!("   Parsed: {:?}, Remaining: {:?}", result, remaining);
        },
        None => println!("   Parse failed"),
    }
}

fn main() {
    parser_examples();
}
