//! Advanced Parser Library - Type-safe DSL Engine
//!
//! This example demonstrates how to build a sophisticated parser combinator library
//! using Rustica's functional programming abstractions. It showcases:
//!
//! - Parser combinators using Choice for alternatives
//! - Type-safe DSL construction with Applicative and Alternative
//! - SQL query parser as a practical DSL example
//! - Monadic composition for complex parsing logic

use rustica::datatypes::choice::Choice;
use rustica::traits::alternative::Alternative;
use std::fmt::Debug;

/// Core Parser type that represents a parsing function
///
/// A parser takes an input slice and returns a Choice of successful parses,
/// where each parse contains the result and remaining input.
pub struct Parser<I, O>
where
    I: Clone + Debug,
    O: Clone + Debug,
{
    parse_fn: std::rc::Rc<dyn Fn(&[I]) -> Choice<(O, &[I])>>,
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
    /// Create a new parser from a parsing function
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&[I]) -> Choice<(O, &[I])> + 'static,
    {
        Parser {
            parse_fn: std::rc::Rc::new(f),
        }
    }

    /// Run the parser on input
    pub fn parse<'a>(&self, input: &'a [I]) -> Choice<(O, &'a [I])> {
        (self.parse_fn)(input)
    }

    /// Alternative combinator - try this parser, if it fails, try the other
    pub fn or<P: Into<Parser<I, O>>>(self, other: P) -> Parser<I, O> {
        let other = other.into();
        Parser::new(move |input| {
            let first_result = self.parse(input);
            if first_result.is_empty() {
                other.parse(input)
            } else {
                first_result.alt(&other.parse(input))
            }
        })
    }

    /// Monadic bind - sequence parsers with dependent results
    pub fn and_then<B, F>(self, f: F) -> Parser<I, B>
    where
        F: Fn(O) -> Parser<I, B> + 'static,
        B: Clone + Debug + Send + Sync + 'static,
    {
        Parser::new(move |input| {
            let results = self.parse(input);
            let mut combined = Choice::new_empty();
            for (result, remaining) in results.into_iter() {
                let next_results = f(result).parse(remaining);
                combined = combined.alt(&next_results);
            }
            combined
        })
    }

    /// Applicative apply - apply a parser of functions to a parser of values
    pub fn apply<B, F>(func_parser: Parser<I, F>, value_parser: Parser<I, O>) -> Parser<I, B>
    where
        F: Fn(O) -> B + Clone + Debug + Send + Sync + 'static,
        B: Clone + Debug + Send + Sync + 'static,
    {
        Parser::new(move |input| {
            let mut combined = Choice::new_empty();
            for (func, remaining1) in func_parser.parse(input).into_iter() {
                for (value, remaining2) in value_parser.parse(remaining1).into_iter() {
                    combined = combined.alt(&Choice::new((func(value), remaining2), vec![]));
                }
            }
            combined
        })
    }

    /// Map over the result of a successful parse
    pub fn map<B, F>(self, f: F) -> Parser<I, B>
    where
        F: Fn(O) -> B + 'static,
        B: Clone + Debug + Send + Sync + 'static,
    {
        Parser::new(move |input| {
            let mut combined = Choice::new_empty();
            for (result, remaining) in self.parse(input).into_iter() {
                combined = combined.alt(&Choice::new((f(result), remaining), vec![]));
            }
            combined
        })
    }

    /// Parse zero or more occurrences
    pub fn many(self) -> Parser<I, Vec<O>> {
        Parser::new(move |input| {
            let mut results = Vec::new();
            let mut current_input = input;

            loop {
                match self.parse(current_input).into_iter().next() {
                    Some((result, remaining)) => {
                        results.push(result);
                        current_input = remaining;
                    },
                    None => break,
                }
            }

            Choice::new((results, current_input), vec![])
        })
    }

    /// Parse one or more occurrences
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

    /// Optional parser - succeeds with None if the parser fails
    pub fn optional(self) -> Parser<I, Option<O>> {
        Parser::new(move |input| match self.parse(input).into_iter().next() {
            Some((result, remaining)) => Choice::new((Some(result), remaining), vec![]),
            None => Choice::new((None, input), vec![]),
        })
    }
}

/// Basic parsers for common patterns

/// Parse a specific item
pub fn item<I>(expected: I) -> Parser<I, I>
where
    I: Clone + Debug + PartialEq + Send + Sync + 'static,
{
    Parser::new(move |input: &[I]| {
        if let Some((first, rest)) = input.split_first() {
            if *first == expected {
                Choice::new((first.clone(), rest), vec![])
            } else {
                Choice::new_empty()
            }
        } else {
            Choice::new_empty()
        }
    })
}

/// Parse any item that satisfies a predicate
pub fn satisfy<I, F>(predicate: F) -> Parser<I, I>
where
    I: Clone + Debug + PartialEq + Send + Sync + 'static,
    F: Fn(&I) -> bool + 'static,
{
    Parser::new(move |input: &[I]| {
        if let Some((first, rest)) = input.split_first() {
            if predicate(first) {
                Choice::new((first.clone(), rest), vec![])
            } else {
                Choice::new_empty()
            }
        } else {
            Choice::new_empty()
        }
    })
}

/// Parse a sequence of items
pub fn sequence<I>(expected: Vec<I>) -> Parser<I, Vec<I>>
where
    I: Clone + Debug + PartialEq + Send + Sync + 'static,
{
    Parser::new(move |input: &[I]| {
        if input.len() >= expected.len() && input[..expected.len()] == expected[..] {
            Choice::new((expected.clone(), &input[expected.len()..]), vec![])
        } else {
            Choice::new_empty()
        }
    })
}

// SQL DSL Example

#[derive(Clone, Debug, PartialEq)]
pub enum SqlQuery {
    Select { columns: Vec<String>, table: String },
    Insert { table: String, values: Vec<String> },
    Update { table: String, set_clause: String },
}

#[derive(Clone, Debug, PartialEq)]
pub struct SelectClause {
    pub columns: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FromClause {
    pub table: String,
}

/// Parse whitespace
fn whitespace() -> Parser<char, Vec<char>> {
    satisfy(|c: &char| c.is_whitespace()).many()
}

/// Parse a word (alphanumeric characters)
fn word() -> Parser<char, String> {
    satisfy(|c: &char| c.is_alphanumeric() || *c == '_')
        .many1()
        .map(|chars| chars.into_iter().collect())
}

/// Parse a keyword (case-insensitive)
fn keyword(kw: &'static str) -> Parser<char, String> {
    Parser::new(move |input: &[char]| {
        if input.len() < kw.len() {
            return Choice::new_empty();
        }

        let matches = kw
            .chars()
            .zip(input.iter())
            .all(|(expected, actual)| expected.eq_ignore_ascii_case(actual));

        if matches {
            Choice::new((kw.to_string(), &input[kw.len()..]), vec![])
        } else {
            Choice::new_empty()
        }
    })
}

/// Parse SELECT clause
fn select_parser() -> Parser<char, SelectClause> {
    word().and_then(|first_col| {
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
}

/// Parse FROM clause
fn from_parser() -> Parser<char, FromClause> {
    whitespace()
        .and_then(|_| keyword("FROM"))
        .and_then(|_| whitespace())
        .and_then(|_| word())
        .map(|table| FromClause { table })
}

/// Parse INSERT statement
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

/// Parse UPDATE statement
fn update_parser() -> Parser<char, SqlQuery> {
    keyword("UPDATE")
        .and_then(|_| whitespace())
        .and_then(|_| word())
        .and_then(|table| {
            whitespace()
                .and_then(|_| keyword("SET"))
                .and_then(|_| whitespace())
                .and_then(|_| word()) // Simplified: just parse one word for SET clause
                .map(move |set_clause| SqlQuery::Update {
                    table: table.clone(),
                    set_clause,
                })
        })
}

/// Main SQL query parser that combines all statement types
pub fn sql_query_parser() -> Parser<char, SqlQuery> {
    select_parser()
        .and_then(|select_clause| {
            from_parser().map(move |from_clause| SqlQuery::Select {
                columns: select_clause.columns.clone(),
                table: from_clause.table,
            })
        })
        .or(insert_parser())
        .or(update_parser())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_parsers() {
        let input = ['a', 'b', 'c'];

        // Test item parser
        let parser = item('a');
        let result = parser.parse(&input);
        assert!(!result.is_empty());

        // Test sequence parser
        let seq_parser = sequence(vec!['a', 'b']);
        let seq_result = seq_parser.parse(&input);
        assert!(!seq_result.is_empty());
    }

    #[test]
    fn test_combinator_or() {
        let input = ['b'];
        let parser = item('a').or(item('b'));
        let result = parser.parse(&input);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_sql_select_parser() {
        let input: Vec<char> = "SELECT name FROM users".chars().collect();
        let parser = sql_query_parser();
        let result = parser.parse(&input);

        if let Some((query, _)) = result.into_iter().next() {
            match query {
                SqlQuery::Select { columns, table } => {
                    assert_eq!(columns, vec!["name"]);
                    assert_eq!(table, "users");
                },
                _ => panic!("Expected SELECT query"),
            }
        } else {
            panic!("Parser failed");
        }
    }

    #[test]
    fn test_many_combinator() {
        let input = ['a', 'a', 'a', 'b'];
        let parser = item('a').many();
        let result = parser.parse(&input);

        if let Some((results, remaining)) = result.into_iter().next() {
            assert_eq!(results.len(), 3);
            assert_eq!(remaining, &['b']);
        } else {
            panic!("Many parser failed");
        }
    }
}

/// Example usage demonstrating the parser library
pub fn parser_examples() {
    println!("=== Advanced Parser Library Examples ===\n");

    // Example 1: Basic item parsing
    println!("1. Basic Item Parsing:");
    let input = ['h', 'e', 'l', 'l', 'o'];
    let parser = item('h');
    match parser.parse(&input).into_iter().next() {
        Some((result, remaining)) => {
            println!("   Parsed: {:?}, Remaining: {:?}", result, remaining);
        },
        None => println!("   Parse failed"),
    }

    // Example 2: Alternative parsing
    println!("\n2. Alternative Parsing (OR combinator):");
    let parser = item('x').or(item('h'));
    match parser.parse(&input).into_iter().next() {
        Some((result, remaining)) => {
            println!("   Parsed: {:?}, Remaining: {:?}", result, remaining);
        },
        None => println!("   Parse failed"),
    }

    // Example 3: Sequence parsing
    println!("\n3. Sequence Parsing:");
    let hello_parser = sequence(vec!['h', 'e', 'l', 'l', 'o']);
    match hello_parser.parse(&input).into_iter().next() {
        Some((result, remaining)) => {
            println!("   Parsed: {:?}, Remaining: {:?}", result, remaining);
        },
        None => println!("   Parse failed"),
    }

    // Example 4: SQL Query Parsing
    println!("\n4. SQL Query Parsing:");
    let queries = vec![
        "SELECT name FROM users",
        "SELECT id, email FROM customers",
        "INSERT INTO users VALUES data",
        "UPDATE users SET active",
    ];

    for query in queries {
        println!("   Query: {}", query);
        let input: Vec<char> = query.chars().collect();
        let parser = sql_query_parser();

        match parser.parse(&input).into_iter().next() {
            Some((parsed_query, _)) => {
                println!("   Result: {:?}", parsed_query);
            },
            None => println!("   Parse failed"),
        }
        println!();
    }

    // Example 5: Many combinator
    println!("5. Many Combinator (parse repeated elements):");
    let repeated_input = ['a', 'a', 'a', 'b', 'c'];
    let many_a_parser = item('a').many();
    match many_a_parser.parse(&repeated_input).into_iter().next() {
        Some((results, remaining)) => {
            println!(
                "   Parsed {} 'a's, Remaining: {:?}",
                results.len(),
                remaining
            );
        },
        None => println!("   Parse failed"),
    }

    println!("\n=== Parser Library Demo Complete ===");
}

fn main() {
    parser_examples();
}
