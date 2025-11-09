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

    pub fn with_expected(mut self, expected: impl Into<String>) -> Self {
        self.expected = Some(expected.into());
        self
    }

    pub fn with_found(mut self, found: impl Into<String>) -> Self {
        self.found = Some(found.into());
        self
    }
}

/// Parse result with error information
pub type ParseResult<I, O> = Result<(O, &'static [I], usize), ParseError>;

/// Core Parser type that represents a parsing function
///
/// A parser takes an input slice and returns a Choice of successful parses,
/// where each parse contains the result and remaining input.
pub struct Parser<I, O>
where
    I: Clone + Debug,
    O: Clone + Debug,
{
    parse_fn: Rc<dyn Fn(&[I]) -> Choice<(O, &[I])>>,
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
            parse_fn: Rc::new(f),
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

    /// Parse elements separated by a separator
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
        .or(Parser::new(|input| Choice::new((vec![], input), vec![])))
    }

    /// Parse elements separated by a separator (at least one element)
    pub fn sep_by1<S>(self, separator: Parser<I, S>) -> Parser<I, Vec<O>>
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
    }

    /// Parse something between two delimiters
    pub fn between<L, R, LO, RO>(
        left: Parser<I, LO>, right: Parser<I, RO>, parser: Parser<I, O>,
    ) -> Parser<I, O>
    where
        LO: Clone + Debug + Send + Sync + 'static,
        RO: Clone + Debug + Send + Sync + 'static,
    {
        left.and_then(move |_| {
            let parser_clone = parser.clone();
            let right_clone = right.clone();
            parser_clone.and_then(move |result| right_clone.clone().map(move |_| result.clone()))
        })
    }

    /// Left-associative chain of binary operations
    pub fn chainl1<F>(self, op: Parser<I, F>) -> Parser<I, O>
    where
        F: Fn(O, O) -> O + Clone + Debug + Send + Sync + 'static,
    {
        let parser_clone = self.clone();
        self.and_then(move |first| {
            let op_clone = op.clone();
            let parser_clone2 = parser_clone.clone();
            op_clone
                .and_then(move |f| parser_clone2.clone().map(move |val| (f.clone(), val)))
                .many()
                .map(move |ops| {
                    ops.into_iter()
                        .fold(first.clone(), |acc, (f, val)| f(acc, val))
                })
        })
    }

    /// Skip this parser (discard result)
    pub fn skip(self) -> Parser<I, ()> {
        self.map(|_| ())
    }

    /// Label a parser for better error messages
    pub fn label(self, _label: &'static str) -> Parser<I, O> {
        // For now, just return self; can enhance with error tracking later
        self
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

/// Parse FROM clause
fn from_parser() -> Parser<char, FromClause> {
    whitespace()
        .and_then(|_| keyword("FROM"))
        .and_then(|_| whitespace())
        .and_then(|_| word())
        .map(|table| FromClause { table })
}

/// Parse operator (=, !=, <, >, etc.)
fn operator_parser() -> Parser<char, String> {
    sequence(vec!['!', '='])
        .map(|_| "!=".to_string())
        .or(item('=').map(|_| "=".to_string()))
        .or(item('<').map(|_| "<".to_string()))
        .or(item('>').map(|_| ">".to_string()))
}

/// Parse a single condition (e.g., "age > 18")
fn condition_parser() -> Parser<char, Condition> {
    word().and_then(|field| {
        let field_clone = field.clone();
        whitespace()
            .and_then(|_| operator_parser())
            .and_then(move |operator| {
                let field_clone2 = field_clone.clone();
                let operator_clone = operator.clone();
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

/// Parse WHERE clause
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
            let table_clone = table.clone();
            whitespace()
                .and_then(|_| keyword("SET"))
                .and_then(|_| whitespace())
                .and_then(|_| word())
                .and_then(move |set_clause| {
                    let table_clone2 = table_clone.clone();
                    let set_clause_clone = set_clause.clone();
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

/// Main SQL query parser that combines all statement types
pub fn sql_query_parser() -> Parser<char, SqlQuery> {
    select_parser()
        .and_then(|select_clause| {
            let columns_clone = select_clause.columns.clone();
            from_parser().and_then(move |from_clause| {
                let columns_clone2 = columns_clone.clone();
                let table_clone = from_clause.table.clone();
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
        "SELECT name FROM users WHERE age > 18",
        "SELECT email FROM customers WHERE active = 1 AND verified = 1",
        "INSERT INTO users VALUES data",
        "UPDATE users SET active",
        "UPDATE users SET status WHERE id = 42",
    ];

    for query in queries {
        println!("   Query: {}", query);
        let input: Vec<char> = query.chars().collect();
        let parser = sql_query_parser();

        match parser.parse(&input).into_iter().next() {
            Some((parsed_query, _)) => {
                println!("   Result: {:#?}", parsed_query);
            },
            None => println!("   Parse failed"),
        }
        println!();
    }

    // Example 5: New Combinators
    println!("5. Advanced Combinators:");

    // sep_by example
    println!("   a) sep_by - Parse comma-separated words:");
    let csv_input: Vec<char> = "apple,banana,cherry".chars().collect();
    let csv_parser = word().sep_by(item(','));
    match csv_parser.parse(&csv_input).into_iter().next() {
        Some((words, remaining)) => {
            println!(
                "      Parsed words: {:?}, Remaining: {:?}",
                words, remaining
            );
        },
        None => println!("      Parse failed"),
    }

    // between example
    println!("\n   b) between - Parse quoted string:");
    let quoted_input: Vec<char> = "\"hello\"".chars().collect();
    let quoted_parser = Parser::<char, String>::between::<char, char, char, char>(
        item('"'),
        item('"'),
        satisfy(|c: &char| *c != '"')
            .many()
            .map(|chars: Vec<char>| chars.into_iter().collect::<String>()),
    );
    match quoted_parser.parse(&quoted_input).into_iter().next() {
        Some((text, remaining)) => {
            println!("      Parsed text: {:?}, Remaining: {:?}", text, remaining);
        },
        None => println!("      Parse failed"),
    }

    // Example 6: Many combinator
    println!("\n6. Many Combinator (parse repeated elements):");
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
