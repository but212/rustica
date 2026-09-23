//! Flagship Example: Functional SQL Engine & Combinators
//!
//! Synthesizes Rustica's core functional abstractions into an end-to-end SQL pipeline:
//! - `Choice`: Backtracking parser combinators with progress guarantees and branch disambiguation.
//! - `ParseError`: Location-aware syntax error diagnostics.
//! - `Parser::between` & `token`: Whitespace-insensitive delimited tuple parsing.
//! - `Prism`: Sum-type traversal for query AST variants (`Select`, `Insert`).
//! - `Validated`: Multi-error accumulating schema and type validation.
//! - `Lens`: Immutable query transformation with structural sharing.
//! - `TryProgram` / `TryHandler`: Algebraic query execution with automatic short-circuiting.
//! - `ContextError`: Contextual error tracing across pipeline boundaries.

use rustica::datatypes::choice::Choice;
use rustica::datatypes::lens::Lens;
use rustica::datatypes::operational::{Command, TryHandler, TryProgram};
use rustica::datatypes::prism::Prism;
use rustica::datatypes::validated::Validated;
use rustica::error::{ContextError, with_context_result};
use rustica::traits::semigroup::Semigroup;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::sync::Arc;

// ============================================================================
// 1. Parser Combinator Core (Choice, ParseError, between, token)
// ============================================================================

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
        if let Some(exp) = &self.expected {
            write!(f, " (expected: {})", exp)?;
        }
        if let Some(found) = &self.found {
            write!(f, " (found: '{}')", found)?;
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

type ParseFn<I, O> = Arc<dyn Fn(&[I]) -> Option<Choice<(O, &[I])>> + Send + Sync>;

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
            parse_fn: Arc::clone(&self.parse_fn),
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
        F: Fn(&[I]) -> Option<Choice<(O, &[I])>> + Send + Sync + 'static,
    {
        Parser {
            parse_fn: Arc::new(f),
        }
    }

    pub fn parse<'a>(&self, input: &'a [I]) -> Option<Choice<(O, &'a [I])>> {
        (self.parse_fn)(input)
    }

    /// Parses input completely, returning `ParseError` on syntax error or unconsumed tokens.
    ///
    /// Disambiguation Policy:
    /// 1. Prioritizes branches that fully consumed input (`remaining.is_empty()`).
    /// 2. If no complete match exists, selects the longest-match branch for error reporting.
    pub fn parse_complete(&self, input: &[I]) -> Result<O, ParseError>
    where
        I: Display,
    {
        match self.parse(input) {
            Some(choice) => {
                let branches: Vec<(O, &[I])> = choice.into_iter().collect();

                // 1. Prioritize complete match
                if let Some((complete_result, _)) = branches.iter().find(|(_, rem)| rem.is_empty())
                {
                    return Ok(complete_result.clone());
                }

                // 2. Fall back to longest match for error reporting
                let (_, best_rem) = branches.iter().min_by_key(|(_, rem)| rem.len()).unwrap();

                let pos = input.len() - best_rem.len();
                let found_sample: String = best_rem.iter().take(5).map(|c| c.to_string()).collect();
                Err(ParseError::new("Unexpected trailing tokens", pos)
                    .with_expected("End of input")
                    .with_found(found_sample))
            },
            None => Err(ParseError::new(
                "Syntax error: input failed to match grammar",
                0,
            )),
        }
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
        F: Fn(O) -> Parser<I, B> + Send + Sync + 'static,
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
        F: Fn(O) -> B + Send + Sync + 'static,
        B: Clone + Debug + Send + Sync + 'static,
    {
        Parser::new(move |input| {
            let results = self.parse(input)?;
            let mapped = results.map(|(res, rem)| (f(res), rem));
            Some(mapped)
        })
    }

    /// Greedily parses zero or more occurrences using a deterministic Kleene-star policy.
    ///
    /// Commits to the first match per iteration to avoid exponential branch explosion (`O(k^n)`).
    /// Full alternative exploration is preserved in `or()`, `and_then()`, and `parse_complete()`.
    /// Guaranteed to terminate if an iteration consumes zero tokens.
    pub fn many(self) -> Parser<I, Vec<O>> {
        Parser::new(move |input| {
            let mut results = Vec::new();
            let mut current_input = input;

            while let Some(choice) = self.parse(current_input) {
                let (result, remaining) = choice.into_iter().next().unwrap();
                if remaining.len() == current_input.len() {
                    // Progress check: break immediately to prevent infinite loop on zero-width match
                    break;
                }
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

    /// Parses elements separated by a delimiter without spurious empty choices on match.
    pub fn sep_by<S>(self, separator: Parser<I, S>) -> Parser<I, Vec<O>>
    where
        S: Clone + Debug + Send + Sync + 'static,
    {
        let parser_clone = self.clone();
        let parsed = self.and_then(move |first| {
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
        });

        Parser::new(move |input| match parsed.parse(input) {
            Some(choice) => Some(choice),
            None => Some(Choice::single((vec![], input))),
        })
    }

    /// Parses content enclosed by open and close delimiters.
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
    F: Fn(&I) -> bool + Send + Sync + 'static,
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

// ============================================================================
// 2. Lexer Utilities & SQL Parser Implementation
// ============================================================================

pub const RESERVED_KEYWORDS: &[&str] = &[
    "SELECT", "FROM", "WHERE", "INSERT", "INTO", "VALUES", "AND", "OR",
];

fn whitespace() -> Parser<char, Vec<char>> {
    satisfy(|c: &char| c.is_whitespace()).many()
}

/// Lexeme wrapper: absorbs preceding and trailing whitespace around a token.
pub fn token<O: Clone + Debug + Send + Sync + 'static>(p: Parser<char, O>) -> Parser<char, O> {
    whitespace()
        .and_then(move |_| p.clone())
        .and_then(|res| whitespace().map(move |_| res.clone()))
}

fn word() -> Parser<char, String> {
    satisfy(|c: &char| c.is_alphanumeric() || *c == '_')
        .many1()
        .map(|chars| chars.into_iter().collect())
}

/// Parses an identifier, rejecting reserved SQL keywords.
fn identifier() -> Parser<char, String> {
    token(Parser::new(|input| {
        let choice = word().parse(input)?;
        let (w, rem) = choice.into_iter().next().unwrap();
        if RESERVED_KEYWORDS
            .iter()
            .any(|kw| kw.eq_ignore_ascii_case(&w))
        {
            None
        } else {
            Some(Choice::single((w, rem)))
        }
    }))
}

fn keyword(kw: &'static str) -> Parser<char, String> {
    token(Parser::new(move |input: &[char]| {
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
    }))
}

fn operator_parser() -> Parser<char, String> {
    token(
        sequence(vec!['!', '='])
            .map(|_| "!=".to_string())
            .or(item('=').map(|_| "=".to_string()))
            .or(item('<').map(|_| "<".to_string()))
            .or(item('>').map(|_| ">".to_string())),
    )
}

#[derive(Clone, Debug, PartialEq)]
pub enum SqlQuery {
    Select(SelectStatement),
    Insert(InsertStatement),
}

#[derive(Clone, Debug, PartialEq)]
pub struct SelectStatement {
    pub columns: Vec<String>,
    pub table: String,
    pub where_clause: Option<Condition>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct InsertStatement {
    pub table: String,
    pub values: Vec<String>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Condition {
    pub field: String,
    pub operator: String,
    pub value: String,
}

fn condition_parser() -> Parser<char, Condition> {
    identifier().and_then(|field| {
        let field_clone = field;
        operator_parser().and_then(move |operator| {
            let field_clone2 = field_clone.clone();
            let operator_clone = operator;
            identifier().map(move |value| Condition {
                field: field_clone2.clone(),
                operator: operator_clone.clone(),
                value,
            })
        })
    })
}

fn where_parser() -> Parser<char, Condition> {
    keyword("WHERE").and_then(|_| condition_parser())
}

pub fn select_query_parser() -> Parser<char, SelectStatement> {
    keyword("SELECT").and_then(|_| {
        identifier().sep_by(token(item(','))).and_then(|columns| {
            keyword("FROM")
                .and_then(|_| identifier())
                .and_then(move |table| {
                    let columns_clone = columns.clone();
                    where_parser()
                        .optional()
                        .map(move |where_clause| SelectStatement {
                            columns: columns_clone.clone(),
                            table: table.clone(),
                            where_clause,
                        })
                })
        })
    })
}

pub fn insert_query_parser() -> Parser<char, InsertStatement> {
    keyword("INSERT")
        .and_then(|_| keyword("INTO"))
        .and_then(|_| identifier())
        .and_then(|table| {
            keyword("VALUES")
                .and_then(|_| {
                    let values_parser = identifier().sep_by(token(item(',')));
                    Parser::between(token(item('(')), token(item(')')), values_parser)
                })
                .map(move |values| InsertStatement {
                    table: table.clone(),
                    values,
                })
        })
}

pub fn sql_parser() -> Parser<char, SqlQuery> {
    select_query_parser()
        .map(SqlQuery::Select)
        .or(insert_query_parser().map(SqlQuery::Insert))
}

// ============================================================================
// 3. Prism: Sum-Type Traversal for AST Statements
// ============================================================================

pub const fn select_query_prism() -> Prism<
    SqlQuery,
    SelectStatement,
    impl Fn(&SqlQuery) -> Option<SelectStatement>,
    impl Fn(SelectStatement) -> SqlQuery,
> {
    Prism::new(
        |q: &SqlQuery| match q {
            SqlQuery::Select(s) => Some(s.clone()),
            _ => None,
        },
        SqlQuery::Select,
    )
}

pub const fn insert_query_prism() -> Prism<
    SqlQuery,
    InsertStatement,
    impl Fn(&SqlQuery) -> Option<InsertStatement>,
    impl Fn(InsertStatement) -> SqlQuery,
> {
    Prism::new(
        |q: &SqlQuery| match q {
            SqlQuery::Insert(i) => Some(i.clone()),
            _ => None,
        },
        SqlQuery::Insert,
    )
}

// ============================================================================
// 4. Validated: Multi-Error Accumulating Schema & Type Validation
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DataType {
    Int,
    Text,
}

#[derive(Clone, Debug)]
pub struct ColumnSchema {
    pub name: String,
    pub data_type: DataType,
}

#[derive(Clone, Debug)]
pub struct TableSchema {
    pub name: String,
    pub columns: Vec<ColumnSchema>,
}

#[derive(Clone, Debug)]
pub struct DatabaseSchema {
    pub tables: Vec<TableSchema>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CheckedSelect {
    pub table: String,
    pub columns: Vec<String>,
    pub where_clause: Option<Condition>,
}

pub fn validate_select_query(
    stmt: &SelectStatement, schema: &DatabaseSchema,
) -> Validated<CheckedSelect, String> {
    let table_schema = schema.tables.iter().find(|t| t.name == stmt.table);

    // Rule 1: Table existence
    let valid_table = match table_schema {
        Some(t) => Validated::valid(t.clone()),
        None => Validated::invalid(format!("Unknown table '{}'", stmt.table)),
    };

    // Rule 2: Column existence
    let valid_columns = match table_schema {
        Some(t) => {
            let mut errors = Vec::new();
            for col in &stmt.columns {
                if !t.columns.iter().any(|c| c.name == *col) {
                    errors.push(format!(
                        "Column '{}' does not exist in table '{}'",
                        col, stmt.table
                    ));
                }
            }
            if errors.is_empty() {
                Validated::valid(stmt.columns.clone())
            } else {
                Validated::invalid_many(errors)
            }
        },
        None => Validated::valid(stmt.columns.clone()), // Table check already reported
    };

    // Rule 3: Where clause syntax and type compatibility
    let valid_where = match (&stmt.where_clause, table_schema) {
        (Some(cond), Some(t)) => {
            let mut errors = Vec::new();
            let col_def = t.columns.iter().find(|c| c.name == cond.field);

            match col_def {
                Some(col) => {
                    // Check operator support for column type
                    if ["<", ">"].contains(&cond.operator.as_str()) {
                        if col.data_type != DataType::Int {
                            errors.push(format!(
                                "Relational operator '{}' cannot be applied to text column '{}'",
                                cond.operator, cond.field
                            ));
                        }
                        if cond.value.parse::<i64>().is_err() {
                            errors.push(format!(
                                "Invalid integer literal '{}' for numeric comparison on column '{}'",
                                cond.value, cond.field
                            ));
                        }
                    } else if !["=", "!="].contains(&cond.operator.as_str()) {
                        errors.push(format!("Unsupported operator '{}'", cond.operator));
                    }
                },
                None => {
                    errors.push(format!(
                        "WHERE condition field '{}' does not exist in table '{}'",
                        cond.field, stmt.table
                    ));
                },
            }

            if errors.is_empty() {
                Validated::valid(Some(cond.clone()))
            } else {
                Validated::invalid_many(errors)
            }
        },
        (Some(cond), None) => {
            // Validate independent operator validity when table is unknown
            if !["=", "!=", "<", ">"].contains(&cond.operator.as_str()) {
                Validated::invalid(format!("Unsupported operator '{}'", cond.operator))
            } else {
                Validated::valid(Some(cond.clone()))
            }
        },
        (None, _) => Validated::valid(None),
    };

    valid_table.zip_with3(valid_columns, valid_where, |tbl, cols, where_cl| {
        CheckedSelect {
            table: tbl.name,
            columns: cols,
            where_clause: where_cl,
        }
    })
}

// ============================================================================
// 5. Lens: Structural Query & Schema Accessors
// ============================================================================

#[allow(clippy::type_complexity)]
pub const fn select_columns_lens() -> Lens<
    SelectStatement,
    Vec<String>,
    impl Fn(&SelectStatement) -> Vec<String>,
    impl Fn(SelectStatement, Vec<String>) -> SelectStatement,
> {
    Lens::new(
        |s: &SelectStatement| s.columns.clone(),
        |s, columns| SelectStatement { columns, ..s },
    )
}

#[allow(clippy::type_complexity)]
pub const fn select_table_lens() -> Lens<
    SelectStatement,
    String,
    impl Fn(&SelectStatement) -> String,
    impl Fn(SelectStatement, String) -> SelectStatement,
> {
    Lens::new(
        |s: &SelectStatement| s.table.clone(),
        |s, table| SelectStatement { table, ..s },
    )
}

// ============================================================================
// 6. Operational Monad: Pure Algebraic Fallible Execution (TryProgram / TryHandler)
// ============================================================================

pub type Row = HashMap<String, String>;

#[derive(Debug, Clone)]
pub struct ScanTable {
    pub table: String,
}

impl Command for ScanTable {
    type Output = Vec<Row>;
}

#[derive(Debug, Clone)]
pub struct FilterRows {
    pub rows: Vec<Row>,
    pub condition: Option<Condition>,
}

impl Command for FilterRows {
    type Output = Vec<Row>;
}

#[derive(Debug, Clone)]
pub struct ProjectColumns {
    pub rows: Vec<Row>,
    pub columns: Vec<String>,
}

impl Command for ProjectColumns {
    type Output = Vec<Row>;
}

pub struct InMemoryDb {
    pub tables: HashMap<String, Vec<Row>>,
}

impl TryHandler<ScanTable, &'static str> for InMemoryDb {
    fn try_handle(&mut self, cmd: ScanTable) -> Result<Vec<Row>, &'static str> {
        self.tables
            .get(&cmd.table)
            .cloned()
            .ok_or("Storage error: table not found in data store")
    }
}

impl TryHandler<FilterRows, &'static str> for InMemoryDb {
    fn try_handle(&mut self, cmd: FilterRows) -> Result<Vec<Row>, &'static str> {
        match cmd.condition {
            None => Ok(cmd.rows),
            Some(cond) => {
                let mut matched_rows = Vec::new();
                for row in cmd.rows {
                    if let Some(val) = row.get(&cond.field) {
                        let is_match = match cond.operator.as_str() {
                            "=" => val == &cond.value,
                            "!=" => val != &cond.value,
                            ">" => {
                                let row_num = val
                                    .parse::<i64>()
                                    .map_err(|_| "Type error: expected integer in table row")?;
                                let cond_num = cond.value.parse::<i64>().map_err(
                                    |_| "Type error: expected integer in condition literal",
                                )?;
                                row_num > cond_num
                            },
                            "<" => {
                                let row_num = val
                                    .parse::<i64>()
                                    .map_err(|_| "Type error: expected integer in table row")?;
                                let cond_num = cond.value.parse::<i64>().map_err(
                                    |_| "Type error: expected integer in condition literal",
                                )?;
                                row_num < cond_num
                            },
                            _ => return Err("Execution error: unsupported operator"),
                        };
                        if is_match {
                            matched_rows.push(row);
                        }
                    }
                }
                Ok(matched_rows)
            },
        }
    }
}

impl TryHandler<ProjectColumns, &'static str> for InMemoryDb {
    fn try_handle(&mut self, cmd: ProjectColumns) -> Result<Vec<Row>, &'static str> {
        Ok(cmd
            .rows
            .into_iter()
            .map(|row| {
                let mut projected = HashMap::new();
                for col in &cmd.columns {
                    if let Some(val) = row.get(col) {
                        projected.insert(col.clone(), val.clone());
                    }
                }
                projected
            })
            .collect())
    }
}

/// Builds a fallible query pipeline with `TryProgram`, providing automatic short-circuiting.
pub fn build_query_program(stmt: CheckedSelect) -> TryProgram<InMemoryDb, Vec<Row>, &'static str> {
    ScanTable { table: stmt.table }
        .try_suspend()
        .bind(move |rows| {
            FilterRows {
                rows,
                condition: stmt.where_clause,
            }
            .try_suspend()
        })
        .bind(move |filtered| {
            ProjectColumns {
                rows: filtered,
                columns: stmt.columns,
            }
            .try_suspend()
        })
}

// ============================================================================
// 7. ContextError: Execution Failure Tracing
// ============================================================================

pub fn execute_query(
    program: TryProgram<InMemoryDb, Vec<Row>, &'static str>, db: &mut InMemoryDb,
) -> Result<Vec<Row>, ContextError<&'static str>> {
    let result = with_context_result(
        program.try_run(db),
        "Query execution engine pipeline step failure",
    )?;
    Ok(result)
}

// ============================================================================
// 8. Main Demonstration & Contract Verification
// ============================================================================

fn main() {
    println!("=== Rustica Flagship: Advanced Parser & Functional SQL Engine ===\n");

    // ------------------------------------------------------------------------
    // Part 1: Core Combinator Invariants & Disambiguation (L-01, L-02, L-06, L-08)
    // ------------------------------------------------------------------------
    println!("--- Part 1: Core Combinator Invariants (L-01, L-02, L-06, L-08) ---");

    // L-01: Parser::many must terminate on zero-width match without hanging
    let zero_progress_parser = item('a').optional().many();
    let sample = ['b'];
    let choice_res = zero_progress_parser.parse(&sample).unwrap();
    let (parsed_items, remaining) = choice_res.into_iter().next().unwrap();
    assert_eq!(parsed_items, Vec::<Option<char>>::new());
    assert_eq!(remaining, &['b']);
    println!("  many() zero-width termination verified: no infinite loop.");

    // L-02: Parser::sep_by must not inject empty alternative when elements match
    let sep_parser = item('a').sep_by(item(','));
    let sep_sample = ['a', ',', 'a'];
    let sep_res = sep_parser.parse(&sep_sample).unwrap();
    assert_eq!(
        sep_res.len(),
        1,
        "sep_by must produce exactly 1 choice on matching input"
    );
    let (elems, rem) = sep_res.into_iter().next().unwrap();
    println!(
        "  sep_by() choice purity: parsed {:?}, remaining: {:?}",
        elems, rem
    );
    assert_eq!(elems, vec!['a', 'a']);
    assert_eq!(rem, &[]);

    // L-06: Choice resolution prioritizes full match over partial match
    let p_short = sequence(vec!['f', 'o', 'o']);
    let p_long = sequence(vec!['f', 'o', 'o', 'b', 'a', 'r']);
    let ambiguous = p_short.or(p_long);
    let input: Vec<char> = "foobar".chars().collect();
    let complete_res = ambiguous.parse_complete(&input);
    assert!(complete_res.is_ok());
    assert_eq!(complete_res.unwrap(), vec!['f', 'o', 'o', 'b', 'a', 'r']);
    println!("  Choice resolution prioritized complete match 'foobar' over prefix match 'foo'.");

    // L-08: Parser is genuinely Send + Sync (thread-safe Arc backing)
    let thread_parser = sql_parser();
    let thread_handle = std::thread::spawn(move || {
        let thread_input: Vec<char> = "SELECT id FROM users".chars().collect();
        thread_parser.parse_complete(&thread_input)
    });
    let thread_result = thread_handle.join().unwrap();
    assert!(thread_result.is_ok());
    println!("  Parser verified Send + Sync: safely moved across thread boundary.\n");

    // ------------------------------------------------------------------------
    // Part 2: SQL Parsing with Robust Whitespace & Keyword Rejection (L-05, L-09)
    // ------------------------------------------------------------------------
    println!("--- Part 2: SQL Parsing with Robust Whitespace & Keyword Rejection (L-05, L-09) ---");

    // Query with spaces around commas, operators, and keywords
    let query_str = "SELECT   name  ,  age   FROM   users   WHERE   age  >  20";
    let input_chars: Vec<char> = query_str.chars().collect();
    let parsed_query = sql_parser().parse_complete(&input_chars);
    match &parsed_query {
        Ok(query) => println!(
            "  Successfully parsed query with arbitrary whitespace:\n  {:?}",
            query
        ),
        Err(e) => println!("  Parse failure:\n  {}", e),
    }
    assert!(parsed_query.is_ok());

    // L-09: Reserved keyword rejection (FROM cannot be a column name)
    let invalid_kw_query: Vec<char> = "SELECT FROM FROM users".chars().collect();
    let kw_err = sql_parser().parse_complete(&invalid_kw_query);
    assert!(kw_err.is_err());
    println!("  Reserved keyword rejection verified: 'FROM' rejected as column identifier.");

    // Test ParseError on invalid query with unexpected trailing tokens
    let invalid_str = "SELECT name FROM users WHERE age > 20 @@@";
    let invalid_chars: Vec<char> = invalid_str.chars().collect();
    let parse_err = sql_parser().parse_complete(&invalid_chars);
    assert!(parse_err.is_err());
    println!("  Diagnostics on syntax error: {}", parse_err.unwrap_err());

    // Test INSERT parsing using Parser::between with whitespace-padded tuples
    let insert_str = "INSERT INTO users VALUES ( alice , 30 )";
    let insert_chars: Vec<char> = insert_str.chars().collect();
    let parsed_insert = sql_parser().parse_complete(&insert_chars).unwrap();
    println!("  Parsed INSERT using between(): {:?}", parsed_insert);
    println!();

    // ------------------------------------------------------------------------
    // Part 3: AST Sum-Type Traversal with Prism
    // ------------------------------------------------------------------------
    println!("--- Part 3: AST Sum-Type Traversal with Prism ---");

    let sel_prism = select_query_prism();
    let ins_prism = insert_query_prism();

    let is_select = sel_prism.preview(&parsed_insert);
    assert_eq!(is_select, None);
    let extracted_insert = ins_prism.preview(&parsed_insert);
    assert!(extracted_insert.is_some());
    println!(
        "  Prism preview correctly focused on Insert variant: {:?}",
        extracted_insert.unwrap()
    );

    let reviewed_query = sel_prism.review(SelectStatement {
        columns: vec!["id".to_string()],
        table: "accounts".to_string(),
        where_clause: None,
    });
    println!(
        "  Prism review constructed SqlQuery AST: {:?}",
        reviewed_query
    );
    println!();

    // ------------------------------------------------------------------------
    // Part 4: Semantic Analysis & Multi-Error Accumulation with Validated (L-07)
    // ------------------------------------------------------------------------
    println!("--- Part 4: Multi-Error Accumulating Schema & Type Validation (L-07) ---");

    let schema = DatabaseSchema {
        tables: vec![TableSchema {
            name: "users".to_string(),
            columns: vec![
                ColumnSchema {
                    name: "id".to_string(),
                    data_type: DataType::Int,
                },
                ColumnSchema {
                    name: "name".to_string(),
                    data_type: DataType::Text,
                },
                ColumnSchema {
                    name: "age".to_string(),
                    data_type: DataType::Int,
                },
            ],
        }],
    };

    // Valid query
    let valid_stmt = SelectStatement {
        columns: vec!["name".to_string(), "age".to_string()],
        table: "users".to_string(),
        where_clause: Some(Condition {
            field: "age".to_string(),
            operator: ">".to_string(),
            value: "20".to_string(),
        }),
    };
    let checked_valid = validate_select_query(&valid_stmt, &schema);
    match &checked_valid {
        Validated::Valid(checked) => println!("  Valid query schema check: {:?}", checked),
        Validated::Invalid(errs) => panic!("Expected valid, got: {:?}", errs),
    }

    // Invalid query: wrong column, relational operator applied to Text column, bad integer literal
    let invalid_stmt = SelectStatement {
        columns: vec!["salary".to_string()],
        table: "users".to_string(),
        where_clause: Some(Condition {
            field: "name".to_string(), // name is DataType::Text!
            operator: ">".to_string(), // relational operator on Text fails!
            value: "not_a_number".to_string(),
        }),
    };
    let checked_invalid = validate_select_query(&invalid_stmt, &schema);
    match checked_invalid {
        Validated::Valid(_) => panic!("Expected validation errors"),
        Validated::Invalid(errors) => {
            println!(
                "  Validation correctly accumulated {} error(s):",
                errors.len()
            );
            for (i, err) in errors.iter().enumerate() {
                println!("    [{}] {}", i + 1, err);
            }
            assert_eq!(errors.len(), 3); // missing column + relational on text + non-int literal
        },
    }
    println!();

    // ------------------------------------------------------------------------
    // Part 5: Query Transformation with Lens
    // ------------------------------------------------------------------------
    println!("--- Part 5: Query Transformation with Lens ---");

    let col_lens = select_columns_lens();
    println!("  Original columns: {:?}", col_lens.get(&valid_stmt));

    // Immutable transformation: project only 'name'
    let restricted_stmt = col_lens.set(valid_stmt.clone(), vec!["name".to_string()]);
    println!("  Lens projected columns: {:?}", restricted_stmt.columns);
    assert_eq!(restricted_stmt.columns, vec!["name".to_string()]);
    assert_eq!(restricted_stmt.table, "users"); // Preserves other fields

    // Structural sharing check
    let unchanged_stmt = col_lens.modify(valid_stmt.clone(), |cols| cols);
    assert_eq!(unchanged_stmt, valid_stmt);
    println!("  Lens identity modification preserves structural equality.\n");

    // ------------------------------------------------------------------------
    // Part 6: Operational Monad Query Engine with TryProgram & ContextError (L-10)
    // ------------------------------------------------------------------------
    println!("--- Part 6: Operational Monad Query Engine (TryProgram & ContextError) (L-10) ---");

    let mut db = InMemoryDb {
        tables: HashMap::from([(
            "users".to_string(),
            vec![
                HashMap::from([
                    ("id".to_string(), "1".to_string()),
                    ("name".to_string(), "Alice".to_string()),
                    ("age".to_string(), "25".to_string()),
                ]),
                HashMap::from([
                    ("id".to_string(), "2".to_string()),
                    ("name".to_string(), "Bob".to_string()),
                    ("age".to_string(), "18".to_string()),
                ]),
                HashMap::from([
                    ("id".to_string(), "3".to_string()),
                    ("name".to_string(), "Charlie".to_string()),
                    ("age".to_string(), "32".to_string()),
                ]),
            ],
        )]),
    };

    let checked_query = checked_valid.unwrap();
    let query_program = build_query_program(checked_query);
    let rows = execute_query(query_program, &mut db).expect("Query execution failed");
    println!(
        "  TryProgram executed successfully. Result rows count: {}",
        rows.len()
    );
    for (i, row) in rows.iter().enumerate() {
        println!("    Row #{}: {:?}", i + 1, row);
    }
    assert_eq!(rows.len(), 2); // Alice (25) and Charlie (32) > 20

    // Demonstrate automatic short-circuiting with ContextError on storage failure
    let missing_table_query = CheckedSelect {
        table: "archived_users".to_string(),
        columns: vec!["name".to_string()],
        where_clause: None,
    };
    let failing_program = build_query_program(missing_table_query);
    match execute_query(failing_program, &mut db) {
        Ok(_) => panic!("Expected storage failure"),
        Err(context_err) => {
            println!(
                "\n  Execution error accumulated context chain:\n  {}",
                context_err.error_chain()
            );
            assert!(
                context_err
                    .error_chain()
                    .contains("Query execution engine pipeline step failure")
            );
            assert!(
                context_err
                    .error_chain()
                    .contains("Storage error: table not found in data store")
            );
        },
    }

    println!("\n=== All Examples & Invariant Contracts Verified Successfully ===");
}
