//! Domain DSL & Effect Separation Example
//!
//! Demonstrates the two complementary approaches to domain DSLs in Rustica:
//! 1. `Program` / `TryProgram` (Operational Monad):
//!    - Statically typed: each command declares its output type via `Command::Output`.
//!    - Zero dynamic downcasting, 100% compile-time type-safe handler dispatch.
//! 2. `Free` Monad:
//!    - Reusable AST (`Clone`): allows AST inspection, dry-runs, and natural transformations.
//!    - Stack-safe iterative trampoline execution.

use rustica::datatypes::free::{AnyValue, Free};
use rustica::datatypes::operational::{Command, Handler, Program};
use std::sync::Arc;

// ============================================================================
// Scenario 1: Operational Monad (`Program`)
// ============================================================================
// Commands declare their return types at compile time.

#[derive(Debug, Clone)]
pub struct CheckStock {
    pub item_id: &'static str,
    pub quantity: u32,
}

impl Command for CheckStock {
    type Output = bool;
}

#[derive(Debug, Clone)]
pub struct ChargeCard {
    pub card_number: &'static str,
    pub amount_cents: u64,
}

impl Command for ChargeCard {
    type Output = Result<String, &'static str>;
}

#[derive(Debug, Clone)]
pub struct SendReceipt {
    pub email: &'static str,
    pub tx_id: String,
}

impl Command for SendReceipt {
    type Output = ();
}

/// In-memory interpreter for the Operational Monad commands
pub struct ProductionOrderHandler {
    pub available_stock: u32,
    pub receipts_sent: Vec<(String, String)>,
}

impl Handler<CheckStock> for ProductionOrderHandler {
    fn handle(&mut self, cmd: CheckStock) -> bool {
        self.available_stock >= cmd.quantity
    }
}

impl Handler<ChargeCard> for ProductionOrderHandler {
    fn handle(&mut self, cmd: ChargeCard) -> Result<String, &'static str> {
        if cmd.amount_cents > 0 {
            Ok(format!("tx_prod_{}", cmd.amount_cents))
        } else {
            Err("invalid amount")
        }
    }
}

impl Handler<SendReceipt> for ProductionOrderHandler {
    fn handle(&mut self, cmd: SendReceipt) {
        self.receipts_sent.push((cmd.email.to_string(), cmd.tx_id));
    }
}

fn run_operational_monad_example() {
    println!("--- 1. Operational Monad (Program) ---");

    // Compose statically typed pipeline
    let pipeline = CheckStock {
        item_id: "rust-book",
        quantity: 1,
    }
    .suspend()
    .and_then(|in_stock| {
        if in_stock {
            ChargeCard {
                card_number: "4111-xxxx-xxxx-1111",
                amount_cents: 4500,
            }
            .suspend()
        } else {
            Program::pure(Err("out of stock"))
        }
    })
    .and_then(|charge_res| match charge_res {
        Ok(tx_id) => SendReceipt {
            email: "user@example.com",
            tx_id: tx_id.clone(),
        }
        .suspend()
        .map(move |_| Ok(tx_id)),
        Err(e) => Program::pure(Err(e)),
    });

    let mut handler = ProductionOrderHandler {
        available_stock: 5,
        receipts_sent: Vec::new(),
    };

    let result = pipeline.run(&mut handler);
    println!("Execution result: {:?}", result);
    assert_eq!(result, Ok("tx_prod_4500".to_string()));
    assert_eq!(handler.receipts_sent.len(), 1);
    println!("Receipt sent to: {:?}", handler.receipts_sent[0]);
    println!();
}

// ============================================================================
// Scenario 2: Free Monad (`Free<F, A>`)
// ============================================================================
// An inspectable AST that can be cloned, dry-run, or interpreted differently.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderOp {
    ReserveItem { item: &'static str, qty: u32 },
    ProcessPayment { amount: u64 },
}

impl OrderOp {
    pub fn reserve(item: &'static str, qty: u32) -> Free<Self, ()> {
        Free::suspend(Self::ReserveItem { item, qty })
    }

    pub fn payment(amount: u64) -> Free<Self, String> {
        Free::suspend(Self::ProcessPayment { amount })
    }
}

fn run_free_monad_example() {
    println!("--- 2. Free Monad (Free<F, A>) ---");

    // Build the program AST once
    let program: Free<OrderOp, String> =
        OrderOp::reserve("rust-book", 2).then(OrderOp::payment(9000));

    // Free monads are Clone: we can run a "Dry Run / Cost Estimator" interpreter first
    let mut total_cost: u64 = 0;
    let dry_run_program = program.clone();
    let _: String = dry_run_program.run(|op| match op {
        OrderOp::ReserveItem { .. } => Arc::new(()) as AnyValue,
        OrderOp::ProcessPayment { amount } => {
            total_cost += amount;
            Arc::new("dry_run_tx".to_string()) as AnyValue
        },
    });
    println!(
        "Dry-run complete. Total estimated payment: {} cents",
        total_cost
    );
    assert_eq!(total_cost, 9000);

    // Now execute the exact same program AST with a real execution interpreter!
    let mut audit_log: Vec<String> = Vec::new();
    let final_tx: String = program.run(|op| match op {
        OrderOp::ReserveItem { item, qty } => {
            audit_log.push(format!("RESERVED {qty}x {item}"));
            Arc::new(()) as AnyValue
        },
        OrderOp::ProcessPayment { amount } => {
            let tx = format!("REAL_TX_{amount}");
            audit_log.push(format!("CHARGED {amount}"));
            Arc::new(tx) as AnyValue
        },
    });

    println!("Live execution tx: {final_tx}");
    println!("Audit log entries: {:?}", audit_log);
    assert_eq!(final_tx, "REAL_TX_9000");
    assert_eq!(audit_log.len(), 2);
}

fn main() {
    println!("=== Rustica Domain DSL & Effect Separation ===\n");
    run_operational_monad_example();
    run_free_monad_example();
}
