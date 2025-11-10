use rustica::error::{
    ErrorPipeline, accumulate_context, format_error_chain, with_context_result,
    wrap_in_composable_result_boxed,
};

// Large-scale pipeline: Error handling and context accumulation per business logic unit
fn parse_config(content: &str) -> Result<i32, &'static str> {
    content.parse::<i32>().map_err(|_| "Parse config error")
}
fn connect_db() -> Result<(), &'static str> {
    Err("DB connection error")
}
fn process_data(val: i32) -> Result<(), &'static str> {
    if val % 2 == 0 {
        Ok(())
    } else {
        Err("Odd number error")
    }
}

fn main() {
    let config_str = "not_a_number";

    // Pipeline declaration: Context accumulation on failure at each step
    let final_result =
        ErrorPipeline::new(wrap_in_composable_result_boxed(parse_config(config_str)))
            .with_context("Failed to parse loaded config")
            .and_then(|cfg| {
                with_context_result(connect_db(), "DB connection attempt failed").map(|_| cfg)
            })
            .with_context("Error occurred during DB connection")
            .and_then(|cfg| {
                with_context_result(process_data(cfg), "Error during data processing").map(|_| cfg)
            })
            .recover(|mut boxed_e| {
                // Final recovery path with context
                *boxed_e = boxed_e
                    .with_context("Final automatic recovery attempt".to_string())
                    .with_context("Notice: Automatic error handling".to_string());
                Err(boxed_e)
            })
            .finish();

    // Error tracking and analysis/documentation
    match final_result {
        Ok(_) => println!("Data processing successful"),
        Err(err) => {
            println!("Deep error tracking:");
            println!("{}", format_error_chain(&err)); // Display error chain + all contexts at a glance
        },
    }

    // Example of bulk error accumulation/analysis
    let errors = vec![
        ("first", "step 1 failed"),
        ("second", "step 2 failed"),
        ("final", "final error occurred"),
    ];
    let chained_error = accumulate_context("base error", errors.iter().map(|e| e.1));
    println!("Bulk accumulated error chain analysis:");
    println!("{}", format_error_chain(&chained_error));
}
