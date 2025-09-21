/// Re-exports for function category operations and types.
///
/// This module provides access to the core function category implementation,
/// including the main `FunctionCategory` type, morphism type aliases, and
/// convenient macros for function composition and pipelining.
///
/// # Exports
///
/// - `FunctionCategory`: The main category implementation for functions
/// - `FunctionMorphism`: Type alias for function morphisms with static lifetime bounds
/// - `function`: Macro for creating named function morphisms
/// - `pipe`: Macro for creating function pipelines with left-to-right composition
pub use crate::category::function_category::{FunctionCategory, FunctionMorphism, function, pipe};
