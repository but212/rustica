/// Re-exports for function category operations and types.
///
/// This module provides access to the core function category implementation,
/// including the main `FunctionCategory` type, morphism type aliases, and
/// convenient macros for creating morphisms and pipelining.
///
/// # Exports
///
/// - `FunctionCategory`: The main category implementation for functions
/// - `FunctionMorphism`: Type alias for function morphisms with static lifetime bounds
/// - `function`: Macro for creating named function morphisms
/// - `pipe`: Macro for creating function pipelines with left-to-right composition
/// - `compose`: Macro for creating function composition
pub use crate::category::function_category::{
    FunctionCategory, FunctionMorphism, compose, function, pipe,
};
