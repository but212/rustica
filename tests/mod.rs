// Macro definitions for testing laws and properties
#[macro_use]
pub mod laws;

// Core datatype tests
pub mod datatypes;

// Integration tests across modules
pub mod integration;

// Trait implementation tests
pub mod traits;

// Option and Result trait implementation tests
pub mod traits_impl_option_result;

// Monad transformer tests
pub mod transformers;

// Utility function tests
pub mod utils_test;

// Category tests
pub mod category;

pub mod error;
