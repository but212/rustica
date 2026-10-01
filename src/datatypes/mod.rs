#![doc = include_str!("../../docs/datatypes/README.md")]

pub mod choice;
pub mod free;
pub mod lens;
pub mod operational;
pub mod prism;
pub mod validated;

pub use choice::ChoiceError;
pub use free::FreeError;

// Backward-compatibility alias for former datatypes::error module
pub mod error {
    pub use crate::datatypes::choice::ChoiceError;
    pub use crate::datatypes::free::FreeError;
}
