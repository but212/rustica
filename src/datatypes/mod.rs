/// This module contains various data types and structures used in the library.
///
/// # Submodules
///
/// - `either`: Represents a value of one of two possible types.
/// - `state`: Provides the State monad for stateful computations.
/// - `validated`: Offers validation with accumulating errors.
/// - `writer`: Implements the Writer monad for logging during computations.
/// - `reader`: Provides the Reader monad for computations with a shared environment.
/// - `maybe`: Represents optional values.
/// - `cont`: Implements the Continuation monad.
/// - `async_monad`: Provides monadic operations for asynchronous computations.
/// - `io`: Handles Input/Output operations.
/// - `free`: Implements the Free monad.
/// - `choice`: Represents a choice between multiple options.
/// - `lens`: Implements functional lenses for focusing on parts of data structures.
/// - `prism`: Provides prisms for working with sum types.
pub mod either;
pub mod state;
pub mod validated;
pub mod writer;
pub mod reader;
pub mod maybe;
pub mod cont;
pub mod async_monad;
pub mod io;
pub mod free;
pub mod choice;
pub mod lens;
pub mod prism;
pub use prism::Prism;