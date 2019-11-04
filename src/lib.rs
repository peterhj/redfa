pub use regex::Regex;
pub use dfa::{State, Dfa};
pub mod regex;
pub mod derivatives;
pub mod dfa;
pub mod colls;
#[cfg(test)] mod tests;
