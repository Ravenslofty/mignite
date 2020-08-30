//! Utilities for working with majority-inverter graphs.
//!
//! Majority-inverter graphs represent boolean logic graphs as a combination of three-input majority gates and
//! inverters (NOT gates). These two gates are enough to represent any logic function (i.e. they are universal).
//!
//! The choice of a three-input majority gate as a representation might seem odd, but it has useful properties.
//! A majority gate can be considered as an AND of two of its inputs if the third input is zero, since both inputs
//! would have to be true for the majority to be true. It can also be considered as an OR gate if the third gate is
//! one, since only one input needs to be true for the majority to be true. However, since it can compute the majority
//! of its inputs, it is more powerful than the combination of AND/OR.
//!
//! Additionally, majority gates can be used for error tolerance. For example, a tree can be triplicated into three
//! segments connected to a majority gate, and each segment can make an overly-general assumption (a logic error).
//! Provided that these logic errors do not overlap (i.e. that only one segment produces a wrong result given the
//! inputs), the result of the majority gate will still be correct. This can provide major logic savings.
//!
//! A three input majority gate will be notated as `M(x, y, z)`, and the inversion of `x` as `x'`.
//!
//! Majority logic has five main axioms:
//! - Commutativity: permuting the inputs does not change the result, because majority gates are order-insensitive.
//! - Majority: if a gate has two identical input terms, the gate can be replaced with that term, because that term 
//!   decides the gate output.
//!   Likewise, if a gate has a term and its inversion as inputs, then the gate can be replaced with the third input,
//!   because the third input term decides the gate output.
//! - Associativity: a term in a child gate can be swapped with a term in its parent without changing the result.
//! - Distributivity: input terms can be pushed down a level without changing the result.
//! - Inverter Propagation: a gate with three inverted input terms can move the inverter to its output.

#![forbid(unsafe_code)]
#![warn(clippy::pedantic, clippy::nursery)]
#![warn(missing_docs)]

pub mod mig5;
pub mod traits;