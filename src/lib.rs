//! Define and manipulate Boolean variables and rules that depend on their state.
//!
//! [Boolean  variables](Variable) are identified by an integer UID which can be used to define Boolean rules (below)
//! and to manipulate [states](State) and [patterns](Pattern) based on [selections of variables](VarSet).
//! A [State] is a set of all variables associated to the ```true``` value: other variables are implicitly ```false```.
//! A [Pattern] is defined by two sets of fixed variables (```true``` or ```false```), while other variables remain free.
//! This pattern represents all the states in which the fixed variables take the same value.
//!
//! According to the [Rule trait](Rule), a Boolean rule describes a set of conditions on the Boolean variables.
//! These conditions can be tested in a specific [State]: the rule evaluates to ```true``` if they are satisfied.
//! Note that a rule can not be evaluated in a pattern as it can be true for some of its states and false for others.
//! This crate provides several alternative representations of Boolean rules, as well as conversions between them.
//!
//! ```
//! use bokit::{Pattern, State, Variable};
//! use std::iter::FromIterator;
//! # use bokit::BokitError;
//! # fn main() -> Result<(), BokitError> {
//!
//! // Create some variables
//! let a = Variable::from(0);
//! let b = Variable::from(1);
//! let c = Variable::from(2);
//! let d = Variable::from(3);
//!
//! // Create states and patterns with these variables
//! let state1 = State::from_iter([b,c]);
//! let state2 = State::from_iter([a,c]);
//! let pattern: Pattern = "1--0".parse()?;
//!
//! assert!(!pattern.contains_state(&state1));
//! assert!( pattern.contains_state(&state2));
//!
//! # Ok(())
//! # }
//! ```
//!
//! # Boolean expressions
//!
//! A [Boolean expression](Expr) combines conditions on individual variables (atoms) with Boolean operators (AND, OR, NOT).
//! It is defined as a tree where internal nodes are operators and leaves are atoms (constraints on variables).
//!
//! ```
//! use bokit::{Expr, Rule, State, Variable};
//! # use bokit::BokitError;
//! # fn main() -> Result<(), BokitError> {
//!
//! // Define some variables
//! let a = Variable::from(0);
//! let b = Variable::from(1);
//! let c = Variable::from(2);
//!
//! // Define an expression based on these variables
//! let expr = a & (b | !c);
//!
//! // Evaluate the expression on a state
//! let state: State = "011".parse()?;
//! if expr.eval(&state) {
//!     println!("'{}' is true in state '{}'", &expr, &state);
//! }
//! # Ok(())
//! # }
//! ```
//!
//! # Lists of implicants
//!
//! An implicants of a rule is a pattern such that the rule is true for all states of the pattern. A rule can then be defined
//! by a [list of implicants](Implicants) covering all states for which the rule is true. Note that this definition
//! corresponds to the *truth table* of the rule if all implicants are single states.
//!
//! ```
//! use bokit::{Implicants, Pattern};
//! # use bokit::BokitError;
//! # fn main() -> Result<(), BokitError> {
//!
//! // Define a rule defined as a list of implicants.
//! // Note that if a pattern of the list is included in one of its predecessors, it may be removed.
//! let mut implicants: Implicants = "0-10 ; 0-11 ; 1-11".parse()?;
//! assert_eq!(implicants.len(), 3);
//!
//! // Unlike expressions, lists of implicants can be partially evaluated with a pattern
//! let p1: Pattern = "110-".parse()?;
//! let p2: Pattern = "10-1".parse()?;
//! assert!(!implicants.satisfiable_in_pattern( &p1));
//! assert!(implicants.satisfiable_in_pattern( &p2));
//! # Ok(())
//! # }
//! ```
//!
//! # Prime implicants
//!
//! A *prime implicant* is an implicant which is not contained in any other implicant of the rule.
//! The [list of all prime implicants](Primes) of a rule is a particular [list of implicants](Implicants), with some
//! convenient mathematical properties. Safety checks and implicit transformations of the lists of prime implicants
//! are used to ensure their consistency.
//!
//! ```
//! use bokit::{Implicants, Primes};
//! # use bokit::BokitError;
//! # fn main() -> Result<(), BokitError> {
//!
//! // Get a regular list of implicants
//! let implicants: Implicants = "0-10 ; 0-11 ; 1-11".parse()?;
//!
//! // Extract the prime implicants
//! let primes = Primes::from(&implicants);
//! assert_eq!(primes.len(), 2);
//! # Ok(())
//! # }
//! ```
//!
//! # Conversions and abstract rules
//!
//! A rule represented as a list of implicants (primes or not) can be trivially converted into an expression,
//! which gives a DNF (disjunctive Normal Form) of the rule. This conversion is straightforward and does not
//! require complicated computations.
//! A rule represented as an expression can be converted into its sets of prime implicants, however this conversion
//! is more complex, especially if the expression is ill-formed or if the rule has a large number of (prime) implicants.
//!
//! The [SomeRule] enum represents a thin abstraction layer over these core data structures.
//! The concrete data structures mentioned above can be wrapped into an abstract rule and abstract rules can be converted to the concrete formats.
//! Note that this conversion will clone a concrete object if it was already in the desired type. This clone is cheap for expressions but can be
//! expensive (in time and memory) for large lists of (prime) implicants. To avoid this extra cost, we can convert abstract rules into hybrid
//! objects carrying a borrowed reference or an owned converted object using the standard [Copy-on-write](std::borrow::Cow) wrapper.
//!
//! # Collection of named variables
//!
//! In the previous example, each variable is created explicitly by picking an integer UID. The display name of a variable
//! (when printing the variable itself or an expression using it) is then based on this internal identifier.
//! To facilitate the manipulation of variables, we can use a [collection of variables](VarSpace), which lets us
//! create variables using human-readable identifiers (with some naming restrictions to enable their use in formulae).
//!
//! Note that the collection only carries the association between the internal UIDs and the human-readable names,
//! the variables issued by a collection can thus be mixed (with care) with variables defined by an integer UID.
//!
//! ```
//! use bokit::VarSpace;
//! # use bokit::BokitError;
//! # fn main() -> Result<(), BokitError> {
//!
//! let mut variables = VarSpace::default();
//! let v1 = variables.add("A")?;
//! let v2 = variables.add("B")?;
//! let v3 = variables.add("C")?;
//!
//! // Display a named variable
//! assert_eq!( format!("{}", variables.named(&v2)), "B");
//!
//! // Parse an expression using named variables
//! let expr = variables.parse_expression("A & (B | !C)")?;
//!
//! // Check that a rule uses only variables from the collection
//! assert!(variables.check_rule(&expr).is_ok());
//!
//! println!("{}", &expr);
//! println!("{}", variables.named(&expr));
//!
//! // The associated name can be changed
//! variables.set_name(v2, "newName");
//! println!("{}", variables.named(&expr));
//! # Ok(())
//! # }
//! ```

mod convert;
mod error;
mod expr;
mod implicants;
mod parse;
mod pattern;
mod primes;
mod rules;
mod states;
pub mod tools;
mod variable;
mod space;

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

#[macro_use]
extern crate pest_derive;

// Export public structures and API
pub use error::BokitError;
pub use expr::{Expr, Operator};
pub use implicants::Implicants;
pub use pattern::Pattern;
pub use primes::Primes;
pub use rules::{Rule, SomeRule};
pub use states::State;
pub use variable::{VarSet, Variable, VariableID};
pub use space::{Component, VarSpace};
