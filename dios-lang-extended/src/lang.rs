use egg::{self, define_language, Id, Language, FromOp};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::str::FromStr;

#[derive(
    Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Serialize, Deserialize,
)]
pub enum Value {
    // starts with i
    Int(i64),
    // starts with <
    List((Value, List)),
    // tail is no longer unwrappable
    Tail(Vec<Value>),
    // starts with b
    Bool(bool),
}