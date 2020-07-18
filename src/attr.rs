use crate::expr::Expr;
use crate::{Instruction, ToPlusCal};

#[derive(Debug)]
pub struct Attr {
    var: String,
    value: Expr,
}

impl Attr {
    pub fn new(var: String, value: Expr) -> Self {
        Self { var, value }
    }
}

impl Instruction for Attr {}

impl ToPlusCal for Attr {
    fn to_pluscal(&self, indent: usize) -> String {
        format!(
            "{}{} := {};",
            Self::space(indent),
            self.var,
            self.value.to_pluscal(0)
        )
    }
}
