use crate::expr::Expr;
use crate::ToPlusCal;

#[derive(Debug)]
pub enum Cond {
    Ge(Box<Expr>, Box<Expr>),
}

impl ToPlusCal for Cond {
    fn to_pluscal(&self, indent: usize) -> String {
        match self {
            Self::Ge(left, right) => format!(
                "{}{} >= {}",
                Self::space(indent),
                left.to_pluscal(0),
                right.to_pluscal(0)
            ),
        }
    }
}
