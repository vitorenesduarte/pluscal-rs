use crate::attr::Attr;
use crate::cond::Conditional;
use crate::ToPlusCal;

#[derive(Clone, Debug)]
pub enum Expr {
    Var(String),
    Plus(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn set(&self, other: Self) -> Attr {
        match self {
            Expr::Var(name) => Attr::new(name.clone(), other),
            _ => {
                panic!(
                    "can only attribute a value to a variable; found: {:?}",
                    self
                );
            }
        }
    }

    pub fn ge(&self, other: &Self) -> Conditional {
        Conditional::Ge(Box::new(self.clone()), Box::new(other.clone()))
    }

    pub fn plus(&self, other: &Self) -> Expr {
        Expr::Plus(Box::new(self.clone()), Box::new(other.clone()))
    }

    pub fn minus(&self, other: &Self) -> Expr {
        Expr::Minus(Box::new(self.clone()), Box::new(other.clone()))
    }
}

impl ToPlusCal for Expr {
    fn to_pluscal(&self, indent: usize) -> String {
        let expr = match self {
            Self::Var(name) => name.clone(),
            Self::Plus(left, right) => format!("{} + {}", left.to_pluscal(0), right.to_pluscal(0)),
            Self::Minus(left, right) => format!("{} - {}", left.to_pluscal(0), right.to_pluscal(0)),
        };
        format!("{}{}", Self::space(indent), expr)
    }
}
