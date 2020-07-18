use crate::expr::Expr;
use crate::module::Module;
use crate::ToPlusCal;

pub struct NaturalVarBuilder<'a> {
    name: String,
    module: &'a mut Module,
}

impl<'a> NaturalVarBuilder<'a> {
    pub(crate) fn new(name: String, module: &'a mut Module) -> Self {
        Self { name, module }
    }

    pub fn value(self, value: usize) -> Expr {
        self.in_range(value, value)
    }

    pub fn in_range(self, start: usize, end: usize) -> Expr {
        let var = NaturalVar {
            name: self.name.clone(),
            start,
            end,
        };
        self.module.natural_vars.push(var);
        Expr::Var(self.name)
    }
}

pub(crate) struct NaturalVar {
    name: String,
    start: usize,
    end: usize,
}

impl ToPlusCal for NaturalVar {
    fn to_pluscal(&self, indent: usize) -> String {
        let mut s = format!("{}{}", Self::space(indent), self.name);
        if self.start == self.end {
            // not a range
            s.push_str(&format!(" = {}", self.start));
        } else {
            s.push_str(&format!(" \\in {}..{}", self.start, self.end));
        }
        s
    }
}
