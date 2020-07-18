use crate::cond::Cond;
use crate::label::Label;
use crate::{Instruction, ToPlusCal};

#[must_use]
pub struct IfBuilder<'a> {
    parent: &'a mut Label,
    cond: Cond,
    then_label: Option<Label>,
    else_label: Option<Label>,
}

impl<'a> IfBuilder<'a> {
    pub(crate) fn new(parent: &'a mut Label, cond: Cond) -> Self {
        Self {
            parent,
            cond,
            then_label: None,
            else_label: None,
        }
    }

    pub fn then<F>(mut self, f: F) -> Self
    where
        F: Fn(&mut Label),
    {
        assert!(self.then_label.is_none());
        let mut then_label = Label::unnamed();
        f(&mut then_label);
        self.then_label = Some(then_label);
        self
    }

    pub fn end_if(self) {
        let instr = If::new(self.cond, self.then_label, self.else_label);
        self.parent
            .instructions
            .push((crate::label::InstructionType::If, Box::new(instr)));
    }
}

#[derive(Debug)]
pub struct If {
    cond: Cond,
    then_label: Option<Label>,
    else_label: Option<Label>,
}

impl If {
    fn new(cond: Cond, then_label: Option<Label>, else_label: Option<Label>) -> Self {
        Self {
            cond,
            then_label,
            else_label,
        }
    }
}

impl Instruction for If {}

impl ToPlusCal for If {
    fn to_pluscal(&self, indent: usize) -> String {
        let mut s = String::new();
        s.push_str(&format!("{}if ", Self::space(indent)));
        s.push_str(&self.cond.to_pluscal(0));

        s.push_str(" then");
        s.push(crate::NEW_LINE);
        if let Some(label) = &self.then_label {
            s.push_str(&label.to_pluscal(indent + crate::TAB_SIZE));
        }

        if let Some(label) = &self.else_label {
            s.push_str(&format!("{}else ", Self::space(indent)));
            s.push(crate::NEW_LINE);
            s.push_str(&label.to_pluscal(indent + crate::TAB_SIZE));
        }

        s.push_str(&format!("{}end if;", Self::space(indent)));
        s
    }
}
