use crate::attr::Attr;
use crate::cond::Conditional;
use crate::if_::IfBuilder;
use crate::{Instruction, ToPlusCal};

#[derive(Debug)]
pub struct Label {
    name: Option<String>,
    pub(crate) instructions: Vec<Box<dyn Instruction>>,
}

impl Label {
    pub(crate) fn new(name: impl ToString) -> Self {
        Label {
            name: Some(name.to_string()),
            instructions: Vec::new(),
        }
    }

    pub(crate) fn unnamed() -> Self {
        Label {
            name: None,
            instructions: Vec::new(),
        }
    }

    pub fn exec(&mut self, attr: Attr) {
        self.instructions.push(Box::new(attr));
    }

    pub fn if_(&mut self, conditional: Conditional) -> IfBuilder<'_> {
        IfBuilder::new(self, conditional)
    }
}

impl ToPlusCal for Label {
    fn to_pluscal(&self, indent: usize) -> String {
        let mut s = String::new();
        if let Some(name) = &self.name {
            s.push_str(&format!("{}{}:", Self::space(indent), name));
        }
        match self.instructions.len() {
            0 => panic!("found label without instructions"),
            1 => {
                s.push_str(&self.instructions[0].to_pluscal(0));
            }
            _ => {
                for instr in &self.instructions {
                    s.push(crate::NEW_LINE);
                    s.push_str(&instr.to_pluscal(indent + crate::TAB_SIZE));
                }
            }
        }
        s
    }
}
