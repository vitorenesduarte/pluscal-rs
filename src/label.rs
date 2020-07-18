use crate::attr::Attr;
use crate::cond::Conditional;
use crate::if_::{If, IfBuilder};
use crate::{Instruction, ToPlusCal};
use std::any::Any;

#[derive(Debug)]
pub struct Label {
    name: Option<String>,
    pub(crate) instructions: Vec<(InstructionType, Box<dyn Any>)>,
}

#[derive(Debug)]
pub(crate) enum InstructionType {
    Attr,
    If,
    Label,
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

    pub fn label(&mut self, name: impl ToString) -> &mut Label {
        let label = Label::new(name);
        self.instructions
            .push((InstructionType::Label, Box::new(label)));
        // get the last added instruction (casted to `Label`)
        self.instructions
            .last_mut()
            .unwrap()
            .1
            .as_mut()
            .downcast_mut::<Label>()
            .unwrap()
    }

    pub fn exec(&mut self, attr: Attr) {
        self.instructions
            .push((InstructionType::Attr, Box::new(attr)));
    }

    pub fn if_(&mut self, conditional: Conditional) -> IfBuilder<'_> {
        IfBuilder::new(self, conditional)
    }
}

impl Instruction for Label {}

impl ToPlusCal for Label {
    fn to_pluscal(&self, indent: usize) -> String {
        let mut s = String::new();
        let indent = if let Some(name) = &self.name {
            s.push_str(&format!("{}{}:", Self::space(indent), name));
            s.push(crate::NEW_LINE);
            indent + crate::TAB_SIZE
        } else {
            // only increase indent if there's a label
            indent
        };
        match self.instructions.len() {
            0 => panic!("found label without instructions"),
            _ => {
                for instr in &self.instructions {
                    let instr = match instr {
                        (InstructionType::Attr, instr) => {
                            instr.downcast_ref::<Attr>().unwrap().to_pluscal(indent)
                        }
                        (InstructionType::If, instr) => {
                            instr.downcast_ref::<If>().unwrap().to_pluscal(indent)
                        }
                        (InstructionType::Label, instr) => {
                            instr.downcast_ref::<Label>().unwrap().to_pluscal(indent)
                        }
                    };
                    s.push_str(&instr);
                    if self.instructions.len() > 1 {
                        s.push(crate::NEW_LINE);
                    }
                }
            }
        }
        s
    }
}
