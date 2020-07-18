use crate::label::Label;
use crate::var::{NaturalVar, NaturalVarBuilder};
use crate::ToPlusCal;
use std::collections::HashSet;

pub struct Module {
    name: String,
    extends: Vec<String>,
    vars: HashSet<String>,
    pub(crate) natural_vars: Vec<NaturalVar>,
    root: Label,
}

impl Module {
    pub fn new(name: impl ToString) -> Self {
        Self {
            name: name.to_string(),
            extends: Vec::new(),
            vars: HashSet::new(),
            natural_vars: Vec::new(),
            root: Label::unnamed(),
        }
    }

    pub fn extends(&mut self, name: impl ToString) {
        self.extends.push(name.to_string());
    }

    pub fn natural(&mut self, name: impl ToString) -> NaturalVarBuilder<'_> {
        let name = name.to_string();
        assert!(!self.vars.contains(&name));
        self.vars.insert(name.clone());
        NaturalVarBuilder::new(name, self)
    }

    pub fn label(&mut self, name: impl ToString) -> &mut Label {
        self.root.label(name)
    }
}

impl std::fmt::Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut lines = Vec::new();

        let module = ["---- MODULE ", &self.name, " ----"].concat();
        let extends = ["EXTENDS ", &self.extends.join(", ")].concat();
        let start_algorithm = ["(* --algorithm ", &self.name].concat();

        lines.push(module);
        lines.push(extends);
        lines.push(String::new());
        lines.push(start_algorithm);
        lines.push(String::new());

        if !self.vars.is_empty() {
            let mut variables = String::from("variables");
            let declarations = self
                .natural_vars
                .iter()
                .map(|var| var.to_pluscal(crate::TAB_SIZE))
                .collect::<Vec<_>>()
                .join(&format!(",{}", crate::NEW_LINE));

            variables.push(crate::NEW_LINE);
            variables.push_str(&declarations);
            variables.push(';');

            lines.push(variables);
        }

        lines.push(String::new());
        lines.push(String::from("begin"));
        lines.push(self.root.to_pluscal(0));
        lines.push(String::new());
        lines.push(String::from("end algorithm *)"));
        lines.push(String::from("===="));

        write!(f, "{}", lines.join(&crate::NEW_LINE.to_string()))
    }
}
