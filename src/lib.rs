mod attr;
mod cond;
mod expr;
mod if_;
mod label;
mod module;
mod var;

trait Instruction: ToPlusCal + std::fmt::Debug {}

const TAB_SIZE: usize = 4;
const NEW_LINE: char = '\n';

trait ToPlusCal {
    fn to_pluscal(&self, indent: usize) -> String;

    fn space(indent: usize) -> String
    where
        Self: Sized,
    {
        std::iter::repeat(' ').take(indent).collect()
    }
}

pub mod prelude {
    pub use super::module::Module;
}
