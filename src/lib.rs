use std::fmt::Debug;
use std::ops::{BitAnd, BitOr, BitXor, Not};

pub enum GateFunc {
    And,
    Nor,
    Nimpl,
    Xor,
}

pub struct Gate<T> {
    pub i0: T,
    pub i1: T,
    pub func: GateFunc,
}

impl<T> Gate<T> {
    #[inline]
    pub fn new_and(i0: T, i1: T) -> Self {
        Gate {
            i0,
            i1,
            func: GateFunc::And,
        }
    }

    #[inline]
    pub fn new_nor(i0: T, i1: T) -> Self {
        Gate {
            i0,
            i1,
            func: GateFunc::Nor,
        }
    }

    #[inline]
    pub fn new_nimpl(i0: T, i1: T) -> Self {
        Gate {
            i0,
            i1,
            func: GateFunc::Nimpl,
        }
    }

    #[inline]
    pub fn new_xor(i0: T, i1: T) -> Self {
        Gate {
            i0,
            i1,
            func: GateFunc::Xor,
        }
    }
}

impl<T: Copy + Clone> Gate<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    #[inline]
    pub fn eval<Out>(&self, outputs: &[Out]) -> Out
    where
        Out: BitAnd<Output = Out>
            + BitOr<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Clone,
    {
        let i0 = outputs[usize::try_from(self.i0).unwrap()].clone();
        let i1 = outputs[usize::try_from(self.i1).unwrap()].clone();
        match self.func {
            GateFunc::And => i0 & i1,
            GateFunc::Nor => !(i0 | i1),
            GateFunc::Nimpl => i0 & !i1,
            GateFunc::Xor => i0 ^ i1,
        }
    }
}

pub struct Circuit<T> {
    input_len: T,
    gates: Vec<Gate<T>>,
    outputs: Vec<(T, bool)>,
}

impl<T> Circuit<T> {
    pub fn new(input_len: T) -> Self {
        Self {
            input_len,
            gates: vec![],
            outputs: vec![],
        }
    }
}

impl<T: Clone + Copy> Circuit<T> {
    pub fn eval<Out>(&self, inputs: impl IntoIterator<Item = Out>) -> Vec<Out>
    where
        usize: TryFrom<T>,
        <usize as TryFrom<T>>::Error: Debug,
        Out: BitAnd<Output = Out>
            + BitOr<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Default
            + Clone,
    {
        let mut gate_outputs = Vec::from_iter(inputs);
        gate_outputs.resize(self.gates.len(), Out::default());
        for (i, g) in self.gates.iter().enumerate() {
            gate_outputs[usize::try_from(self.input_len).unwrap() + i] = g.eval(&gate_outputs);
        }
        self.outputs
            .iter()
            .map(|&(i, n)| {
                let out = gate_outputs[usize::try_from(i).unwrap()].clone();
                if n {
                    !out
                } else {
                    out
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
