use std::cmp::PartialOrd;
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

impl<T: Clone + Copy + PartialOrd> Circuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    pub fn new(
        input_len: T,
        gates: impl IntoIterator<Item = Gate<T>>,
        outputs: impl IntoIterator<Item = (T, bool)>,
    ) -> Option<Self> {
        let out = Self {
            input_len,
            gates: Vec::from_iter(gates),
            outputs: Vec::from_iter(outputs),
        };
        // verify
        if out.verify() {
            Some(out)
        } else {
            None
        }
    }

    // verification:
    // all inputs and gate outputs must be used except output gates.
    // gate inputs must be different.
    // at least one output must be a last gate ouput.
    fn verify(&self) -> bool {
        // check inputs and gate outputs
        // gate have input less than its output.
        let input_len = usize::try_from(self.input_len).unwrap();
        let output_num = input_len + self.gates.len();
        let mut used_inputs = vec![false; output_num];
        for (i, g) in self.gates.iter().enumerate() {
            let i0 = usize::try_from(g.i0).unwrap();
            let i1 = usize::try_from(g.i1).unwrap();
            let cur_index = input_len + i;
            if i0 == i1 {
                return false;
            }
            if i0 >= cur_index || i1 >= cur_index {
                return false;
            }
            used_inputs[i0] = true;
            used_inputs[i1] = true;
            // check gate inputs
        }
        // fill up outputs - ignore gate outputs - they can be unconnected
        for (o, _) in &self.outputs {
            let o = usize::try_from(*o).unwrap();
            if o >= output_num {
                return false;
            }
            used_inputs[o] = true;
        }
        if !used_inputs.into_iter().all(|x| x) {
            return false;
        }
        // check outputs: at least once output must be last gate output.
        let mut last_output = false;
        for (o, _) in &self.outputs {
            let o = usize::try_from(*o).unwrap();
            if o >= output_num {
                return false;
            }
            if o == output_num - 1 {
                last_output = true;
            }
        }
        last_output
    }

    pub fn eval<Out>(&self, inputs: impl IntoIterator<Item = Out>) -> Vec<Out>
    where
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

    #[test]
    fn test_gate() {
        let inputs = [0b1010, 0b1100];
        for (g, exp) in [
            (Gate::new_and(0, 1), 0b1000),
            (Gate::new_nor(0, 1), 0b0001),
            (Gate::new_nimpl(0, 1), 0b0010),
            (Gate::new_xor(0, 1), 0b0110),
        ] {
            assert_eq!(exp, g.eval(&inputs) & 0b1111);
        }
    }

    #[test]
    fn test_circuit_new() {
        assert!(Circuit::new(2, [Gate::new_xor(0, 1)], [(2, false)]).is_some());
        assert!(Circuit::new(2, [Gate::new_xor(0, 1)], [(2, true)]).is_some());
        assert!(Circuit::new(2, [Gate::new_xor(1, 0)], [(2, false)]).is_some());
        assert!(Circuit::new(2, [Gate::new_xor(0, 1)], [(3, false)]).is_none());
        assert!(Circuit::new(2, [Gate::new_xor(1, 1)], [(2, false)]).is_none());
        assert!(Circuit::new(2, [Gate::new_xor(0, 0)], [(2, false)]).is_none());
        assert!(Circuit::new(2, [Gate::new_xor(0, 1)], [(1, false)]).is_none());

        assert!(
            Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_xor(2, 3)], [(4, false)]).is_some()
        );
        assert!(
            Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_xor(2, 1)], [(4, false)]).is_none()
        );
        assert!(Circuit::new(
            3,
            [Gate::new_xor(0, 1), Gate::new_xor(2, 3)],
            [(3, false), (4, false)]
        )
        .is_some());
        // 3 (gate index 0) and 4 (gate index 1) are outputs - can be unconnected
        assert!(Circuit::new(
            3,
            [Gate::new_xor(0, 1), Gate::new_xor(0, 2)],
            [(3, false), (4, false)]
        )
        .is_some());
        assert!(Circuit::new(
            3,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(1, 2),
                Gate::new_xor(0, 4)
            ],
            [(3, false), (5, false)]
        )
        .is_some());
        // first gate is not connected later
        assert!(Circuit::new(
            3,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(1, 2),
                Gate::new_xor(0, 4)
            ],
            [(5, false)]
        )
        .is_none());
        assert!(Circuit::new(
            3,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(2, 2),
                Gate::new_xor(0, 4)
            ],
            [(3, false), (5, false)]
        )
        .is_none());
    }
}
