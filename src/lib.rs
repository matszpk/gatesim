use std::cmp::{Ord, Ordering, PartialOrd};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::ops::{BitAnd, BitOr, BitXor, Not};
use std::str::FromStr;

use thiserror::Error;

#[derive(Error, Debug)]
pub enum GateParseError<PIError> {
    #[error("Unknown function")]
    UnknownFunction,
    #[error("Syntax error")]
    SyntaxError,
    #[error("ParseIntError {0}")]
    ParseInt(#[from] PIError),
}

#[derive(Error, Debug)]
pub enum CircuitParseError<PIError> {
    #[error("Syntax error")]
    SyntaxError,
    #[error("Invalid circuit")]
    Invalid,
    #[error("ParseIntError {0}")]
    ParseInt(#[from] PIError),
    #[error("GateParseError {0}")]
    Gate(#[from] GateParseError<PIError>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GateFunc {
    And,
    Nor,
    Nimpl,
    Xor,
}

impl Display for GateFunc {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            GateFunc::And => write!(f, "and"),
            GateFunc::Nor => write!(f, "nor"),
            GateFunc::Nimpl => write!(f, "nimpl"),
            GateFunc::Xor => write!(f, "xor"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, Hash)]
pub struct Gate<T: Clone + Copy> {
    pub i0: T,
    pub i1: T,
    pub func: GateFunc,
}

impl<T: Clone + Copy + Debug> Display for Gate<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}({:?},{:?})", self.func, self.i0, self.i1)
    }
}

impl<T: Clone + Copy + PartialOrd> PartialOrd for Gate<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let (selfi0, selfi1, selfrevord) = if let Some(ord) = self.i0.partial_cmp(&self.i1) {
            if ord == Ordering::Less {
                (self.i0, self.i1, false)
            } else {
                (self.i1, self.i0, true)
            }
        } else {
            (self.i1, self.i0, true)
        };
        let (otheri0, otheri1, otherrevord) = if let Some(ord) = other.i0.partial_cmp(&other.i1) {
            if ord == Ordering::Less {
                (other.i0, other.i1, false)
            } else {
                (other.i1, other.i0, true)
            }
        } else {
            (other.i1, other.i0, true)
        };
        if let Some(ord) = selfi1.partial_cmp(&otheri1) {
            if ord == Ordering::Equal {
                if let Some(ord) = selfi0.partial_cmp(&otheri0) {
                    if ord == Ordering::Equal {
                        if self.func == other.func {
                            if selfrevord && !otherrevord {
                                return Some(Ordering::Greater);
                            } else if !selfrevord && otherrevord {
                                return Some(Ordering::Less);
                            } else {
                                return Some(Ordering::Equal);
                            }
                        }
                        return self.func.partial_cmp(&other.func);
                    } else {
                        Some(ord)
                    }
                } else {
                    None
                }
            } else {
                Some(ord)
            }
        } else {
            None
        }
    }
}

impl<T: Clone + Copy + Ord> Gate<T> {
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

impl<T: Clone + Copy + FromStr> FromStr for Gate<T> {
    type Err = GateParseError<<T as FromStr>::Err>;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let (func, r) = if src.starts_with("and(") {
            (GateFunc::And, &src[4..])
        } else if src.starts_with("nor(") {
            (GateFunc::Nor, &src[4..])
        } else if src.starts_with("nimpl(") {
            (GateFunc::Nimpl, &src[6..])
        } else if src.starts_with("xor(") {
            (GateFunc::Xor, &src[4..])
        } else {
            return Err(GateParseError::UnknownFunction);
        };
        let (r, i0) = if let Some(p) = r.find(',') {
            let d = &r[0..p];
            let d = T::from_str(d)?;
            (&r[p + 1..], d)
        } else {
            return Err(GateParseError::SyntaxError);
        };

        let (r, i1) = if let Some(p) = r.find(')') {
            let d = &r[0..p];
            let d = T::from_str(d)?;
            (&r[p + 1..], d)
        } else {
            return Err(GateParseError::SyntaxError);
        };
        if r.is_empty() {
            Ok(Gate { i0, i1, func })
        } else {
            Err(GateParseError::SyntaxError)
        }
    }
}

impl<T: Copy + Clone> Gate<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    #[inline]
    pub fn eval_args<Out>(&self, i0: Out, i1: Out) -> Out
    where
        Out: BitAnd<Output = Out>
            + BitOr<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Clone,
    {
        match self.func {
            GateFunc::And => i0 & i1,
            GateFunc::Nor => !(i0 | i1),
            GateFunc::Nimpl => i0 & !i1,
            GateFunc::Xor => i0 ^ i1,
        }
    }

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Circuit<T: Clone + Copy> {
    input_len: T,
    gates: Vec<Gate<T>>,
    outputs: Vec<(T, bool)>,
}

impl<T: Clone + Copy> Circuit<T> {
    pub fn gates(&self) -> &[Gate<T>] {
        &self.gates
    }

    pub unsafe fn gates_mut(&mut self) -> &mut [Gate<T>] {
        &mut self.gates
    }

    pub fn outputs(&self) -> &[(T, bool)] {
        &self.outputs
    }

    pub unsafe fn outputs_mut(&mut self) -> &mut [(T, bool)] {
        &mut self.outputs
    }

    pub fn input_len(&self) -> T {
        self.input_len
    }

    pub fn len(&self) -> usize {
        self.gates.len()
    }
}

impl<T: Clone + Copy + Debug> Display for Circuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let input_len = usize::try_from(self.input_len).unwrap();
        let mut output_map = vec![(0, false, false); input_len + self.gates.len()];
        write!(f, "{{")?;
        for (i, (v, n)) in self.outputs.iter().enumerate() {
            output_map[usize::try_from(*v).unwrap()] = (i, *n, true);
        }
        for i in 0..input_len {
            if output_map[i].2 {
                write!(
                    f,
                    "{}:{}{}",
                    i,
                    output_map[i].0,
                    if output_map[i].1 { "n" } else { "" }
                )?;
            } else {
                write!(f, "{}", i)?;
            }
            if i + 1 < input_len {
                write!(f, " ")?;
            }
        }
        for (i, g) in self.gates.iter().enumerate() {
            if output_map[input_len + i].2 {
                write!(
                    f,
                    " {}:{}{}",
                    g,
                    output_map[input_len + i].0,
                    if output_map[input_len + i].1 { "n" } else { "" }
                )?;
            } else {
                write!(f, " {}", g)?;
            }
        }
        write!(f, "}}({})", input_len)?;
        Ok(())
    }
}

impl<T> FromStr for Circuit<T>
where
    T: Clone + Copy + FromStr + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Err = CircuitParseError<<T as FromStr>::Err>;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        if src.starts_with("{") {
            let mut input_len = T::default();
            let mut input_touched = vec![];
            let mut output_len = T::default();
            let mut outputs = vec![];
            let mut r = &src[1..];
            let mut end = false;
            loop {
                if let Some(c) = r.chars().next() {
                    if c.is_digit(10) {
                        let p = if let Some(p) = r.find([' ', ':', '}']) {
                            p
                        } else {
                            return Err(CircuitParseError::SyntaxError);
                        };
                        let d = &r[0..p];
                        let input = T::from_str(d)?;
                        r = &r[p..];
                        // fill inputs
                        if input >= input_len {
                            input_len = input + T::from(1u8);
                            input_touched.resize(usize::try_from(input_len).unwrap(), false);
                        }
                        input_touched[usize::try_from(input).unwrap()] = true;

                        match r.chars().next().unwrap() {
                            ' ' => {
                                r = &r[1..];
                                continue;
                            }
                            ':' => {
                                r = &r[1..];
                                if let Some(p) = r.find(['n', ' ', ':', '}']) {
                                    let d = &r[0..p];
                                    let output = T::from_str(d)?;
                                    r = &r[p..];
                                    let neg = if r.chars().next().unwrap() == 'n' {
                                        r = &r[1..];
                                        true
                                    } else {
                                        false
                                    };

                                    // fill outputs
                                    if output >= output_len {
                                        output_len = output + T::from(1u8);
                                        outputs.resize(usize::try_from(output_len).unwrap(), None);
                                    }
                                    outputs[usize::try_from(output).unwrap()] = Some((input, neg));

                                    match r.chars().next().unwrap() {
                                        ' ' => {
                                            r = &r[1..];
                                        }
                                        '}' => {
                                            r = &r[1..];
                                            end = true;
                                            break;
                                        }
                                        _ => {
                                            panic!("Unexpected");
                                        }
                                    };
                                } else {
                                    return Err(CircuitParseError::SyntaxError);
                                }
                            }
                            '}' => {
                                r = &r[1..];
                                end = true;
                                break;
                            }
                            _ => {
                                panic!("Unexpected");
                            }
                        }
                    } else {
                        break;
                    }
                    //Circuit::new(
                } else {
                    return Err(CircuitParseError::SyntaxError);
                }
            }

            if !input_touched.into_iter().all(|x| x) {
                return Err(CircuitParseError::Invalid);
            }

            let mut gates = vec![];
            let input_len = usize::try_from(input_len).unwrap();

            while !end {
                let p = if let Some(p) = r.find(')') {
                    p + 1
                } else {
                    return Err(CircuitParseError::SyntaxError);
                };
                let gstr = &r[0..p];
                gates.push(Gate::<T>::from_str(gstr)?);
                r = &r[p..];

                match r.chars().next().unwrap() {
                    ' ' => {
                        r = &r[1..];
                        continue;
                    }
                    ':' => {
                        r = &r[1..];
                        if let Some(p) = r.find(['n', ' ', ':', '}']) {
                            let d = &r[0..p];
                            let output = T::from_str(d)?;
                            r = &r[p..];
                            let neg = if r.chars().next().unwrap() == 'n' {
                                r = &r[1..];
                                true
                            } else {
                                false
                            };

                            // fill outputs
                            if output >= output_len {
                                output_len = output + T::from(1u8);
                                outputs.resize(usize::try_from(output_len).unwrap(), None);
                            }
                            outputs[usize::try_from(output).unwrap()] =
                                Some((T::try_from(input_len + gates.len() - 1).unwrap(), neg));

                            match r.chars().next().unwrap() {
                                ' ' => {
                                    r = &r[1..];
                                }
                                '}' => {
                                    r = &r[1..];
                                    break;
                                }
                                _ => {
                                    panic!("Unexpected");
                                }
                            };
                        } else {
                            return Err(CircuitParseError::SyntaxError);
                        }
                    }
                    '}' => {
                        r = &r[1..];
                        break;
                    }
                    _ => {
                        panic!("Unexpected");
                    }
                }
            }

            if !outputs.iter().all(|x| x.is_some()) {
                return Err(CircuitParseError::Invalid);
            }

            if let Some(c) = r.chars().next() {
                if c == '(' {
                    if let Some(p) = r.find(')') {
                        let d = &r[1..p];
                        let res_input_len = T::from_str(d)?;
                        if res_input_len != T::try_from(input_len).unwrap() {
                            return Err(CircuitParseError::Invalid);
                        }
                    } else {
                        return Err(CircuitParseError::SyntaxError);
                    }
                } else {
                    return Err(CircuitParseError::SyntaxError);
                }
            }

            if let Some(c) = Circuit::new(
                T::try_from(input_len).unwrap(),
                gates,
                outputs.into_iter().map(|x| x.unwrap()),
            ) {
                return Ok(c);
            } else {
                return Err(CircuitParseError::Invalid);
            }
        } else {
            return Err(CircuitParseError::SyntaxError);
        }
    }
}

impl<T: Clone + Copy + PartialOrd + Ord> Circuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    pub unsafe fn new_unchecked(
        input_len: T,
        gates: impl IntoIterator<Item = Gate<T>>,
        outputs: impl IntoIterator<Item = (T, bool)>,
    ) -> Self {
        Self {
            input_len,
            gates: Vec::from_iter(gates),
            outputs: Vec::from_iter(outputs),
        }
    }

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
    // at least one output must be a last gate ouput.
    pub fn verify(&self) -> bool {
        // check inputs and gate outputs
        // gate have input less than its output.
        let input_len = usize::try_from(self.input_len).unwrap();
        let output_num = input_len + self.gates.len();
        let mut used_inputs = vec![false; output_num];
        for (i, g) in self.gates.iter().enumerate() {
            let i0 = usize::try_from(g.i0).unwrap();
            let i1 = usize::try_from(g.i1).unwrap();
            let cur_index = input_len + i;
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
        if !self.outputs.is_empty() && !self.gates.is_empty() {
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
        } else {
            true
        }
    }

    pub fn eval_to<Out>(&self, gate_outputs: &mut [Out])
    where
        Out: BitAnd<Output = Out>
            + BitOr<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Default
            + Clone,
    {
        let input_len = usize::try_from(self.input_len).unwrap();
        assert_eq!(gate_outputs.len(), input_len + self.gates.len());
        for (i, g) in self.gates.iter().enumerate() {
            gate_outputs[input_len + i] = g.eval(&gate_outputs);
        }
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
        let input_len = usize::try_from(self.input_len).unwrap();
        gate_outputs.resize(input_len + self.gates.len(), Out::default());
        self.eval_to(&mut gate_outputs);
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
        for (g, exp) in [
            (Gate::new_and(0, 1), 0b1000),
            (Gate::new_nor(0, 1), 0b0001),
            (Gate::new_nimpl(0, 1), 0b0010),
            (Gate::new_xor(0, 1), 0b0110),
        ] {
            assert_eq!(exp, g.eval_args(0b1010, 0b1100) & 0b1111);
        }
    }

    #[test]
    fn test_gate_display() {
        assert_eq!("and(0,1)", format!("{}", Gate::new_and(0, 1)));
        assert_eq!("nor(0,1)", format!("{}", Gate::new_nor(0, 1)));
        assert_eq!("nimpl(0,1)", format!("{}", Gate::new_nimpl(0, 1)));
        assert_eq!("xor(0,1)", format!("{}", Gate::new_xor(0, 1)));
    }

    #[test]
    fn test_gate_partial_ord() {
        assert!(Gate::new_and(2, 3) == Gate::new_and(2, 3));
        assert!(Gate::new_and(3, 3) == Gate::new_and(3, 3));
        assert!(Gate::new_and(2, 3) < Gate::new_and(3, 2));
        assert!(Gate::new_and(2, 3) < Gate::new_nor(2, 3));
        assert!(Gate::new_xor(2, 3) > Gate::new_nor(2, 3));
        assert!(Gate::new_and(2, 4) < Gate::new_and(3, 4));
        assert!(Gate::new_and(4, 2) < Gate::new_and(3, 4));
        assert!(Gate::new_and(2, 4) < Gate::new_and(4, 3));
        assert!(Gate::new_and(4, 2) < Gate::new_and(4, 3));
        assert!(Gate::new_and(4, 2) > Gate::new_and(4, 1));
        assert!(Gate::new_and(4, 3) > Gate::new_and(4, 1));
        assert!(Gate::new_and(3, 4) > Gate::new_and(4, 1));
        assert!(Gate::new_and(3, 4) > Gate::new_and(1, 4));
    }

    #[test]
    fn test_gate_from_str() {
        assert_eq!(Gate::new_and(4, 6), Gate::from_str("and(4,6)").unwrap());
        assert_eq!(Gate::new_nor(4, 6), Gate::from_str("nor(4,6)").unwrap());
        assert_eq!(Gate::new_nimpl(4, 6), Gate::from_str("nimpl(4,6)").unwrap());
        assert_eq!(Gate::new_xor(4, 6), Gate::from_str("xor(4,6)").unwrap());
        assert_eq!(
            Gate::new_nimpl(6764, 116),
            Gate::from_str("nimpl(6764,116)").unwrap()
        );
        assert_eq!(
            Err("Syntax error".to_string()),
            Gate::<u8>::from_str("xor(4,6").map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("ParseIntError invalid digit found in string".to_string()),
            Gate::<u8>::from_str("xor(4x,6)").map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("ParseIntError invalid digit found in string".to_string()),
            Gate::<u8>::from_str("xor(4,6x)").map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Unknown function".to_string()),
            Gate::<u8>::from_str("xoor(4,6)").map_err(|x| x.to_string())
        );
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
        // accept same inputs
        assert!(Circuit::new(
            3,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(2, 2),
                Gate::new_xor(0, 4)
            ],
            [(3, false), (5, false)]
        )
        .is_some());
        assert!(Circuit::new(1, [], [(0, false)]).is_some());
        assert!(Circuit::new(2, [], [(0, false), (1, true)]).is_some());
        assert!(Circuit::new(0, [], []).is_some());
    }

    #[test]
    fn circuit_eval() {
        let circuit = Circuit::new(
            3,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(2, 3),
                Gate::new_and(2, 3),
                Gate::new_and(0, 1),
                Gate::new_nor(5, 6),
            ],
            [(4, false), (7, true)],
        )
        .unwrap();
        for i in 0..8 {
            let expected = (i & 1) + ((i & 2) >> 1) + ((i & 4) >> 2);
            assert_eq!(
                vec![(expected & 1) != 0, (expected & 2) != 0],
                circuit.eval([(i & 1) != 0, (i & 2) != 0, (i & 4) != 0]),
                "test {}",
                i
            );
        }

        let circuit = Circuit::new(
            4,
            [
                Gate::new_and(0, 2),
                Gate::new_and(1, 2),
                Gate::new_and(0, 3),
                Gate::new_and(1, 3),
                // add a1*b0 + a0*b1
                Gate::new_xor(5, 6),
                Gate::new_and(5, 6),
                // add c(a1*b0 + a0*b1) + a1*b1
                Gate::new_xor(7, 9),
                Gate::new_and(7, 9),
            ],
            [(4, false), (8, false), (10, false), (11, false)],
        )
        .unwrap();
        for i in 0..16 {
            let expected = (i & 3) * ((i & 12) >> 2);
            assert_eq!(
                vec![
                    (expected & 1) != 0,
                    (expected & 2) != 0,
                    (expected & 4) != 0,
                    (expected & 8) != 0
                ],
                circuit.eval([(i & 1) != 0, (i & 2) != 0, (i & 4) != 0, (i & 8) != 0]),
                "test {}",
                i
            );
        }
    }

    #[test]
    fn circuit_display() {
        assert_eq!(
            concat!(
                "{0 1 2 3 and(0,2):0 and(1,2) and(0,3) and(1,3) xor(5,6):1 ",
                "and(5,6) xor(7,9):2 and(7,9):3}(4)"
            ),
            format!(
                "{}",
                Circuit::new(
                    4,
                    [
                        Gate::new_and(0, 2),
                        Gate::new_and(1, 2),
                        Gate::new_and(0, 3),
                        Gate::new_and(1, 3),
                        // add a1*b0 + a0*b1
                        Gate::new_xor(5, 6),
                        Gate::new_and(5, 6),
                        // add c(a1*b0 + a0*b1) + a1*b1
                        Gate::new_xor(7, 9),
                        Gate::new_and(7, 9),
                    ],
                    [(4, false), (8, false), (10, false), (11, false)],
                )
                .unwrap()
            )
        );
        assert_eq!(
            concat!(
                "{0 1 2 3 and(0,2):0 and(1,2) and(0,3) and(1,3) xor(5,6):1n ",
                "and(5,6) xor(7,9):2 and(7,9):3n}(4)"
            ),
            format!(
                "{}",
                Circuit::new(
                    4,
                    [
                        Gate::new_and(0, 2),
                        Gate::new_and(1, 2),
                        Gate::new_and(0, 3),
                        Gate::new_and(1, 3),
                        // add a1*b0 + a0*b1
                        Gate::new_xor(5, 6),
                        Gate::new_and(5, 6),
                        // add c(a1*b0 + a0*b1) + a1*b1
                        Gate::new_xor(7, 9),
                        Gate::new_and(7, 9),
                    ],
                    [(4, false), (8, true), (10, false), (11, true)],
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn test_circuit_from_str() {
        assert_eq!(
            Circuit::new(1, [], [(0, false)]).unwrap(),
            Circuit::from_str("{0:0}(1)").unwrap()
        );
        assert_eq!(
            Circuit::new(
                3,
                [
                    Gate::new_and(0, 1),
                    Gate::new_nor(0, 2),
                    Gate::new_xor(3, 4),
                ],
                [(5, false)]
            )
            .unwrap(),
            Circuit::from_str("{0 1 2 and(0,1) nor(0,2) xor(3,4):0}(3)").unwrap()
        );
        assert_eq!(
            Circuit::new(
                3,
                [
                    Gate::new_and(0, 1),
                    Gate::new_nor(0, 2),
                    Gate::new_xor(3, 4),
                ],
                [(5, false), (4, true), (2, true)]
            )
            .unwrap(),
            Circuit::from_str("{0 1 2:2n and(0,1) nor(0,2):1n xor(3,4):0}(3)").unwrap()
        );
        assert_eq!(
            Circuit::new(
                3,
                [
                    Gate::new_and(0, 1),
                    Gate::new_nor(0, 2),
                    Gate::new_xor(3, 4),
                    Gate::new_nimpl(1, 5),
                ],
                [(6, true), (4, false), (2, false)]
            )
            .unwrap(),
            Circuit::from_str("{0 1 2:2 and(0,1) nor(0,2):1 xor(3,4) nimpl(1,5):0n}(3)").unwrap()
        );
        assert_eq!(
            Circuit::new(
                3,
                [
                    Gate::new_and(0, 1),
                    Gate::new_nor(0, 2),
                    Gate::new_xor(3, 4),
                    Gate::new_nimpl(1, 5),
                ],
                [(6, true), (4, false), (2, false)]
            )
            .unwrap(),
            Circuit::from_str("{1 2:2 0 and(0,1) nor(0,2):1 xor(3,4) nimpl(1,5):0n}(3)").unwrap()
        );
        assert_eq!(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 2),
                    Gate::new_and(1, 2),
                    Gate::new_and(0, 3),
                    Gate::new_and(1, 3),
                    // add a1*b0 + a0*b1
                    Gate::new_xor(5, 6),
                    Gate::new_and(5, 6),
                    // add c(a1*b0 + a0*b1) + a1*b1
                    Gate::new_xor(7, 9),
                    Gate::new_and(7, 9),
                ],
                [(4, false), (8, true), (10, false), (11, true)],
            )
            .unwrap(),
            Circuit::from_str(concat!(
                "{0 1 2 3 and(0,2):0 and(1,2) and(0,3) and(1,3) xor(5,6):1n ",
                "and(5,6) xor(7,9):2 and(7,9):3n}(4)"
            ))
            .unwrap()
        );
    }
}
