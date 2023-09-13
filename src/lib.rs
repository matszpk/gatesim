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

impl<T: Clone + Copy> Gate<T> {
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
    /// Evaluate gate. Get values of argument from method arguments.
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

    /// Evaluate gate. Get values of argument from output list indexed from 0.
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
            // first loop to parse inputs
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
                                    // parse output
                                    let d = &r[0..p];
                                    let output = T::from_str(d)?;
                                    r = &r[p..];
                                    // output negation mark
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

                                    // skip next char or end
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
                } else {
                    return Err(CircuitParseError::SyntaxError);
                }
            }

            // check whether all inputs are filled
            if !input_touched.into_iter().all(|x| x) {
                return Err(CircuitParseError::Invalid);
            }

            let mut gates = vec![];
            let input_len = usize::try_from(input_len).unwrap();

            // second loop to parse gates
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
                            // parse output
                            let d = &r[0..p];
                            let output = T::from_str(d)?;
                            r = &r[p..];
                            // output negation mark
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

                            // skip next char or end
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

            // check whether if all outputs are filled
            if !outputs.iter().all(|x| x.is_some()) {
                return Err(CircuitParseError::Invalid);
            }

            // parse last part (number of inputs)
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

    /// Verification:
    /// All inputs and gate outputs must be used except output gates.
    /// At least one output must be a last gate ouput.
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

    /// Evaluate gates results (without output negations).
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

    /// Evaluate circuit return outputs (including negation of outputs).
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

impl<T: Clone + Copy + Ord + PartialEq + Eq> From<ClauseCircuit<T>> for Circuit<T>
where
    T: Default + TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn from(circuit: ClauseCircuit<T>) -> Self {
        let mut clauses_gates: Vec<(T, bool)> = vec![];
        let mut gates = vec![];
        let input_len = usize::try_from(circuit.input_len).unwrap();
        for clause in circuit.clauses {
            // organize gates in parallel way

            // routine to get gate with clause inputs
            let get_gate = |l0, n0, l1, n1| {
                let (l0, n0) = if l0 < circuit.input_len {
                    (l0, n0)
                } else {
                    let (i0, in0) = clauses_gates[usize::try_from(l0).unwrap() - input_len];
                    (i0, n0 ^ in0)
                };
                let (l1, n1) = if l1 < circuit.input_len {
                    (l1, n1)
                } else {
                    let (i1, in1) = clauses_gates[usize::try_from(l0).unwrap() - input_len];
                    (i1, n1 ^ in1)
                };
                match clause.kind {
                    ClauseKind::And => {
                        if n0 {
                            if n1 {
                                Gate::new_nor(l0, l1)
                            } else {
                                Gate::new_nimpl(l1, l0)
                            }
                        } else {
                            if n1 {
                                Gate::new_nimpl(l0, l1)
                            } else {
                                Gate::new_and(l0, l1)
                            }
                        }
                    }
                    ClauseKind::Xor => Gate::new_xor(l0, l1),
                }
            };
            let clen = clause.len();
            let level_clen = 1usize << (usize::BITS - clen.leading_zeros() - 1);
            let mut c_gates = vec![];

            let clause_neg = if clause.kind == ClauseKind::Xor {
                clause.literals.iter().fold(false, |a, (_, n)| a ^ n)
            } else {
                false
            };

            if level_clen != clen {
                // organize in two levels
                for j in 0..clen - level_clen {
                    let (l0, n0) = clause.literals[2 * j];
                    let (l1, n1) = clause.literals[2 * j + 1];
                    c_gates.push(get_gate(l0, n0, l1, n1));
                }
                let mut literal_count = (clen - level_clen) << 1;
                let mut c_gates_new = vec![];
                for j in 0..(literal_count >> 2) {
                    let cur_id = gates.len();
                    let cur_id_0 = T::try_from(input_len + cur_id).unwrap();
                    let cur_id_1 = T::try_from(input_len + cur_id + 1).unwrap();
                    gates.push(c_gates[j * 2]);
                    gates.push(c_gates[j * 2 + 1]);
                    c_gates_new.push(Gate {
                        func: match clause.kind {
                            ClauseKind::And => GateFunc::And,
                            ClauseKind::Xor => GateFunc::Xor,
                        },
                        i0: cur_id_0,
                        i1: cur_id_1,
                    });
                }
                // next level
                if ((literal_count >> 1) & 1) != 0 {
                    // odd gate
                    let cur_id = gates.len();
                    let cur_id_0 = T::try_from(input_len + cur_id).unwrap();
                    gates.push(c_gates.pop().unwrap());
                    let (l0, n0) = clause.literals[literal_count];
                    let (l0, n0) = if l0 < circuit.input_len {
                        (l0, n0)
                    } else {
                        let (i0, in0) = clauses_gates[usize::try_from(l0).unwrap() - input_len];
                        (i0, n0 ^ in0)
                    };
                    c_gates_new.push(Gate {
                        func: match clause.kind {
                            ClauseKind::And => {
                                if n0 {
                                    GateFunc::Nimpl
                                } else {
                                    GateFunc::And
                                }
                            }
                            ClauseKind::Xor => GateFunc::Xor,
                        },
                        i0: cur_id_0,
                        i1: l0,
                    });
                    literal_count += 1;
                }
                for j in 0..((clause.len() - literal_count) >> 1) {
                    let j = literal_count + j * 2;
                    let (l0, n0) = clause.literals[j];
                    let (l1, n1) = clause.literals[j + 1];
                    c_gates_new.push(get_gate(l0, n0, l1, n1));
                }
                c_gates = c_gates_new;
            } else {
                // organize in one level
                for j in 0..(clause.len() >> 1) {
                    let (l0, n0) = clause.literals[2 * j];
                    let (l1, n1) = clause.literals[2 * j + 1];
                    c_gates.push(get_gate(l0, n0, l1, n1));
                }
            }
            // create next level of parallelism
            while c_gates.len() >= 2 {
                let mut c_gates_new = vec![];
                for j in 0..(c_gates.len() >> 1) {
                    let cur_id = gates.len();
                    let cur_id_0 = T::try_from(input_len + cur_id).unwrap();
                    let cur_id_1 = T::try_from(input_len + cur_id + 1).unwrap();
                    gates.push(c_gates[j * 2]);
                    gates.push(c_gates[j * 2 + 1]);
                    c_gates_new.push(Gate {
                        func: match clause.kind {
                            ClauseKind::And => GateFunc::And,
                            ClauseKind::Xor => GateFunc::Xor,
                        },
                        i0: cur_id_0,
                        i1: cur_id_1,
                    });
                }
                c_gates = c_gates_new;
            }
            gates.push(c_gates[0]);
            let final_gate_id = T::try_from(input_len + gates.len() - 1).unwrap();
            clauses_gates.push((final_gate_id, clause_neg));
        }
        Circuit::new(
            circuit.input_len,
            gates,
            circuit.outputs.into_iter().map(|(l, n)| {
                let (l, cn) = clauses_gates[usize::try_from(l).unwrap() - input_len];
                (l, cn ^ n)
            }),
        )
        .unwrap()
    }
}

// Clause circuits

#[derive(Error, Debug)]
pub enum ClauseParseError<PIError> {
    #[error("Unknown kind")]
    UnknownKind,
    #[error("Syntax error")]
    SyntaxError,
    #[error("ParseIntError {0}")]
    ParseInt(#[from] PIError),
}

#[derive(Error, Debug)]
pub enum ClauseCircuitParseError<PIError> {
    #[error("Syntax error")]
    SyntaxError,
    #[error("Invalid circuit")]
    Invalid,
    #[error("ParseIntError {0}")]
    ParseInt(#[from] PIError),
    #[error("ClauseParseError {0}")]
    Clause(#[from] ClauseParseError<PIError>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClauseKind {
    And,
    Xor,
}

impl Display for ClauseKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ClauseKind::And => write!(f, "and"),
            ClauseKind::Xor => write!(f, "xor"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Clause<T> {
    pub kind: ClauseKind,
    pub literals: Vec<(T, bool)>,
}

impl<T> Clause<T> {
    #[inline]
    pub fn len(&self) -> usize {
        self.literals.len()
    }
}

impl<T: Clone + Copy + Debug> Display for Clause<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}(", self.kind)?;
        for (i, (l, n)) in self.literals.iter().enumerate() {
            write!(
                f,
                "{:?}{}{}",
                l,
                if *n { "n" } else { "" },
                if i + 1 < self.literals.len() {
                    ','
                } else {
                    ')'
                }
            )?;
        }
        Ok(())
    }
}

impl<T: Clone + Copy> Clause<T> {
    #[inline]
    pub fn new_and(literals: impl IntoIterator<Item = (T, bool)>) -> Self {
        Clause {
            kind: ClauseKind::And,
            literals: Vec::from_iter(literals),
        }
    }

    #[inline]
    pub fn new_xor(literals: impl IntoIterator<Item = (T, bool)>) -> Self {
        Clause {
            kind: ClauseKind::Xor,
            literals: Vec::from_iter(literals),
        }
    }
}

impl<T: Copy + Clone> Clause<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    /// Evaluate clause. Get values of argument from method arguments.
    #[inline]
    pub fn eval_args<Out>(&self, args: impl IntoIterator<Item = Out>) -> Out
    where
        Out: BitAnd<Output = Out> + BitXor<Output = Out> + Not<Output = Out> + Clone + Default,
    {
        let mut args = args.into_iter();
        if let Some(arg) = args.next() {
            let mut out = if self.literals[0].1 { !arg } else { arg };
            match self.kind {
                ClauseKind::And => {
                    for (i, x) in args.enumerate() {
                        out = out & if self.literals[i + 1].1 { !x } else { x };
                    }
                    out
                }
                ClauseKind::Xor => {
                    for (i, x) in args.enumerate() {
                        out = out ^ if self.literals[i + 1].1 { !x } else { x };
                    }
                    out
                }
            }
        } else {
            Out::default()
        }
    }

    /// Evaluate clause. Get values of argument from method arguments.
    #[inline]
    pub fn eval<Out>(&self, values: &[Out]) -> Out
    where
        Out: BitAnd<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Clone
            + Copy
            + Default,
    {
        match self.kind {
            ClauseKind::And => {
                if !self.literals.is_empty() {
                    let l = usize::try_from(self.literals[0].0).unwrap();
                    let mut out = if self.literals[0].1 {
                        !values[l]
                    } else {
                        values[l]
                    };
                    for (l, n) in self.literals.iter().skip(1) {
                        let l = usize::try_from(*l).unwrap();
                        out = out & if *n { !values[l] } else { values[l] };
                    }
                    out
                } else {
                    Out::default()
                }
            }
            ClauseKind::Xor => {
                let mut out = Out::default();
                for (l, n) in self.literals.iter() {
                    let l = usize::try_from(*l).unwrap();
                    out = out ^ if *n { !values[l] } else { values[l] };
                }
                out
            }
        }
    }
}

impl<T: Clone + Copy + FromStr> FromStr for Clause<T> {
    type Err = ClauseParseError<<T as FromStr>::Err>;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let (kind, mut r) = if src.starts_with("and(") {
            (ClauseKind::And, &src[4..])
        } else if src.starts_with("xor(") {
            (ClauseKind::Xor, &src[4..])
        } else {
            return Err(ClauseParseError::UnknownKind);
        };
        let mut literals = vec![];
        while !r.is_empty() {
            let (rnew, i0) = if let Some(p) = r.find([',', 'n', ')']) {
                let d = &r[0..p];
                let d = T::from_str(d)?;
                (&r[p..], d)
            } else {
                return Err(ClauseParseError::SyntaxError);
            };
            r = rnew;
            let (negated, rnew) = if r.chars().next().unwrap() == 'n' {
                (true, &r[1..])
            } else {
                (false, r)
            };
            literals.push((i0, negated));
            if rnew.chars().next().unwrap() == ')' && rnew.len() == 1 {
                break;
            }
            r = &rnew[1..];
        }

        Ok(Clause { kind, literals })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClauseCircuit<T> {
    input_len: T,
    clauses: Vec<Clause<T>>,
    outputs: Vec<(T, bool)>,
}

impl<T: Clone + Copy> ClauseCircuit<T> {
    pub fn clauses(&self) -> &[Clause<T>] {
        &self.clauses
    }

    pub unsafe fn clauses_mut(&mut self) -> &mut [Clause<T>] {
        &mut self.clauses
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
        self.clauses.len()
    }
}

impl<T: Clone + Copy + Debug> Display for ClauseCircuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let input_len = usize::try_from(self.input_len).unwrap();
        let mut output_map = vec![(0, false, false); input_len + self.clauses.len()];
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
        for (i, c) in self.clauses.iter().enumerate() {
            if output_map[input_len + i].2 {
                write!(
                    f,
                    " {}:{}{}",
                    c,
                    output_map[input_len + i].0,
                    if output_map[input_len + i].1 { "n" } else { "" }
                )?;
            } else {
                write!(f, " {}", c)?;
            }
        }
        write!(f, "}}({})", input_len)?;
        Ok(())
    }
}

impl<T: Clone + Copy + PartialOrd + Ord> ClauseCircuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    pub unsafe fn new_unchecked(
        input_len: T,
        clauses: impl IntoIterator<Item = Clause<T>>,
        outputs: impl IntoIterator<Item = (T, bool)>,
    ) -> Self {
        Self {
            input_len,
            clauses: Vec::from_iter(clauses),
            outputs: Vec::from_iter(outputs),
        }
    }

    pub fn new(
        input_len: T,
        clauses: impl IntoIterator<Item = Clause<T>>,
        outputs: impl IntoIterator<Item = (T, bool)>,
    ) -> Option<Self> {
        let out = Self {
            input_len,
            clauses: Vec::from_iter(clauses),
            outputs: Vec::from_iter(outputs),
        };
        // verify
        if out.verify() {
            Some(out)
        } else {
            None
        }
    }

    /// Verification:
    /// All inputs and gate outputs must be used except output gates.
    /// At least one output must be a last gate ouput.
    pub fn verify(&self) -> bool {
        // check inputs and gate outputs
        // gate have input less than its output.
        let input_len = usize::try_from(self.input_len).unwrap();
        let output_num = input_len + self.clauses.len();
        let mut used_inputs = vec![false; output_num];
        for (i, c) in self.clauses.iter().enumerate() {
            let cur_index = input_len + i;
            if c.len() < 2 {
                return false;
            }
            for (l, _) in &c.literals {
                let l = usize::try_from(*l).unwrap();
                if l >= cur_index {
                    return false;
                }
                used_inputs[l] = true;
            }
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
        if !self.outputs.is_empty() && !self.clauses.is_empty() {
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

    /// Evaluate gates results (without output negations).
    pub fn eval_to<Out>(&self, clause_outputs: &mut [Out])
    where
        Out: BitAnd<Output = Out>
            + BitOr<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Default
            + Clone
            + Copy,
    {
        let input_len = usize::try_from(self.input_len).unwrap();
        assert_eq!(clause_outputs.len(), input_len + self.clauses.len());
        for (i, c) in self.clauses.iter().enumerate() {
            clause_outputs[input_len + i] = c.eval(&clause_outputs);
        }
    }

    /// Evaluate circuit return outputs (including negation of outputs).
    pub fn eval<Out>(&self, inputs: impl IntoIterator<Item = Out>) -> Vec<Out>
    where
        Out: BitAnd<Output = Out>
            + BitOr<Output = Out>
            + BitXor<Output = Out>
            + Not<Output = Out>
            + Default
            + Clone
            + Copy,
    {
        let mut clause_outputs = Vec::from_iter(inputs);
        let input_len = usize::try_from(self.input_len).unwrap();
        clause_outputs.resize(input_len + self.clauses.len(), Out::default());
        self.eval_to(&mut clause_outputs);
        self.outputs
            .iter()
            .map(|&(i, n)| {
                let out = clause_outputs[usize::try_from(i).unwrap()].clone();
                if n {
                    !out
                } else {
                    out
                }
            })
            .collect()
    }
}

impl<T> FromStr for ClauseCircuit<T>
where
    T: Clone + Copy + FromStr + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Err = ClauseCircuitParseError<<T as FromStr>::Err>;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        if src.starts_with("{") {
            let mut input_len = T::default();
            let mut input_touched = vec![];
            let mut output_len = T::default();
            let mut outputs = vec![];
            let mut r = &src[1..];
            let mut end = false;
            // first loop to parse inputs
            loop {
                if let Some(c) = r.chars().next() {
                    if c.is_digit(10) {
                        let p = if let Some(p) = r.find([' ', ':', '}']) {
                            p
                        } else {
                            return Err(ClauseCircuitParseError::SyntaxError);
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
                                    // parse output
                                    let d = &r[0..p];
                                    let output = T::from_str(d)?;
                                    r = &r[p..];
                                    // output negation mark
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

                                    // skip next char or end
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
                                    return Err(ClauseCircuitParseError::SyntaxError);
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
                } else {
                    return Err(ClauseCircuitParseError::SyntaxError);
                }
            }

            // check whether all inputs are filled
            if !input_touched.into_iter().all(|x| x) {
                return Err(ClauseCircuitParseError::Invalid);
            }

            let mut clauses = vec![];
            let input_len = usize::try_from(input_len).unwrap();

            // second loop to parse clauses
            while !end {
                let p = if let Some(p) = r.find(')') {
                    p + 1
                } else {
                    return Err(ClauseCircuitParseError::SyntaxError);
                };
                let gstr = &r[0..p];
                clauses.push(Clause::<T>::from_str(gstr)?);
                r = &r[p..];

                match r.chars().next().unwrap() {
                    ' ' => {
                        r = &r[1..];
                        continue;
                    }
                    ':' => {
                        r = &r[1..];
                        if let Some(p) = r.find(['n', ' ', ':', '}']) {
                            // parse output
                            let d = &r[0..p];
                            let output = T::from_str(d)?;
                            r = &r[p..];
                            // output negation mark
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
                                Some((T::try_from(input_len + clauses.len() - 1).unwrap(), neg));

                            // skip next char or end
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
                            return Err(ClauseCircuitParseError::SyntaxError);
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

            // check whether if all outputs are filled
            if !outputs.iter().all(|x| x.is_some()) {
                return Err(ClauseCircuitParseError::Invalid);
            }

            // parse last part (number of inputs)
            if let Some(c) = r.chars().next() {
                if c == '(' {
                    if let Some(p) = r.find(')') {
                        let d = &r[1..p];
                        let res_input_len = T::from_str(d)?;
                        if res_input_len != T::try_from(input_len).unwrap() {
                            return Err(ClauseCircuitParseError::Invalid);
                        }
                    } else {
                        return Err(ClauseCircuitParseError::SyntaxError);
                    }
                } else {
                    return Err(ClauseCircuitParseError::SyntaxError);
                }
            }

            if let Some(c) = ClauseCircuit::new(
                T::try_from(input_len).unwrap(),
                clauses,
                outputs.into_iter().map(|x| x.unwrap()),
            ) {
                return Ok(c);
            } else {
                return Err(ClauseCircuitParseError::Invalid);
            }
        } else {
            return Err(ClauseCircuitParseError::SyntaxError);
        }
    }
}

impl<T: Clone + Copy + Ord + PartialEq + Eq> From<Circuit<T>> for ClauseCircuit<T>
where
    T: Default + TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn from(circuit: Circuit<T>) -> Self {
        ClauseCircuit::new(circuit.input_len, [], []).unwrap()
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
        // two output connected to one gate - first normal, second negated
        assert!(Circuit::new(
            3,
            [Gate::new_xor(0, 1), Gate::new_xor(2, 3)],
            [(3, false), (4, false), (4, true)]
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

    #[test]
    fn test_clause() {
        let inputs = [0b10101010, 0b11001100, 0b11110000];
        for (c, exp) in [
            (
                Clause::new_and([(0, false), (1, false), (2, false)]),
                0b10000000,
            ),
            (
                Clause::new_and([(0, false), (1, false), (2, true)]),
                0b00001000,
            ),
            (
                Clause::new_and([(0, true), (1, false), (2, false)]),
                0b01000000,
            ),
            (
                Clause::new_and([(0, false), (1, true), (2, true)]),
                0b00000010,
            ),
            (
                Clause::new_xor([(0, false), (1, false), (2, false)]),
                0b10010110,
            ),
            (
                Clause::new_xor([(0, false), (1, false), (2, true)]),
                0b01101001,
            ),
            (
                Clause::new_xor([(0, true), (1, false), (2, false)]),
                0b01101001,
            ),
            (
                Clause::new_xor([(0, false), (1, true), (2, true)]),
                0b10010110,
            ),
        ] {
            assert_eq!(exp, c.eval_args(inputs.clone()) & 0b11111111);
        }

        for (c, exp) in [
            (Clause::<u8>::new_and([]), 0b00000000),
            (Clause::<u8>::new_xor([]), 0b00000000),
        ] {
            assert_eq!(exp, c.eval_args::<u8>([]) & 0b11111111);
        }

        for (c, exp) in [
            (
                Clause::new_and([(0, false), (1, false), (2, false)]),
                0b10000000,
            ),
            (
                Clause::new_and([(0, false), (1, false), (2, true)]),
                0b00001000,
            ),
            (
                Clause::new_and([(0, true), (1, false), (2, false)]),
                0b01000000,
            ),
            (
                Clause::new_and([(0, false), (1, true), (2, true)]),
                0b00000010,
            ),
            (
                Clause::new_and([(2, false), (1, true), (0, true)]),
                0b00010000,
            ),
            (Clause::new_and([]), 0b00000000),
            (
                Clause::new_xor([(0, false), (1, false), (2, false)]),
                0b10010110,
            ),
            (
                Clause::new_xor([(0, false), (1, false), (2, true)]),
                0b01101001,
            ),
            (
                Clause::new_xor([(0, true), (1, false), (2, false)]),
                0b01101001,
            ),
            (
                Clause::new_xor([(0, false), (1, true), (2, true)]),
                0b10010110,
            ),
            (
                Clause::new_xor([(2, false), (1, true), (0, true)]),
                0b10010110,
            ),
            (Clause::new_xor([]), 0b00000000),
        ] {
            assert_eq!(exp, c.eval(&inputs) & 0b11111111);
        }
    }

    #[test]
    fn test_clause_display() {
        assert_eq!(
            "and(0,1n,2n)",
            format!("{}", Clause::new_and([(0, false), (1, true), (2, true)]))
        );
        assert_eq!(
            "and(0,1n,2)",
            format!("{}", Clause::new_and([(0, false), (1, true), (2, false)]))
        );
        assert_eq!(
            "xor(0,1n,2n)",
            format!("{}", Clause::new_xor([(0, false), (1, true), (2, true)]))
        );
        assert_eq!(
            "xor(0,1n,2)",
            format!("{}", Clause::new_xor([(0, false), (1, true), (2, false)]))
        );
    }

    #[test]
    fn test_clause_circuit_new() {
        assert!(
            ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(2, false)])
                .is_some()
        );
        assert!(
            ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(2, true)])
                .is_some()
        );
        assert!(
            ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(3, false)])
                .is_none()
        );
        assert!(
            ClauseCircuit::new(2, [Clause::new_xor([(1, false), (1, false)])], [(3, false)])
                .is_none()
        );
        assert!(
            ClauseCircuit::new(2, [Clause::new_xor([(0, false), (0, false)])], [(3, false)])
                .is_none()
        );
        assert!(
            ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(1, false)])
                .is_none()
        );

        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (3, false)])
            ],
            [(4, false)]
        )
        .is_some());
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (1, false)])
            ],
            [(4, false)]
        )
        .is_none());
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (3, false)])
            ],
            [(3, false), (4, false)]
        )
        .is_some());
        // two output connected to one gate - first normal, second negated
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (3, false)])
            ],
            [(3, false), (4, false), (4, true)]
        )
        .is_some());
        // 3 (gate index 0) and 4 (gate index 1) are outputs - can be unconnected
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(0, false), (2, false)])
            ],
            [(3, false), (4, false)]
        )
        .is_some());
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(1, false), (2, false)]),
                Clause::new_xor([(0, false), (4, false)])
            ],
            [(3, false), (5, false)]
        )
        .is_some());
        // first gate is not connected later
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(1, false), (2, false)]),
                Clause::new_xor([(0, false), (4, false)])
            ],
            [(5, false)]
        )
        .is_none());
        // accept same inputs
        assert!(ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (2, true)]),
                Clause::new_xor([(0, false), (4, false)])
            ],
            [(3, false), (5, false)]
        )
        .is_some());
        assert!(ClauseCircuit::new(1, [], [(0, false)]).is_some());
        assert!(ClauseCircuit::new(2, [], [(0, false), (1, true)]).is_some());
        assert!(ClauseCircuit::new(0, [], []).is_some());
    }

    #[test]
    fn clause_circuit_eval() {
        let circuit = ClauseCircuit::new(
            3,
            [
                Clause::new_xor([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (3, false)]),
                Clause::new_and([(2, false), (3, false)]),
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_and([(5, true), (6, true)]),
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
    }

    #[test]
    fn clause_circuit_display() {
        assert_eq!(
            concat!(
                "{0 1 2 3 and(0,1n,2):0 and(1,2) and(0,3) and(1,3) xor(5,6):1 ",
                "and(5,6) xor(7,8,9n):2 and(7,9):3}(4)"
            ),
            format!(
                "{}",
                ClauseCircuit::new(
                    4,
                    [
                        Clause::new_and([(0, false), (1, true), (2, false)]),
                        Clause::new_and([(1, false), (2, false)]),
                        Clause::new_and([(0, false), (3, false)]),
                        Clause::new_and([(1, false), (3, false)]),
                        Clause::new_xor([(5, false), (6, false)]),
                        Clause::new_and([(5, false), (6, false)]),
                        Clause::new_xor([(7, false), (8, false), (9, true)]),
                        Clause::new_and([(7, false), (9, false)]),
                    ],
                    [(4, false), (8, false), (10, false), (11, false)],
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn test_clause_from_str() {
        assert_eq!(
            Clause::new_and([(4, false), (6, false)]),
            Clause::from_str("and(4,6)").unwrap()
        );
        assert_eq!(
            Clause::new_xor([(4, false), (6, false)]),
            Clause::from_str("xor(4,6)").unwrap()
        );
        assert_eq!(
            Clause::new_and([(6764, false), (116, false), (5671, false)]),
            Clause::from_str("and(6764,116,5671)").unwrap()
        );
        assert_eq!(
            Clause::new_and([(6764, false), (116, true), (5671, true)]),
            Clause::from_str("and(6764,116n,5671n)").unwrap()
        );
        assert_eq!(
            Err("Syntax error".to_string()),
            Clause::<u8>::from_str("xor(4,6").map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("ParseIntError invalid digit found in string".to_string()),
            Clause::<u8>::from_str("xor(4x,6)").map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("ParseIntError invalid digit found in string".to_string()),
            Clause::<u8>::from_str("xor(4,6x)").map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Unknown kind".to_string()),
            Clause::<u8>::from_str("xoor(4,6)").map_err(|x| x.to_string())
        );
    }

    #[test]
    fn test_clause_circuit_from_str() {
        assert_eq!(
            ClauseCircuit::new(1, [], [(0, false)]).unwrap(),
            ClauseCircuit::from_str("{0:0}(1)").unwrap()
        );
        assert_eq!(
            ClauseCircuit::new(
                3,
                [
                    Clause::new_and([(0, false), (1, false)]),
                    Clause::new_and([(0, true), (2, true)]),
                    Clause::new_xor([(3, false), (4, false)]),
                ],
                [(5, false)]
            )
            .unwrap(),
            ClauseCircuit::from_str("{0 1 2 and(0,1) and(0n,2n) xor(3,4):0}(3)").unwrap()
        );
        assert_eq!(
            ClauseCircuit::new(
                3,
                [
                    Clause::new_and([(0, false), (1, false)]),
                    Clause::new_and([(0, true), (2, true)]),
                    Clause::new_xor([(3, false), (4, false)]),
                ],
                [(5, false), (4, true), (2, true)]
            )
            .unwrap(),
            ClauseCircuit::from_str("{0 1 2:2n and(0,1) and(0n,2n):1n xor(3,4):0}(3)").unwrap()
        );
        assert_eq!(
            ClauseCircuit::new(
                3,
                [
                    Clause::new_and([(0, false), (1, false)]),
                    Clause::new_and([(0, true), (1, false), (2, true)]),
                    Clause::new_xor([(3, false), (4, false)]),
                ],
                [(5, false), (4, true), (2, true)]
            )
            .unwrap(),
            ClauseCircuit::from_str("{0 1 2:2n and(0,1) and(0n,1,2n):1n xor(3,4):0}(3)").unwrap()
        );
    }

    #[test]
    fn test_circuit_from_clause_circuit_0() {
        for (c, eg, ng) in [
            (
                Clause::new_and([(0, false), (1, false)]),
                Gate::new_and(0, 1),
                false,
            ),
            (
                Clause::new_and([(0, true), (1, false)]),
                Gate::new_nimpl(1, 0),
                false,
            ),
            (
                Clause::new_and([(0, false), (1, true)]),
                Gate::new_nimpl(0, 1),
                false,
            ),
            (
                Clause::new_and([(0, true), (1, true)]),
                Gate::new_nor(0, 1),
                false,
            ),
            (
                Clause::new_xor([(0, false), (1, false)]),
                Gate::new_xor(0, 1),
                false,
            ),
            (
                Clause::new_xor([(0, true), (1, false)]),
                Gate::new_xor(0, 1),
                true,
            ),
            (
                Clause::new_xor([(0, false), (1, true)]),
                Gate::new_xor(0, 1),
                true,
            ),
            (
                Clause::new_xor([(0, true), (1, true)]),
                Gate::new_xor(0, 1),
                false,
            ),
        ] {
            assert_eq!(
                Circuit::new(2, [eg], [(2, ng)]).unwrap(),
                Circuit::from(ClauseCircuit::new(2, [c.clone()], [(2, false)]).unwrap()),
                "testgc {}",
                c
            );
        }
        // include not-negated clause and negated output
        assert_eq!(
            Circuit::new(2, [Gate::new_xor(0, 1),], [(2, true)]).unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    2,
                    [Clause::new_xor([(0, false), (1, false),]),],
                    [(2, true)]
                )
                .unwrap()
            )
        );
        // include negated clause and negated output
        assert_eq!(
            Circuit::new(2, [Gate::new_xor(0, 1),], [(2, false)]).unwrap(),
            Circuit::from(
                ClauseCircuit::new(2, [Clause::new_xor([(0, true), (1, false),]),], [(2, true)])
                    .unwrap()
            )
        );

        assert_eq!(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(4, 5)
                ],
                [(6, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    4,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false)
                    ]),],
                    [(4, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                4,
                [
                    Gate::new_nimpl(1, 0),
                    Gate::new_nimpl(2, 3),
                    Gate::new_and(4, 5)
                ],
                [(6, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    4,
                    [Clause::new_and([
                        (0, true),
                        (1, false),
                        (2, false),
                        (3, true)
                    ]),],
                    [(4, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(3, [Gate::new_and(0, 1), Gate::new_and(3, 2),], [(4, false)]).unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    3,
                    [Clause::new_and([(0, false), (1, false), (2, false)]),],
                    [(3, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                3,
                [Gate::new_and(0, 1), Gate::new_nimpl(3, 2),],
                [(4, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    3,
                    [Clause::new_and([(0, false), (1, false), (2, true)]),],
                    [(3, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                5,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(5, 2),
                    Gate::new_and(3, 4),
                    Gate::new_and(6, 7),
                ],
                [(8, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    5,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false),
                        (4, false)
                    ]),],
                    [(5, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                6,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(6, 7),
                    Gate::new_and(4, 5),
                    Gate::new_and(8, 9),
                ],
                [(10, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    6,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false),
                        (4, false),
                        (5, false),
                    ]),],
                    [(6, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                7,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(4, 5),
                    Gate::new_and(7, 8),
                    Gate::new_and(9, 6),
                    Gate::new_and(10, 11),
                ],
                [(12, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    7,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false),
                        (4, false),
                        (5, false),
                        (6, false),
                    ]),],
                    [(7, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                8,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(4, 5),
                    Gate::new_and(6, 7),
                    Gate::new_and(8, 9),
                    Gate::new_and(10, 11),
                    Gate::new_and(12, 13),
                ],
                [(14, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    8,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false),
                        (4, false),
                        (5, false),
                        (6, false),
                        (7, false),
                    ]),],
                    [(8, false)]
                )
                .unwrap()
            )
        );

        assert_eq!(
            Circuit::new(
                10,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(10, 11),
                    Gate::new_and(4, 5),
                    Gate::new_and(6, 7),
                    Gate::new_and(8, 9),
                    Gate::new_and(12, 13),
                    Gate::new_and(14, 15),
                    Gate::new_and(16, 17),
                ],
                [(18, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    10,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false),
                        (4, false),
                        (5, false),
                        (6, false),
                        (7, false),
                        (8, false),
                        (9, false),
                    ]),],
                    [(10, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                13,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(4, 5),
                    Gate::new_and(6, 7),
                    Gate::new_and(8, 9),
                    Gate::new_and(13, 14),
                    Gate::new_and(15, 16),
                    Gate::new_and(17, 10),
                    Gate::new_and(11, 12),
                    Gate::new_and(18, 19),
                    Gate::new_and(20, 21),
                    Gate::new_and(22, 23),
                ],
                [(24, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    13,
                    [Clause::new_and([
                        (0, false),
                        (1, false),
                        (2, false),
                        (3, false),
                        (4, false),
                        (5, false),
                        (6, false),
                        (7, false),
                        (8, false),
                        (9, false),
                        (10, false),
                        (11, false),
                        (12, false),
                    ]),],
                    [(13, false)]
                )
                .unwrap()
            )
        );
    }

    #[test]
    fn test_circuit_from_clause_circuit() {
        assert_eq!(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(4, 2),
                    Gate::new_xor(0, 1),
                    Gate::new_xor(6, 3),
                    Gate::new_nor(1, 2),
                    Gate::new_and(8, 3),
                    Gate::new_nimpl(7, 5),
                    Gate::new_and(10, 9),
                ],
                [(5, false), (11, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    4,
                    [
                        Clause::new_and([(0, false), (1, false), (2, false),]),
                        Clause::new_xor([(0, false), (1, false), (3, false),]),
                        Clause::new_and([(1, true), (2, true), (3, false),]),
                        Clause::new_and([(4, true), (5, false), (6, false),]),
                    ],
                    [(4, false), (7, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(4, 2),
                    Gate::new_xor(0, 1),
                    Gate::new_xor(6, 3),
                    Gate::new_nor(1, 2),
                    Gate::new_and(8, 3),
                    Gate::new_nor(5, 7),
                    Gate::new_and(10, 9),
                ],
                [(5, false), (11, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    4,
                    [
                        Clause::new_and([(0, false), (1, false), (2, false),]),
                        Clause::new_xor([(0, false), (1, true), (3, false),]),
                        Clause::new_and([(1, true), (2, true), (3, false),]),
                        Clause::new_and([(4, true), (5, false), (6, false),]),
                    ],
                    [(4, false), (7, false)]
                )
                .unwrap()
            )
        );
        assert_eq!(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(4, 2),
                    Gate::new_xor(0, 1),
                    Gate::new_xor(6, 3),
                    Gate::new_nor(1, 2),
                    Gate::new_and(8, 3),
                    Gate::new_nimpl(7, 5),
                    Gate::new_and(10, 9),
                ],
                [(5, false), (11, false)]
            )
            .unwrap(),
            Circuit::from(
                ClauseCircuit::new(
                    4,
                    [
                        Clause::new_and([(0, false), (1, false), (2, false),]),
                        Clause::new_xor([(0, false), (1, true), (3, false),]),
                        Clause::new_and([(1, true), (2, true), (3, false),]),
                        Clause::new_and([(4, true), (5, true), (6, false),]),
                    ],
                    [(4, false), (7, false)]
                )
                .unwrap()
            )
        );
    }
}
