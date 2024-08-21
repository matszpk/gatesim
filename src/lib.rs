use std::cmp::{Ord, Ordering, PartialOrd};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::Hash;
use std::iter;
use std::ops::{BitAnd, BitOr, BitXor, Not};
use std::str::FromStr;

use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use thiserror::Error;

pub struct FmtLiner<'a, T> {
    pub inner: &'a T,
    pub indent: usize,
    pub indent2: usize,
}

impl<'a, T> FmtLiner<'a, T> {
    pub fn new(inner: &'a T, indent: usize, indent2: usize) -> Self {
        Self {
            inner,
            indent,
            indent2,
        }
    }
}

fn to_single_spaces(s: &str) -> String {
    let mut out = String::new();
    let mut start = true;
    let mut count = 0;
    for c in s.chars() {
        if c.is_whitespace() {
            if !start && count < 1 {
                out.push(' ');
            }
            count += 1;
        } else {
            out.push(c);
            start = false;
            count = 0;
        }
    }
    if count >= 1 {
        out.pop();
    }
    out
}

#[inline]
fn skip_single_space(s: &str) -> &str {
    if let Some(b' ') = s.bytes().next() {
        &s[1..]
    } else {
        s
    }
}

/// Parse error for Gate.
#[derive(Error, Debug)]
pub enum GateParseError<PIError> {
    #[error("Unknown function")]
    UnknownFunction,
    #[error("Syntax error")]
    SyntaxError,
    #[error("ParseIntError {0}")]
    ParseInt(#[from] PIError),
}

/// Parse error for Circuit.
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

/// Gate function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum GateFunc {
    /// And logical operation.
    And,
    /// Not-Or logical operation: !(a or b).
    Nor,
    /// Nimpl logical operation: (a and !b) <=> !(!a or b).
    Nimpl,
    /// Xor logical operation: (a xor b).
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
        // order gate inputs by id inputs. selfrevord - true if reversed order of gates input
        let (selfi0, selfi1, selfrevord) = if let Some(ord) = self.i0.partial_cmp(&self.i1) {
            if ord == Ordering::Less {
                (self.i0, self.i1, false)
            } else {
                (self.i1, self.i0, true)
            }
        } else {
            (self.i1, self.i0, true)
        };
        // order gate inputs by id inputs. selfrevord - true if reversed order of gates input
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
        let src = to_single_spaces(src);
        let (func, r) = if src.starts_with("and(") {
            (GateFunc::And, &src[4..])
        } else if src.starts_with("nor(") {
            (GateFunc::Nor, &src[4..])
        } else if src.starts_with("nimpl(") {
            (GateFunc::Nimpl, &src[6..])
        } else if src.starts_with("xor(") {
            (GateFunc::Xor, &src[4..])
        } else if src.starts_with("and (") {
            (GateFunc::And, &src[5..])
        } else if src.starts_with("nor (") {
            (GateFunc::Nor, &src[5..])
        } else if src.starts_with("nimpl (") {
            (GateFunc::Nimpl, &src[7..])
        } else if src.starts_with("xor (") {
            (GateFunc::Xor, &src[5..])
        } else {
            return Err(GateParseError::UnknownFunction);
        };
        let r = skip_single_space(r);
        let (r, i0) = if let Some(p) = r.find(',') {
            let r = skip_single_space(r);
            let d = &r[0..p];
            let d = if let Some(b' ') = d.bytes().last() {
                &d[0..p - 1]
            } else {
                d
            };
            let d = T::from_str(d)?;
            (&r[p + 1..], d)
        } else {
            return Err(GateParseError::SyntaxError);
        };

        let r = skip_single_space(r);
        let (r, i1) = if let Some(p) = r.find(')') {
            let r = skip_single_space(r);
            let d = &r[0..p];
            let d = if let Some(b' ') = d.bytes().last() {
                &d[0..p - 1]
            } else {
                d
            };
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

/// serde support

impl<T: Clone + Copy + Debug> Serialize for Gate<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

struct GateVisitor<T> {
    t: std::marker::PhantomData<T>,
}

impl<'de, T: Clone + Copy + FromStr> Visitor<'de> for GateVisitor<T>
where
    <T as FromStr>::Err: Debug,
{
    type Value = Gate<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("gate")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        Gate::<T>::from_str(v).map_err(|e| E::custom(format!("{:?}", e)))
    }
}

impl<'de, T: Clone + Copy + FromStr> Deserialize<'de> for Gate<T>
where
    <T as FromStr>::Err: Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<Gate<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(GateVisitor::<T> {
            t: std::marker::PhantomData,
        })
    }
}

/// Single binary gate.
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

impl<T> Circuit<T>
where
    T: Clone + Copy + Ord,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    pub fn add_output(&mut self, out: (T, bool)) {
        let input_len = usize::try_from(self.input_len).unwrap();
        assert!(out.0 < T::try_from(self.gates.len() + input_len).unwrap());
        self.outputs.push(out);
    }
}

impl<T: Clone + Copy + Debug> Display for Circuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let input_len = usize::try_from(self.input_len).unwrap();
        let mut output_map = vec![vec![]; input_len + self.gates.len()];
        write!(f, "{{")?;
        for (i, (v, n)) in self.outputs.iter().enumerate() {
            output_map[usize::try_from(*v).unwrap()].push((i, *n));
        }
        // first circuit inputs
        for i in 0..input_len {
            write!(f, "{}", i)?;
            for op in &output_map[i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
            if i + 1 < input_len {
                write!(f, " ")?;
            }
        }
        // next circuit gates
        for (i, g) in self.gates.iter().enumerate() {
            write!(f, " {}", g)?;
            for op in &output_map[input_len + i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
        }
        write!(f, "}}({})", input_len)?;
        Ok(())
    }
}

impl<'a, T: Clone + Copy + Debug> Display for FmtLiner<'a, Circuit<T>>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let input_len = usize::try_from(self.inner.input_len).unwrap();
        let mut output_map = vec![vec![]; input_len + self.inner.gates.len()];
        let indent = iter::repeat(' ').take(self.indent).collect::<String>();
        let indent2 = iter::repeat(' ').take(self.indent2).collect::<String>();
        writeln!(f, "{}{{", indent)?;
        for (i, (v, n)) in self.inner.outputs.iter().enumerate() {
            output_map[usize::try_from(*v).unwrap()].push((i, *n));
        }
        // first circuit inputs
        for i in 0..input_len {
            write!(f, "{}{}", indent2, i)?;
            for op in &output_map[i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
            if i + 1 < input_len {
                writeln!(f, "")?;
            }
        }
        // next circuit gates
        for (i, g) in self.inner.gates.iter().enumerate() {
            write!(f, "\n{}{}", indent2, g)?;
            for op in &output_map[input_len + i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
        }
        writeln!(f, "\n{}}}({})", indent, input_len)?;
        Ok(())
    }
}

/// Circuit defined as list of gates connected together, number of inputs and list of outputs.
/// Any output can be logically negated. Number in gate input is index of output.
/// First outputs are inputs. Next inputs are outputs of previous gates.
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
        let src = to_single_spaces(src);
        if src.starts_with("{") {
            let mut input_len = T::default();
            let mut input_touched = vec![];
            let mut output_len = T::default();
            let mut outputs = vec![];
            let mut r = &src[1..];
            let mut end = false;
            if r == "}(0)" {
                return Ok(Circuit::new(T::default(), [], []).unwrap());
            }
            if let Some(' ') = r.chars().next() {
                r = &r[1..];
            }
            // first loop to parse inputs
            'a: loop {
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
                                if let Some('}') = r.chars().next() {
                                    r = &r[1..];
                                    end = true;
                                    break;
                                }
                                continue;
                            }
                            ':' => {
                                r = &r[1..];
                                loop {
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
                                            outputs
                                                .resize(usize::try_from(output_len).unwrap(), None);
                                        }
                                        outputs[usize::try_from(output).unwrap()] =
                                            Some((input, neg));

                                        // skip next char or end
                                        match r.chars().next().unwrap() {
                                            ' ' => {
                                                r = &r[1..];
                                                if let Some('}') = r.chars().next() {
                                                    r = &r[1..];
                                                    end = true;
                                                    break 'a;
                                                }
                                                break;
                                            }
                                            '}' => {
                                                r = &r[1..];
                                                end = true;
                                                break 'a;
                                            }
                                            ':' => {
                                                r = &r[1..];
                                            }
                                            _ => {
                                                return Err(CircuitParseError::SyntaxError);
                                            }
                                        }
                                    } else {
                                        return Err(CircuitParseError::SyntaxError);
                                    }
                                }
                            }
                            '}' => {
                                r = &r[1..];
                                end = true;
                                break;
                            }
                            _ => {
                                return Err(CircuitParseError::SyntaxError);
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
            'a: while !end {
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
                        if let Some('}') = r.chars().next() {
                            r = &r[1..];
                            break;
                        }
                        continue;
                    }
                    ':' => {
                        r = &r[1..];
                        loop {
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
                                        if let Some('}') = r.chars().next() {
                                            r = &r[1..];
                                            break 'a;
                                        }
                                        break;
                                    }
                                    '}' => {
                                        r = &r[1..];
                                        break 'a;
                                    }
                                    ':' => {
                                        r = &r[1..];
                                    }
                                    _ => {
                                        return Err(CircuitParseError::SyntaxError);
                                    }
                                }
                            } else {
                                return Err(CircuitParseError::SyntaxError);
                            }
                        }
                    }
                    '}' => {
                        r = &r[1..];
                        break;
                    }
                    _ => {
                        return Err(CircuitParseError::SyntaxError);
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
                        if !r[p + 1..].is_empty() {
                            return Err(CircuitParseError::SyntaxError);
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

/// serde support

impl<T: Clone + Copy + Debug> Serialize for Circuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}", FmtLiner::new(self, 4, 8)))
    }
}

struct CircuitVisitor<T> {
    t: std::marker::PhantomData<T>,
}

impl<'de, T> Visitor<'de> for CircuitVisitor<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    type Value = Circuit<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("circuit")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        Circuit::<T>::from_str(v).map_err(|e| E::custom(format!("{:?}", e)))
    }
}

impl<'de, T> Deserialize<'de> for Circuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<Circuit<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(CircuitVisitor::<T> {
            t: std::marker::PhantomData,
        })
    }
}

impl<T: Clone + Copy + PartialOrd + Ord> Circuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    /// unsafe version without verifying circuit.
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

    /// safe constructor with verifying circuit.
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
    /// Converts ClauseCircuit into Circuit with parallel ordering of gates.
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
                    let (i1, in1) = clauses_gates[usize::try_from(l1).unwrap() - input_len];
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
                clause.literals.iter().fold(false, |a, (l, n)| {
                    if *l < circuit.input_len {
                        a ^ n
                    } else {
                        let (_, in0) = clauses_gates[usize::try_from(*l).unwrap() - input_len];
                        a ^ n ^ in0
                    }
                })
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
                if l >= circuit.input_len {
                    let (l, cn) = clauses_gates[usize::try_from(l).unwrap() - input_len];
                    (l, cn ^ n)
                } else {
                    (l, n)
                }
            }),
        )
        .unwrap()
    }
}

impl<T: Clone + Copy + Ord + PartialEq + Eq> Circuit<T>
where
    T: Default + TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    /// Converts ClauseCircuit into Circuit with sequential ordering of gates.
    pub fn from_seq(circuit: ClauseCircuit<T>) -> Self {
        let mut clauses_gates: Vec<(T, bool)> = vec![];
        let mut gates = vec![];
        let input_len = usize::try_from(circuit.input_len).unwrap();
        for clause in circuit.clauses {
            // organize gates in sequential way

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
                    let (i1, in1) = clauses_gates[usize::try_from(l1).unwrap() - input_len];
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
            let clause_neg = if clause.kind == ClauseKind::Xor {
                clause.literals.iter().fold(false, |a, (l, n)| {
                    if *l < circuit.input_len {
                        a ^ n
                    } else {
                        let (_, in0) = clauses_gates[usize::try_from(*l).unwrap() - input_len];
                        a ^ n ^ in0
                    }
                })
            } else {
                false
            };

            {
                let (l0, n0) = clause.literals[0];
                let (l1, n1) = clause.literals[1];
                gates.push(get_gate(l0, n0, l1, n1));
            }
            for &(l0, n0) in &clause.literals[2..] {
                let cur_id_0 = T::try_from(input_len + gates.len() - 1).unwrap();
                let (l0, n0) = if l0 < circuit.input_len {
                    (l0, n0)
                } else {
                    let (i0, in0) = clauses_gates[usize::try_from(l0).unwrap() - input_len];
                    (i0, n0 ^ in0)
                };
                gates.push(Gate {
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
            }

            let final_gate_id = T::try_from(input_len + gates.len() - 1).unwrap();
            clauses_gates.push((final_gate_id, clause_neg));
        }
        Circuit::new(
            circuit.input_len,
            gates,
            circuit.outputs.into_iter().map(|(l, n)| {
                if l >= circuit.input_len {
                    let (l, cn) = clauses_gates[usize::try_from(l).unwrap() - input_len];
                    (l, cn ^ n)
                } else {
                    (l, n)
                }
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
    /// And clause.
    And,
    /// Xor clause.
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

    #[inline]
    pub fn clear(&mut self) {
        self.literals.clear();
    }
}

impl<T: Clone + Copy> From<Gate<T>> for Clause<T> {
    fn from(g: Gate<T>) -> Clause<T> {
        match g.func {
            GateFunc::And => Clause::new_and([(g.i0, false), (g.i1, false)]),
            GateFunc::Nor => Clause::new_and([(g.i0, true), (g.i1, true)]),
            GateFunc::Nimpl => Clause::new_and([(g.i0, false), (g.i1, true)]),
            GateFunc::Xor => Clause::new_xor([(g.i0, false), (g.i1, false)]),
        }
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

/// serde support

impl<T: Clone + Copy + Debug> Serialize for Clause<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

struct ClauseVisitor<T> {
    t: std::marker::PhantomData<T>,
}

impl<'de, T: Clone + Copy + FromStr> Visitor<'de> for ClauseVisitor<T>
where
    <T as FromStr>::Err: Debug,
{
    type Value = Clause<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("clause")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        Clause::<T>::from_str(v).map_err(|e| E::custom(format!("{:?}", e)))
    }
}

impl<'de, T: Clone + Copy + FromStr> Deserialize<'de> for Clause<T>
where
    <T as FromStr>::Err: Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<Clause<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(ClauseVisitor::<T> {
            t: std::marker::PhantomData,
        })
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
        let args = args.into_iter();
        match self.kind {
            ClauseKind::And => {
                let mut out = !Out::default();
                for (i, x) in args.enumerate() {
                    out = out & if self.literals[i].1 { !x } else { x };
                }
                out
            }
            ClauseKind::Xor => {
                let mut out = Out::default();
                for (i, x) in args.enumerate() {
                    out = out ^ if self.literals[i].1 { !x } else { x };
                }
                out
            }
        }
    }

    /// Evaluate clause. Get values of argument from method arguments.
    #[inline]
    pub fn eval<Out>(&self, values: &[Out]) -> Out
    where
        Out: BitAnd<Output = Out> + BitXor<Output = Out> + Not<Output = Out> + Clone + Default,
    {
        match self.kind {
            ClauseKind::And => {
                let mut out = !Out::default();
                for (l, n) in self.literals.iter() {
                    let l = usize::try_from(*l).unwrap();
                    out = out
                        & if *n {
                            !values[l].clone()
                        } else {
                            values[l].clone()
                        };
                }
                out
            }
            ClauseKind::Xor => {
                let mut out = Out::default();
                for (l, n) in self.literals.iter() {
                    let l = usize::try_from(*l).unwrap();
                    out = out
                        ^ if *n {
                            !values[l].clone()
                        } else {
                            values[l].clone()
                        };
                }
                out
            }
        }
    }
}

impl<T: Clone + Copy + FromStr> FromStr for Clause<T> {
    type Err = ClauseParseError<<T as FromStr>::Err>;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        let src = to_single_spaces(src);
        let (kind, mut r) = if src.starts_with("and(") {
            (ClauseKind::And, &src[4..])
        } else if src.starts_with("xor(") {
            (ClauseKind::Xor, &src[4..])
        } else if src.starts_with("and (") {
            (ClauseKind::And, &src[5..])
        } else if src.starts_with("xor (") {
            (ClauseKind::Xor, &src[5..])
        } else {
            return Err(ClauseParseError::UnknownKind);
        };
        let mut literals = vec![];
        r = skip_single_space(r);
        while !r.is_empty() {
            let (rnew, i0) = if let Some(p) = r.find([',', 'n', ')']) {
                let d = &r[0..p];
                let d = if let Some(b' ') = d.bytes().last() {
                    &d[0..p - 1]
                } else {
                    d
                };
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
            r = skip_single_space(r);
        }

        Ok(Clause { kind, literals })
    }
}

/// Circuit defined as list of clauses connected together, number of inputs and list of outputs.
/// Any output can be logically negated. Number in clause literal is index of output.
/// First outputs are inputs. Next inputs are outputs of previous clauses.
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

impl<T> ClauseCircuit<T>
where
    T: Clone + Copy + Ord,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    pub fn add_output(&mut self, out: (T, bool)) {
        let input_len = usize::try_from(self.input_len).unwrap();
        assert!(out.0 < T::try_from(self.clauses.len() + input_len).unwrap());
        self.outputs.push(out);
    }
}

impl<T: Clone + Copy + Debug> Display for ClauseCircuit<T>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let input_len = usize::try_from(self.input_len).unwrap();
        let mut output_map = vec![vec![]; input_len + self.clauses.len()];
        write!(f, "{{")?;
        for (i, (v, n)) in self.outputs.iter().enumerate() {
            output_map[usize::try_from(*v).unwrap()].push((i, *n));
        }
        // first circuit inputs
        for i in 0..input_len {
            write!(f, "{}", i)?;
            for op in &output_map[i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
            if i + 1 < input_len {
                write!(f, " ")?;
            }
        }
        // next circuit gates
        for (i, c) in self.clauses.iter().enumerate() {
            write!(f, " {}", c)?;
            for op in &output_map[input_len + i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
        }
        write!(f, "}}({})", input_len)?;
        Ok(())
    }
}

impl<'a, T: Clone + Copy + Debug> Display for FmtLiner<'a, ClauseCircuit<T>>
where
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let input_len = usize::try_from(self.inner.input_len).unwrap();
        let mut output_map = vec![vec![]; input_len + self.inner.clauses.len()];
        let indent = iter::repeat(' ').take(self.indent).collect::<String>();
        let indent2 = iter::repeat(' ').take(self.indent2).collect::<String>();
        writeln!(f, "{}{{", indent)?;
        for (i, (v, n)) in self.inner.outputs.iter().enumerate() {
            output_map[usize::try_from(*v).unwrap()].push((i, *n));
        }
        // first circuit inputs
        for i in 0..input_len {
            write!(f, "{}{}", indent2, i)?;
            for op in &output_map[i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
            if i + 1 < input_len {
                writeln!(f, "")?;
            }
        }
        // next circuit gates
        for (i, c) in self.inner.clauses.iter().enumerate() {
            write!(f, "\n{}{}", indent2, c)?;
            for op in &output_map[input_len + i] {
                write!(f, ":{}{}", op.0, if op.1 { "n" } else { "" })?;
            }
        }
        writeln!(f, "\n{}}}({})", indent, input_len)?;
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
        let src = to_single_spaces(src);
        if src.starts_with("{") {
            let mut input_len = T::default();
            let mut input_touched = vec![];
            let mut output_len = T::default();
            let mut outputs = vec![];
            let mut r = &src[1..];
            if r == "}(0)" {
                return Ok(ClauseCircuit::new(T::default(), [], []).unwrap());
            }
            let mut end = false;
            r = if let Some(' ') = r.chars().next() {
                &r[1..]
            } else {
                r
            };
            // first loop to parse inputs
            'a: loop {
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
                                if let Some('}') = r.chars().next() {
                                    r = &r[1..];
                                    end = true;
                                    break;
                                }
                                continue;
                            }
                            ':' => {
                                r = &r[1..];
                                loop {
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
                                            outputs
                                                .resize(usize::try_from(output_len).unwrap(), None);
                                        }
                                        outputs[usize::try_from(output).unwrap()] =
                                            Some((input, neg));

                                        // skip next char or end
                                        match r.chars().next().unwrap() {
                                            ' ' => {
                                                r = &r[1..];
                                                if let Some('}') = r.chars().next() {
                                                    r = &r[1..];
                                                    end = true;
                                                    break 'a;
                                                }
                                                break;
                                            }
                                            '}' => {
                                                r = &r[1..];
                                                end = true;
                                                break 'a;
                                            }
                                            ':' => {
                                                r = &r[1..];
                                            }
                                            _ => {
                                                return Err(ClauseCircuitParseError::SyntaxError);
                                            }
                                        }
                                    } else {
                                        return Err(ClauseCircuitParseError::SyntaxError);
                                    }
                                }
                            }
                            '}' => {
                                r = &r[1..];
                                end = true;
                                break;
                            }
                            _ => {
                                return Err(ClauseCircuitParseError::SyntaxError);
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
            'a: while !end {
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
                        if let Some('}') = r.chars().next() {
                            r = &r[1..];
                            break;
                        }
                        continue;
                    }
                    ':' => {
                        r = &r[1..];
                        loop {
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
                                outputs[usize::try_from(output).unwrap()] = Some((
                                    T::try_from(input_len + clauses.len() - 1).unwrap(),
                                    neg,
                                ));

                                // skip next char or end
                                match r.chars().next().unwrap() {
                                    ' ' => {
                                        r = &r[1..];
                                        if let Some('}') = r.chars().next() {
                                            r = &r[1..];
                                            break 'a;
                                        }
                                        break;
                                    }
                                    '}' => {
                                        r = &r[1..];
                                        break 'a;
                                    }
                                    ':' => {
                                        r = &r[1..];
                                    }
                                    _ => {
                                        return Err(ClauseCircuitParseError::SyntaxError);
                                    }
                                }
                            } else {
                                return Err(ClauseCircuitParseError::SyntaxError);
                            }
                        }
                    }
                    '}' => {
                        r = &r[1..];
                        break;
                    }
                    _ => {
                        return Err(ClauseCircuitParseError::SyntaxError);
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
                        if !r[p + 1..].is_empty() {
                            return Err(ClauseCircuitParseError::SyntaxError);
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

/// serde support

impl<T: Clone + Copy + Debug> Serialize for ClauseCircuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}", FmtLiner::new(self, 4, 8)))
    }
}

struct ClauseCircuitVisitor<T> {
    t: std::marker::PhantomData<T>,
}

impl<'de, T> Visitor<'de> for ClauseCircuitVisitor<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    type Value = ClauseCircuit<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("clause circuit")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        ClauseCircuit::<T>::from_str(v).map_err(|e| E::custom(format!("{:?}", e)))
    }
}

impl<'de, T> Deserialize<'de> for ClauseCircuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<ClauseCircuit<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(ClauseCircuitVisitor::<T> {
            t: std::marker::PhantomData,
        })
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
        let input_len = usize::try_from(circuit.input_len).unwrap();
        let mut used_outputs = vec![0u8; circuit.len()];
        for g in &circuit.gates {
            let i0 = usize::try_from(g.i0).unwrap();
            let i1 = usize::try_from(g.i1).unwrap();
            if i0 >= input_len {
                if used_outputs[i0 - input_len] < 2 {
                    used_outputs[i0 - input_len] += 1;
                }
            }
            if i1 >= input_len {
                if used_outputs[i1 - input_len] < 2 {
                    used_outputs[i1 - input_len] += 1;
                }
            }
        }

        for (o, _) in &circuit.outputs {
            let o = usize::try_from(*o).unwrap();
            if o >= input_len {
                if used_outputs[o - input_len] < 2 {
                    used_outputs[o - input_len] += 1;
                }
            }
        }

        // collect clauses
        #[derive(Clone, Copy, Debug)]
        struct StackEntry {
            node: usize,
            way: u8,
            clause_id: Option<usize>,
            put_clause_0: bool,
            put_clause_1: bool,
        }
        let mut visited = vec![false; circuit.gates.len()];
        let mut clauses: Vec<Clause<T>> = vec![];
        let mut clause_ids = vec![None; circuit.gates.len()];
        for (o, _) in &circuit.outputs {
            let o = usize::try_from(*o).unwrap();
            if o < input_len {
                continue;
            }
            let mut stack = Vec::<StackEntry>::new();
            stack.push(StackEntry {
                node: o - input_len,
                way: 0,
                clause_id: None,
                put_clause_0: false,
                put_clause_1: false,
            });
            while !stack.is_empty() {
                let top = stack.last_mut().unwrap();
                let node_index = top.node;
                let g = &circuit.gates[node_index];
                match top.way {
                    0 => {
                        if !visited[node_index] {
                            visited[node_index] = true;
                        } else {
                            stack.pop();
                            continue;
                        }
                        if top.clause_id.is_none() {
                            // create new clause
                            top.clause_id = Some(clauses.len());
                            clause_ids[node_index] = Some(clauses.len());
                            clauses.push(Clause {
                                kind: match g.func {
                                    GateFunc::And | GateFunc::Nor | GateFunc::Nimpl => {
                                        ClauseKind::And
                                    }
                                    GateFunc::Xor => ClauseKind::Xor,
                                },
                                literals: vec![],
                            });
                        }

                        let clause_id = top.clause_id.unwrap();
                        let kind = clauses[clause_id].kind;

                        let i0 = usize::try_from(g.i0).unwrap();
                        top.way += 1;
                        if i0 >= input_len {
                            // put clause
                            let func0 = circuit.gates[i0 - input_len].func;
                            let node0_index = i0 - input_len;
                            // determine whether clause must be propagated
                            let propagate_clause = used_outputs[node0_index] < 2
                                && ((kind == ClauseKind::And
                                    && (g.func == GateFunc::And || g.func == GateFunc::Nimpl)
                                    && func0 != GateFunc::Xor)
                                    || (kind == ClauseKind::Xor && func0 == GateFunc::Xor));
                            if !propagate_clause {
                                top.put_clause_0 = true;
                            }
                            stack.push(StackEntry {
                                node: node0_index,
                                way: 0,
                                clause_id: if propagate_clause {
                                    Some(clause_id)
                                } else {
                                    None
                                },
                                put_clause_0: false,
                                put_clause_1: false,
                            });
                        } else {
                            // put literal
                            clauses[clause_id]
                                .literals
                                .push((g.i0, g.func == GateFunc::Nor));
                        }
                    }
                    1 => {
                        let clause_id = top.clause_id.unwrap();
                        let kind = clauses[clause_id].kind;

                        let i1 = usize::try_from(g.i1).unwrap();
                        top.way += 1;
                        if i1 >= input_len {
                            // put clause
                            let func1 = circuit.gates[i1 - input_len].func;
                            let node1_index = i1 - input_len;
                            // determine whether clause must be propagated
                            let propagate_clause = used_outputs[node1_index] < 2
                                && ((kind == ClauseKind::And
                                    && g.func == GateFunc::And
                                    && func1 != GateFunc::Xor)
                                    || (kind == ClauseKind::Xor && func1 == GateFunc::Xor));
                            if !propagate_clause {
                                top.put_clause_1 = true;
                            }
                            stack.push(StackEntry {
                                node: node1_index,
                                way: 0,
                                clause_id: if propagate_clause {
                                    Some(clause_id)
                                } else {
                                    None
                                },
                                put_clause_0: false,
                                put_clause_1: false,
                            });
                        } else {
                            // put literal
                            clauses[clause_id]
                                .literals
                                .push((g.i1, g.func == GateFunc::Nimpl || g.func == GateFunc::Nor));
                        }
                    }
                    _ => {
                        let i0 = usize::try_from(g.i0).unwrap();
                        let i1 = usize::try_from(g.i1).unwrap();

                        let clause_id = top.clause_id.unwrap();

                        if top.put_clause_0 {
                            // add literal to clause if no clause propagation
                            clauses[clause_id].literals.push((
                                T::try_from(clause_ids[i0 - input_len].unwrap() + input_len)
                                    .unwrap(),
                                g.func == GateFunc::Nor,
                            ));
                        }
                        if top.put_clause_1 {
                            // add literal to clause if no clause propagation
                            clauses[clause_id].literals.push((
                                T::try_from(clause_ids[i1 - input_len].unwrap() + input_len)
                                    .unwrap(),
                                g.func == GateFunc::Nor || g.func == GateFunc::Nimpl,
                            ));
                        }
                        stack.pop();
                    }
                }
            }
        }

        // make clause id translation table
        let mut clause_trans = vec![0; clauses.len()];
        for (i, clause_id) in clause_ids.iter().filter_map(|x| x.as_ref()).enumerate() {
            clause_trans[*clause_id] = i;
        }

        // translate clauses ids by using translation table
        for clause in &mut clauses {
            for (l, _) in &mut clause.literals {
                if *l >= circuit.input_len {
                    *l = T::try_from(
                        input_len + clause_trans[usize::try_from(*l).unwrap() - input_len],
                    )
                    .unwrap();
                }
            }
        }
        // reorder clauses by using translation table
        let mut clauses_new = vec![];
        for clause_id in clause_ids.iter().filter_map(|x| x.as_ref()) {
            clauses_new.push(clauses[*clause_id].clone());
        }
        // finally translate same clause_ids
        for clause_id in &mut clause_ids {
            if let Some(clause_id) = clause_id {
                *clause_id = clause_trans[*clause_id];
            }
        }

        ClauseCircuit::new(
            circuit.input_len,
            clauses_new,
            circuit.outputs.into_iter().map(|(l, n)| {
                if l >= circuit.input_len {
                    (
                        T::try_from(
                            clause_ids[usize::try_from(l).unwrap() - input_len].unwrap()
                                + input_len,
                        )
                        .unwrap(),
                        n,
                    )
                } else {
                    (l, n)
                }
            }),
        )
        .unwrap()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quant {
    Exists,
    All,
}

impl Display for Quant {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Quant::Exists => write!(f, "e"),
            Quant::All => write!(f, "a"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantCircuit<T: Clone + Copy> {
    quants: Vec<Quant>,
    circuit: Circuit<T>,
}

impl<T> QuantCircuit<T>
where
    T: Clone + Copy,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    pub fn new(quants: impl IntoIterator<Item = Quant>, circuit: Circuit<T>) -> Option<Self> {
        let out = Self {
            quants: quants.into_iter().collect::<Vec<_>>(),
            circuit,
        };
        if usize::try_from(out.circuit.input_len()).unwrap() == out.quants.len()
            && out.circuit.outputs().len() == 1
        {
            Some(out)
        } else {
            None
        }
    }

    pub fn circuit(&self) -> &Circuit<T> {
        &self.circuit
    }

    pub fn quants(&self) -> &[Quant] {
        &self.quants
    }
}

impl<T> Display for QuantCircuit<T>
where
    T: Clone + Copy + Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}",
            self.quants
                .iter()
                .map(|q| match q {
                    Quant::Exists => 'e',
                    Quant::All => 'a',
                })
                .collect::<String>(),
            self.circuit
        )
    }
}

impl<'a, T> Display for FmtLiner<'a, QuantCircuit<T>>
where
    T: Clone + Copy + Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let indent = iter::repeat(' ').take(self.indent).collect::<String>();
        write!(
            f,
            "{}{}\n{}",
            indent,
            self.inner
                .quants
                .iter()
                .map(|q| match q {
                    Quant::Exists => 'e',
                    Quant::All => 'a',
                })
                .collect::<String>(),
            FmtLiner::new(&self.inner.circuit, self.indent, self.indent2)
        )
    }
}

impl<T> FromStr for QuantCircuit<T>
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
        let src = to_single_spaces(src);
        let r = &src;
        if let Some(p) = r.find([' ']) {
            if !r.as_bytes()[0..p]
                .iter()
                .all(|qc| *qc == b'e' || *qc == b'a')
            {
                return Err(CircuitParseError::SyntaxError);
            }
            let quants = r.as_bytes()[0..p]
                .iter()
                .map(|qc| match *qc {
                    b'e' => Quant::Exists,
                    b'a' => Quant::All,
                    _ => {
                        panic!("Unexpected!");
                    }
                })
                .collect::<Vec<_>>();
            let circuit = Circuit::from_str(&r[p..])?;
            if usize::try_from(circuit.input_len()).unwrap() == quants.len()
                && circuit.outputs().len() == 1
            {
                Ok(QuantCircuit { quants, circuit })
            } else {
                Err(CircuitParseError::Invalid)
            }
        } else {
            Err(CircuitParseError::SyntaxError)
        }
    }
}

/// serde support

impl<T: Clone + Copy + Debug> Serialize for QuantCircuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}", FmtLiner::new(self, 4, 8)))
    }
}

struct QuantCircuitVisitor<T> {
    t: std::marker::PhantomData<T>,
}

impl<'de, T> Visitor<'de> for QuantCircuitVisitor<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    type Value = QuantCircuit<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("quant circuit")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        QuantCircuit::<T>::from_str(v).map_err(|e| E::custom(format!("{:?}", e)))
    }
}

impl<'de, T> Deserialize<'de> for QuantCircuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<QuantCircuit<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(QuantCircuitVisitor::<T> {
            t: std::marker::PhantomData,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantClauseCircuit<T: Clone + Copy> {
    quants: Vec<Quant>,
    circuit: ClauseCircuit<T>,
}

impl<T> QuantClauseCircuit<T>
where
    T: Clone + Copy,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    pub fn new(quants: impl IntoIterator<Item = Quant>, circuit: ClauseCircuit<T>) -> Option<Self> {
        let out = Self {
            quants: quants.into_iter().collect::<Vec<_>>(),
            circuit,
        };
        if usize::try_from(out.circuit.input_len()).unwrap() == out.quants.len()
            && out.circuit.outputs().len() == 1
        {
            Some(out)
        } else {
            None
        }
    }

    pub fn circuit(&self) -> &ClauseCircuit<T> {
        &self.circuit
    }

    pub fn quants(&self) -> &[Quant] {
        &self.quants
    }
}

impl<T> Display for QuantClauseCircuit<T>
where
    T: Clone + Copy + Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}",
            self.quants
                .iter()
                .map(|q| match q {
                    Quant::Exists => 'e',
                    Quant::All => 'a',
                })
                .collect::<String>(),
            self.circuit
        )
    }
}

impl<'a, T> Display for FmtLiner<'a, QuantClauseCircuit<T>>
where
    T: Clone + Copy + Debug,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let indent = iter::repeat(' ').take(self.indent).collect::<String>();
        write!(
            f,
            "{}{}\n{}",
            indent,
            self.inner
                .quants
                .iter()
                .map(|q| match q {
                    Quant::Exists => 'e',
                    Quant::All => 'a',
                })
                .collect::<String>(),
            FmtLiner::new(&self.inner.circuit, self.indent, self.indent2)
        )
    }
}

impl<T> FromStr for QuantClauseCircuit<T>
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
        let src = to_single_spaces(src);
        let r = &src;
        if let Some(p) = r.find([' ']) {
            if !r.as_bytes()[0..p]
                .iter()
                .all(|qc| *qc == b'e' || *qc == b'a')
            {
                return Err(ClauseCircuitParseError::SyntaxError);
            }
            let quants = r.as_bytes()[0..p]
                .iter()
                .map(|qc| match *qc {
                    b'e' => Quant::Exists,
                    b'a' => Quant::All,
                    _ => {
                        panic!("Unexpected!");
                    }
                })
                .collect::<Vec<_>>();
            let circuit = ClauseCircuit::from_str(&r[p..])?;
            if usize::try_from(circuit.input_len()).unwrap() == quants.len()
                && circuit.outputs().len() == 1
            {
                Ok(QuantClauseCircuit { quants, circuit })
            } else {
                Err(ClauseCircuitParseError::Invalid)
            }
        } else {
            Err(ClauseCircuitParseError::SyntaxError)
        }
    }
}

/// serde support

impl<T: Clone + Copy + Debug> Serialize for QuantClauseCircuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}", FmtLiner::new(self, 4, 8)))
    }
}

struct QuantClauseCircuitVisitor<T> {
    t: std::marker::PhantomData<T>,
}

impl<'de, T> Visitor<'de> for QuantClauseCircuitVisitor<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    type Value = QuantClauseCircuit<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("quant clause circuit")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        QuantClauseCircuit::<T>::from_str(v).map_err(|e| E::custom(format!("{:?}", e)))
    }
}

impl<'de, T> Deserialize<'de> for QuantClauseCircuit<T>
where
    T: Clone + Copy + FromStr + Debug + Default + PartialOrd + Ord + std::ops::Add<Output = T>,
    T: From<u8>,
    usize: TryFrom<T>,
    <usize as TryFrom<T>>::Error: Debug,
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
    <T as FromStr>::Err: Debug,
{
    fn deserialize<D>(deserializer: D) -> Result<QuantClauseCircuit<T>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(QuantClauseCircuitVisitor::<T> {
            t: std::marker::PhantomData,
        })
    }
}

macro_rules! impl_circuit_from {
    ($t1:ty, $t2:ty) => {
        impl From<Gate<$t1>> for Gate<$t2> {
            fn from(t: Gate<$t1>) -> Self {
                Gate {
                    func: t.func,
                    i0: t.i0.into(),
                    i1: t.i1.into(),
                }
            }
        }

        impl From<Circuit<$t1>> for Circuit<$t2> {
            fn from(t: Circuit<$t1>) -> Self {
                Self {
                    input_len: t.input_len.into(),
                    gates: t.gates.into_iter().map(|x| x.into()).collect::<Vec<_>>(),
                    outputs: t
                        .outputs
                        .into_iter()
                        .map(|(x, n)| (x.into(), n))
                        .collect::<Vec<_>>(),
                }
            }
        }

        impl From<QuantCircuit<$t1>> for QuantCircuit<$t2> {
            fn from(t: QuantCircuit<$t1>) -> Self {
                Self {
                    quants: t.quants,
                    circuit: t.circuit.into(),
                }
            }
        }

        impl From<Clause<$t1>> for Clause<$t2> {
            fn from(t: Clause<$t1>) -> Self {
                Clause {
                    kind: t.kind,
                    literals: t
                        .literals
                        .into_iter()
                        .map(|(x, n)| (x.into(), n))
                        .collect::<Vec<_>>(),
                }
            }
        }

        impl From<ClauseCircuit<$t1>> for ClauseCircuit<$t2> {
            fn from(t: ClauseCircuit<$t1>) -> Self {
                Self {
                    input_len: t.input_len.into(),
                    clauses: t.clauses.into_iter().map(|x| x.into()).collect::<Vec<_>>(),
                    outputs: t
                        .outputs
                        .into_iter()
                        .map(|(x, n)| (x.into(), n))
                        .collect::<Vec<_>>(),
                }
            }
        }

        impl From<QuantClauseCircuit<$t1>> for QuantClauseCircuit<$t2> {
            fn from(t: QuantClauseCircuit<$t1>) -> Self {
                Self {
                    quants: t.quants,
                    circuit: t.circuit.into(),
                }
            }
        }
    };
}

impl_circuit_from!(u8, u16);
impl_circuit_from!(u8, u32);
impl_circuit_from!(u8, u64);
impl_circuit_from!(u8, usize);
impl_circuit_from!(u16, u32);
impl_circuit_from!(u16, u64);
impl_circuit_from!(u16, usize);
impl_circuit_from!(u32, u64);

macro_rules! impl_circuit_try_from {
    ($t1:ty, $t2:ty) => {
        impl TryFrom<Gate<$t1>> for Gate<$t2> {
            type Error = <$t2 as TryFrom<$t1>>::Error;
            fn try_from(t: Gate<$t1>) -> Result<Self, Self::Error> {
                Ok(Gate {
                    func: t.func,
                    i0: t.i0.try_into()?,
                    i1: t.i1.try_into()?,
                })
            }
        }

        impl TryFrom<Circuit<$t1>> for Circuit<$t2> {
            type Error = <$t2 as TryFrom<$t1>>::Error;
            fn try_from(t: Circuit<$t1>) -> Result<Self, Self::Error> {
                Ok(Self {
                    input_len: t.input_len.try_into()?,
                    gates: t
                        .gates
                        .into_iter()
                        .map(|x| x.try_into())
                        .collect::<Result<Vec<_>, _>>()?,
                    outputs: t
                        .outputs
                        .into_iter()
                        .map(|(x, n)| x.try_into().map(|x| (x, n)))
                        .collect::<Result<Vec<_>, _>>()?,
                })
            }
        }

        impl TryFrom<QuantCircuit<$t1>> for QuantCircuit<$t2> {
            type Error = <$t2 as TryFrom<$t1>>::Error;
            fn try_from(t: QuantCircuit<$t1>) -> Result<Self, Self::Error> {
                Ok(Self {
                    quants: t.quants,
                    circuit: t.circuit.try_into()?,
                })
            }
        }

        impl TryFrom<Clause<$t1>> for Clause<$t2> {
            type Error = <$t2 as TryFrom<$t1>>::Error;
            fn try_from(t: Clause<$t1>) -> Result<Self, Self::Error> {
                Ok(Clause {
                    kind: t.kind,
                    literals: t
                        .literals
                        .into_iter()
                        .map(|(x, n)| x.try_into().map(|x| (x, n)))
                        .collect::<Result<Vec<_>, _>>()?,
                })
            }
        }

        impl TryFrom<ClauseCircuit<$t1>> for ClauseCircuit<$t2> {
            type Error = <$t2 as TryFrom<$t1>>::Error;
            fn try_from(t: ClauseCircuit<$t1>) -> Result<Self, Self::Error> {
                Ok(Self {
                    input_len: t.input_len.try_into()?,
                    clauses: t
                        .clauses
                        .into_iter()
                        .map(|x| x.try_into())
                        .collect::<Result<Vec<_>, _>>()?,
                    outputs: t
                        .outputs
                        .into_iter()
                        .map(|(x, n)| x.try_into().map(|x| (x, n)))
                        .collect::<Result<Vec<_>, _>>()?,
                })
            }
        }

        impl TryFrom<QuantClauseCircuit<$t1>> for QuantClauseCircuit<$t2> {
            type Error = <$t2 as TryFrom<$t1>>::Error;
            fn try_from(t: QuantClauseCircuit<$t1>) -> Result<Self, Self::Error> {
                Ok(Self {
                    quants: t.quants,
                    circuit: t.circuit.try_into()?,
                })
            }
        }
    };
}

impl_circuit_try_from!(u16, u8);
impl_circuit_try_from!(u32, u8);
impl_circuit_try_from!(u64, u8);
impl_circuit_try_from!(u32, u16);
impl_circuit_try_from!(u64, u16);
impl_circuit_try_from!(u64, u32);
impl_circuit_try_from!(usize, u8);
impl_circuit_try_from!(usize, u16);
impl_circuit_try_from!(usize, u32);
impl_circuit_try_from!(usize, u64);
impl_circuit_try_from!(u32, usize);
impl_circuit_try_from!(u64, usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_single_spaces() {
        assert_eq!("abbb", to_single_spaces("abbb"));
        assert_eq!("abbb", to_single_spaces("   abbb"));
        assert_eq!("ab bc", to_single_spaces(" \n\t  ab  \t\n bc"));
        assert_eq!("ab bc", to_single_spaces(" \n\t  ab  \t\n bc  \t\t"));
    }
}
