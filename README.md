## GateSim

The base library of the Gate Project. It provides basic types of circuits and basic
methods to operate on that circuits. The library doesn't provide complex simulation
routines. This library is really base of the Gate Project.

The basic type of circuit [Circuit] is constructed from gates of following types:
* 'and' - AND gate that returns true if two inputs are true, otherwise returns false.
* 'nor' - NOR (negation of OR) gate that returns true if two inputs are false,
   otherwise returns false.
* 'nimpl' - NIMPL (negation of implication) gate that returns true if first input is true
   and second is false, otherwise it returns false.
* 'xor' - XOR gate that return true if inputs are different.

The type of circuit is parametrized by type of wire index. It can be unsigned integer
for example `u32`.

The circuit defined by input length (number), gates and outputs that are defined by
wire and negation. If wire index is index of circuit's input or index of gate's output.
The input of circuit starts from 0. The output of gate starts from input length number.
The circuit can be constructed from gates satisfied following constraints:
* All inputs for all gates and output wires are correct types
  (input is less than current gate output wire index).
* All inputs are used by some gates or circuit outputs.
* All gate outputs are used some gates or circuit outputs.

Additional type of circuit [ClauseCircuit] is constructed from clauses. The clause is
gate that uses any number of inputs. The clause contains literals (input wire that can be
negated or not). The are two clause types:
* 'and' clause that returns true if all literals are true.
  If clause have no inputs then returns true.
* 'xor' clause that returns true if number of literals of true value is odd.
  If clause have no inputs then returns false.

Similary, the clause circuit defined by input length (number),
clauses and outputs that are defined by wire and negation.
If wire index is index of circuit's input or gate's output.
The input of circuit starts from 0. The output of gate starts from input length number.
The circuit can be constructed from gates satisfied following constraints:
* All inputs for all clauses and output wires are correct types
  (input is less than current clause output wire index).
* All inputs are used by some clauses or circuit outputs.
* All clauses outputs are used some clauses or circuit outputs.

Derived [QuantCircuit] from [Circuit] provides additional information about quantifiers.
These quantifiers can be used to evaluate or solve quantified formula defined by circuit.
There are two types of quantifiers:
* 'all' - formula is satisified if circuit returns true for all combinations of inputs.
* 'exists' - formula is satisified if circuit returns true for some combinations of inputs.

Number of quantifiers must match to input length. Any sequence of quantifiers for inputs
determine single quantifier for some input length. Number of output must be 1.

For describe: `[all,all,exists,exists,all,all]` - formula is true if for all combinations of
input0, input1 can be found some combination of input2,input3 all combinations
input4, input5 circuit returns true.

Similary, [QuantClauseCircuit] is derive from [ClauseCircuit]. It provides
information about quantifiers. These same constraints applied like in QuantCircuits.
