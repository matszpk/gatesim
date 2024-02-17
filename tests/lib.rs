use gatesim::*;
use std::str::FromStr;

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
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (  4  ,  6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_nor(4, 6),
        Gate::from_str("  nor  (  4  ,  6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_nimpl(4, 6),
        Gate::from_str("  nimpl  (  4  ,  6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_xor(4, 6),
        Gate::from_str("  xor (  4  ,  6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (4  ,  6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (4  ,  6)  ").unwrap()
    );
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (4  ,  6)").unwrap()
    );
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (4  ,6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (   4,  6  )  ").unwrap()
    );
    assert_eq!(
        Gate::new_and(4, 6),
        Gate::from_str("  and (   4,6  )  ").unwrap()
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

    assert!(Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_xor(2, 3)], [(4, false)]).is_some());
    assert!(Circuit::new(3, [Gate::new_xor(0, 1), Gate::new_xor(2, 1)], [(4, false)]).is_none());
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
    // two circuit outputs to same gate output
    assert!(Circuit::new(
        3,
        [
            Gate::new_xor(0, 1),
            Gate::new_xor(1, 2),
            Gate::new_xor(0, 4)
        ],
        [(3, false), (5, false), (5, true)]
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
            "{0 1 2 3 and(0,2):0 and(1,2) and(0,3) and(1,3) xor(5,6):1:4n ",
            "and(5,6) xor(7,9):2:5 and(7,9):3}(4)"
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
                [
                    (4, false),
                    (8, false),
                    (10, false),
                    (11, false),
                    (8, true),
                    (10, false)
                ],
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
    assert_eq!(
        concat!(
            "{0 1:1n:2 2 3 and(0,2):0 and(1,2) and(0,3) and(1,3) xor(5,6):3n ",
            "and(5,6) xor(7,9):4 and(7,9):5n}(4)"
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
                [
                    (4, false),
                    (1, true),
                    (1, false),
                    (8, true),
                    (10, false),
                    (11, true)
                ],
            )
            .unwrap()
        )
    );
}

#[test]
fn circuit_display_fmt_liner() {
    assert_eq!(
        r##"    {
        0
        1
        2
        3
        and(0,2):0
        and(1,2)
        and(0,3)
        and(1,3)
        xor(5,6):1
        and(5,6)
        xor(7,9):2
        and(7,9):3
    }(4)
"##,
        format!(
            "{}",
            FmtLiner::new(
                &Circuit::new(
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
                .unwrap(),
                4,
                8
            )
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
        Circuit::new(1, [], [(0, false)]).unwrap(),
        Circuit::from_str("{0:0}").unwrap()
    );
    assert_eq!(
        Circuit::new(1, [], [(0, false)]).unwrap(),
        Circuit::from_str("{  0:0   }").unwrap()
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
            3,
            [
                Gate::new_and(0, 1),
                Gate::new_nor(0, 2),
                Gate::new_xor(3, 4),
                Gate::new_nimpl(1, 5),
            ],
            [(6, true), (4, false), (2, false), (2, true), (4, false)]
        )
        .unwrap(),
        Circuit::from_str("{1 2:2:3n 0 and(0,1) nor(0,2):1:4 xor(3,4) nimpl(1,5):0n}(3)").unwrap()
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
        Circuit::from_str("{1 2:2 0 and(0,1) nor(0,2):1 xor(3,4) nimpl(1,5):0n}").unwrap()
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
            [(4, false), (8, false), (10, false), (11, false)],
        )
        .unwrap(),
        Circuit::from_str(
            r##"    {
        0
        1
        2
        3
        and(0,2):0
        and(1,2)
        and(0,3)
        and(1,3)
        xor(5,6):1
        and(5,6)
        xor(7,9):2
        and(7,9):3
    }(4)
"##
        )
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
        (Clause::<u8>::new_and([]), 0b11111111),
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
        (Clause::new_and([]), 0b11111111),
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
        ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(2, false)]).is_some()
    );
    assert!(
        ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(2, true)]).is_some()
    );
    assert!(
        ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(3, false)]).is_none()
    );
    assert!(
        ClauseCircuit::new(2, [Clause::new_xor([(1, false), (1, false)])], [(3, false)]).is_none()
    );
    assert!(
        ClauseCircuit::new(2, [Clause::new_xor([(0, false), (0, false)])], [(3, false)]).is_none()
    );
    assert!(
        ClauseCircuit::new(2, [Clause::new_xor([(0, false), (1, false)])], [(1, false)]).is_none()
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
    assert_eq!(
        concat!(
            "{0 1 2:7n:8 3 and(0,1n,2):0:4n and(1,2) and(0,3) and(1,3) xor(5,6):1 ",
            "and(5,6) xor(7,8,9n):2:6 and(7,9):3:5n}(4)"
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
                [
                    (4, false),
                    (8, false),
                    (10, false),
                    (11, false),
                    (4, true),
                    (11, true),
                    (10, false),
                    (2, true),
                    (2, false)
                ],
            )
            .unwrap()
        )
    );
}

#[test]
fn clause_circuit_display_fmt_liner() {
    assert_eq!(
        r##"    {
        0
        1
        2
        3
        and(0,1n,2):0
        and(1,2)
        and(0,3)
        and(1,3)
        xor(5,6):1
        and(5,6)
        xor(7,8,9n):2
        and(7,9):3
    }(4)
"##,
        format!(
            "{}",
            FmtLiner::new(
                &ClauseCircuit::new(
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
                .unwrap(),
                4,
                8
            )
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
    assert_eq!(
        Clause::new_and([(4, false), (6, false)]),
        Clause::from_str("and (4,6)").unwrap()
    );
    assert_eq!(
        Clause::new_xor([(4, false), (6, false)]),
        Clause::from_str("xor (4,6)").unwrap()
    );
    assert_eq!(
        Clause::new_xor([(4, false), (6, false)]),
        Clause::from_str("xor ( 4,6)").unwrap()
    );
    assert_eq!(
        Clause::new_xor([(4, false), (6, false)]),
        Clause::from_str("xor ( 4, 6)").unwrap()
    );
    assert_eq!(
        Clause::new_xor([(4, false), (6, false)]),
        Clause::from_str("xor ( 4 , 6 )").unwrap()
    );
}

#[test]
fn test_clause_circuit_from_str() {
    assert_eq!(
        ClauseCircuit::new(1, [], [(0, false)]).unwrap(),
        ClauseCircuit::from_str("{0:0}(1)").unwrap()
    );
    assert_eq!(
        ClauseCircuit::new(1, [], [(0, false)]).unwrap(),
        ClauseCircuit::from_str("{0:0}").unwrap()
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
    assert_eq!(
        ClauseCircuit::new(
            3,
            [
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_and([(0, true), (1, false), (2, true)]),
                Clause::new_xor([(3, false), (4, false)]),
            ],
            [(5, false), (4, true), (2, true), (2, true), (5, false)]
        )
        .unwrap(),
        ClauseCircuit::from_str("{0 1 2:2n:3n and(0,1) and(0n,1,2n):1n xor(3,4):0:4}(3)").unwrap()
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
        ClauseCircuit::from_str("{0 1 2:2n and(0,1) and(0n,1,2n):1n xor(3,4):0}").unwrap()
    );
    assert_eq!(
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
        .unwrap(),
        ClauseCircuit::from_str(
            r##"    {
        0
        1
        2
        3
        and(0,1n,2):0
        and(1,2)
        and(0,3)
        and(1,3)
        xor(5,6):1
        and(5,6)
        xor(7,8,9n):2
        and(7,9):3
    }(4)
"##
        )
        .unwrap()
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
        Circuit::new(2, [Gate::new_xor(0, 1),], [(0, false), (2, false)]).unwrap(),
        Circuit::from(
            ClauseCircuit::new(
                2,
                [Clause::new_xor([(0, true), (1, false),]),],
                [(0, false), (2, true)]
            )
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

    assert_eq!(
        Circuit::new(
            4,
            [
                Gate::new_and(0, 1),
                Gate::new_and(4, 2),
                Gate::new_xor(0, 1),
                Gate::new_xor(3, 5),
                Gate::new_xor(6, 7),
                Gate::new_nor(1, 2),
                Gate::new_and(9, 3),
                Gate::new_xor(5, 10),
                Gate::new_xor(11, 3),
                Gate::new_nor(5, 8),
                Gate::new_nor(10, 12),
                Gate::new_and(13, 14),
            ],
            [(5, false), (15, true)]
        )
        .unwrap(),
        Circuit::from(
            ClauseCircuit::new(
                4,
                [
                    Clause::new_and([(0, false), (1, false), (2, false),]),
                    Clause::new_xor([(0, false), (1, true), (3, false), (4, true)]),
                    Clause::new_and([(1, true), (2, true), (3, false),]),
                    Clause::new_xor([(4, false), (6, true), (3, false),]),
                    Clause::new_and([(4, true), (5, true), (6, true), (7, false)]),
                ],
                [(4, false), (8, true)]
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
                Gate::new_xor(3, 5),
                Gate::new_xor(6, 7),
                Gate::new_nor(1, 2),
                Gate::new_and(9, 3),
                Gate::new_xor(5, 8),
                Gate::new_xor(11, 3),
                Gate::new_nimpl(8, 5),
                Gate::new_nimpl(12, 10),
                Gate::new_and(13, 14),
            ],
            [(5, false), (15, true)]
        )
        .unwrap(),
        Circuit::from(
            ClauseCircuit::new(
                4,
                [
                    Clause::new_and([(0, false), (1, false), (2, false),]),
                    Clause::new_xor([(0, false), (1, true), (3, false), (4, false)]),
                    Clause::new_and([(1, true), (2, true), (3, false),]),
                    Clause::new_xor([(4, false), (5, true), (3, false),]),
                    Clause::new_and([(4, true), (5, true), (6, true), (7, false)]),
                ],
                [(4, false), (8, true)]
            )
            .unwrap()
        )
    );

    // evaluation test
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
    let circuit = Circuit::from(circuit);
    for i in 0..8 {
        let expected = (i & 1) + ((i & 2) >> 1) + ((i & 4) >> 2);
        assert_eq!(
            vec![(expected & 1) != 0, (expected & 2) != 0],
            circuit.eval([(i & 1) != 0, (i & 2) != 0, (i & 4) != 0]),
            "test {}",
            i
        );
    }

    let circuit = ClauseCircuit::new(
        4,
        [
            Clause::new_and([(0, false), (2, false)]),
            Clause::new_and([(1, false), (2, false)]),
            Clause::new_and([(0, false), (3, false)]),
            Clause::new_and([(1, false), (3, false)]),
            // add a1*b0 + a0*b1
            Clause::new_xor([(5, false), (6, false)]),
            Clause::new_and([(5, false), (6, false)]),
            // add c(a1*b0 + a0*b1) + a1*b1
            Clause::new_xor([(7, false), (9, false)]),
            Clause::new_and([(7, false), (9, false)]),
        ],
        [(4, false), (8, false), (10, false), (11, false)],
    )
    .unwrap();
    let circuit = Circuit::from(circuit);
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
fn test_circuit_from_seq_clause_circuit_0() {
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
            Circuit::from_seq(ClauseCircuit::new(2, [c.clone()], [(2, false)]).unwrap()),
            "testgc {}",
            c
        );
    }

    // include not-negated clause and negated output
    assert_eq!(
        Circuit::new(2, [Gate::new_xor(0, 1),], [(2, true)]).unwrap(),
        Circuit::from_seq(
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
        Circuit::from_seq(
            ClauseCircuit::new(2, [Clause::new_xor([(0, true), (1, false),]),], [(2, true)])
                .unwrap()
        )
    );

    assert_eq!(
        Circuit::new(2, [Gate::new_xor(0, 1),], [(0, false), (2, false)]).unwrap(),
        Circuit::from_seq(
            ClauseCircuit::new(
                2,
                [Clause::new_xor([(0, true), (1, false),]),],
                [(0, false), (2, true)]
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
                Gate::new_and(5, 3)
            ],
            [(6, false)]
        )
        .unwrap(),
        Circuit::from_seq(
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
                Gate::new_and(4, 2),
                Gate::new_nimpl(5, 3)
            ],
            [(6, false)]
        )
        .unwrap(),
        Circuit::from_seq(
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
        Circuit::from_seq(
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
        Circuit::from_seq(
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
                Gate::new_nimpl(0, 1),
                Gate::new_and(5, 2),
                Gate::new_nimpl(6, 3),
                Gate::new_and(7, 4),
            ],
            [(8, false)]
        )
        .unwrap(),
        Circuit::from_seq(
            ClauseCircuit::new(
                5,
                [Clause::new_and([
                    (0, false),
                    (1, true),
                    (2, false),
                    (3, true),
                    (4, false)
                ]),],
                [(5, false)]
            )
            .unwrap()
        )
    );
    assert_eq!(
        Circuit::new(
            5,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(5, 2),
                Gate::new_xor(6, 3),
                Gate::new_xor(7, 4),
            ],
            [(8, false)]
        )
        .unwrap(),
        Circuit::from_seq(
            ClauseCircuit::new(
                5,
                [Clause::new_xor([
                    (0, false),
                    (1, true),
                    (2, false),
                    (3, true),
                    (4, false)
                ]),],
                [(5, false)]
            )
            .unwrap()
        )
    );
    assert_eq!(
        Circuit::new(
            5,
            [
                Gate::new_xor(0, 1),
                Gate::new_xor(5, 2),
                Gate::new_xor(6, 3),
                Gate::new_xor(7, 4),
            ],
            [(8, true)]
        )
        .unwrap(),
        Circuit::from_seq(
            ClauseCircuit::new(
                5,
                [Clause::new_xor([
                    (0, false),
                    (1, true),
                    (2, false),
                    (3, true),
                    (4, true)
                ]),],
                [(5, false)]
            )
            .unwrap()
        )
    );
}

#[test]
fn test_circuit_from_seq_clause_circuit() {
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
        Circuit::from_seq(
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
        Circuit::from_seq(
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
                Gate::new_xor(7, 5),
                Gate::new_nor(1, 2),
                Gate::new_and(9, 3),
                Gate::new_xor(5, 8),
                Gate::new_xor(11, 3),
                Gate::new_nimpl(8, 5),
                Gate::new_nimpl(13, 10),
                Gate::new_and(14, 12),
            ],
            [(5, false), (15, true)]
        )
        .unwrap(),
        Circuit::from_seq(
            ClauseCircuit::new(
                4,
                [
                    Clause::new_and([(0, false), (1, false), (2, false),]),
                    Clause::new_xor([(0, false), (1, true), (3, false), (4, false)]),
                    Clause::new_and([(1, true), (2, true), (3, false),]),
                    Clause::new_xor([(4, false), (5, true), (3, false),]),
                    Clause::new_and([(4, true), (5, true), (6, true), (7, false)]),
                ],
                [(4, false), (8, true)]
            )
            .unwrap()
        )
    );

    // evaluation test
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
    let circuit = Circuit::from_seq(circuit);
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
fn test_clause_circuit_from_circuit_0() {
    for (c, eg, ng) in [
        (
            Clause::new_and([(0, false), (1, false)]),
            Gate::new_and(0, 1),
            false,
        ),
        (
            Clause::new_and([(1, false), (0, true)]),
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
            Clause::new_xor([(0, false), (1, false)]),
            Gate::new_xor(0, 1),
            true,
        ),
    ] {
        assert_eq!(
            ClauseCircuit::new(2, [c.clone()], [(2, ng)]).unwrap(),
            ClauseCircuit::from(Circuit::new(2, [eg], [(2, ng)]).unwrap()),
            "testgc {}",
            eg
        );
    }

    assert_eq!(
        ClauseCircuit::new(
            2,
            [Clause::new_xor([(0, false), (1, false),]),],
            [(2, true)]
        )
        .unwrap(),
        ClauseCircuit::from(Circuit::new(2, [Gate::new_xor(0, 1),], [(2, true)]).unwrap())
    );
    assert_eq!(
        ClauseCircuit::new(
            2,
            [Clause::new_xor([(0, false), (1, false),]),],
            [(1, true), (2, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(2, [Gate::new_xor(0, 1),], [(1, true), (2, false)]).unwrap()
        )
    );

    assert_eq!(
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
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_and(4, 5)
                ],
                [(6, false)]
            )
            .unwrap()
        )
    );
    assert_eq!(
        ClauseCircuit::new(
            4,
            [Clause::new_and([
                (0, true),
                (1, true),
                (2, false),
                (3, true)
            ]),],
            [(4, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                4,
                [
                    Gate::new_nor(0, 1),
                    Gate::new_nimpl(2, 3),
                    Gate::new_and(4, 5)
                ],
                [(6, false)]
            )
            .unwrap()
        )
    );
    assert_eq!(
        ClauseCircuit::new(
            4,
            [Clause::new_xor([
                (0, false),
                (1, false),
                (2, false),
                (3, false)
            ]),],
            [(4, true)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                4,
                [
                    Gate::new_xor(0, 1),
                    Gate::new_xor(2, 3),
                    Gate::new_xor(4, 5)
                ],
                [(6, true)]
            )
            .unwrap()
        )
    );
    assert_eq!(
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
        .unwrap(),
        ClauseCircuit::from(
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
            .unwrap()
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            7,
            [Clause::new_and([
                (6, false),
                (5, false),
                (4, false),
                (3, false),
                (2, false),
                (0, false),
                (1, false),
            ]),],
            [(7, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                7,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 7),
                    Gate::new_and(3, 8),
                    Gate::new_and(4, 9),
                    Gate::new_and(5, 10),
                    Gate::new_and(6, 11),
                ],
                [(12, false)]
            )
            .unwrap()
        )
    );

    assert_eq!(
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
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                7,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(7, 2),
                    Gate::new_and(8, 3),
                    Gate::new_and(9, 4),
                    Gate::new_and(10, 5),
                    Gate::new_and(11, 6),
                ],
                [(12, false)]
            )
            .unwrap()
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            3,
            [Clause::new_and([(0, false), (1, false), (2, false)]),],
            [(3, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(3, [Gate::new_and(0, 1), Gate::new_and(3, 2),], [(4, false)]).unwrap(),
        )
    );
}

#[test]
fn test_clause_circuit_from_circuit() {
    assert_eq!(
        ClauseCircuit::new(
            3,
            [
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_and([(2, false), (3, true)])
            ],
            [(4, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                3,
                [Gate::new_and(0, 1), Gate::new_nimpl(2, 3),],
                [(4, false)]
            )
            .unwrap(),
        )
    );
    assert_eq!(
        ClauseCircuit::new(
            3,
            [
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_xor([(2, false), (3, false)])
            ],
            [(4, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(3, [Gate::new_and(0, 1), Gate::new_xor(2, 3),], [(4, false)]).unwrap(),
        )
    );
    assert_eq!(
        ClauseCircuit::new(
            3,
            [
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_and([(2, false), (3, false)]),
                Clause::new_xor([(3, false), (4, false)])
            ],
            [(5, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                3,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_xor(3, 4),
                ],
                [(5, false)]
            )
            .unwrap(),
        )
    );
    assert_eq!(
        ClauseCircuit::new(
            3,
            [
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_and([(2, false), (3, false)]),
                Clause::new_and([(3, true), (4, true)])
            ],
            [(5, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                3,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_nor(3, 4),
                ],
                [(5, false)]
            )
            .unwrap(),
        )
    );
    assert_eq!(
        ClauseCircuit::new(
            4,
            [
                Clause::new_and([(0, false), (1, false)]),
                Clause::new_and([(2, false), (3, false)]),
                Clause::new_and([(4, true), (5, true)])
            ],
            [(6, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                4,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 3),
                    Gate::new_nor(4, 5),
                ],
                [(6, false)]
            )
            .unwrap(),
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            6,
            [
                Clause::new_and([(2, false), (0, false), (1, false)]),
                Clause::new_xor([(5, false), (3, false), (4, false)]),
                Clause::new_and([(6, false), (7, false)]),
                Clause::new_and([(6, true), (7, true)]),
                Clause::new_xor([(8, false), (9, false)])
            ],
            [(10, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                6,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 6),
                    Gate::new_xor(3, 4),
                    Gate::new_xor(5, 8),
                    Gate::new_and(7, 9),
                    Gate::new_nor(7, 9),
                    Gate::new_xor(10, 11),
                ],
                [(12, false)]
            )
            .unwrap(),
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            9,
            [
                Clause::new_and([(2, false), (0, false), (1, false)]),
                Clause::new_xor([(7, false), (3, false), (5, false)]),
                Clause::new_and([(4, true), (6, true), (8, true)]),
                Clause::new_and([(9, true), (10, true), (11, true)])
            ],
            [(12, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                9,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 9),
                    Gate::new_xor(3, 5),
                    Gate::new_xor(7, 11),
                    Gate::new_nor(4, 6),
                    Gate::new_nimpl(13, 8),
                    Gate::new_nor(10, 12),
                    Gate::new_nimpl(15, 14),
                ],
                [(16, false)]
            )
            .unwrap(),
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            9,
            [
                Clause::new_and([(2, false), (0, false), (1, false)]),
                Clause::new_xor([(7, false), (3, false), (5, false)]),
                Clause::new_and([(4, true), (6, true)]),
                Clause::new_and([(8, false), (11, true)]),
                Clause::new_and([(9, true), (10, true), (12, true)])
            ],
            [(13, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                9,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 9),
                    Gate::new_xor(3, 5),
                    Gate::new_xor(7, 11),
                    Gate::new_nor(4, 6),
                    Gate::new_nimpl(8, 13),
                    Gate::new_nor(10, 12),
                    Gate::new_nimpl(15, 14),
                ],
                [(16, false)]
            )
            .unwrap(),
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            9,
            [
                Clause::new_and([(2, false), (0, false), (1, false)]),
                Clause::new_xor([(7, false), (3, false), (5, false)]),
                Clause::new_and([(4, true), (6, true), (8, true)]),
                Clause::new_xor([(9, false), (10, false), (11, false)]),
                Clause::new_and([(9, false), (10, false), (11, false), (12, true)])
            ],
            [(13, true)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                9,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 9),
                    Gate::new_xor(3, 5),
                    Gate::new_xor(7, 11),
                    Gate::new_nor(4, 6),
                    Gate::new_nimpl(13, 8),
                    Gate::new_and(10, 12),
                    Gate::new_and(14, 15),
                    Gate::new_xor(10, 12),
                    Gate::new_xor(14, 17),
                    Gate::new_nimpl(16, 18),
                ],
                [(19, true)]
            )
            .unwrap(),
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            9,
            [
                Clause::new_xor([(7, false), (3, false), (5, false)]),
                Clause::new_and([(4, true), (6, true), (8, true)]),
                Clause::new_and([(2, false), (0, false), (1, false), (9, false), (10, false)]),
            ],
            [(10, false), (11, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                9,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 9),
                    Gate::new_xor(3, 5),
                    Gate::new_xor(7, 11),
                    Gate::new_nor(4, 6),
                    Gate::new_nimpl(13, 8),
                    Gate::new_and(10, 12),
                    Gate::new_and(14, 15),
                ],
                [(14, false), (16, false)]
            )
            .unwrap(),
        )
    );

    assert_eq!(
        ClauseCircuit::new(
            9,
            [
                Clause::new_xor([(7, false), (3, false), (5, false)]),
                Clause::new_and([
                    (4, true),
                    (6, true),
                    (8, true),
                    (2, false),
                    (0, false),
                    (1, false),
                    (9, false)
                ]),
            ],
            [(10, false)]
        )
        .unwrap(),
        ClauseCircuit::from(
            Circuit::new(
                9,
                [
                    Gate::new_and(0, 1),
                    Gate::new_and(2, 9),
                    Gate::new_xor(3, 5),
                    Gate::new_xor(7, 11),
                    Gate::new_nor(4, 6),
                    Gate::new_nimpl(13, 8),
                    Gate::new_and(10, 12),
                    Gate::new_and(14, 15),
                ],
                [(16, false)]
            )
            .unwrap(),
        )
    );

    // evaluation test
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
    let circuit = ClauseCircuit::from(circuit);
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
    let circuit = ClauseCircuit::from(circuit);
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
