use super::*;

fn word(atom: u32) -> LinearWord<u32> {
    LinearWord {
        terms: BTreeMap::from([(atom, 1)]),
        constant: 0,
        lower: 0,
        upper: 3,
    }
}

#[test]
fn warmed_paths_follow_tightened_bounds_and_disconnected_contradictions() {
    let (x, y, z) = (word(1), word(2), word(3));
    let mut graph = Graph::new();
    graph.word(&x, &mut LogicBudget::default()).unwrap();
    graph.word(&y, &mut LogicBudget::default()).unwrap();
    assert!(
        !graph
            .entails(Comparison::Less, &x, &y, &mut LogicBudget::default())
            .unwrap()
    );
    graph
        .comparison(Comparison::Less, &x, &y, &mut LogicBudget::default())
        .unwrap();
    assert!(
        graph
            .entails(Comparison::Less, &x, &y, &mut LogicBudget::default())
            .unwrap()
    );
    assert!(
        !graph
            .entails(Comparison::Equal, &x, &y, &mut LogicBudget::default())
            .unwrap()
    );
    let mut exhausted = LogicBudget::default();
    exhausted.charge(MAX_SUBSTITUTION_NODES).unwrap();
    assert_eq!(graph.consistent(&mut exhausted), Err(LogicError::Budget));
    // A new component is checked even if the requested comparison was already
    // proved. No successful cached path may hide a later contradiction.
    graph
        .comparison(Comparison::Less, &z, &z, &mut LogicBudget::default())
        .unwrap();
    assert_eq!(
        graph.entails(Comparison::Less, &x, &y, &mut LogicBudget::default()),
        Err(LogicError::Unproved)
    );
}

#[test]
fn reused_difference_graphs_match_a_small_exhaustive_integer_oracle() {
    let terms = [word(1), word(2), word(3)];
    let premises = [
        (Comparison::LessEqual, 0, 1),
        (Comparison::Less, 1, 2),
        (Comparison::LessEqual, 2, 0),
        (Comparison::Equal, 0, 2),
    ];
    let holds = |op, a, b| match op {
        Comparison::Equal => a == b,
        Comparison::Less => a < b,
        Comparison::LessEqual => a <= b,
    };
    for mask in 0..16 {
        let mut graph = Graph::new();
        for term in &terms {
            graph.word(term, &mut LogicBudget::default()).unwrap();
        }
        // Warm the graph before adding premises to exercise invalidation.
        graph.consistent(&mut LogicBudget::default()).unwrap();
        for (bit, (op, a, b)) in premises.iter().enumerate() {
            if mask & (1 << bit) != 0 {
                graph
                    .comparison(*op, &terms[*a], &terms[*b], &mut LogicBudget::default())
                    .unwrap();
            }
        }
        let mut models = Vec::new();
        for x in 0..=3 {
            for y in 0..=3 {
                for z in 0..=3 {
                    let values = [x, y, z];
                    if premises.iter().enumerate().all(|(bit, (op, a, b))| {
                        mask & (1 << bit) == 0 || holds(*op, values[*a], values[*b])
                    }) {
                        models.push(values);
                    }
                }
            }
        }
        for a in 0..3 {
            for b in 0..3 {
                for op in [Comparison::Equal, Comparison::Less, Comparison::LessEqual] {
                    let expected = if models.is_empty() {
                        Err(LogicError::Unproved)
                    } else {
                        Ok(models.iter().all(|values| holds(op, values[a], values[b])))
                    };
                    for _ in 0..2 {
                        assert_eq!(
                            graph.entails(op, &terms[a], &terms[b], &mut LogicBudget::default()),
                            expected,
                            "mask={mask} {a} {op:?} {b}"
                        );
                    }
                }
            }
        }
    }
}
