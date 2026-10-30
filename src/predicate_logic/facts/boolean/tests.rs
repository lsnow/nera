use super::*;

#[test]
fn theory_observation_projection_preserves_identity_polarity_and_read_only_queries() {
    let mut graph = BooleanGraph::<u32>::new();
    let mut budget = LogicBudget::default();
    let a = graph.external(0, &mut budget).unwrap();
    let _spectator = graph.external(1, &mut budget).unwrap();
    let b = graph.external(2, &mut budget).unwrap();
    let gate = graph.gate(BooleanOperation::Or, a, b, &mut budget).unwrap();
    graph.assign(gate, true).unwrap();
    assert_eq!(
        graph
            .forced_many_with_models(
                &[a],
                &[b.not()],
                &mut budget,
                &mut |truths, _| Ok(truths[0]),
            )
            .unwrap(),
        [Some(true)]
    );
    assert_eq!(graph.known(a), None);
    assert_eq!(graph.known(b), None);
    assert_eq!(graph.forced(a, &mut budget), Ok(None));
}

#[test]
fn batch_projection_omits_free_spectators_but_keeps_all_admitted_dependencies() {
    let mut graph = BooleanGraph::<u32>::new();
    let mut budget = LogicBudget::default();
    let a = graph.external(0, &mut budget).unwrap();
    let b = graph.external(1, &mut budget).unwrap();
    let mut spectators = Vec::new();
    for id in 2..34 {
        spectators.push(graph.external(id, &mut budget).unwrap());
    }
    for right in [b, b.not()] {
        let gate = graph
            .gate(BooleanOperation::Or, a, right, &mut budget)
            .unwrap();
        graph.assign(gate, true).unwrap();
    }
    graph.propagate(&mut budget).unwrap();
    let mut observations = vec![a, b];
    observations.extend(spectators);
    assert_eq!(
        graph
            .constrained_observations(&observations, &mut budget)
            .unwrap(),
        [a, b]
    );
    assert_eq!(
        graph.forced_many(&[a, b], &mut budget).unwrap(),
        [Some(true), None]
    );
    assert_eq!(graph.known(a), None);
}

#[test]
fn disconnected_inconsistent_guarantees_cannot_disappear_from_projection() {
    let mut graph = BooleanGraph::<u32>::new();
    let mut budget = LogicBudget::default();
    let a = graph.external(0, &mut budget).unwrap();
    let b = graph.external(1, &mut budget).unwrap();
    let query = graph.external(2, &mut budget).unwrap();
    for left in [a, a.not()] {
        for right in [b, b.not()] {
            let gate = graph
                .gate(BooleanOperation::Or, left, right, &mut budget)
                .unwrap();
            graph.assign(gate, true).unwrap();
        }
    }
    graph.propagate(&mut budget).unwrap();
    assert_eq!(graph.forced(query, &mut budget), Err(LogicError::Unproved));
}
