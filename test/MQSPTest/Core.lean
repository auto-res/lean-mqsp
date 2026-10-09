import MQSP

/-! Axiom audits for the core results. -/

/-- info: 'MQSP.Junction.isUnitary_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.isUnitary_steady

/-- info: 'MQSP.DSum.adjoint_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.DSum.adjoint_block

/-- info: 'MQSP.Junction.series_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.series_steady

/--
info: 'MQSP.Clock.isEncodingOf_quditize' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Clock.isEncodingOf_quditize

/-- info: 'MQSP.Junction.toeplitz_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.toeplitz_block

/-- info: 'MQSP.Junction.queries_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.queries_eq

/-- info: 'MQSP.Junction.directSum_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.directSum_steady

/-- info: 'MQSP.Junction.inverse_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.inverse_steady

/-- info: 'MQSP.Junction.spectator_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.spectator_steady

/--
info: 'MQSP.Junction.steady_adj_sub_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Junction.steady_adj_sub_weighted
