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
