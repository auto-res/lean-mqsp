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

/-- info: 'MQSP.Junction.isUnitary_steady₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.isUnitary_steady₀

/-- info: 'MQSP.Junction.cayley_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.cayley_steady

/-- info: 'MQSP.QSVT.proj_UΦ_proj_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.QSVT.proj_UΦ_proj_odd

/-- info: 'MQSP.QSVT.proj_UΦ_proj_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.QSVT.proj_UΦ_proj_even

/-- info: 'MQSP.Signals.blk_reflWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Signals.blk_reflWalk

/--
info: 'MQSP.Junction.norm_G_le_of_partial_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Junction.norm_G_le_of_partial_bound

/--
info: 'MQSP.Junction.ChainData.steady_eq_circuit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Junction.ChainData.steady_eq_circuit

/--
info: 'MQSP.Junction.norm_steady_sub_steady_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Junction.norm_steady_sub_steady_le

/-- info: 'MQSP.Junction.subst_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.subst_steady

/-- info: 'MQSP.QSVT.qsp_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.QSVT.qsp_steady

/--
info: 'MQSP.Junction.ChainData.isEncodingOf_chain_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Junction.ChainData.isEncodingOf_chain_endpoint

/--
info: 'MQSP.Spectral.norm_polyCalc_sub_cfc_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Spectral.norm_polyCalc_sub_cfc_le

/-- info: 'MQSP.Poly.exists_amplifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Poly.exists_amplifier

/-- info: 'MQSP.Junction.isEncodingOf_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.isEncodingOf_uniform

/-- info: 'MQSP.Prog.steady_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Prog.steady_subst

/--
info: 'MQSP.Junction.CayleyData.steady_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Junction.CayleyData.steady_eq

/-- info: 'MQSP.Junction.hamSim_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.hamSim_steady

/--
info: 'MQSP.QSVT.norm_average_sub_cfc_le_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.QSVT.norm_average_sub_cfc_le_odd

/-- info: 'MQSP.Resource.oaa_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Resource.oaa_block

/-- info: 'MQSP.CPE.readout_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.CPE.readout_one

/-- info: 'MQSP.QSVT.exists_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.QSVT.exists_phases

/--
info: 'MQSP.QSVT.exists_phases_proj_average_proj_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.QSVT.exists_phases_proj_average_proj_odd

/-- info: 'MQSP.QSVT.exists_qsvt_approx_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.QSVT.exists_qsvt_approx_odd

/-- info: 'MQSP.Resource.sq_sum_sqrt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Resource.sq_sum_sqrt_le

/-- info: 'MQSP.Junction.ap1_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.ap1_steady

/--
info: 'MQSP.Signals.isEncodingOf_prepQuery' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MQSP.Signals.isEncodingOf_prepQuery

/-- info: 'MQSP.Junction.close_steady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MQSP.Junction.close_steady
