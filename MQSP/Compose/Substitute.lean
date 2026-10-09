/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Extend
import MQSP.Compose.Series

/-!
# Module substitution (COMP-7; mQSP §5.2 Substitute)

An outer module `MA` with ports `ιA` and an inner module `MB` whose public space is the port
space `KA j₀` of `MA` compose by *substitution*: the feedback connection of port `j₀` is
implemented by `MB` instead of an oracle. The public space of `MB` becomes private relative to
the outer module (an identity wire of zero cost, kept as port `j₀` with the fixed oracle `1`),
and the new private space is `LA ⊕ₕ LB` with ports `ιA ⊕ ιB`. The system matrix is
`(S_A ⊕ 1_{LB}) ∘ (1_P ⊕ S_B')` where `S_B'` is `S_B` acting on `(π_{j₀})† KA j₀ ⊕ LB` and the
identity on its orthogonal complement.

At `z = 1` the steady value is the outer steady value with the oracle at `j₀` replaced by
`F_B` (mQSP §5.2: `A_A + B_A F_B (1 - D_A F_B)⁻¹ C_A`), the catalyst is
`Γ_A' ψ ⊕ Γ_B (π_{j₀} Γ_A' ψ)`, and the weights of `MB`'s ports are those of `MB` on the
transmitted state `π_{j₀} Γ_A' ψ` (thrifty nesting).
-/

namespace MQSP

universe u₁ u₂ v₁ v₂ w x

open scoped InnerProductSpace

section Aux

variable {X : Type*} {Y : Type*} [HSpace X] [HSpace Y]

/-- If `V` is an isometry and `S` is unitary, then `V S V† + (1 - V V†)` is unitary. -/
private theorem isUnitary_conj_add_one_sub' {V : X →L[ℂ] Y} (hV : IsIsometry V)
    {S : X →L[ℂ] X} (hS : IsUnitary S) : IsUnitary (V ∘L S ∘L V† + (1 - V ∘L V†)) := by
  apply isUnitary_of_isIsometry
  refine ContinuousLinearMap.ext (fun y => ?_)
  have h1 := hV.apply_adjoint_apply
  have h2 := hS.isIsometry.apply_adjoint_apply
  simp only [map_add, map_sub, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, adjoint_one, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply, one_apply_eq_self, h1, h2, sub_self, add_zero]
  abel

/-- `1 ⊕ U` is unitary when `U` is. -/
private theorem isUnitary_block_one {U : Y →L[ℂ] Y} (hU : IsUnitary U) :
    IsUnitary (DSum.block (1 : X →L[ℂ] X) 0 0 U) := by
  refine ⟨?_, ?_⟩ <;> rw [DSum.adjoint_block, DSum.block_comp_block] <;> simp [hU.1, hU.2]

end Aux

namespace Ports

variable {L : Type v₁} [HSpace L] {ι : Type u₁} [Fintype ι] [DecidableEq ι]
variable {K : ι → Type w} [∀ i, HSpace (K i)]

/-- Replacing the oracle at port `j` changes the feedback only on that port. -/
theorem feedback_update (ps : Ports L K) (O : OracleTuple K) (j : ι) (V : K j →L[ℂ] K j)
    (v : L) :
    ps.feedback (Function.update O j V) v =
      ps.feedback O v - (ps.π j)† (O j (ps.π j v)) + (ps.π j)† (V (ps.π j v)) := by
  have hj := Finset.mem_univ j
  have h1 := Finset.add_sum_erase Finset.univ
    (fun i => (ps.π i)† (Function.update O j V i (ps.π i v))) hj
  have h2 := Finset.add_sum_erase Finset.univ (fun i => (ps.π i)† (O i (ps.π i v))) hj
  have h3 : ∑ i ∈ Finset.univ.erase j, (ps.π i)† (Function.update O j V i (ps.π i v)) =
      ∑ i ∈ Finset.univ.erase j, (ps.π i)† (O i (ps.π i v)) :=
    Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self] at h1
  rw [ps.feedback_apply, ps.feedback_apply, ← h1, ← h2, h3]
  abel

end Ports

namespace Junction

section Generic

variable {P' : Type*} {L' : Type*} [HSpace P'] [HSpace L'] {ι' : Type*} [Fintype ι']
variable {K' : ι' → Type*} [∀ i, HSpace (K' i)]

/-- A pointwise solution of the fixed-point equation `g = C x + D Q g` is the catalyst. -/
theorem eq_catalyst_apply (M : Junction P' L' K') {O : OracleTuple K'} (h : M.IsRegular O)
    {x : P'} {g : L'} (hg : M.C x + M.D (M.Q O g) = g) : g = M.catalyst O x := by
  refine (M.isRegular_iff_injective O).1 h ?_
  have hc := congrArg (fun T : P' →L[ℂ] L' => T x) (M.catalyst_eq h)
  simp only [add_apply, ContinuousLinearMap.comp_apply] at hc
  simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
  rw [sub_eq_of_eq_add hg.symm, sub_eq_of_eq_add hc]

theorem fst_S_mk (M : Junction P' L' K') (x : P') (w : L') :
    DSum.fst (M.S (DSum.mk x w)) = M.A x + M.B w := by
  rw [S_apply]
  rfl

theorem snd_S_mk (M : Junction P' L' K') (x : P') (w : L') :
    DSum.snd (M.S (DSum.mk x w)) = M.C x + M.D w := by
  rw [S_apply]
  rfl

end Generic

variable {P : Type x} [HSpace P]
variable {LA : Type v₁} {LB : Type v₂} [HSpace LA] [HSpace LB]
variable {ιA : Type u₁} {ιB : Type u₂} [Fintype ιA] [Fintype ιB]
variable {KA : ιA → Type w} {KB : ιB → Type w} [∀ i, HSpace (KA i)] [∀ i, HSpace (KB i)]

/-- The isometry embedding `KA j₀ ⊕ₕ LB` into `LA ⊕ₕ LB` through the port `j₀`. -/
noncomputable def substEmbed (MA : Junction P LA KA) (j₀ : ιA) :
    KA j₀ ⊕ₕ LB →L[ℂ] LA ⊕ₕ LB :=
  DSum.block ((MA.ports.π j₀)†) 0 0 1

theorem substEmbed_apply (MA : Junction P LA KA) (j₀ : ιA) (v : KA j₀ ⊕ₕ LB) :
    substEmbed MA j₀ v = DSum.mk ((MA.ports.π j₀)† (DSum.fst v)) (DSum.snd v) := by
  rw [substEmbed, DSum.block_apply]
  simp

theorem adjoint_substEmbed (MA : Junction P LA KA) (j₀ : ιA) :
    (substEmbed (LB := LB) MA j₀)† = DSum.block (MA.ports.π j₀) 0 0 1 := by
  rw [substEmbed, DSum.adjoint_block, ContinuousLinearMap.adjoint_adjoint, map_zero, map_zero,
    adjoint_one]

theorem adjoint_substEmbed_apply (MA : Junction P LA KA) (j₀ : ιA) (v : LA ⊕ₕ LB) :
    (substEmbed MA j₀)† v = DSum.mk (MA.ports.π j₀ (DSum.fst v)) (DSum.snd v) := by
  rw [adjoint_substEmbed, DSum.block_apply]
  simp

theorem isIsometry_substEmbed (MA : Junction P LA KA) (j₀ : ιA) :
    IsIsometry (substEmbed (LB := LB) MA j₀) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, substEmbed_apply, adjoint_substEmbed_apply, DSum.fst_mk,
    DSum.snd_mk, MA.ports.π_adj_apply_self, one_apply_eq_self, DSum.mk_fst_snd]

/-- `S_B` acting on the port-`j₀` sector and `LB`, and the identity elsewhere. -/
noncomputable def substInner (MA : Junction P LA KA) (j₀ : ιA) (MB : Junction (KA j₀) LB KB) :
    LA ⊕ₕ LB →L[ℂ] LA ⊕ₕ LB :=
  substEmbed MA j₀ ∘L MB.S ∘L (substEmbed MA j₀)† +
    (1 - substEmbed MA j₀ ∘L (substEmbed MA j₀)†)

theorem isUnitary_substInner (MA : Junction P LA KA) (j₀ : ιA) (MB : Junction (KA j₀) LB KB) :
    IsUnitary (substInner MA j₀ MB) :=
  isUnitary_conj_add_one_sub' (isIsometry_substEmbed MA j₀) MB.isUnitary_S

theorem substInner_apply (MA : Junction P LA KA) (j₀ : ιA) (MB : Junction (KA j₀) LB KB)
    (a : LA) (b : LB) :
    substInner MA j₀ MB (DSum.mk a b) =
      DSum.mk (a - (MA.ports.π j₀)† (MA.ports.π j₀ a) +
          (MA.ports.π j₀)† (DSum.fst (MB.S (DSum.mk (MA.ports.π j₀ a) b))))
        (DSum.snd (MB.S (DSum.mk (MA.ports.π j₀ a) b))) := by
  ext
  · simp only [substInner, add_apply, sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, substEmbed_apply, adjoint_substEmbed_apply, DSum.fst_mk,
      DSum.snd_mk, map_add, map_sub]
    abel
  · simp only [substInner, add_apply, sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, substEmbed_apply, adjoint_substEmbed_apply, DSum.fst_mk,
      DSum.snd_mk, map_add, map_sub, sub_self, add_zero]

/-- COMP-7 (mQSP §5.2 Substitute). Substitute `MB` for the oracle at port `j₀` of `MA`. -/
noncomputable def subst (MA : Junction P LA KA) (j₀ : ιA) (MB : Junction (KA j₀) LB KB) :
    Junction P (LA ⊕ₕ LB) (Sum.elim KA KB) where
  S := DSum.extendR LB MA.S ∘L DSum.block 1 0 0 (substInner MA j₀ MB)
  isUnitary_S := by
    exact (DSum.isUnitary_extendR MA.isUnitary_S).comp
      (isUnitary_block_one (isUnitary_substInner MA j₀ MB))
  ports := MA.ports.sum MB.ports
  delay
    | Sum.inl i => MA.delay i
    | Sum.inr i => MB.delay i
  one_le_delay
    | Sum.inl i => MA.one_le_delay i
    | Sum.inr i => MB.one_le_delay i

variable (MA : Junction P LA KA) (j₀ : ιA) (MB : Junction (KA j₀) LB KB)

/-- The feedback of the substituted module is block diagonal. -/
theorem subst_Q (O : OracleTuple (Sum.elim KA KB)) :
    (subst MA j₀ MB).Q O = DSum.block (MA.Q O.left) 0 0 (MB.Q O.right) :=
  Ports.sum_feedback _ _ _

/-- The substituted system matrix on a feedback state. -/
theorem subst_S_Q_apply (O : OracleTuple (Sum.elim KA KB)) (ψ : P) (a : LA) (b : LB) :
    (subst MA j₀ MB).S (DSum.mk ψ ((subst MA j₀ MB).Q O (DSum.mk a b))) =
      DSum.extendR LB MA.S
        (DSum.mk ψ (substInner MA j₀ MB (DSum.mk (MA.Q O.left a) (MB.Q O.right b)))) := by
  rw [subst_Q, DSum.block_apply]
  simp only [subst, ContinuousLinearMap.comp_apply, DSum.block_apply, DSum.fst_mk, DSum.snd_mk,
    zero_apply, add_zero, zero_add, one_apply_eq_self]

variable [DecidableEq ιA]

/-- The effective outer oracle tuple: port `j₀` carries the inner steady value `F_B`. -/
noncomputable def substOuter (O : OracleTuple (Sum.elim KA KB)) : OracleTuple KA :=
  Function.update O.left j₀ (MB.steady O.right)

/-- The inner loop at its steady state turns the outer feedback into that of `substOuter`. -/
theorem substInner_steady {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (g : LA) :
    substInner MA j₀ MB (DSum.mk (MA.Q O.left g)
        (MB.Q O.right (MB.catalyst O.right (MA.ports.π j₀ g)))) =
      DSum.mk (MA.Q (substOuter j₀ MB O) g) (MB.catalyst O.right (MA.ports.π j₀ g)) := by
  have hπ : MA.ports.π j₀ (MA.Q O.left g) = MA.ports.π j₀ g := by
    rw [Q, Ports.π_feedback_apply, hid, one_apply_eq_self]
  have hQ : MA.Q (substOuter j₀ MB O) g = MA.Q O.left g -
      (MA.ports.π j₀)† (MA.ports.π j₀ g) +
        (MA.ports.π j₀)† (MB.steady O.right (MA.ports.π j₀ g)) := by
    rw [Q, substOuter, Ports.feedback_update, hid, one_apply_eq_self]
    rfl
  rw [substInner_apply, hπ, MB.steady_state_eq hB, DSum.fst_mk, DSum.snd_mk, hQ]

/-- The steady-state equation of the substituted module. -/
theorem subst_S_steady {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (hA : MA.IsRegular (substOuter j₀ MB O)) (ψ : P) :
    (subst MA j₀ MB).S (DSum.mk ψ ((subst MA j₀ MB).Q O
        (DSum.mk (MA.catalyst (substOuter j₀ MB O) ψ)
          (MB.catalyst O.right (MA.ports.π j₀ (MA.catalyst (substOuter j₀ MB O) ψ)))))) =
      DSum.mk (MA.steady (substOuter j₀ MB O) ψ)
        (DSum.mk (MA.catalyst (substOuter j₀ MB O) ψ)
          (MB.catalyst O.right (MA.ports.π j₀ (MA.catalyst (substOuter j₀ MB O) ψ)))) := by
  rw [subst_S_Q_apply, substInner_steady MA j₀ MB hid hB, DSum.extendR_apply,
    MA.steady_state_eq hA, DSum.fst_mk, DSum.snd_mk]

/-- COMP-7. Regularity of the substituted module, for an identity wire at `j₀`. -/
theorem subst_isRegular {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (hA : MA.IsRegular (substOuter j₀ MB O)) :
    (subst MA j₀ MB).IsRegular O := by
  rw [isRegular_iff_injective]
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  obtain ⟨gA, gB, rfl⟩ : ∃ gA gB, v = DSum.mk gA gB := ⟨_, _, (DSum.mk_fst_snd v).symm⟩
  rw [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, sub_eq_zero] at hv
  have hv' : DSum.snd ((subst MA j₀ MB).S
      (DSum.mk 0 ((subst MA j₀ MB).Q O (DSum.mk gA gB)))) = DSum.mk gA gB := hv.symm
  have hπ : MA.ports.π j₀ (MA.Q O.left gA) = MA.ports.π j₀ gA := by
    rw [Q, Ports.π_feedback_apply, hid, one_apply_eq_self]
  have h2 := congrArg DSum.snd hv'
  rw [subst_S_Q_apply, substInner_apply, DSum.extendR_apply, hπ] at h2
  simp only [DSum.snd_mk, snd_S_mk] at h2
  obtain rfl := MB.eq_catalyst_apply hB h2
  rw [subst_S_Q_apply, substInner_steady MA j₀ MB hid hB, DSum.extendR_apply] at hv'
  have h1 := congrArg DSum.fst hv'
  simp only [DSum.snd_mk, DSum.fst_mk, snd_S_mk] at h1
  obtain rfl : gA = 0 := (MA.eq_catalyst_apply hA h1).trans (map_zero _)
  simp

/-- COMP-7. The catalyst of the substituted module: `Γ_A' ψ ⊕ Γ_B (π_{j₀} Γ_A' ψ)`. -/
theorem subst_catalyst {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (hA : MA.IsRegular (substOuter j₀ MB O)) :
    (subst MA j₀ MB).catalyst O =
      DSum.inl ∘L MA.catalyst (substOuter j₀ MB O) +
        DSum.inr ∘L MB.catalyst O.right ∘L MA.ports.π j₀ ∘L MA.catalyst (substOuter j₀ MB O) := by
  symm
  refine catalyst_unique _ (subst_isRegular MA j₀ MB hid hB hA) ?_
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hcand : (DSum.inl ∘L MA.catalyst (substOuter j₀ MB O) +
      DSum.inr ∘L MB.catalyst O.right ∘L MA.ports.π j₀ ∘L MA.catalyst (substOuter j₀ MB O) :
        P →L[ℂ] LA ⊕ₕ LB) ψ =
      DSum.mk (MA.catalyst (substOuter j₀ MB O) ψ)
        (MB.catalyst O.right (MA.ports.π j₀ (MA.catalyst (substOuter j₀ MB O) ψ))) := by
    ext <;> simp
  have hCD : ∀ w, (subst MA j₀ MB).C ψ + (subst MA j₀ MB).D w =
      DSum.snd ((subst MA j₀ MB).S (DSum.mk ψ w)) := by
    intro w
    rw [S_apply]
    rfl
  rw [hcand, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hcand,
    hCD, subst_S_steady MA j₀ MB hid hB hA, DSum.snd_mk]

/-- COMP-7 (mQSP §5.2 Substitute). The steady value of the substituted module is the outer
steady value with `F_B` substituted at port `j₀`. -/
theorem subst_steady {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (hA : MA.IsRegular (substOuter j₀ MB O)) :
    (subst MA j₀ MB).steady O = MA.steady (substOuter j₀ MB O) := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hcand : (subst MA j₀ MB).catalyst O ψ =
      DSum.mk (MA.catalyst (substOuter j₀ MB O) ψ)
        (MB.catalyst O.right (MA.ports.π j₀ (MA.catalyst (substOuter j₀ MB O) ψ))) := by
    rw [subst_catalyst MA j₀ MB hid hB hA]
    ext <;> simp
  have hAB : ∀ w, (subst MA j₀ MB).A ψ + (subst MA j₀ MB).B w =
      DSum.fst ((subst MA j₀ MB).S (DSum.mk ψ w)) := by
    intro w
    rw [S_apply]
    rfl
  rw [steady, add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hcand,
    hAB, subst_S_steady MA j₀ MB hid hB hA, DSum.fst_mk]

/-- COMP-7. Weights of the outer ports are those of `MA` with `F_B` substituted. -/
theorem subst_weight_inl {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (hA : MA.IsRegular (substOuter j₀ MB O)) (i : ιA) (ψ : P) :
    (subst MA j₀ MB).weight O (Sum.inl i) ψ = MA.weight (substOuter j₀ MB O) i ψ := by
  have h : DSum.fst ((subst MA j₀ MB).catalyst O ψ) = MA.catalyst (substOuter j₀ MB O) ψ := by
    rw [subst_catalyst MA j₀ MB hid hB hA]
    simp
  change ‖MA.ports.π i (DSum.fst ((subst MA j₀ MB).catalyst O ψ))‖ ^ 2 = _
  rw [h]
  rfl

/-- COMP-7 (thrifty nesting). Weights of the inner ports are those of `MB` on the transmitted
state `π_{j₀} Γ_A' ψ`. -/
theorem subst_weight_inr {O : OracleTuple (Sum.elim KA KB)} (hid : O.left j₀ = 1)
    (hB : MB.IsRegular O.right) (hA : MA.IsRegular (substOuter j₀ MB O)) (k : ιB) (ψ : P) :
    (subst MA j₀ MB).weight O (Sum.inr k) ψ =
      MB.weight O.right k (MA.ports.π j₀ (MA.catalyst (substOuter j₀ MB O) ψ)) := by
  have h : DSum.snd ((subst MA j₀ MB).catalyst O ψ) =
      MB.catalyst O.right (MA.ports.π j₀ (MA.catalyst (substOuter j₀ MB O) ψ)) := by
    rw [subst_catalyst MA j₀ MB hid hB hA]
    simp
  change ‖MB.ports.π k (DSum.snd ((subst MA j₀ MB).catalyst O ψ))‖ ^ 2 = _
  rw [h]
  rfl

end Junction

end MQSP
