/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Extend
import MQSP.Compose.Series

/-!
# Direct sum of junctions (COMP-4; mQSP §5.2 DirectSum)

Two junctions on orthogonal public branches `P₁`, `P₂` combine to a junction on `P₁ ⊕ₕ P₂`
with private space `L₁ ⊕ₕ L₂`, ports `ι₁ ⊕ ι₂`, system matrix `S₁ ⊕ S₂` (after regrouping
`(P₁ ⊕ L₁) ⊕ (P₂ ⊕ L₂) ≅ (P₁ ⊕ P₂) ⊕ (L₁ ⊕ L₂)`), transfer value `F₁ ⊕ F₂`, catalyst
`Γ₁ ⊕ Γ₂` and weights `W₁ ⊕ W₂` (Eq. (5.15)). Preparing and projecting a branch flag
(`Project` with `|+⟩`) turns this into the LCU `(F₁ + F₂)/2`.
-/

namespace MQSP

universe u₁ u₂ v₁ v₂ w x₁ x₂

open scoped InnerProductSpace

namespace DSum

variable {P₁ : Type x₁} {P₂ : Type x₂} {L₁ : Type v₁} {L₂ : Type v₂}
  [HSpace P₁] [HSpace P₂] [HSpace L₁] [HSpace L₂]

/-- The regrouped direct sum `S₁ ⊕ S₂` of `S₁ : P₁ ⊕ L₁ → P₁ ⊕ L₁` and `S₂ : P₂ ⊕ L₂ → P₂ ⊕ L₂`
acting on `(P₁ ⊕ₕ P₂) ⊕ₕ (L₁ ⊕ₕ L₂)`. -/
noncomputable def sumRegroup (S₁ : P₁ ⊕ₕ L₁ →L[ℂ] P₁ ⊕ₕ L₁) (S₂ : P₂ ⊕ₕ L₂ →L[ℂ] P₂ ⊕ₕ L₂) :
    (P₁ ⊕ₕ P₂) ⊕ₕ (L₁ ⊕ₕ L₂) →L[ℂ] (P₁ ⊕ₕ P₂) ⊕ₕ (L₁ ⊕ₕ L₂) :=
  block
    (block (fst ∘L S₁ ∘L inl) 0 0 (fst ∘L S₂ ∘L inl))
    (block (fst ∘L S₁ ∘L inr) 0 0 (fst ∘L S₂ ∘L inr))
    (block (snd ∘L S₁ ∘L inl) 0 0 (snd ∘L S₂ ∘L inl))
    (block (snd ∘L S₁ ∘L inr) 0 0 (snd ∘L S₂ ∘L inr))

theorem sumRegroup_apply (S₁ : P₁ ⊕ₕ L₁ →L[ℂ] P₁ ⊕ₕ L₁) (S₂ : P₂ ⊕ₕ L₂ →L[ℂ] P₂ ⊕ₕ L₂)
    (x₁ : P₁) (x₂ : P₂) (y₁ : L₁) (y₂ : L₂) :
    sumRegroup S₁ S₂ (mk (mk x₁ x₂) (mk y₁ y₂)) =
      mk (mk (fst (S₁ (mk x₁ y₁))) (fst (S₂ (mk x₂ y₂))))
         (mk (snd (S₁ (mk x₁ y₁))) (snd (S₂ (mk x₂ y₂)))) := by
  have h₁ : S₁ (mk x₁ y₁) = S₁ (inl x₁) + S₁ (inr y₁) := by rw [mk_eq_inl_add_inr, map_add]
  have h₂ : S₂ (mk x₂ y₂) = S₂ (inl x₂) + S₂ (inr y₂) := by rw [mk_eq_inl_add_inr, map_add]
  rw [h₁, h₂]
  ext <;> simp [sumRegroup, block_apply]

theorem isUnitary_sumRegroup {S₁ : P₁ ⊕ₕ L₁ →L[ℂ] P₁ ⊕ₕ L₁} {S₂ : P₂ ⊕ₕ L₂ →L[ℂ] P₂ ⊕ₕ L₂}
    (h₁ : IsUnitary S₁) (h₂ : IsUnitary S₂) : IsUnitary (sumRegroup S₁ S₂) := by
  refine isUnitary_of_isIsometry (isIsometry_of_norm fun v => ?_)
  obtain ⟨a, b, rfl⟩ : ∃ a b, v = mk a b := ⟨fst v, snd v, rfl⟩
  obtain ⟨x₁, x₂, rfl⟩ : ∃ x₁ x₂, a = mk x₁ x₂ := ⟨fst a, snd a, rfl⟩
  obtain ⟨y₁, y₂, rfl⟩ : ∃ y₁ y₂, b = mk y₁ y₂ := ⟨fst b, snd b, rfl⟩
  have f₁ := norm_sq_eq (S₁ (mk x₁ y₁))
  have f₂ := norm_sq_eq (S₂ (mk x₂ y₂))
  rw [h₁.isIsometry.norm_map, norm_sq_eq, fst_mk, snd_mk] at f₁
  rw [h₂.isIsometry.norm_map, norm_sq_eq, fst_mk, snd_mk] at f₂
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sumRegroup_apply]
  simp only [norm_sq_eq, fst_mk, snd_mk]
  linarith

end DSum

namespace Junction

variable {P₁ : Type x₁} {P₂ : Type x₂} [HSpace P₁] [HSpace P₂]
variable {L₁ : Type v₁} {L₂ : Type v₂} [HSpace L₁] [HSpace L₂]
variable {ι₁ : Type u₁} {ι₂ : Type u₂} [Fintype ι₁] [Fintype ι₂]
variable {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w} [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)]

/-- COMP-4 (mQSP §5.2 DirectSum). Orthogonal branches `M₁ ⊕ M₂`. -/
noncomputable def directSum (M₁ : Junction P₁ L₁ K₁) (M₂ : Junction P₂ L₂ K₂) :
    Junction (P₁ ⊕ₕ P₂) (L₁ ⊕ₕ L₂) (Sum.elim K₁ K₂) where
  S := DSum.sumRegroup M₁.S M₂.S
  isUnitary_S := DSum.isUnitary_sumRegroup M₁.isUnitary_S M₂.isUnitary_S
  ports := M₁.ports.sum M₂.ports
  delay
    | Sum.inl i => M₁.delay i
    | Sum.inr i => M₂.delay i
  one_le_delay
    | Sum.inl i => M₁.one_le_delay i
    | Sum.inr i => M₂.one_le_delay i

variable (M₁ : Junction P₁ L₁ K₁) (M₂ : Junction P₂ L₂ K₂)

theorem directSum_A : (M₁.directSum M₂).A = DSum.block M₁.A 0 0 M₂.A :=
  DSum.fst_block_inl _ _ _ _
theorem directSum_B : (M₁.directSum M₂).B = DSum.block M₁.B 0 0 M₂.B :=
  DSum.fst_block_inr _ _ _ _
theorem directSum_C : (M₁.directSum M₂).C = DSum.block M₁.C 0 0 M₂.C :=
  DSum.snd_block_inl _ _ _ _
theorem directSum_D : (M₁.directSum M₂).D = DSum.block M₁.D 0 0 M₂.D :=
  DSum.snd_block_inr _ _ _ _

/-- The feedback of a direct sum is block diagonal. -/
theorem directSum_Q (O : OracleTuple (Sum.elim K₁ K₂)) :
    (M₁.directSum M₂).Q O = DSum.block (M₁.Q O.left) 0 0 (M₂.Q O.right) :=
  Ports.sum_feedback _ _ _

theorem directSum_isRegular {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.directSum M₂).IsRegular O := by
  rw [isRegular_iff_injective] at h₁ h₂ ⊢
  rw [directSum_D, directSum_Q]
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  have e1 := congrArg DSum.fst hv
  have e2 := congrArg DSum.snd hv
  simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub,
    DSum.fst_block_apply, DSum.snd_block_apply, zero_apply, add_zero, zero_add,
    map_zero] at e1 e2
  have g1 : DSum.fst v = 0 := h₁ <| by
    rw [map_zero, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
    exact e1
  have g2 : DSum.snd v = 0 := h₂ <| by
    rw [map_zero, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
    exact e2
  exact DSum.ext (g1.trans (map_zero _).symm) (g2.trans (map_zero _).symm)

/-- COMP-4. The catalyst of a direct sum is `Γ₁ ⊕ Γ₂`. -/
theorem directSum_catalyst {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.directSum M₂).catalyst O =
      DSum.block (M₁.catalyst O.left) 0 0 (M₂.catalyst O.right) := by
  symm
  refine catalyst_unique _ (M₁.directSum_isRegular M₂ h₁ h₂) ?_
  rw [directSum_C, directSum_D, directSum_Q, DSum.block_comp_block, DSum.block_comp_block,
    DSum.block_add]
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, add_zero, zero_add]
  rw [DSum.block_ext_iff]
  exact ⟨M₁.catalyst_eq h₁, rfl, rfl, M₂.catalyst_eq h₂⟩

/-- COMP-4. The transfer value of a direct sum is `F₁ ⊕ F₂`. -/
theorem directSum_steady {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.directSum M₂).steady O =
      DSum.block (M₁.steady O.left) 0 0 (M₂.steady O.right) := by
  conv_lhs => rw [steady]
  rw [directSum_A, directSum_B, directSum_Q, directSum_catalyst M₁ M₂ h₁ h₂,
    DSum.block_comp_block, DSum.block_comp_block, DSum.block_add]
  simp only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, add_zero, zero_add]
  rfl

/-- COMP-4 (mQSP Eq. (5.15)). Weights of the left ports. -/
theorem directSum_weight_inl {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) (i : ι₁) (ψ : P₁ ⊕ₕ P₂) :
    (M₁.directSum M₂).weight O (Sum.inl i) ψ = M₁.weight O.left i (DSum.fst ψ) := by
  have h : DSum.fst ((M₁.directSum M₂).catalyst O ψ) = M₁.catalyst O.left (DSum.fst ψ) := by
    rw [directSum_catalyst M₁ M₂ h₁ h₂]
    simp
  change ‖M₁.ports.π i (DSum.fst ((M₁.directSum M₂).catalyst O ψ))‖ ^ 2 = _
  rw [h]
  rfl

/-- COMP-4 (mQSP Eq. (5.15)). Weights of the right ports. -/
theorem directSum_weight_inr {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) (i : ι₂) (ψ : P₁ ⊕ₕ P₂) :
    (M₁.directSum M₂).weight O (Sum.inr i) ψ = M₂.weight O.right i (DSum.snd ψ) := by
  have h : DSum.snd ((M₁.directSum M₂).catalyst O ψ) = M₂.catalyst O.right (DSum.snd ψ) := by
    rw [directSum_catalyst M₁ M₂ h₁ h₂]
    simp
  change ‖M₂.ports.π i (DSum.snd ((M₁.directSum M₂).catalyst O ψ))‖ ^ 2 = _
  rw [h]
  rfl

end Junction

end MQSP
