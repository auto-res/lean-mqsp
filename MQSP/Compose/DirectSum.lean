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
  sorry

theorem isUnitary_sumRegroup {S₁ : P₁ ⊕ₕ L₁ →L[ℂ] P₁ ⊕ₕ L₁} {S₂ : P₂ ⊕ₕ L₂ →L[ℂ] P₂ ⊕ₕ L₂}
    (h₁ : IsUnitary S₁) (h₂ : IsUnitary S₂) : IsUnitary (sumRegroup S₁ S₂) := by
  sorry

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

theorem directSum_A : (M₁.directSum M₂).A = DSum.block M₁.A 0 0 M₂.A := by sorry
theorem directSum_B : (M₁.directSum M₂).B = DSum.block M₁.B 0 0 M₂.B := by sorry
theorem directSum_C : (M₁.directSum M₂).C = DSum.block M₁.C 0 0 M₂.C := by sorry
theorem directSum_D : (M₁.directSum M₂).D = DSum.block M₁.D 0 0 M₂.D := by sorry

theorem directSum_isRegular {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.directSum M₂).IsRegular O := by sorry

/-- COMP-4. The catalyst of a direct sum is `Γ₁ ⊕ Γ₂`. -/
theorem directSum_catalyst {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.directSum M₂).catalyst O =
      DSum.block (M₁.catalyst O.left) 0 0 (M₂.catalyst O.right) := by sorry

/-- COMP-4. The transfer value of a direct sum is `F₁ ⊕ F₂`. -/
theorem directSum_steady {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.directSum M₂).steady O =
      DSum.block (M₁.steady O.left) 0 0 (M₂.steady O.right) := by sorry

/-- COMP-4 (mQSP Eq. (5.15)). Weights of the left ports. -/
theorem directSum_weight_inl {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) (i : ι₁) (ψ : P₁ ⊕ₕ P₂) :
    (M₁.directSum M₂).weight O (Sum.inl i) ψ = M₁.weight O.left i (DSum.fst ψ) := by sorry

/-- COMP-4 (mQSP Eq. (5.15)). Weights of the right ports. -/
theorem directSum_weight_inr {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) (i : ι₂) (ψ : P₁ ⊕ₕ P₂) :
    (M₁.directSum M₂).weight O (Sum.inr i) ψ = M₂.weight O.right i (DSum.snd ψ) := by sorry

end Junction

end MQSP
