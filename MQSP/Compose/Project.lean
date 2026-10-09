/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.BlockEncoding
import MQSP.Compose.DirectSum

/-!
# Projection and linear combinations (COMP-8 Project, LCU; mQSP §5.2, GSLW Lemma 52)

*Project* extracts a block encoding from a module's steady value through isometries
`Vin`, `Vout` on the public space: `Vout† F Vin`. Combined with *DirectSum*, preparing and
projecting a branch flag onto `|+⟩` gives the LCU `(F₁ + F₂)/2` of two branch modules
(mQSP §5.2 DirectSum; GSLW Cor 18 / Lemma 52 in the two-term case).
-/

namespace MQSP

universe u v w x

open scoped InnerProductSpace

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-- COMP-8 (Project). The steady value is an encoding of its projected block. -/
theorem isEncodingOf_steady {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O)
    {Pin Pout : Type*} [HSpace Pin] [HSpace Pout] {Vin : Pin →L[ℂ] P} {Vout : Pout →L[ℂ] P}
    (hin : IsIsometry Vin) (hout : IsIsometry Vout) :
    IsEncodingOf (M.steady O) Vin Vout (Vout† ∘L M.steady O ∘L Vin) :=
  ⟨M.isUnitary_steady hO h, hin, hout, rfl⟩

end Junction

namespace DSum

variable {P : Type x} [HSpace P]

/-- The `|+⟩`-flag isometry `ψ ↦ (ψ ⊕ ψ)/√2 : P → P ⊕ₕ P`. -/
noncomputable def plus : P →L[ℂ] P ⊕ₕ P :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (inl + inr)

/-- `(1/√2)² = 1/2` in `ℂ`. -/
theorem sqrt_two_inv_mul_self :
    ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The adjoint of the `|+⟩`-flag isometry: `⟨+| = (fst + snd)/√2`. -/
theorem adjoint_plus : (plus : P →L[ℂ] P ⊕ₕ P)† = ((Real.sqrt 2)⁻¹ : ℂ) • (fst + snd) := by
  rw [plus, map_smulₛₗ, map_add, adjoint_inl, adjoint_inr, map_inv₀, Complex.conj_ofReal]

theorem isIsometry_plus : IsIsometry (plus : P →L[ℂ] P ⊕ₕ P) := by
  rw [IsIsometry, adjoint_plus, plus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, sqrt_two_inv_mul_self,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_add,
    fst_comp_inl, fst_comp_inr, snd_comp_inl, snd_comp_inr, add_zero, zero_add, ← two_smul ℂ,
    smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- `⟨+| (F₁ ⊕ F₂) |+⟩ = (F₁ + F₂)/2`. -/
theorem plus_adj_block_plus (F₁ F₂ : P →L[ℂ] P) :
    (plus : P →L[ℂ] P ⊕ₕ P)† ∘L block F₁ 0 0 F₂ ∘L plus = ((2 : ℂ)⁻¹) • (F₁ + F₂) := by
  rw [adjoint_plus, plus, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, sqrt_two_inv_mul_self,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_add, fst_block_inl, fst_block_inr, snd_block_inl, snd_block_inr,
    add_zero, zero_add]

end DSum

namespace Junction

variable {P : Type x} [HSpace P]
variable {L₁ L₂ : Type v} [HSpace L₁] [HSpace L₂]
variable {ι₁ ι₂ : Type u} [Fintype ι₁] [Fintype ι₂]
variable {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w} [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)]

/-- COMP-8 (LCU). The direct sum of two modules, flagged by `|+⟩`, encodes `(F₁ + F₂)/2`. -/
theorem isEncodingOf_lcu (M₁ : Junction P L₁ K₁) (M₂ : Junction P L₂ K₂)
    {O : OracleTuple (Sum.elim K₁ K₂)} (hO : O.IsUnitary)
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    IsEncodingOf ((M₁.directSum M₂).steady O) DSum.plus DSum.plus
      (((2 : ℂ)⁻¹) • (M₁.steady O.left + M₂.steady O.right)) :=
  ⟨(M₁.directSum M₂).isUnitary_steady hO (M₁.directSum_isRegular M₂ h₁ h₂),
    DSum.isIsometry_plus, DSum.isIsometry_plus,
    by rw [directSum_steady M₁ M₂ h₁ h₂, DSum.plus_adj_block_plus]⟩

end Junction

end MQSP
