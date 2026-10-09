/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg

/-!
# Block encodings and projected unitary encodings (CORE-6)

A *projected unitary encoding* (GSLW Def 11, mQSP Eq. (1.16)) of `A : Pin →L[ℂ] Pout` is a
unitary `U` on a larger space `H` together with isometries `Vin : Pin → H`, `Vout : Pout → H`
such that `Vout† U Vin = A`. The usual block encoding `(⟨0| ⊗ I) U (|0⟩ ⊗ I) = A/λ` is the case
`H = Reg n E`, `Vin = Vout = Reg.single 0`. The clock-selected block of a quditization
(mQSP Eq. (1.10)) is the case where `Vin`, `Vout` are the clock-state isometries.

We state the notion with explicit isometries (rather than projectors `Π = V V†`) because this
is what composes: `Series + Project` gives products, `DirectSum + Project` gives linear
combinations.
-/

namespace MQSP

universe u v w

open scoped InnerProductSpace

/-- Isometries compose. -/
theorem IsIsometry.comp {E : Type u} {F : Type v} {G : Type w} [HSpace E] [HSpace F] [HSpace G]
    {V : F →L[ℂ] G} {W : E →L[ℂ] F} (hV : IsIsometry V) (hW : IsIsometry W) :
    IsIsometry (V ∘L W) := by
  rw [IsIsometry, ContinuousLinearMap.adjoint_comp,
    show (W† ∘L V†) ∘L (V ∘L W) = W† ∘L (V† ∘L V) ∘L W by
      simp only [ContinuousLinearMap.comp_assoc],
    hV, one_comp]
  exact hW

/-- CORE-6. `U` encodes `A` between the isometries `Vin` and `Vout`: `Vout† U Vin = A`. -/
structure IsEncodingOf {H : Type u} {Pin : Type v} {Pout : Type w} [HSpace H] [HSpace Pin]
    [HSpace Pout] (U : H →L[ℂ] H) (Vin : Pin →L[ℂ] H) (Vout : Pout →L[ℂ] H)
    (A : Pin →L[ℂ] Pout) : Prop where
  isUnitary : IsUnitary U
  isIsometry_in : IsIsometry Vin
  isIsometry_out : IsIsometry Vout
  block : Vout† ∘L U ∘L Vin = A

namespace IsEncodingOf

variable {H : Type u} {Pin : Type v} {Pout : Type w} [HSpace H] [HSpace Pin] [HSpace Pout]
  {U : H →L[ℂ] H} {Vin : Pin →L[ℂ] H} {Vout : Pout →L[ℂ] H} {A : Pin →L[ℂ] Pout}

/-- An encoded operator is a contraction. -/
theorem opNorm_le_one (h : IsEncodingOf U Vin Vout A) : ‖A‖ ≤ 1 := by
  have hout : ‖Vout†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact h.isIsometry_out.opNorm_le_one
  rw [← h.block]
  calc ‖Vout† ∘L U ∘L Vin‖ ≤ ‖Vout†‖ * (‖U‖ * ‖Vin‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by
        gcongr
        · exact h.isUnitary.opNorm_le_one
        · exact h.isIsometry_in.opNorm_le_one
    _ = 1 := by norm_num

/-- The adjoint unitary encodes the adjoint. -/
theorem adjoint (h : IsEncodingOf U Vin Vout A) : IsEncodingOf (U†) Vout Vin (A†) := by
  refine ⟨h.isUnitary.adjoint, h.isIsometry_out, h.isIsometry_in, ?_⟩
  rw [← h.block, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- Encodings compose with known isometries on both sides. -/
theorem comp_isometry {Pin' : Type*} {Pout' : Type*} [HSpace Pin'] [HSpace Pout']
    (h : IsEncodingOf U Vin Vout A) {Win : Pin' →L[ℂ] Pin} {Wout : Pout' →L[ℂ] Pout}
    (hin : IsIsometry Win) (hout : IsIsometry Wout) :
    IsEncodingOf U (Vin ∘L Win) (Vout ∘L Wout) (Wout† ∘L A ∘L Win) := by
  refine ⟨h.isUnitary, h.isIsometry_in.comp hin, h.isIsometry_out.comp hout, ?_⟩
  rw [← h.block, ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

/-- The standard block encoding `(⟨0| ⊗ I) U (|0⟩ ⊗ I) = A` on `Reg n E`. -/
abbrev Standard {n : ℕ} {E : Type u} [HSpace E] (U : Reg (n + 1) E →L[ℂ] Reg (n + 1) E)
    (A : E →L[ℂ] E) : Prop :=
  IsEncodingOf U (Reg.single 0) (Reg.single 0) A

end IsEncodingOf

end MQSP
