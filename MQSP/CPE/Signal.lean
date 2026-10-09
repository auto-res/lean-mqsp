/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.QSVT.Core
import MQSP.Compose.Project

/-!
# Phase signals for coherent estimation (CPE-1, CPE-2; Rall §2)

Coherent phase estimation reads the phase of a unitary `U = ∑_λ e^{iθ_λ} P_λ` one bit at a
time. The *phase signal* is the equal-weight LCU of `1` and `U` on a flag qubit:

  `W = |0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U`,  `(⟨+| ⊗ 1) W (|+⟩ ⊗ 1) = (1 + U)/2`,

whose action on an eigenvector `U ψ = e^{iθ} ψ` is `e^{iθ/2} cos(θ/2) ψ`. Thus `(1 + U)/2` is a
projected unitary encoding (`Pr = Pr' = |+⟩⟨+| ⊗ 1`) of a normal operator with singular values
`|cos(θ/2)|`, and `A†A ψ = cos²(θ/2) ψ`. Applying QSVT with an even phase sequence gives, on
every eigenvector, the scalar `p_Φ(cos²(θ/2))` (CPE-2: bit extraction reduces to a scalar
evaluation on each eigenspace; the amplifying polynomial `A_{η→δ}` makes it `≈ 0` or `≈ 1`
according to the bit of `θ`).
-/

namespace MQSP

universe u

open scoped InnerProductSpace
open Polynomial

namespace CPE

variable {H : Type u} [HSpace H]

/-- CPE-1. The phase-signal unitary `W = 1 ⊕ U` on `H ⊕ₕ H` (flag qubit `|0⟩ ↦ 1`, `|1⟩ ↦ U`). -/
noncomputable def phaseSignal (U : H →L[ℂ] H) : H ⊕ₕ H →L[ℂ] H ⊕ₕ H := DSum.block 1 0 0 U

/-- The `|+⟩`-flag projector `|+⟩⟨+| ⊗ 1 = plus plus†` on `H ⊕ₕ H`. -/
noncomputable def plusProj : H ⊕ₕ H →L[ℂ] H ⊕ₕ H := DSum.plus ∘L (DSum.plus : H →L[ℂ] H ⊕ₕ H)†

/-- `plus† (plus v) = v` (the `|+⟩`-flag is an isometry). -/
theorem plus_adj_plus_apply (v : H) : (DSum.plus : H →L[ℂ] H ⊕ₕ H)† (DSum.plus v) = v := by
  rw [← ContinuousLinearMap.comp_apply, DSum.isIsometry_plus, one_apply_eq_self]

theorem isProj_plusProj : IsProj (plusProj (H := H)) := by
  refine ⟨?_, ?_⟩
  · rw [plusProj, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  · rw [plusProj, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc _ DSum.plus,
      DSum.isIsometry_plus, one_comp]

theorem isUnitary_phaseSignal {U : H →L[ℂ] H} (hU : IsUnitary U) : IsUnitary (phaseSignal U) := by
  unfold phaseSignal
  constructor <;>
  · rw [DSum.adjoint_block, DSum.block_comp_block]
    simp [hU.1, hU.2]

/-- CPE-1. The `|+⟩`-block of the phase signal is `(1 + U)/2`. -/
theorem plus_adj_phaseSignal_plus (U : H →L[ℂ] H) :
    (DSum.plus : H →L[ℂ] H ⊕ₕ H)† ∘L phaseSignal U ∘L DSum.plus = (2 : ℂ)⁻¹ • (1 + U) :=
  DSum.plus_adj_block_plus 1 U

/-- The encoded operator `A = plusProj W plusProj` equals `plus ((1+U)/2) plus†`. -/
theorem enc_phaseSignal (U : H →L[ℂ] H) :
    QSVT.enc (phaseSignal U) plusProj plusProj =
      DSum.plus ∘L ((2 : ℂ)⁻¹ • (1 + U)) ∘L (DSum.plus : H →L[ℂ] H ⊕ₕ H)† := by
  rw [← plus_adj_phaseSignal_plus]
  simp only [QSVT.enc, plusProj, ContinuousLinearMap.comp_assoc]

/-- CPE-1. On an eigenvector `U ψ = e^{iθ} ψ`, `(1 + U)/2` acts as the scalar
`e^{iθ/2} cos(θ/2)`. -/
theorem half_one_add_apply_eigen (U : H →L[ℂ] H) {ψ : H} {θ : ℝ}
    (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) :
    ((2 : ℂ)⁻¹ • (1 + U)) ψ =
      (Complex.exp ((θ / 2) * Complex.I) * (Real.cos (θ / 2) : ℂ)) • ψ := by
  have h1 : Complex.exp (θ * Complex.I) =
      Complex.exp ((θ / 2) * Complex.I) * Complex.exp ((θ / 2) * Complex.I) := by
    rw [← Complex.exp_add]; ring_nf
  have h2 : Complex.exp ((θ / 2) * Complex.I) * Complex.exp (-(θ / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; ring_nf
  have key : (2 : ℂ)⁻¹ * (1 + Complex.exp (θ * Complex.I)) =
      Complex.exp ((θ / 2) * Complex.I) * (Real.cos (θ / 2) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos, h1]
    push_cast
    linear_combination (-1 / 2 : ℂ) * h2
  rw [← key, smul_apply, add_apply, one_apply_eq_self, hψ, mul_smul, add_smul, one_smul]

/-- On an eigenvector `U ψ = e^{iθ} ψ` of a unitary, `U† ψ = e^{-iθ} ψ`. -/
theorem adjoint_apply_eigen {U : H →L[ℂ] H} (hU : IsUnitary U) {ψ : H} {θ : ℝ}
    (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) :
    U† ψ = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) • ψ := by
  have h := congrArg (U†) hψ
  rw [← ContinuousLinearMap.comp_apply, hU.1, one_apply_eq_self, map_smul] at h
  conv_rhs => rw [h]
  rw [smul_smul, ← Complex.exp_add]
  push_cast
  rw [neg_mul, neg_add_cancel, Complex.exp_zero, one_smul]

/-- The adjoint of `(1 + U)/2` is `(1 + U†)/2`. -/
theorem adjoint_half_one_add (U : H →L[ℂ] H) :
    ((2 : ℂ)⁻¹ • (1 + U))† = (2 : ℂ)⁻¹ • (1 + U†) := by
  rw [map_smulₛₗ, map_add, adjoint_one, map_inv₀, map_ofNat]

/-- CPE-1. `A†A` acts on the lifted eigenvector `plus ψ` as `cos²(θ/2)`. -/
theorem enc_adj_enc_apply_eigen {U : H →L[ℂ] H} (hU : IsUnitary U) {ψ : H} {θ : ℝ}
    (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) :
    ((QSVT.enc (phaseSignal U) plusProj plusProj)† ∘L QSVT.enc (phaseSignal U) plusProj plusProj)
      (DSum.plus ψ) = ((Real.cos (θ / 2) ^ 2 : ℝ) : ℂ) • DSum.plus ψ := by
  rw [enc_phaseSignal, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, adjoint_half_one_add]
  simp only [ContinuousLinearMap.comp_apply, plus_adj_plus_apply]
  rw [half_one_add_apply_eigen U hψ, map_smul,
    half_one_add_apply_eigen _ (adjoint_apply_eigen hU hψ), smul_smul, ← map_smul]
  congr 2
  have h2 : Complex.exp ((θ / 2) * Complex.I) * Complex.exp (-(θ / 2) * Complex.I) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; ring_nf
  push_cast
  rw [neg_div, Complex.cos_neg]
  linear_combination (Complex.cos (θ / 2)) ^ 2 * h2

/-- A polynomial in `A` acts on an eigenvector `A v = c v` as the scalar `p(c)`. -/
theorem aeval_apply_eigen {E : Type*} [HSpace E] {A : E →L[ℂ] E} {v : E} {c : ℂ}
    (h : A v = c • v) (p : ℂ[X]) : aeval A p v = p.eval c • v := by
  induction p using Polynomial.induction_on with
  | C a => rw [aeval_C, eval_C, ContinuousLinearMap.algebraMap_apply]
  | add p q hp hq => rw [map_add, add_apply, hp, hq, eval_add, add_smul]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_apply_eq_comp, h, map_smul, ih,
      smul_smul, eval_mul_X, mul_comm]

/-- CPE-2 (bit extraction on an eigenspace). For an even phase sequence `Φ`, the projected
QSVT of the phase signal acts on `plus ψ` as the scalar `p_Φ(cos²(θ/2))`. -/
theorem proj_UΦ_plus_eigen {U : H →L[ℂ] H} (hU : IsUnitary U) (Φ : List ℝ)
    (hΦ : Φ.length % 2 = 0) {ψ : H} {θ : ℝ} (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) :
    (plusProj ∘L QSVT.UΦ (phaseSignal U) plusProj plusProj Φ ∘L plusProj)
      (DSum.plus ψ) =
      ((QSVT.pqΦ Φ).1.eval ((Real.cos (θ / 2) ^ 2 : ℝ) : ℂ)) • DSum.plus ψ := by
  have hp : plusProj (DSum.plus ψ) = DSum.plus ψ := by
    rw [plusProj, ContinuousLinearMap.comp_apply, plus_adj_plus_apply]
  rw [QSVT.proj_UΦ_proj_even (isUnitary_phaseSignal hU) isProj_plusProj isProj_plusProj Φ hΦ,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hp,
    aeval_apply_eigen (enc_adj_enc_apply_eigen hU hψ), map_smul, hp]

end CPE

end MQSP
