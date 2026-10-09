/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Modules.Query

/-!
# The first-order all-pass module (LIB-1; mQSP Eq. (4.66)–(4.71), §5.1)

For a one-dimensional phase oracle `O(x) = x` (`|x| = 1`) and `0 < a < 1`, the all-pass
section `AP1_a` has the `2×2` unitary system matrix `S = [[-a, √(1-a²)], [√(1-a²), a]]`
(Eq. (4.67)), transfer function `(zx - a)/(1 - a z x)` (a Blaschke factor loaded by the
query), steady value `(x - a)/(1 - a x)` and catalyst weight `(1 - a²)/|1 - a x|²`
(Eq. (4.69)). Under the gap promise `|1 - x| ≥ Δ` the weight is at most `2(1-a)/(aΔ²)`
(Eq. (4.70)), and the pole `z = (a x)⁻¹` stays away from `1` (Eq. (4.71)).
-/

namespace MQSP

universe u

namespace Junction

section Helpers

theorem ap1_sqrt_mul_self {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (Real.sqrt (1 - a ^ 2) : ℂ) * (Real.sqrt (1 - a ^ 2) : ℂ) = 1 - (a : ℂ) ^ 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
  push_cast; ring

theorem ap1_smul_one_eq_one {k : ℂ} (h : k = 1) : k • (1 : ℂ →L[ℂ] ℂ) = 1 := by
  subst h; exact one_smul ℂ (1 : ℂ →L[ℂ] ℂ)

theorem ap1_smul_one_eq_zero {k : ℂ} (h : k = 0) : k • (1 : ℂ →L[ℂ] ℂ) = 0 := by
  subst h; exact zero_smul ℂ (1 : ℂ →L[ℂ] ℂ)

/-- The system matrix of `AP1_a` (Eq. (4.67)) is unitary: `a² + (1 - a²) = 1`. -/
theorem ap1_isUnitary_S {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IsUnitary (DSum.block ((-(a : ℂ)) • (1 : ℂ →L[ℂ] ℂ))
      ((Real.sqrt (1 - a ^ 2) : ℂ) • (1 : ℂ →L[ℂ] ℂ))
      ((Real.sqrt (1 - a ^ 2) : ℂ) • (1 : ℂ →L[ℂ] ℂ)) ((a : ℂ) • (1 : ℂ →L[ℂ] ℂ))) := by
  have hs := ap1_sqrt_mul_self ha ha1
  constructor <;>
  · rw [DSum.adjoint_block, DSum.block_comp_block, ← DSum.block_one_zero_zero_one,
      DSum.block_ext_iff]
    simp only [map_smulₛₗ, adjoint_one, Complex.conj_ofReal, map_neg,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, one_comp, smul_smul,
      ← add_smul]
    exact ⟨ap1_smul_one_eq_one (by linear_combination hs), ap1_smul_one_eq_zero (by ring),
      ap1_smul_one_eq_zero (by ring), ap1_smul_one_eq_one (by linear_combination hs)⟩

end Helpers

/-- LIB-1 (mQSP Eq. (4.67)). The first-order all-pass junction on `P = L = ℂ`. -/
noncomputable def ap1 (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : Junction ℂ ℂ (onePort ℂ) where
  S := DSum.block ((-(a : ℂ)) • 1) ((Real.sqrt (1 - a ^ 2) : ℂ) • 1)
    ((Real.sqrt (1 - a ^ 2) : ℂ) • 1) ((a : ℂ) • 1)
  isUnitary_S := ap1_isUnitary_S ha ha1
  ports := Ports.one ℂ
  delay _ := 1
  one_le_delay _ := le_rfl

variable {a : ℝ} (ha : 0 < a) (ha1 : a < 1)

@[simp] theorem ap1_A : (ap1 a ha ha1).A = (-(a : ℂ)) • 1 := DSum.fst_block_inl _ _ _ _
@[simp] theorem ap1_B : (ap1 a ha ha1).B = (Real.sqrt (1 - a ^ 2) : ℂ) • 1 :=
  DSum.fst_block_inr _ _ _ _
@[simp] theorem ap1_C : (ap1 a ha ha1).C = (Real.sqrt (1 - a ^ 2) : ℂ) • 1 :=
  DSum.snd_block_inl _ _ _ _
@[simp] theorem ap1_D : (ap1 a ha ha1).D = (a : ℂ) • 1 := DSum.snd_block_inr _ _ _ _
@[simp] theorem ap1_π (i : One) : (ap1 a ha ha1).ports.π i = 1 := rfl

theorem ap1_Q (U : ℂ →L[ℂ] ℂ) : (ap1 a ha ha1).Q (oneOracle U) = U := by
  rw [Q, Ports.feedback, Fintype.sum_unique]
  simp only [ap1_π, adjoint_one, one_comp, comp_one]
  rfl

/-- The phase oracle `x` as an operator on `ℂ`. -/
noncomputable def phaseOracle (x : ℂ) : ℂ →L[ℂ] ℂ := x • 1

theorem isUnitary_phaseOracle {x : ℂ} (hx : ‖x‖ = 1) : IsUnitary (phaseOracle x) := by
  have h1 : (starRingEnd ℂ) x * x = 1 := by rw [Complex.conj_mul', hx]; simp
  have h2 : x * (starRingEnd ℂ) x = 1 := by rw [mul_comm, h1]
  unfold phaseOracle
  constructor
  · rw [map_smulₛₗ, adjoint_one, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      one_comp, smul_smul, h1, one_smul]
  · rw [map_smulₛₗ, adjoint_one, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      one_comp, smul_smul, h2, one_smul]

omit ha ha1 in
/-- mQSP Eq. (4.71): for `|x| = 1` and `0 < a < 1`, `|a x| = a < 1`, so `1 - a x ≠ 0`. -/
theorem ap1_one_sub_ne_zero (ha : 0 < a) (ha1 : a < 1) {x : ℂ} (hx : ‖x‖ = 1) :
    1 - (a : ℂ) * x ≠ 0 := by
  intro h
  have h1 : ‖(a : ℂ) * x‖ = a := by
    rw [norm_mul, hx, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have h2 : (a : ℂ) * x = 1 := (sub_eq_zero.1 h).symm
  rw [h2, norm_one] at h1
  linarith

/-- The loop is regular whenever `a x ≠ 1` (always, for `|x| = 1` and `a < 1`). -/
theorem ap1_isRegular {x : ℂ} (hx : ‖x‖ = 1) :
    (ap1 a ha ha1).IsRegular (oneOracle (phaseOracle x)) := by
  rw [isRegular_iff_injective, ap1_D, ap1_Q, injective_iff_map_eq_zero]
  intro v hv
  simp only [phaseOracle, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
    smul_apply, smul_eq_mul] at hv
  have h : (1 - (a : ℂ) * x) * v = 0 := by linear_combination hv
  exact (mul_eq_zero.1 h).resolve_left (ap1_one_sub_ne_zero ha ha1 hx)

/-- The catalyst of the all-pass loop is the scalar `(1 - a x)⁻¹ √(1 - a²)`. -/
theorem ap1_catalyst {x : ℂ} (hx : ‖x‖ = 1) :
    (ap1 a ha ha1).catalyst (oneOracle (phaseOracle x)) =
      ((1 - (a : ℂ) * x)⁻¹ * (Real.sqrt (1 - a ^ 2) : ℂ)) • 1 := by
  have hne := ap1_one_sub_ne_zero ha ha1 hx
  refine ((ap1 a ha ha1).catalyst_unique (ap1_isRegular ha ha1 hx) ?_).symm
  rw [ap1_C, ap1_D, ap1_Q]
  ext
  simp [phaseOracle]
  field_simp
  ring

/-- LIB-1 (mQSP Eq. (4.66) at `z = 1`). The steady value is the Blaschke factor
`(x - a)/(1 - a x)`. -/
theorem ap1_steady {x : ℂ} (hx : ‖x‖ = 1) :
    (ap1 a ha ha1).steady (oneOracle (phaseOracle x)) = ((x - a) / (1 - a * x)) • 1 := by
  have hne := ap1_one_sub_ne_zero ha ha1 hx
  have hs := ap1_sqrt_mul_self ha ha1
  rw [steady, ap1_catalyst ha ha1 hx, ap1_A, ap1_B, ap1_Q]
  ext
  simp [phaseOracle]
  field_simp
  linear_combination x * hs

/-- LIB-1 (mQSP Eq. (4.69)). The catalyst weight is `(1 - a²)/|1 - a x|²`. -/
theorem ap1_weight {x : ℂ} (hx : ‖x‖ = 1) (ψ : ℂ) :
    (ap1 a ha ha1).weight (oneOracle (phaseOracle x)) () ψ =
      (1 - a ^ 2) / ‖1 - a * x‖ ^ 2 * ‖ψ‖ ^ 2 := by
  rw [weight, ap1_π, one_apply_eq_self, ap1_catalyst ha ha1 hx, smul_apply, one_apply_eq_self,
    norm_smul, mul_pow, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, Real.sq_sqrt (by nlinarith), inv_pow]
  ring

omit ha ha1 in
/-- mQSP Eq. (4.70): `|1 - a x|² = (1 - a)² + a |1 - x|²` for `|x| = 1`. -/
theorem ap1_norm_one_sub_sq {x : ℂ} (hx : ‖x‖ = 1) :
    ‖1 - (a : ℂ) * x‖ ^ 2 = (1 - a) ^ 2 + a * ‖1 - x‖ ^ 2 := by
  have h := congrArg (· ^ 2) hx
  simp only [Complex.sq_norm, Complex.normSq_apply, one_pow] at h ⊢
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero,
    zero_sub]
  linear_combination (a ^ 2 - a) * h

/-- LIB-1 (mQSP Eq. (4.70)). Under the gap promise `|1 - x| ≥ Δ`, the weight is at most
`2(1 - a)/(a Δ²)` (per unit input). -/
theorem ap1_weight_le {x : ℂ} (hx : ‖x‖ = 1) {Δ : ℝ} (hΔ : 0 < Δ) (hgap : Δ ≤ ‖1 - x‖)
    (ψ : ℂ) :
    (ap1 a ha ha1).weight (oneOracle (phaseOracle x)) () ψ ≤
      2 * (1 - a) / (a * Δ ^ 2) * ‖ψ‖ ^ 2 := by
  rw [ap1_weight ha ha1 hx]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hn := ap1_norm_one_sub_sq (a := a) hx
  have hΔ2 : a * Δ ^ 2 ≤ ‖1 - (a : ℂ) * x‖ ^ 2 := by
    have : Δ ^ 2 ≤ ‖1 - x‖ ^ 2 := pow_le_pow_left₀ hΔ.le hgap 2
    rw [hn]; nlinarith
  have hpos : 0 < a * Δ ^ 2 := by positivity
  calc (1 - a ^ 2) / ‖1 - (a : ℂ) * x‖ ^ 2 ≤ (1 - a ^ 2) / (a * Δ ^ 2) :=
        div_le_div_of_nonneg_left (by nlinarith) hpos hΔ2
    _ ≤ 2 * (1 - a) / (a * Δ ^ 2) := by
      apply div_le_div_of_nonneg_right _ hpos.le
      nlinarith

end Junction

end MQSP
