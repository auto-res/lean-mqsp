/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.CPE.Signal

/-!
# Reading the answer qubit (CPE-2; Rall Lemma 10 / Thm 12 step)

The QSVT of the phase signal with an even phase list sends the lifted eigenvector `plus ψ`
(`ψ` an eigenvector of `U` with eigenphase `θ`) to `s • plus ψ + t • minus ψ`, where
`s = p_Φ(cos²(θ/2))` is the realised scalar and `|s|² + |t|² = 1`: the output register is
deterministic on each eigenspace (the *complementary amplitude* lies on `minus ψ`, so the data
`ψ` is untouched and only the flag qubit rotates). Reading the flag qubit in the `|±⟩` basis
therefore yields the bit: if `s ≥ 1 - δ` the state is within `√(2δ)` of `plus ψ`; if `s ≤ δ`
it is within `√2 δ` of a phase times `minus ψ`. These are the per-eigenspace readout lemmas
used by coherent phase estimation (Rall Thm 12 reads the QSVT ancilla as the answer qubit).
-/

namespace MQSP

universe u

open scoped InnerProductSpace
open Polynomial

namespace CPE

variable {H : Type u} [HSpace H]

/-- The `|-⟩`-flag isometry `ψ ↦ (ψ ⊕ -ψ)/√2`. -/
noncomputable def minus : H →L[ℂ] H ⊕ₕ H :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (DSum.inl - DSum.inr)

/-- The adjoint of the `|-⟩`-flag isometry: `⟨-| = (fst - snd)/√2`. -/
theorem adjoint_minus :
    (minus : H →L[ℂ] H ⊕ₕ H)† = ((Real.sqrt 2)⁻¹ : ℂ) • (DSum.fst - DSum.snd) := by
  rw [minus, map_smulₛₗ, map_sub, DSum.adjoint_inl, DSum.adjoint_inr, map_inv₀,
    Complex.conj_ofReal]

theorem isIsometry_minus : IsIsometry (minus : H →L[ℂ] H ⊕ₕ H) := by
  rw [IsIsometry, adjoint_minus, minus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, DSum.sqrt_two_inv_mul_self,
    ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub,
    DSum.fst_comp_inl, DSum.fst_comp_inr, DSum.snd_comp_inl, DSum.snd_comp_inr, sub_zero,
    zero_sub, sub_neg_eq_add, ← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem plus_adj_minus : (DSum.plus : H →L[ℂ] H ⊕ₕ H)† ∘L minus = 0 := by
  rw [DSum.adjoint_plus, minus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub, DSum.fst_comp_inl,
    DSum.fst_comp_inr, DSum.snd_comp_inl, DSum.snd_comp_inr, sub_zero, zero_sub,
    add_neg_cancel, smul_zero]

/-- `plus plus† + minus minus† = 1` on `H ⊕ₕ H`. -/
theorem plus_add_minus :
    DSum.plus ∘L (DSum.plus : H →L[ℂ] H ⊕ₕ H)† + minus ∘L (minus : H →L[ℂ] H ⊕ₕ H)† = 1 := by
  have h : ((DSum.inl : H →L[ℂ] H ⊕ₕ H) + DSum.inr) ∘L (DSum.fst + DSum.snd) +
      (DSum.inl - DSum.inr) ∘L (DSum.fst - DSum.snd) =
      (DSum.inl ∘L DSum.fst + DSum.inr ∘L DSum.snd) +
        (DSum.inl ∘L DSum.fst + DSum.inr ∘L DSum.snd) := by
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub]
    abel
  rw [DSum.adjoint_plus, adjoint_minus, DSum.plus, minus, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    smul_smul, smul_smul, DSum.sqrt_two_inv_mul_self, ← smul_add, h, DSum.inl_fst_add_inr_snd,
    ← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- `(1 - plusProj) = minus minus†`. -/
theorem one_sub_plusProj : (1 : H ⊕ₕ H →L[ℂ] H ⊕ₕ H) - plusProj = minus ∘L minus† := by
  rw [plusProj, ← plus_add_minus, add_sub_cancel_left]

/-- `⟨-| (F₁ ⊕ F₂) |+⟩ = (F₁ - F₂)/2`. -/
theorem minus_adj_block_plus (F₁ F₂ : H →L[ℂ] H) :
    (minus : H →L[ℂ] H ⊕ₕ H)† ∘L DSum.block F₁ 0 0 F₂ ∘L DSum.plus = ((2 : ℂ)⁻¹) • (F₁ - F₂) := by
  rw [adjoint_minus, DSum.plus, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, DSum.sqrt_two_inv_mul_self]
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.sub_comp, DSum.fst_block_inl,
    DSum.fst_block_inr, DSum.snd_block_inl, DSum.snd_block_inr, sub_zero, zero_sub,
    ← sub_eq_add_neg]

/-- `|+⟩ ⊗ ψ` and `|-⟩ ⊗ φ` are orthogonal. -/
theorem inner_plus_minus (ψ φ : H) : ⟪DSum.plus ψ, minus φ⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    plus_adj_minus, zero_apply, inner_zero_right]

/-- Pythagoras on `span {plus ψ, minus ψ}` for a unit vector `ψ`. -/
theorem norm_sq_smul_plus_add_smul_minus {ψ : H} (hψ1 : ‖ψ‖ = 1) (a b : ℂ) :
    ‖a • DSum.plus ψ + b • minus ψ‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [@norm_add_sq ℂ, inner_smul_left, inner_smul_right, inner_plus_minus, mul_zero, mul_zero,
    map_zero, mul_zero, add_zero, norm_smul, norm_smul, DSum.isIsometry_plus.norm_map,
    isIsometry_minus.norm_map, hψ1, mul_one, mul_one]

/-- CPE-2 (structure of the output on an eigenspace). For an even phase list, the QSVT of the
phase signal maps `plus ψ` into `span {plus ψ, minus ψ}`. -/
theorem UΦ_plus_eigen_decomp {U : H →L[ℂ] H} (hU : IsUnitary U) (Φ : List ℝ)
    (hΦ : Φ.length % 2 = 0) {ψ : H} {θ : ℝ} (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) :
    ∃ t : ℂ, QSVT.UΦ (phaseSignal U) plusProj plusProj Φ (DSum.plus ψ) =
      ((QSVT.pqΦ Φ).1.eval ((Real.cos (θ / 2) ^ 2 : ℝ) : ℂ)) • DSum.plus ψ + t • minus ψ := by
  have hW := isUnitary_phaseSignal hU
  have hs := QSVT.shape_altFrom hW isProj_plusProj isProj_plusProj Φ
    (QSVT.shape_one (U := phaseSignal U) (Pr' := plusProj) isProj_plusProj)
  unfold QSVT.Shape at hs
  rw [zero_add, ite_eq_left hΦ] at hs
  have hp : plusProj (DSum.plus ψ) = DSum.plus ψ := by
    rw [plusProj, ContinuousLinearMap.comp_apply, plus_adj_plus_apply]
  have hv := DFunLike.congr_fun hs (DSum.plus ψ)
  rw [one_sub_plusProj] at hv
  simp only [ContinuousLinearMap.comp_apply, add_apply, hp, map_smul,
    aeval_apply_eigen (enc_adj_enc_apply_eigen hU hψ)] at hv
  have hA : plusProj ((phaseSignal U) (DSum.plus ψ)) =
      (Complex.exp ((θ / 2) * Complex.I) * (Real.cos (θ / 2) : ℂ)) • DSum.plus ψ := by
    calc plusProj ((phaseSignal U) (DSum.plus ψ))
        = QSVT.enc (phaseSignal U) plusProj plusProj (DSum.plus ψ) := by
          simp only [QSVT.enc, ContinuousLinearMap.comp_apply, hp]
      _ = _ := by
          rw [enc_phaseSignal, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
            plus_adj_plus_apply, half_one_add_apply_eigen U hψ, map_smul]
  have hm : minus ((minus : H →L[ℂ] H ⊕ₕ H)† ((phaseSignal U)† (DSum.plus ψ))) =
      ((2 : ℂ)⁻¹ * (1 - Complex.exp (((-θ : ℝ) : ℂ) * Complex.I))) • minus ψ := by
    rw [phaseSignal, DSum.adjoint_block, adjoint_one, map_zero,
      ← ContinuousLinearMap.comp_apply _ DSum.plus,
      ← ContinuousLinearMap.comp_apply ((minus : H →L[ℂ] H ⊕ₕ H)†), minus_adj_block_plus,
      smul_apply, sub_apply, one_apply_eq_self, adjoint_apply_eigen hU hψ, ← one_smul ℂ ψ,
      smul_smul, ← sub_smul, one_smul, map_smul, map_smul, smul_smul, mul_one]
  rw [hA, map_smul, map_smul, map_smul, hm, smul_smul, smul_smul] at hv
  exact ⟨_, hv⟩

/-- Unitarity gives `|s|² + |t|² = 1` for the two amplitudes on a unit eigenvector. -/
theorem norm_sq_add_norm_sq_eq_one {U : H →L[ℂ] H} (hU : IsUnitary U) (Φ : List ℝ)
    (hΦ : Φ.length % 2 = 0) {ψ : H} (hψ1 : ‖ψ‖ = 1) {s t : ℂ}
    (h : QSVT.UΦ (phaseSignal U) plusProj plusProj Φ (DSum.plus ψ) =
      s • DSum.plus ψ + t • minus ψ) : ‖s‖ ^ 2 + ‖t‖ ^ 2 = 1 := by
  have _ := hΦ
  have hn : ‖QSVT.UΦ (phaseSignal U) plusProj plusProj Φ (DSum.plus ψ)‖ = 1 := by
    rw [(QSVT.isUnitary_UΦ (isUnitary_phaseSignal hU) isProj_plusProj isProj_plusProj
      Φ).isIsometry.norm_map, DSum.isIsometry_plus.norm_map, hψ1]
  rw [← norm_sq_smul_plus_add_smul_minus hψ1, ← h, hn, one_pow]

/-- CPE-2 (readout, bit `0`). If the realised scalar is real and `≥ 1 - δ`, the output is
within `√(2δ)` of the input `plus ψ` (flag stays `|+⟩`). -/
theorem readout_zero {ψ : H} (hψ1 : ‖ψ‖ = 1) {s t : ℂ} (hst : ‖s‖ ^ 2 + ‖t‖ ^ 2 = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hs : (s.re : ℂ) = s) (hs1 : 1 - δ ≤ s.re) (hs2 : s.re ≤ 1) :
    ‖(s • DSum.plus ψ + t • minus ψ) - DSum.plus ψ‖ ≤ Real.sqrt (2 * δ) := by
  have _ := hδ
  have _ := hs2
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, s = a := ⟨s.re, hs.symm⟩
  rw [Complex.ofReal_re] at hs1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hst
  have hv : ((a : ℂ) • DSum.plus ψ + t • minus ψ) - DSum.plus ψ =
      ((a - 1 : ℝ) : ℂ) • DSum.plus ψ + t • minus ψ := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]; abel
  rw [hv]
  apply Real.le_sqrt_of_sq_le
  rw [norm_sq_smul_plus_add_smul_minus hψ1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith

/-- CPE-2 (readout, bit `1`). If the realised scalar is real with `0 ≤ s ≤ δ ≤ 1`, the output
is within `√2 δ` of a phase times `minus ψ` (flag flips to `|-⟩`, data `ψ` intact). -/
theorem readout_one {ψ : H} (hψ1 : ‖ψ‖ = 1) {s t : ℂ} (hst : ‖s‖ ^ 2 + ‖t‖ ^ 2 = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hs : (s.re : ℂ) = s) (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ δ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖(s • DSum.plus ψ + t • minus ψ) - c • minus ψ‖ ≤ Real.sqrt 2 * δ := by
  have _ := hδ1
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, s = a := ⟨s.re, hs.symm⟩
  rw [Complex.ofReal_re] at hs0 hs1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hst
  have hr0 : 0 ≤ ‖t‖ := norm_nonneg t
  have hr1 : ‖t‖ ≤ 1 := by nlinarith
  obtain ⟨c, hc1, hc⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ ‖t - c‖ = 1 - ‖t‖ := by
    by_cases ht : t = 0
    · refine ⟨1, norm_one, ?_⟩
      rw [ht, zero_sub, norm_neg, norm_one, norm_zero, sub_zero]
    · have hr : 0 < ‖t‖ := norm_pos_iff.mpr ht
      refine ⟨t / (‖t‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm, div_self hr.ne']
      · have h1 : t - t / (‖t‖ : ℂ) = ((1 - ‖t‖⁻¹ : ℝ) : ℂ) * t := by
          push_cast; ring
        have h2 : 1 ≤ ‖t‖⁻¹ := (one_le_inv₀ hr).mpr hr1
        rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        field_simp
        ring
  refine ⟨c, hc1, ?_⟩
  have hv : ((a : ℂ) • DSum.plus ψ + t • minus ψ) - c • minus ψ =
      (a : ℂ) • DSum.plus ψ + (t - c) • minus ψ := by
    rw [sub_smul]; abel
  rw [hv, ← Real.sqrt_sq hδ, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.le_sqrt_of_sq_le
  rw [norm_sq_smul_plus_add_smul_minus hψ1, Complex.norm_real, Real.norm_eq_abs, sq_abs, hc]
  nlinarith [mul_nonneg hr0 (sub_nonneg.2 hr1), mul_le_mul hs1 hs1 hs0 hδ]

end CPE

end MQSP
