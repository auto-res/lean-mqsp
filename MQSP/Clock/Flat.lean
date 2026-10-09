/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Compile.Clock
import MQSP.Clock.Transient

/-!
# Box clocks (CLK-3; mQSP §3.2, survey route S4)

The simplest flat clock: a uniform input window of length `Lw` and a uniform output window of
length `Lw + D`, both normalised, with one label. Its clock matrix is rank one,
`X o i = (1/√Lw) (1/√(Lw+D))` for `i < Lw`, `o < Lw + D`, and its weights are
`cₙ(X) = (Lw - |…|)/√(Lw (Lw + D))`: exactly `√(Lw/(Lw+D))` for `0 ≤ n ≤ D` (a flat
plateau), decreasing linearly to `0` at `n = Lw + D`. Rescaling by `α = √(1 + D/Lw)` gives
weights `1` on the plateau at normalization `α`, which suffices for normalization-two results
(mQSP Cor 3.10, Thm 1.1 at `δ = 1`) without the optimal flat clock of Lemma 3.5.
-/

namespace MQSP

namespace Clock

/-- The uniform window of length `Lw` inside `Fin N` (one label). -/
noncomputable def box (N Lw : ℕ) : Fin 1 → Fin N → ℂ :=
  fun _ i => if (i : ℕ) < Lw then ((Real.sqrt Lw)⁻¹ : ℂ) else 0

theorem isNormalized_box (N Lw : ℕ) (h0 : 0 < Lw) (hN : Lw ≤ N) : IsNormalized (box N Lw) := by
  unfold IsNormalized box
  simp only [Fin.sum_univ_one, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < Lw then ‖((Real.sqrt Lw)⁻¹ : ℂ)‖ ^ 2 else 0) N,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hfilt : (Finset.range N).filter (· < Lw) = Finset.range Lw := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt, Finset.card_range, ← Complex.ofReal_inv, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  exact mul_inv_cancel₀ (by exact_mod_cast h0.ne')

/-- The clock matrix of the box pair is the rank-one indicator of the two windows,
`X o i = (√Lw √(Lw+D))⁻¹ [i < Lw] [o < Lw + D]`. -/
theorem clockX_box (N Lw D : ℕ) (o i : Fin N) :
    clockX (box N Lw) (box N (Lw + D)) o i =
      if (i : ℕ) < Lw ∧ (o : ℕ) < Lw + D then
        (((Real.sqrt Lw * Real.sqrt (Lw + D))⁻¹ : ℝ) : ℂ) else 0 := by
  unfold clockX box
  rw [Fin.sum_univ_one]
  by_cases hi : (i : ℕ) < Lw <;> by_cases ho : (o : ℕ) < Lw + D <;>
    simp [hi, ho, mul_comm]

/-- The box weights count the `i < Lw` with `i + n < Lw + D`: `min Lw (Lw + D - n)` of them,
each contributing `(√Lw √(Lw+D))⁻¹`. -/
private theorem weights_box_eq_aux (N Lw D n : ℕ) (hN : Lw + D ≤ N) :
    weights (clockX (box N Lw) (box N (Lw + D))) n =
      (((min Lw (Lw + D - n) : ℕ) : ℝ) / (Real.sqrt Lw * Real.sqrt (Lw + D)) : ℝ) := by
  set c : ℂ := (((Real.sqrt Lw * Real.sqrt (Lw + D))⁻¹ : ℝ) : ℂ) with hc
  unfold weights
  simp only [clockX_box]
  rw [Fin.sum_univ_eq_sum_range (fun o => ∑ i : Fin N,
      if (i : ℕ) + n = o then (if (i : ℕ) < Lw ∧ o < Lw + D then c else 0) else 0) N]
  have key : ∀ o : ℕ, (∑ i : Fin N,
      if (i : ℕ) + n = o then (if (i : ℕ) < Lw ∧ o < Lw + D then c else 0) else 0) =
      ∑ i ∈ Finset.range N, if i + n = o then (if i < Lw ∧ o < Lw + D then c else 0) else 0 :=
    fun o => Fin.sum_univ_eq_sum_range
      (fun i => if i + n = o then (if i < Lw ∧ o < Lw + D then c else 0) else 0) N
  simp only [key]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const,
    nsmul_eq_mul]
  have hfilt : (Finset.range N).filter (fun a => a + n < N ∧ a < Lw ∧ a + n < Lw + D) =
      Finset.range (min Lw (Lw + D - n)) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt, Finset.card_range, hc, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_inv, div_eq_mul_inv]

/-- The clock weights of the box pair `(box Lw, box (Lw + D))`: `√(Lw/(Lw+D))` on the plateau
`0 ≤ n ≤ D`. -/
theorem weights_box_plateau (N Lw D n : ℕ) (h0 : 0 < Lw) (hN : Lw + D ≤ N) (hn : n ≤ D) :
    weights (clockX (box N Lw) (box N (Lw + D))) n =
      ((Real.sqrt Lw / Real.sqrt (Lw + D) : ℝ) : ℂ) := by
  have _ := h0
  rw [weights_box_eq_aux N Lw D n hN, show min Lw (Lw + D - n) = Lw by omega,
    div_mul_eq_div_div, Real.div_sqrt]

/-- The box weights are real, in `[0, 1]` and vanish beyond `Lw + D`. -/
theorem weights_box_eq (N Lw D n : ℕ) (h0 : 0 < Lw) (hN : Lw + D ≤ N) :
    weights (clockX (box N Lw) (box N (Lw + D))) n =
      (((min Lw (Lw + D - n) : ℕ) : ℝ) / (Real.sqrt Lw * Real.sqrt (Lw + D)) : ℝ) := by
  have _ := h0
  exact weights_box_eq_aux N Lw D n hN

/-- Adjacent box weights differ by at most `1/√(Lw (Lw+D))` and agree on the plateau. -/
theorem weights_box_sub_le (N Lw D n : ℕ) (h0 : 0 < Lw) (hN : Lw + D ≤ N) :
    ‖weights (clockX (box N Lw) (box N (Lw + D))) n -
      weights (clockX (box N Lw) (box N (Lw + D))) (n + 1)‖ ≤
      (if n < D then 0 else (Real.sqrt Lw * Real.sqrt (Lw + D))⁻¹) := by
  have hden : 0 < Real.sqrt Lw * Real.sqrt (Lw + D) :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast h0))
      (Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (by exact_mod_cast h0) (Nat.cast_nonneg _)))
  rw [weights_box_eq N Lw D n h0 hN, weights_box_eq N Lw D (n + 1) h0 hN,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← sub_div, abs_div,
    abs_of_pos hden]
  split_ifs with hnD
  · rw [show min Lw (Lw + D - n) = min Lw (Lw + D - (n + 1)) by omega, sub_self, abs_zero,
      zero_div]
  · have h1 : ((min Lw (Lw + D - (n + 1)) : ℕ) : ℝ) ≤ ((min Lw (Lw + D - n) : ℕ) : ℝ) :=
      Nat.cast_le.2 (by omega)
    have h2 : ((min Lw (Lw + D - n) : ℕ) : ℝ) ≤ ((min Lw (Lw + D - (n + 1)) : ℕ) : ℝ) + 1 := by
      have h : min Lw (Lw + D - n) ≤ min Lw (Lw + D - (n + 1)) + 1 := by omega
      exact_mod_cast h
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 hden.le) (abs_le.2 ⟨by linarith, by linarith⟩)

end Clock

end MQSP
