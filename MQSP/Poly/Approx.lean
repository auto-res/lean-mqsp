/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Poly.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Existence of bounded parity approximants (POLY-2)

Qualitative existence results for the polynomials used by QSVT and coherent estimation,
from the Weierstrass approximation theorem (Mathlib, `exists_polynomial_near_continuousMap`)
plus parity symmetrisation `P(x) ↦ (P(x) ± P(-x))/2` and rescaling (`Poly.approxOn_rescale`):

* every continuous even (odd) `f` on `[-1, 1]` with `|f| ≤ 1` has, for every `ε > 0`, an even
  (odd) polynomial `P` with `|P| ≤ 1` on `[-1, 1]` and `|P - f| ≤ ε` on `[-1, 1]`;
* the sign function on `κ ≤ |x| ≤ 1` (via the continuous odd ramp `signRamp κ`): an odd `P`
  bounded by `1` with `|P - sgn| ≤ ε` for `κ ≤ |x| ≤ 1` (GSLW Lemma 25 without the degree
  bound; the quantitative `O(κ⁻¹ log ε⁻¹)` degree is a separate theorem);
* the amplifying polynomial `A_{η→δ}` on `[0, 1]` (Rall Lemma 11 / CPE): `0 ≤ A ≤ 1` on
  `[0, 1]`, `A ≥ 1 - δ` on `[0, 1/2 - η]`, `A ≤ δ` on `[1/2 + η, 1]`.

Degree bounds are deliberately not part of these statements; they live with the
quantitative approximation theory.
-/

namespace MQSP

namespace Poly

open Polynomial

/-- The even symmetrisation `(P(x) + P(-x))/2`. -/
noncomputable def evenize (P : ℝ[X]) : ℝ[X] := C (1 / 2) * (P + P.comp (-X))

/-- The odd symmetrisation `(P(x) - P(-x))/2`. -/
noncomputable def oddize (P : ℝ[X]) : ℝ[X] := C (1 / 2) * (P - P.comp (-X))

theorem evenize_eval (P : ℝ[X]) (x : ℝ) : (evenize P).eval x = (P.eval x + P.eval (-x)) / 2 := by
  rw [evenize, eval_mul, eval_C, eval_add, eval_comp, eval_neg, eval_X]
  ring

theorem oddize_eval (P : ℝ[X]) (x : ℝ) : (oddize P).eval x = (P.eval x - P.eval (-x)) / 2 := by
  rw [oddize, eval_mul, eval_C, eval_sub, eval_comp, eval_neg, eval_X]
  ring

/-- The coefficients of `P(-x)`: `coeff (P.comp (-X)) k = (-1)^k coeff P k`. -/
private lemma coeff_comp_neg_X (P : ℝ[X]) (k : ℕ) :
    (P.comp (-X)).coeff k = (-1) ^ k * P.coeff k := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial n a =>
    have h1 : (-1 : ℝ[X]) ^ n = C ((-1) ^ n) := by rw [C_pow, C_neg, C_1]
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, ← mul_assoc, h1,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · rw [h, mul_comm]
    · rw [mul_zero]

private lemma isEven_C_mul (c : ℝ) {P : ℝ[X]} (hP : IsEven P) : IsEven (C c * P) :=
  fun k hk => by rw [coeff_C_mul, hP k hk, mul_zero]

private lemma isOdd_C_mul (c : ℝ) {P : ℝ[X]} (hP : IsOdd P) : IsOdd (C c * P) :=
  fun k hk => by rw [coeff_C_mul, hP k hk, mul_zero]

theorem isEven_evenize (P : ℝ[X]) : IsEven (evenize P) := by
  intro k hk
  rw [evenize, coeff_C_mul, coeff_add, coeff_comp_neg_X, (Nat.odd_iff.mpr hk).neg_one_pow]
  ring

theorem isOdd_oddize (P : ℝ[X]) : IsOdd (oddize P) := by
  intro k hk
  rw [oddize, coeff_C_mul, coeff_sub, coeff_comp_neg_X, (Nat.even_iff.mpr hk).neg_one_pow]
  ring

/-- POLY-2 (Weierstrass). Every continuous `f` on `[-1, 1]` is uniformly approximable. -/
theorem exists_approx (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℝ[X], ApproxOn P f (Set.Icc (-1) 1) ε := by
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-1) 1 f hf ε hε
  exact ⟨P, fun x hx => (hP x hx).le⟩

private lemma neg_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : -x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- POLY-2. Even bounded approximants of even continuous targets bounded by `1`. -/
theorem exists_even_approx (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1))
    (hsym : ∀ x, f (-x) = f x) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℝ[X], IsEven P ∧ BoundedOn P (Set.Icc (-1) 1) 1 ∧ ApproxOn P f (Set.Icc (-1) 1) ε := by
  obtain ⟨P₀, hP₀⟩ := exists_approx f hf (half_pos hε)
  have h₁ : ApproxOn (evenize P₀) f (Set.Icc (-1) 1) (ε / 2) := by
    intro x hx
    have e : (evenize P₀).eval x - f x =
        ((P₀.eval x - f x) + (P₀.eval (-x) - f (-x))) / 2 := by
      rw [evenize_eval, hsym]
      ring
    have ha := hP₀ x hx
    have hb := hP₀ (-x) (neg_mem_Icc hx)
    rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    calc |(P₀.eval x - f x) + (P₀.eval (-x) - f (-x))|
        ≤ |P₀.eval x - f x| + |P₀.eval (-x) - f (-x)| := abs_add_le _ _
      _ ≤ ε / 2 * 2 := by linarith
  obtain ⟨hA, hB⟩ := approxOn_rescale _ f _ (ε / 2) (half_pos hε).le h₁ hb
  refine ⟨_, isEven_C_mul _ (isEven_evenize P₀), hB, ?_⟩
  rwa [mul_div_cancel₀ ε two_ne_zero] at hA

/-- POLY-2. Odd bounded approximants of odd continuous targets bounded by `1`. -/
theorem exists_odd_approx (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-1) 1))
    (hsym : ∀ x, f (-x) = -f x) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℝ[X], IsOdd P ∧ BoundedOn P (Set.Icc (-1) 1) 1 ∧ ApproxOn P f (Set.Icc (-1) 1) ε := by
  obtain ⟨P₀, hP₀⟩ := exists_approx f hf (half_pos hε)
  have h₁ : ApproxOn (oddize P₀) f (Set.Icc (-1) 1) (ε / 2) := by
    intro x hx
    have e : (oddize P₀).eval x - f x =
        ((P₀.eval x - f x) - (P₀.eval (-x) - f (-x))) / 2 := by
      rw [oddize_eval, hsym]
      ring
    have ha := hP₀ x hx
    have hb := hP₀ (-x) (neg_mem_Icc hx)
    rw [e, abs_div, abs_two, div_le_iff₀ two_pos]
    calc |(P₀.eval x - f x) - (P₀.eval (-x) - f (-x))|
        ≤ |P₀.eval x - f x| + |P₀.eval (-x) - f (-x)| := abs_sub _ _
      _ ≤ ε / 2 * 2 := by linarith
  obtain ⟨hA, hB⟩ := approxOn_rescale _ f _ (ε / 2) (half_pos hε).le h₁ hb
  refine ⟨_, isOdd_C_mul _ (isOdd_oddize P₀), hB, ?_⟩
  rwa [mul_div_cancel₀ ε two_ne_zero] at hA

/-- The continuous odd ramp: `sgn x` for `|x| ≥ κ`, linear on `[-κ, κ]`. -/
noncomputable def signRamp (κ : ℝ) (x : ℝ) : ℝ := max (-1) (min 1 (x / κ))

theorem signRamp_eq_sign {κ : ℝ} (hκ : 0 < κ) {x : ℝ} (hx : κ ≤ |x|) :
    signRamp κ x = SignType.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h] at hx
    have h1 : x / κ ≤ -1 := by rw [div_le_iff₀ hκ]; linarith
    rw [signRamp, min_eq_right (by linarith), max_eq_left h1, sign_neg h, SignType.coe_neg_one]
  · rw [h, abs_zero] at hx
    exact absurd hx (not_le.mpr hκ)
  · rw [abs_of_pos h] at hx
    have h1 : 1 ≤ x / κ := by rw [le_div_iff₀ hκ]; linarith
    rw [signRamp, min_eq_left h1, max_eq_right (by norm_num), sign_pos h, SignType.coe_one]

private lemma signRamp_neg (κ x : ℝ) : signRamp κ (-x) = -signRamp κ x := by
  simp only [signRamp, max_def, min_def, neg_div]
  split_ifs <;> linarith

private lemma abs_signRamp_le (κ x : ℝ) : |signRamp κ x| ≤ 1 :=
  abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- POLY-2 (sign approximation, existence form of GSLW Lemma 25). -/
theorem exists_sign_approx {κ ε : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hε : 0 < ε) :
    ∃ P : ℝ[X], IsOdd P ∧ BoundedOn P (Set.Icc (-1) 1) 1 ∧
      ∀ x : ℝ, κ ≤ |x| → |x| ≤ 1 → |P.eval x - SignType.sign x| ≤ ε := by
  have hc : Continuous (signRamp κ) :=
    continuous_const.max (continuous_const.min (continuous_id.div_const κ))
  obtain ⟨P, hodd, hbd, happ⟩ := exists_odd_approx (signRamp κ) hc.continuousOn
    (signRamp_neg κ) (fun x _ => abs_signRamp_le κ x) hε
  refine ⟨P, hodd, hbd, fun x hx hx1 => ?_⟩
  have _ := hκ1
  rw [← signRamp_eq_sign hκ hx]
  exact happ x (abs_le.mp hx1)

/-- POLY-2 (amplifying polynomial, Rall Lemma 11). For `0 < η < 1/2` and `0 < δ`, a polynomial
`A` with `0 ≤ A ≤ 1` on `[0, 1]`, `A ≥ 1 - δ` on `[0, 1/2 - η]` and `A ≤ δ` on `[1/2 + η, 1]`. -/
theorem exists_amplifier {η δ : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (hδ : 0 < δ) :
    ∃ A : ℝ[X], (∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ A.eval y ∧ A.eval y ≤ 1) ∧
      (∀ y ∈ Set.Icc (0 : ℝ) (1 / 2 - η), 1 - δ ≤ A.eval y) ∧
      (∀ y ∈ Set.Icc (1 / 2 + η) (1 : ℝ), A.eval y ≤ δ) := by
  obtain ⟨P, -, hbd, happ⟩ :=
    exists_sign_approx (κ := 2 * η) (ε := 2 * δ) (by linarith) (by linarith) (by linarith)
  have hev : ∀ y : ℝ, (C (1 / 2) * (1 - P.comp (C 2 * X - C 1))).eval y =
      (1 - P.eval (2 * y - 1)) / 2 := fun y => by
    rw [eval_mul, eval_C, eval_sub, eval_one, eval_comp, eval_sub, eval_mul, eval_C, eval_C,
      eval_X]
    ring
  refine ⟨C (1 / 2) * (1 - P.comp (C 2 * X - C 1)), fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_⟩
  · have h := abs_le.mp (hbd (2 * y - 1) ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    rw [hev]
    constructor <;> linarith [h.1, h.2]
  · have hx : 2 * y - 1 < 0 := by linarith [hy.2]
    have h := happ (2 * y - 1) (by rw [abs_of_neg hx]; linarith [hy.2])
      (by rw [abs_of_neg hx]; linarith [hy.1])
    rw [sign_neg hx, SignType.coe_neg_one] at h
    rw [hev]
    linarith [(abs_le.mp h).2]
  · have hx : 0 < 2 * y - 1 := by linarith [hy.1]
    have h := happ (2 * y - 1) (by rw [abs_of_pos hx]; linarith [hy.1])
      (by rw [abs_of_pos hx]; linarith [hy.2])
    rw [sign_pos hx, SignType.coe_one] at h
    rw [hev]
    linarith [(abs_le.mp h).1]

end Poly

end MQSP
