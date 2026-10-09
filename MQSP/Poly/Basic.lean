/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomials with parity, bounded on `[-1, 1]` (POLY-1)

The signal-side approximation theory of QSVT (GSLW §5.2) and of coherent estimation is
language independent: it concerns real polynomials `P` of definite parity with `|P| ≤ 1` on
`[-1, 1]` approximating a target function on a subset of `[-1, 1]`. This file fixes the
vocabulary used by `MQSP.QSVT` and `MQSP.CPE`:

* `Parity.IsEven/IsOdd` for polynomials, and the decomposition `P(x) = x^{n mod 2} p(x²)`
  (`evenPart`/`oddPart` in `y = x²`) that feeds the SVD-free singular value transformation;
* `BoundedOn P S c`: `|P x| ≤ c` for `x ∈ S`; `ApproxOn P f S ε`: `|P x - f x| ≤ ε` on `S`;
* Chebyshev polynomials `T n` (`Polynomial.Chebyshev.T ℝ n`) as the basic bounded family.
-/

namespace MQSP

namespace Poly

open Polynomial

/-- A polynomial is even if all odd coefficients vanish. -/
def IsEven (P : ℝ[X]) : Prop := ∀ k, k % 2 = 1 → P.coeff k = 0

/-- A polynomial is odd if all even coefficients vanish. -/
def IsOdd (P : ℝ[X]) : Prop := ∀ k, k % 2 = 0 → P.coeff k = 0

/-- `P` is bounded by `c` on `S`. -/
def BoundedOn (P : ℝ[X]) (S : Set ℝ) (c : ℝ) : Prop := ∀ x ∈ S, |P.eval x| ≤ c

/-- `P` approximates `f` within `ε` on `S`. -/
def ApproxOn (P : ℝ[X]) (f : ℝ → ℝ) (S : Set ℝ) (ε : ℝ) : Prop := ∀ x ∈ S, |P.eval x - f x| ≤ ε

/-- The polynomial `p` in `y = x²` with `P(x) = p(x²)` for even `P`. -/
noncomputable def evenCore (P : ℝ[X]) : ℝ[X] := ∑ k ∈ Finset.range (P.natDegree + 1),
  if k % 2 = 0 then C (P.coeff k) * X ^ (k / 2) else 0

/-- The polynomial `p` in `y = x²` with `P(x) = x p(x²)` for odd `P`. -/
noncomputable def oddCore (P : ℝ[X]) : ℝ[X] := ∑ k ∈ Finset.range (P.natDegree + 1),
  if k % 2 = 1 then C (P.coeff k) * X ^ (k / 2) else 0

theorem IsEven.eval_eq (P : ℝ[X]) (h : IsEven P) (x : ℝ) :
    P.eval x = (evenCore P).eval (x ^ 2) := by
  rw [eval_eq_sum_range, evenCore, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · rw [eval_mul, eval_C, eval_pow, eval_X, ← pow_mul,
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk)]
  · rw [h k (by omega), eval_zero, zero_mul]

theorem IsOdd.eval_eq (P : ℝ[X]) (h : IsOdd P) (x : ℝ) :
    P.eval x = x * (oddCore P).eval (x ^ 2) := by
  rw [eval_eq_sum_range, oddCore, eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hk
  · have hx : x ^ k = x * (x ^ 2) ^ (k / 2) := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega
    rw [eval_mul, eval_C, eval_pow, eval_X, hx]
    ring
  · rw [h k (by omega), eval_zero, zero_mul, mul_zero]

theorem IsEven.neg_eval (P : ℝ[X]) (h : IsEven P) (x : ℝ) : P.eval (-x) = P.eval x := by
  rw [IsEven.eval_eq P h, IsEven.eval_eq P h, neg_sq]

theorem IsOdd.neg_eval (P : ℝ[X]) (h : IsOdd P) (x : ℝ) : P.eval (-x) = -P.eval x := by
  rw [IsOdd.eval_eq P h, IsOdd.eval_eq P h, neg_sq, neg_mul]

/-- The Chebyshev polynomial `T n` is bounded by `1` on `[-1, 1]`. -/
theorem chebyshev_boundedOn (n : ℕ) :
    BoundedOn (Chebyshev.T ℝ n) (Set.Icc (-1) 1) 1 := by
  intro x hx
  rw [← Real.cos_arccos hx.1 hx.2, Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

/-- Coefficient parity of `T n`: the `k`-th coefficient vanishes when `n + k` is odd. -/
private lemma chebyshev_coeff_eq_zero (n : ℕ) :
    ∀ k, (n + k) % 2 = 1 → (Chebyshev.T ℝ n).coeff k = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k hk
  match n, ih, hk with
  | 0, _, hk =>
    rw [Nat.cast_zero, Chebyshev.T_zero, coeff_one]
    exact ite_eq_right (by omega)
  | 1, _, hk =>
    rw [Nat.cast_one, Chebyshev.T_one, coeff_X]
    exact ite_eq_right (by omega)
  | m + 2, ih, hk =>
    have hT : Chebyshev.T ℝ ((m + 2 : ℕ) : ℤ) =
        X * (2 * Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ)) - Chebyshev.T ℝ (m : ℤ) := by
      push_cast
      rw [Chebyshev.T_add_two]
      ring
    rw [hT, coeff_sub, ih m (by omega) k (by omega), sub_zero]
    cases k with
    | zero => exact coeff_X_mul_zero _
    | succ k =>
      rw [coeff_X_mul, coeff_ofNat_mul, ih (m + 1) (by omega) k (by omega), mul_zero]

/-- `T n` has parity `n`. -/
theorem chebyshev_isEven (n : ℕ) (hn : n % 2 = 0) : IsEven (Chebyshev.T ℝ n) :=
  fun k hk => chebyshev_coeff_eq_zero n k (by omega)

theorem chebyshev_isOdd (n : ℕ) (hn : n % 2 = 1) : IsOdd (Chebyshev.T ℝ n) :=
  fun k hk => chebyshev_coeff_eq_zero n k (by omega)

/-- Composition of approximations: if `P ≈ f` within `ε` on `S` and `|P| ≤ 1`, then
`P ≈ f` after rescaling by `1/(1+ε)` is within `2ε` and bounded by `1/(1+ε) < 1`. -/
theorem approxOn_rescale (P : ℝ[X]) (f : ℝ → ℝ) (S : Set ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hP : ApproxOn P f S ε) (hf : ∀ x ∈ S, |f x| ≤ 1) :
    ApproxOn (C (1 / (1 + ε)) * P) f S (2 * ε) ∧
      BoundedOn (C (1 / (1 + ε)) * P) S 1 := by
  have hpos : 0 < 1 + ε := by linarith
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := hP x hx
    have h2 := hf x hx
    rw [eval_mul, eval_C]
    have e : 1 / (1 + ε) * P.eval x - f x = ((P.eval x - f x) - ε * f x) / (1 + ε) := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |P.eval x - f x - ε * f x| ≤ |P.eval x - f x| + |ε * f x| := abs_sub _ _
      _ = |P.eval x - f x| + ε * |f x| := by rw [abs_mul, abs_of_nonneg hε]
      _ ≤ ε + ε * 1 := by gcongr
      _ ≤ 2 * ε * (1 + ε) := by nlinarith
  · have h1 := hP x hx
    have h2 := hf x hx
    rw [eval_mul, eval_C, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (1 + ε)),
      div_mul_eq_mul_div, one_mul, div_le_one hpos]
    calc |P.eval x| = |(P.eval x - f x) + f x| := by rw [sub_add_cancel]
      _ ≤ |P.eval x - f x| + |f x| := abs_add_le _ _
      _ ≤ 1 + ε := by linarith

end Poly

end MQSP
