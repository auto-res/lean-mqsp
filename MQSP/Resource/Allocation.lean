/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Weighted delay allocation (RES-3; mQSP Lemma 3.12, Eq. (1.18))

When the leading horizon is a weighted sum of the port delays, `N ≈ ∑ⱼ aⱼ rⱼ`, and the
weighted query cost is `⟨C, q⟩ ≤ N ∑ⱼ Cⱼ/rⱼ`, the delays `rⱼ ∝ √(Cⱼ/aⱼ)` minimise the product
and give the cost `(∑ⱼ √(aⱼ Cⱼ))² = ⟨C, a⟩_{1/2}` (mQSP Eq. (1.18)):

  `(∑ⱼ √(aⱼ Cⱼ))² ≤ (∑ⱼ aⱼ rⱼ) (∑ⱼ Cⱼ / rⱼ)`  for all `rⱼ > 0`, with equality at `rⱼ = √(Cⱼ/aⱼ)`.

This is the Cauchy–Schwarz inequality; the paper's Lemma 3.12 is the `p`-norm generalisation.
Expensive, weakly weighted oracles are queried less often.
-/

namespace MQSP

namespace Resource

open Finset

variable {ι : Type*} [Fintype ι]

/-- RES-3 (mQSP Eq. (1.18), lower bound). For positive weights `a`, costs `C` and delays `r`,
`(∑ √(a C))² ≤ (∑ a r) (∑ C / r)`. -/
theorem sq_sum_sqrt_le (a C r : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hC : ∀ j, 0 ≤ C j)
    (hr : ∀ j, 0 < r j) :
    (∑ j, Real.sqrt (a j * C j)) ^ 2 ≤ (∑ j, a j * r j) * (∑ j, C j / r j) := by
  refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => mul_nonneg (ha j) (hr j).le)
    (fun j _ => div_nonneg (hC j) (hr j).le) fun j _ => ?_
  rw [Real.sq_sqrt (mul_nonneg (ha j) (hC j))]
  have := (hr j).ne'
  exact le_of_eq (by field_simp)

/-- RES-3 (mQSP Eq. (1.18), optimal allocation). With `rⱼ = √(Cⱼ / aⱼ)` the bound is attained:
`(∑ a r) (∑ C / r) = (∑ √(a C))²`. -/
theorem optimal_allocation (a C : ι → ℝ) (ha : ∀ j, 0 < a j) (hC : ∀ j, 0 < C j) :
    (∑ j, a j * Real.sqrt (C j / a j)) * (∑ j, C j / Real.sqrt (C j / a j)) =
      (∑ j, Real.sqrt (a j * C j)) ^ 2 := by
  have h₁ : ∀ j, a j * Real.sqrt (C j / a j) = Real.sqrt (a j * C j) := fun j => by
    have hj : a j * C j = a j ^ 2 * (C j / a j) := by
      have := (ha j).ne'
      field_simp
    rw [hj, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ha j).le]
  have h₂ : ∀ j, C j / Real.sqrt (C j / a j) = Real.sqrt (a j * C j) := fun j => by
    rw [div_eq_iff (Real.sqrt_pos.2 (div_pos (hC j) (ha j))).ne',
      ← Real.sqrt_mul (mul_nonneg (ha j).le (hC j).le)]
    have hj : a j * C j * (C j / a j) = C j ^ 2 := by
      have := (ha j).ne'
      field_simp
    rw [hj, Real.sqrt_sq (hC j).le]
  simp_rw [h₁, h₂, sq]

/-- The optimal weighted cost is at most `‖a‖₁ ‖C‖₁` (the aggregate-oracle comparison of
mQSP Table 9): `(∑ √(a C))² ≤ (∑ a)(∑ C)`. -/
theorem sq_sum_sqrt_le_sum_mul_sum (a C : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hC : ∀ j, 0 ≤ C j) :
    (∑ j, Real.sqrt (a j * C j)) ^ 2 ≤ (∑ j, a j) * (∑ j, C j) :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => ha j) (fun j _ => hC j)
    fun j _ => (Real.sq_sqrt (mul_nonneg (ha j) (hC j))).le

end Resource

end MQSP
