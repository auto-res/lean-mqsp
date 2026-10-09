/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Impulse
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The generating function and coefficient tail bounds (CLK-4; mQSP §3, S7)

The delayed transfer function is the generating function `G(z) = ∑ₙ zⁿ G n` of the impulse
response. Since every coefficient is a contraction (`‖G n‖ ≤ 1`, from the Toeplitz lift) the
series converges on the open unit disk. When `G` extends analytically to a larger disk
`|z| < R` with `‖G(z)‖ ≤ M` there, the Cauchy estimates give the geometric tail bound
`‖G n‖ ≤ M R^{-n}` and hence, for the uniform clock on `[0, N)`,
`‖∑_{n ≥ N} G n‖ ≤ M R^{-N} / (1 - R^{-1})` (mQSP Eq. (3.118)-type bounds; the global-radius
route S7 of the survey, which needs no contour deformation). Modules whose transfer function
has poles away from the closed unit disk (FPAA, gapped all-pass sections) fall in this case.
-/

namespace MQSP

universe u v w x

open Finset

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (O : OracleTuple K)

/-- CLK-4. The generating function `G(z) = ∑ₙ zⁿ • G n` (defined by `tsum`). -/
noncomputable def genFun (z : ℂ) : P →L[ℂ] P := ∑' n : ℕ, z ^ n • M.G O n

/-- The partial sums `∑_{n<N} zⁿ • G n`. -/
noncomputable def genFunPartial (N : ℕ) (z : ℂ) : P →L[ℂ] P :=
  ∑ n ∈ Finset.range N, z ^ n • M.G O n

/-- With contractive coefficients the series converges absolutely on the open unit disk. -/
theorem summable_genFun (hG : ∀ n, ‖M.G O n‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ n • M.G O n) := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun n => ?_
  rw [norm_smul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg z) n) (hG n)


/-- CLK-4 (Cauchy estimate, global-radius form S7). If the coefficients satisfy
`‖∑_{n<N} zⁿ G n‖ ≤ M'` uniformly for `|z| = r` (for all `N`), then `‖G n‖ ≤ M' / rⁿ`. -/
theorem norm_G_le_of_partial_bound {r M' : ℝ} (hr : 0 < r)
    (hb : ∀ N, ∀ z : ℂ, ‖z‖ = r → ‖M.genFunPartial O N z‖ ≤ M') (n : ℕ) :
    ‖M.G O n‖ ≤ M' / r ^ n := by
  have hfun : M.genFunPartial O (n + 1) = fun z => ∑ k ∈ range (n + 1), z ^ k • M.G O k := rfl
  have hdiff : Differentiable ℂ (M.genFunPartial O (n + 1)) := by
    rw [hfun]
    fun_prop
  have hderiv : iteratedDeriv n (M.genFunPartial O (n + 1)) 0 = (n.factorial : ℂ) • M.G O n := by
    rw [hfun]
    simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_smul_const,
      iteratedDeriv_fun_pow_zero]
    simp
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) n hr
    hdiff.diffContOnCl (fun z hz => hb (n + 1) z (by simpa using hz))
  rw [hderiv, norm_smul, Complex.norm_natCast, mul_div_assoc] at h
  exact le_of_mul_le_mul_left h (by positivity)

/-- CLK-4. Geometric coefficient decay gives a geometric tail bound for the uniform clock:
if `‖G n‖ ≤ M' ρⁿ` with `ρ < 1` then `‖∑_{N ≤ n < N'} G n‖ ≤ M' ρ^N / (1 - ρ)` for all `N'`. -/
theorem norm_tail_le_of_geometric {M' ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M')
    (hG : ∀ n, ‖M.G O n‖ ≤ M' * ρ ^ n) (N N' : ℕ) :
    ‖∑ n ∈ Finset.Ico N N', M.G O n‖ ≤ M' * ρ ^ N / (1 - ρ) := by
  calc ‖∑ n ∈ Finset.Ico N N', M.G O n‖ ≤ ∑ n ∈ Finset.Ico N N', M' * ρ ^ n :=
        (norm_sum_le _ _).trans (sum_le_sum fun n _ => hG n)
    _ = M' * ∑ n ∈ Finset.Ico N N', ρ ^ n := (mul_sum _ _ _).symm
    _ ≤ M' * (ρ ^ N / (1 - ρ)) := mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hρ0 hρ1) hM
    _ = M' * ρ ^ N / (1 - ρ) := (mul_div_assoc _ _ _).symm

end Junction

end MQSP
