/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.HSpace
import MQSP.Poly.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Spectral mapping for a single Hermitian signal (CORE-7)

For one self-adjoint signal `A` (a Hermitian block encoding), scalar statements on the
spectrum lift to operator statements through the continuous functional calculus of the
C*-algebra `H →L[ℂ] H`:

* a real polynomial `P` with `|P| ≤ c` on `[-1, 1]` gives `‖P(A)‖ ≤ c` for a Hermitian
  contraction `A` (the spectral mapping principle mQSP §5 / GSLW §5 use silently);
* if `P` approximates a continuous target `f` within `ε` on `[-1, 1]` then
  `‖P(A) - f(A)‖ ≤ ε` where `f(A) = cfc f A`;
* on an eigenvector `A ψ = λ ψ`, `P(A) ψ = P(λ) ψ` (no continuity needed: the per-eigenspace
  error bookkeeping of coherent estimation).

Here `P(A)` is `Polynomial.aeval A (P.map (algebraMap ℝ ℂ))`, matching the polynomial
functional calculus used by the SVD-free QSVT theorem.
-/

namespace MQSP

universe u

open Polynomial
open scoped InnerProductSpace

namespace Spectral

variable {H : Type u} [HSpace H]

/-- The complexified polynomial functional calculus `P(A)` for a real polynomial. -/
noncomputable abbrev polyCalc (A : H →L[ℂ] H) (P : ℝ[X]) : H →L[ℂ] H :=
  aeval A (P.map (algebraMap ℝ ℂ))

/-- The spectrum of a self-adjoint contraction lies in `[-1, 1]`. -/
theorem spectrum_subset_Icc {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (h1 : ‖A‖ ≤ 1) :
    spectrum ℝ A ⊆ Set.Icc (-1) 1 := by
  have _ := hA
  intro x hx
  have hxC : algebraMap ℝ ℂ x ∈ spectrum ℂ A := (spectrum.algebraMap_mem_iff ℂ).2 hx
  have hn := spectrum.subset_closedBall_norm_mul (𝕜 := ℂ) A hxC
  rw [Metric.mem_closedBall, dist_zero_right, Complex.coe_algebraMap, Complex.norm_real,
    Real.norm_eq_abs] at hn
  have h1' : ‖A‖ * ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
    (mul_le_of_le_one_right (norm_nonneg A) ContinuousLinearMap.norm_id_le).trans h1
  exact abs_le.1 (hn.trans h1')

/-- The polynomial calculus agrees with the continuous functional calculus. -/
theorem cfc_eval_eq_polyCalc {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (P : ℝ[X]) :
    cfc (fun x : ℝ => P.eval x) A = polyCalc A P := by
  rw [cfc_polynomial P A hA, polyCalc, Polynomial.aeval_map_algebraMap]

/-- CORE-7. Spectral mapping bound: `|P| ≤ c` on `[-1, 1]` ⟹ `‖P(A)‖ ≤ c`. -/
theorem norm_polyCalc_le {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (h1 : ‖A‖ ≤ 1) {P : ℝ[X]}
    {c : ℝ} (hc : 0 ≤ c) (hP : Poly.BoundedOn P (Set.Icc (-1) 1) c) : ‖polyCalc A P‖ ≤ c := by
  rw [← cfc_eval_eq_polyCalc hA]
  refine norm_cfc_le hc fun x hx => ?_
  rw [Real.norm_eq_abs]
  exact hP x (spectrum_subset_Icc hA h1 hx)

/-- CORE-7. Approximation on the spectrum lifts to the operator norm:
`|P - f| ≤ ε` on `[-1, 1]` ⟹ `‖P(A) - f(A)‖ ≤ ε` for continuous `f`. -/
theorem norm_polyCalc_sub_cfc_le {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (h1 : ‖A‖ ≤ 1)
    {P : ℝ[X]} {f : ℝ → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 ≤ ε)
    (hP : Poly.ApproxOn P f (Set.Icc (-1) 1) ε) : ‖polyCalc A P - cfc f A‖ ≤ ε := by
  rw [← cfc_eval_eq_polyCalc hA, ← cfc_sub (fun x : ℝ => P.eval x) f A
    (P.continuous.continuousOn) hf.continuousOn]
  refine norm_cfc_le hε fun x hx => ?_
  rw [Real.norm_eq_abs]
  exact hP x (spectrum_subset_Icc hA h1 hx)

/-- Helper for `aeval_apply_eigenvector` (stated before its use below). -/
theorem aeval_apply_eigenvector_aux (A : H →L[ℂ] H) (p : ℂ[X]) {ψ : H} {l : ℂ}
    (hψ : A ψ = l • ψ) : aeval A p ψ = p.eval l • ψ := by
  induction p using Polynomial.induction_on with
  | C c => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, mul_apply_eq_comp, aeval_X, hψ, map_smul, ih,
      smul_smul]
    congr 1
    simp only [eval_mul, eval_X, eval_C, eval_pow]
    ring

/-- On an eigenvector, `P(A) ψ = P(λ) • ψ` (holds for every polynomial, no self-adjointness
needed). -/
theorem polyCalc_apply_eigenvector (A : H →L[ℂ] H) (P : ℝ[X]) {ψ : H} {l : ℝ}
    (hψ : A ψ = (l : ℂ) • ψ) : polyCalc A P ψ = ((P.eval l : ℝ) : ℂ) • ψ := by
  rw [polyCalc, aeval_apply_eigenvector_aux A _ hψ, Polynomial.eval_map_algebraMap,
    ← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval]

/-- The same for a complex polynomial `p` and a complex eigenvalue. -/
theorem aeval_apply_eigenvector (A : H →L[ℂ] H) (p : ℂ[X]) {ψ : H} {l : ℂ}
    (hψ : A ψ = l • ψ) : aeval A p ψ = p.eval l • ψ :=
  aeval_apply_eigenvector_aux A p hψ

/-- Self-adjoint operators have real eigenvalues: if `A ψ = l • ψ` with `ψ ≠ 0` then `l` is
real. -/
theorem eigenvalue_real {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) {ψ : H} (hψ0 : ψ ≠ 0) {l : ℂ}
    (hψ : A ψ = l • ψ) : (l.re : ℂ) = l := by
  have h1 : ⟪ψ, A ψ⟫_ℂ = l * (‖ψ‖ ^ 2 : ℝ) := by
    rw [hψ, inner_smul_right, inner_self_eq_norm_sq_to_K]; norm_cast
  have h2 : ⟪A ψ, ψ⟫_ℂ = (starRingEnd ℂ) l * (‖ψ‖ ^ 2 : ℝ) := by
    rw [hψ, inner_smul_left, inner_self_eq_norm_sq_to_K]; norm_cast
  have h3 : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hA.star_eq]
  have hn : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.2 hψ0
    exact_mod_cast pow_ne_zero 2 this
  have h4 : (starRingEnd ℂ) l = l := mul_right_cancel₀ hn (by rw [← h1, ← h2, h3])
  exact Complex.conj_eq_iff_re.1 h4

end Spectral

end MQSP
