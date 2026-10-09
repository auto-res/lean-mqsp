/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.QSVT.Phases
import MQSP.QSVT.Hermitian
import MQSP.Poly.Approx

/-!
# Synthesis: from a target function to a QSVT program (QSVT-6; GSLW §5 pattern)

The pipeline of a QSVT application, assembled from the reusable theorems:

1. approximation (`Poly/Approx`): a bounded odd/even polynomial `P` with `|P - f| ≤ ε` on
   `[-1, 1]` (Weierstrass; quantitative degree bounds are a separate concern);
2. synthesis (`QSVT/Phases`, GSLW Cor 10): phases `Φ` with `Re P_Φ = P`;
3. the QSVT theorem (`QSVT/Core`, `QSVT/RealPoly`): `Pr (U_Φ + U_{-Φ})/2 Pr = P(A)`;
4. spectral mapping (`Core/Spectral`): `‖P(A) - f(A)‖ ≤ ε`.

Hence for every Hermitian projected unitary encoding `A = Pr U Pr` and every continuous odd
target `f` bounded by `1`, there is a phase list `Φ` whose averaged QSVT circuit implements
`f(A)` within `ε` (`exists_qsvt_approx_odd`); likewise for even targets.
-/

namespace MQSP

universe u

open Polynomial

namespace QSVT

variable {H : Type u} [HSpace H]

/-- An odd polynomial is `X * (oddCore P).comp (X^2)`. -/
theorem odd_eq_X_mul_oddCore_comp (P : ℝ[X]) (h : Poly.IsOdd P) :
    X * (Poly.oddCore P).comp (X ^ 2) = P := by
  refine Polynomial.funext fun x => ?_
  rw [eval_mul, eval_X, eval_comp, eval_pow, eval_X, ← Poly.IsOdd.eval_eq P h]

/-- An even polynomial is `(evenCore P).comp (X^2)`. -/
theorem even_eq_evenCore_comp (P : ℝ[X]) (h : Poly.IsEven P) :
    (Poly.evenCore P).comp (X ^ 2) = P := by
  refine Polynomial.funext fun x => ?_
  rw [eval_comp, eval_pow, eval_X, ← Poly.IsEven.eval_eq P h]

/-- QSVT-6 (odd targets). For a Hermitian encoding `A = Pr U Pr` (contraction) and a
continuous odd `f` with `|f| ≤ 1` on `[-1, 1]`, there are phases `Φ` (odd length) whose
averaged QSVT circuit implements `f(A)` within `ε`. -/
theorem exists_qsvt_approx_odd {U Pr : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hA : IsSelfAdjoint (enc U Pr Pr)) (h1 : ‖enc U Pr Pr‖ ≤ 1) {f : ℝ → ℝ} (hf : Continuous f)
    (hodd : ∀ x, f (-x) = -f x) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : List ℝ, Φ.length % 2 = 1 ∧
      ‖Pr ∘L ((2 : ℂ)⁻¹ • (UΦ U Pr Pr Φ + UΦ U Pr Pr (Φ.map Neg.neg))) ∘L Pr -
        cfc f (enc U Pr Pr)‖ ≤ ε := by
  obtain ⟨P, hP, hPb, hPa⟩ := Poly.exists_odd_approx f hf.continuousOn hodd hb hε
  set n := if P.natDegree % 2 = 1 then P.natDegree else P.natDegree + 1 with hn_def
  have hn2 : n % 2 = 1 := by
    rw [hn_def]; split_ifs <;> omega
  have hn1 : 1 ≤ n := by omega
  have hdeg : P.natDegree ≤ n := by
    rw [hn_def]; split_ifs <;> omega
  have hn0 : ¬ n % 2 = 0 := by omega
  obtain ⟨Φ, hlen, hΦ⟩ := exists_phases P n hn1 hdeg (by rw [ite_eq_right hn0]; exact hP) hPb
  rw [ite_eq_right hn0] at hΦ
  have hΦ2 : Φ.length % 2 = 1 := by rw [hlen]; exact hn2
  refine ⟨Φ, hΦ2, norm_average_sub_cfc_le_odd hU hPr hA h1 Φ hΦ2 hΦ hf hε.le ?_⟩
  rw [odd_eq_X_mul_oddCore_comp P hP]
  exact hPa

end QSVT

end MQSP
