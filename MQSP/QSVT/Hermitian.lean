/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.QSVT.RealPoly
import MQSP.Core.Spectral

/-!
# QSVT of a Hermitian signal and the approximation theorem (QSVT-3/6; GSLW §5)

For a projected unitary encoding with equal projectors `Pr = Pr'` whose encoded operator
`A = Pr U Pr` is self-adjoint, the singular value transformation is the ordinary polynomial
calculus: `Pr U_Φ Pr = P_Φ(A)` with `P_Φ(x) = x^{|Φ| mod 2} p_Φ(x²)` (the spectral mapping of
mQSP §5 / GSLW §5: "for Hermitian `A`, `P^{(SV)}(A) = P(A)`"). Averaging with the negated
phases gives `Re P_Φ (A)`; if `Re P_Φ = P` approximates a continuous target `f` within `ε` on
`[-1, 1]`, the circuit implements `f(A)` within `ε` in operator norm (`Core/Spectral`).
The realisation of a prescribed `P` by phases is `MQSP.QSVT.exists_phases` (QSVT-2).
-/

namespace MQSP

universe u

open Polynomial

namespace QSVT

variable {H : Type u} [HSpace H]

/-- The real polynomial realised by `Φ`: `x^{|Φ| mod 2} · Re p_Φ(x²)`, as a complex polynomial. -/
noncomputable def realized (Φ : List ℝ) : ℂ[X] :=
  if Φ.length % 2 = 0 then (rePoly (pqΦ Φ).1).comp (X ^ 2)
  else X * (rePoly (pqΦ Φ).1).comp (X ^ 2)

/-- For a self-adjoint operator, `p(A†A) = (p.comp (X^2))(A)`. -/
theorem aeval_adjoint_comp_self {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (p : ℂ[X]) :
    aeval (A† ∘L A) p = aeval A (p.comp (X ^ 2)) := by
  have h2 : A† ∘L A = A ^ 2 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hA.star_eq, pow_two]
    rfl
  rw [h2, aeval_comp, map_pow, aeval_X]

/-- For a self-adjoint encoded operator, `A ∘ p(A†A) = (X * p.comp (X^2))(A)`. -/
theorem enc_comp_aeval_eq {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (p : ℂ[X]) :
    A ∘L aeval (A† ∘L A) p = aeval A (X * p.comp (X ^ 2)) := by
  rw [aeval_adjoint_comp_self hA, aeval_mul, aeval_X]
  rfl

/-- For a projection `Pr` and `A = Pr U Pr`, `Pr ∘ p(A†A) ∘ Pr = Pr ∘ (p.comp (X^2))(A) ∘ Pr`
when `A` is self-adjoint. -/
theorem proj_aeval_proj_eq {U Pr : H →L[ℂ] H} (hPr : IsProj Pr) (hA : IsSelfAdjoint (enc U Pr Pr))
    (p : ℂ[X]) :
    Pr ∘L aeval ((enc U Pr Pr)† ∘L enc U Pr Pr) p ∘L Pr =
      Pr ∘L aeval (enc U Pr Pr) (p.comp (X ^ 2)) ∘L Pr := by
  have _ := hPr
  rw [aeval_adjoint_comp_self hA]

/-- QSVT-3 (Hermitian case, odd). `Pr U_Φ Pr = P_Φ(A)` with `P_Φ(x) = x p_Φ(x²)`. -/
theorem proj_UΦ_proj_odd_hermitian {U Pr : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hA : IsSelfAdjoint (enc U Pr Pr)) (Φ : List ℝ) (hΦ : Φ.length % 2 = 1) :
    Pr ∘L UΦ U Pr Pr Φ ∘L Pr = aeval (enc U Pr Pr) (X * (pqΦ Φ).1.comp (X ^ 2)) := by
  rw [proj_UΦ_proj_odd hU hPr hPr Φ hΦ, enc_comp_aeval_eq hA]

/-- QSVT-6 (approximation theorem, odd case). If the real part of the QSP polynomial of `Φ`
is `P` (as a polynomial in `y = x²`, so that the realised real polynomial is `x P(x²)`), and
`x P(x²)` approximates a continuous `f` within `ε` on `[-1, 1]`, then the averaged circuit
implements `f(A)` within `ε`. -/
theorem norm_average_sub_cfc_le_odd {U Pr : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hA : IsSelfAdjoint (enc U Pr Pr)) (h1 : ‖enc U Pr Pr‖ ≤ 1) (Φ : List ℝ)
    (hΦ : Φ.length % 2 = 1) {P : ℝ[X]} (hreal : rePoly (pqΦ Φ).1 = P.map (algebraMap ℝ ℂ))
    {f : ℝ → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : Poly.ApproxOn (X * P.comp (X ^ 2)) f (Set.Icc (-1) 1) ε) :
    ‖Pr ∘L ((2 : ℂ)⁻¹ • (UΦ U Pr Pr Φ + UΦ U Pr Pr (Φ.map Neg.neg))) ∘L Pr -
      cfc f (enc U Pr Pr)‖ ≤ ε := by
  rw [proj_average_proj_odd hU hPr hPr Φ hΦ, hreal, enc_comp_aeval_eq hA]
  have hpoly : aeval (enc U Pr Pr) (X * (P.map (algebraMap ℝ ℂ)).comp (X ^ 2)) =
      Spectral.polyCalc (enc U Pr Pr) (X * P.comp (X ^ 2)) := by
    rw [Spectral.polyCalc, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_comp,
      Polynomial.map_pow, Polynomial.map_X]
  rw [hpoly]
  exact Spectral.norm_polyCalc_sub_cfc_le hA h1 hf hε happrox

end QSVT

end MQSP
