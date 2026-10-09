/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.HSpace
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quantum singular value transformation, SVD-free (QSVT-3; GSLW Thm 17, Cor 18)

Let `U` be unitary on `H` and `Pr, Pr'` (= `Pr̃`) orthogonal projections: a *projected unitary
encoding* of `A = Pr' U Pr` (GSLW Def 11). The alternating phase sequence (GSLW Def 15) applies,
in time order, `U`, `e^{iφ(2Pr'-1)}`, `U†`, `e^{iφ'(2Pr-1)}`, `U`, … . We parametrise it by the
time-ordered list of phases `Φ = [φ₁, φ₂, …]` (GSLW's `φ_n` is our first phase).

**Two-block recursion (Route A, no SVD).** With `B = (1 - Pr') U Pr` we have `A†A + B†B = Pr`,
and for the partial products `Vₖ` (first `k` steps) one proves by induction

* `k` even: `Vₖ Pr = Pr ∘ pₖ(A†A) + ((1 - Pr) U† A) ∘ qₖ(A†A)`,
* `k` odd:  `Vₖ Pr = A ∘ pₖ(A†A) + B ∘ qₖ(A†A)`,

where the polynomial pair `(pₖ, qₖ)` in `y = x²` obeys the scalar QSP recursion
(reflection convention, `y`-form of GSLW Thm 3):
step `k` even with phase `φ`: `p' = e^{iφ}(p + q - y q)`, `q' = e^{-iφ}(p - y q)`;
step `k` odd with phase `φ`:  `p' = e^{iφ}(y (p - q) + q)`, `q' = e^{-iφ}(p - q)`.

Consequently (GSLW Thm 17): for odd `n`, `Pr' U_Φ Pr = A ∘ pₙ(A†A)`, the singular value
transformation by the odd polynomial `P(x) = x pₙ(x²)`; for even `n`,
`Pr U_Φ Pr = Pr ∘ pₙ(A†A) ∘ Pr`, the SVT by the even polynomial `P(x) = pₙ(x²)`.
Negating all phases conjugates the polynomial pair (GSLW Cor 18), so averaging `U_Φ` and
`U_{-Φ}` implements `Re P`. The scalar QSP theory is the special case `H = ℂ²`.
-/

namespace MQSP

universe u

open scoped InnerProductSpace
open Polynomial

namespace QSVT

variable {H : Type u} [HSpace H]

/-- The phase operator `e^{iφ(2Pr - 1)} = e^{iφ} Pr + e^{-iφ} (1 - Pr)`. -/
noncomputable def phaseOp (Pr : H →L[ℂ] H) (φ : ℝ) : H →L[ℂ] H :=
  Complex.exp (φ * Complex.I) • Pr + Complex.exp (-(φ * Complex.I)) • (1 - Pr)

theorem isUnitary_phaseOp {Pr : H →L[ℂ] H} (hPr : IsProj Pr) (φ : ℝ) :
    IsUnitary (phaseOp Pr φ) := by
  sorry

theorem phaseOp_comp_proj {Pr : H →L[ℂ] H} (hPr : IsProj Pr) (φ : ℝ) :
    phaseOp Pr φ ∘L Pr = Complex.exp (φ * Complex.I) • Pr := by
  sorry

theorem phaseOp_comp_one_sub_proj {Pr : H →L[ℂ] H} (hPr : IsProj Pr) (φ : ℝ) :
    phaseOp Pr φ ∘L (1 - Pr) = Complex.exp (-(φ * Complex.I)) • (1 - Pr) := by
  sorry

/-- The encoded operator `A = Pr' U Pr`. -/
noncomputable abbrev enc (U Pr Pr' : H →L[ℂ] H) : H →L[ℂ] H := Pr' ∘L U ∘L Pr

/-- The complementary block `B = (1 - Pr') U Pr`. -/
noncomputable abbrev encC (U Pr Pr' : H →L[ℂ] H) : H →L[ℂ] H := (1 - Pr') ∘L U ∘L Pr

/-- `A†A + B†B = Pr` for unitary `U` and projections `Pr, Pr'`. -/
theorem enc_adj_enc_add {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') :
    (enc U Pr Pr')† ∘L enc U Pr Pr' + (encC U Pr Pr')† ∘L encC U Pr Pr' = Pr := by
  sorry

/-- Step `k` (0-indexed) with phase `φ`: `e^{iφ(2Pr'-1)} U` for even `k`, `e^{iφ(2Pr-1)} U†`
for odd `k`. -/
noncomputable def stepOp (U Pr Pr' : H →L[ℂ] H) (k : ℕ) (φ : ℝ) : H →L[ℂ] H :=
  if k % 2 = 0 then phaseOp Pr' φ ∘L U else phaseOp Pr φ ∘L U†

/-- Apply the steps for the phases in `Φ`, starting at step number `k`, after `V`. -/
noncomputable def altFrom (U Pr Pr' : H →L[ℂ] H) : List ℝ → ℕ → (H →L[ℂ] H) → (H →L[ℂ] H)
  | [], _, V => V
  | φ :: Φ, k, V => altFrom U Pr Pr' Φ (k + 1) (stepOp U Pr Pr' k φ ∘L V)

/-- QSVT-1 (GSLW Def 15, time-ordered). The alternating phase sequence `U_Φ`. -/
noncomputable def UΦ (U Pr Pr' : H →L[ℂ] H) (Φ : List ℝ) : H →L[ℂ] H :=
  altFrom U Pr Pr' Φ 0 1

theorem isUnitary_UΦ {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) : IsUnitary (UΦ U Pr Pr' Φ) := by
  sorry

/-- One step of the scalar QSP recursion on the polynomial pair `(p, q)` in `y = x²`. -/
noncomputable def pqStep (k : ℕ) (φ : ℝ) (st : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  if k % 2 = 0 then
    (C (Complex.exp (φ * Complex.I)) * (st.1 + st.2 - X * st.2),
      C (Complex.exp (-(φ * Complex.I))) * (st.1 - X * st.2))
  else
    (C (Complex.exp (φ * Complex.I)) * (X * (st.1 - st.2) + st.2),
      C (Complex.exp (-(φ * Complex.I))) * (st.1 - st.2))

/-- The polynomial pair after the steps for `Φ`, starting at step `k` from `st`. -/
noncomputable def pqFrom : List ℝ → ℕ → ℂ[X] × ℂ[X] → ℂ[X] × ℂ[X]
  | [], _, st => st
  | φ :: Φ, k, st => pqFrom Φ (k + 1) (pqStep k φ st)

/-- QSVT-3. The QSP polynomial pair `(p_Φ, q_Φ)` of a phase list (in the variable `y = x²`). -/
noncomputable def pqΦ (Φ : List ℝ) : ℂ[X] × ℂ[X] := pqFrom Φ 0 (1, 0)

/-- The two-block shape of a partial product after `k` steps. -/
def Shape (U Pr Pr' : H →L[ℂ] H) (k : ℕ) (V : H →L[ℂ] H) (st : ℂ[X] × ℂ[X]) : Prop :=
  if k % 2 = 0 then
    V ∘L Pr = Pr ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') st.1 +
      ((1 - Pr) ∘L U† ∘L enc U Pr Pr') ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') st.2
  else
    V ∘L Pr = enc U Pr Pr' ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') st.1 +
      encC U Pr Pr' ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') st.2

/-- QSVT-3 (two-block recursion). One step preserves the shape and advances the pair. -/
theorem shape_step {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr) (hPr' : IsProj Pr')
    {k : ℕ} {V : H →L[ℂ] H} {st : ℂ[X] × ℂ[X]} (h : Shape U Pr Pr' k V st) (φ : ℝ) :
    Shape U Pr Pr' (k + 1) (stepOp U Pr Pr' k φ ∘L V) (pqStep k φ st) := by
  sorry

theorem shape_altFrom {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) {k : ℕ} {V : H →L[ℂ] H} {st : ℂ[X] × ℂ[X]}
    (h : Shape U Pr Pr' k V st) :
    Shape U Pr Pr' (k + Φ.length) (altFrom U Pr Pr' Φ k V) (pqFrom Φ k st) := by
  sorry

theorem shape_one {U Pr Pr' : H →L[ℂ] H} (hPr : IsProj Pr) : Shape U Pr Pr' 0 1 (1, 0) := by
  sorry

/-- QSVT-3 (GSLW Thm 17, odd case). For an odd number of phases,
`Pr' U_Φ Pr = A ∘ p_Φ(A†A)`: the singular value transformation of `A` by `x ↦ x p_Φ(x²)`. -/
theorem proj_UΦ_proj_odd {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 1) :
    Pr' ∘L UΦ U Pr Pr' Φ ∘L Pr =
      enc U Pr Pr' ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (pqΦ Φ).1 := by
  sorry

/-- QSVT-3 (GSLW Thm 17, even case). For an even number of phases,
`Pr U_Φ Pr = Pr ∘ p_Φ(A†A) ∘ Pr`: the SVT of `A` by the even polynomial `x ↦ p_Φ(x²)`. -/
theorem proj_UΦ_proj_even {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 0) :
    Pr ∘L UΦ U Pr Pr' Φ ∘L Pr =
      Pr ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (pqΦ Φ).1 ∘L Pr := by
  sorry

/-- GSLW Cor 18 (conjugation): negating all phases conjugates the polynomial pair. -/
theorem pqΦ_neg (Φ : List ℝ) :
    pqΦ (Φ.map Neg.neg) = ((pqΦ Φ).1.map (starRingEnd ℂ), (pqΦ Φ).2.map (starRingEnd ℂ)) := by
  sorry

/-- The degree of `p_Φ` is at most `⌊|Φ|/2⌋` (so `P(x) = x^{n mod 2} p(x²)` has degree ≤ `n`). -/
theorem natDegree_pqΦ_fst_le (Φ : List ℝ) : (pqΦ Φ).1.natDegree ≤ Φ.length / 2 := by
  sorry

end QSVT

end MQSP
