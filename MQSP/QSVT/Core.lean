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

theorem phaseOp_mul_of_mul_eq {P X : H →L[ℂ] H} (φ : ℝ) (hX : P * X = X) :
    phaseOp P φ * X = Complex.exp (φ * Complex.I) • X := by
  simp only [phaseOp, add_mul, smul_mul_assoc, sub_mul, one_mul, hX, sub_self, smul_zero,
    add_zero]

theorem phaseOp_mul_of_mul_eq_zero {P X : H →L[ℂ] H} (φ : ℝ) (hX : P * X = 0) :
    phaseOp P φ * X = Complex.exp (-(φ * Complex.I)) • X := by
  simp only [phaseOp, add_mul, smul_mul_assoc, sub_mul, one_mul, hX, sub_zero, smul_zero,
    zero_add]

theorem phaseOp_mul_phaseOp {P : H →L[ℂ] H} (hP : P * P = P) (a b : ℝ) :
    phaseOp P a * phaseOp P b = phaseOp P (a + b) := by
  have h1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
  rw [phaseOp.eq_1 P b, mul_add, mul_smul_comm, mul_smul_comm, phaseOp_mul_of_mul_eq a hP,
    phaseOp_mul_of_mul_eq_zero a h1, smul_smul, smul_smul, phaseOp]
  congr 2 <;> rw [← Complex.exp_add] <;> congr 1 <;> push_cast <;> ring

theorem phaseOp_zero (P : H →L[ℂ] H) : phaseOp P 0 = 1 := by
  simp [phaseOp]

theorem adjoint_phaseOp {P : H →L[ℂ] H} (hP : P† = P) (φ : ℝ) :
    (phaseOp P φ)† = phaseOp P (-φ) := by
  rw [phaseOp, phaseOp, ← ContinuousLinearMap.star_eq_adjoint, star_add, star_smul, star_smul,
    star_sub, star_one, ContinuousLinearMap.star_eq_adjoint, hP]
  congr 2 <;> rw [Complex.star_def, ← Complex.exp_conj] <;> congr 1 <;>
    simp [Complex.conj_ofReal, Complex.conj_I]

theorem isUnitary_phaseOp {Pr : H →L[ℂ] H} (hPr : IsProj Pr) (φ : ℝ) :
    IsUnitary (phaseOp Pr φ) := by
  have h2 : Pr * Pr = Pr := hPr.2
  constructor
  · change (phaseOp Pr φ)† * phaseOp Pr φ = 1
    rw [adjoint_phaseOp hPr.1, phaseOp_mul_phaseOp h2, neg_add_cancel, phaseOp_zero]
  · change phaseOp Pr φ * (phaseOp Pr φ)† = 1
    rw [adjoint_phaseOp hPr.1, phaseOp_mul_phaseOp h2, add_neg_cancel, phaseOp_zero]

theorem phaseOp_comp_proj {Pr : H →L[ℂ] H} (hPr : IsProj Pr) (φ : ℝ) :
    phaseOp Pr φ ∘L Pr = Complex.exp (φ * Complex.I) • Pr :=
  phaseOp_mul_of_mul_eq (P := Pr) (X := Pr) φ hPr.2

theorem phaseOp_comp_one_sub_proj {Pr : H →L[ℂ] H} (hPr : IsProj Pr) (φ : ℝ) :
    phaseOp Pr φ ∘L (1 - Pr) = Complex.exp (-(φ * Complex.I)) • (1 - Pr) := by
  have h2 : Pr * Pr = Pr := hPr.2
  exact phaseOp_mul_of_mul_eq_zero (P := Pr) (X := 1 - Pr) φ
    (by rw [mul_sub, mul_one, h2, sub_self])

/-- The encoded operator `A = Pr' U Pr`. -/
noncomputable abbrev enc (U Pr Pr' : H →L[ℂ] H) : H →L[ℂ] H := Pr' ∘L U ∘L Pr

/-- The complementary block `B = (1 - Pr') U Pr`. -/
noncomputable abbrev encC (U Pr Pr' : H →L[ℂ] H) : H →L[ℂ] H := (1 - Pr') ∘L U ∘L Pr

section Facts

variable {U Pr Pr' : H →L[ℂ] H}

theorem adjoint_enc (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    (enc U Pr Pr')† = Pr * (U† * Pr') := by
  rw [enc, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hPr.1, hPr'.1]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem adjoint_encC (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    (encC U Pr Pr')† = Pr * (U† * (1 - Pr')) := by
  rw [encC, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, hPr.1,
    hPr'.one_sub.1]
  exact ContinuousLinearMap.comp_assoc _ _ _

theorem adjoint_enc_comp_enc (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    (enc U Pr Pr')† ∘L enc U Pr Pr' = Pr * (U† * enc U Pr Pr') := by
  have h2' : Pr' * Pr' = Pr' := hPr'.2
  rw [adjoint_enc hPr hPr']
  change Pr * (U† * Pr') * (Pr' * (U * Pr)) = Pr * (U† * (Pr' * (U * Pr)))
  rw [mul_assoc, mul_assoc, ← mul_assoc Pr' Pr', h2']

theorem proj_mul_enc (hPr' : IsProj Pr') : Pr' * enc U Pr Pr' = enc U Pr Pr' := by
  have h2' : Pr' * Pr' = Pr' := hPr'.2
  change Pr' * (Pr' * (U * Pr)) = Pr' * (U * Pr)
  rw [← mul_assoc, h2']

theorem proj_mul_encC (hPr' : IsProj Pr') : Pr' * encC U Pr Pr' = 0 := by
  have h2' : Pr' * Pr' = Pr' := hPr'.2
  change Pr' * ((1 - Pr') * (U * Pr)) = 0
  rw [← mul_assoc, mul_sub, mul_one, h2', sub_self, zero_mul]

theorem proj_mul_adjoint_enc_comp_enc (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    Pr * ((enc U Pr Pr')† ∘L enc U Pr Pr') = (enc U Pr Pr')† ∘L enc U Pr Pr' := by
  have h2 : Pr * Pr = Pr := hPr.2
  rw [adjoint_enc_comp_enc hPr hPr', ← mul_assoc, h2]

theorem proj_mul_encW (hPr : IsProj Pr) : Pr * ((1 - Pr) ∘L U† ∘L enc U Pr Pr') = 0 := by
  have h2 : Pr * Pr = Pr := hPr.2
  change Pr * ((1 - Pr) * (U† * enc U Pr Pr')) = 0
  rw [← mul_assoc, mul_sub, mul_one, h2, sub_self, zero_mul]

theorem mul_proj_eq (U Pr Pr' : H →L[ℂ] H) : U * Pr = enc U Pr Pr' + encC U Pr Pr' := by
  change U * Pr = Pr' * (U * Pr) + (1 - Pr') * (U * Pr)
  rw [← add_mul, add_sub_cancel, one_mul]

theorem mul_encW (hU : IsUnitary U) (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    U * ((1 - Pr) ∘L U† ∘L enc U Pr Pr') =
      enc U Pr Pr' - (enc U Pr Pr' + encC U Pr Pr') * ((enc U Pr Pr')† ∘L enc U Pr Pr') := by
  have hU2 : U * U† = 1 := hU.2
  calc U * ((1 - Pr) ∘L U† ∘L enc U Pr Pr')
      = U * U† * enc U Pr Pr' - U * (Pr * (U† * enc U Pr Pr')) := by
        change U * ((1 - Pr) * (U† * enc U Pr Pr')) = _
        noncomm_ring
    _ = enc U Pr Pr' - U * ((enc U Pr Pr')† ∘L enc U Pr Pr') := by
        rw [hU2, one_mul, adjoint_enc_comp_enc hPr hPr']
    _ = enc U Pr Pr' - U * (Pr * ((enc U Pr Pr')† ∘L enc U Pr Pr')) := by
        rw [proj_mul_adjoint_enc_comp_enc hPr hPr']
    _ = _ := by rw [← mul_assoc U Pr, mul_proj_eq U Pr Pr']

theorem adjoint_mul_enc (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    U† * enc U Pr Pr' =
      (enc U Pr Pr')† ∘L enc U Pr Pr' + (1 - Pr) ∘L U† ∘L enc U Pr Pr' := by
  rw [adjoint_enc_comp_enc hPr hPr']
  change _ = Pr * (U† * enc U Pr Pr') + (1 - Pr) * (U† * enc U Pr Pr')
  rw [← add_mul, add_sub_cancel, one_mul]

theorem adjoint_mul_encC (hU : IsUnitary U) (hPr : IsProj Pr) (hPr' : IsProj Pr') :
    U† * encC U Pr Pr' =
      Pr - (enc U Pr Pr')† ∘L enc U Pr Pr' - (1 - Pr) ∘L U† ∘L enc U Pr Pr' := by
  have hU1 : U† * U = 1 := hU.1
  have h : U† * ((1 - Pr') * (U * Pr)) = U† * U * Pr - U† * (Pr' * (U * Pr)) := by
    noncomm_ring
  rw [hU1, one_mul] at h
  rw [sub_sub, ← adjoint_mul_enc hPr hPr']
  exact h

end Facts

/-- `A†A + B†B = Pr` for unitary `U` and projections `Pr, Pr'`. -/
theorem enc_adj_enc_add {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') :
    (enc U Pr Pr')† ∘L enc U Pr Pr' + (encC U Pr Pr')† ∘L encC U Pr Pr' = Pr := by
  have hU1 : U† * U = 1 := hU.1
  have h2 : Pr * Pr = Pr := hPr.2
  have h2' : Pr' * Pr' = Pr' := hPr'.2
  have h3 : (1 - Pr') * (1 - Pr') = 1 - Pr' := hPr'.one_sub.2
  rw [adjoint_enc hPr hPr', adjoint_encC hPr hPr']
  change Pr * (U† * Pr') * (Pr' * (U * Pr)) + Pr * (U† * (1 - Pr')) * ((1 - Pr') * (U * Pr)) = Pr
  calc Pr * (U† * Pr') * (Pr' * (U * Pr)) + Pr * (U† * (1 - Pr')) * ((1 - Pr') * (U * Pr))
      = Pr * U† * (Pr' * Pr') * U * Pr + Pr * U† * ((1 - Pr') * (1 - Pr')) * U * Pr := by
        noncomm_ring
    _ = Pr * (U† * U) * Pr := by rw [h2', h3]; noncomm_ring
    _ = Pr := by rw [hU1, mul_one, h2]

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

theorem isUnitary_stepOp {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (k : ℕ) (φ : ℝ) : IsUnitary (stepOp U Pr Pr' k φ) := by
  unfold stepOp
  split_ifs
  · exact (isUnitary_phaseOp hPr' φ).comp hU
  · exact (isUnitary_phaseOp hPr φ).comp hU.adjoint

theorem isUnitary_altFrom {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') :
    ∀ (Φ : List ℝ) (k : ℕ) (V : H →L[ℂ] H), IsUnitary V → IsUnitary (altFrom U Pr Pr' Φ k V)
  | [], _, _, hV => hV
  | φ :: Φ, k, _, hV =>
    isUnitary_altFrom hU hPr hPr' Φ (k + 1) _ ((isUnitary_stepOp hU hPr hPr' k φ).comp hV)

theorem isUnitary_UΦ {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) : IsUnitary (UΦ U Pr Pr' Φ) :=
  isUnitary_altFrom hU hPr hPr' Φ 0 1 isUnitary_one

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
theorem even_core {U Pr A B W y ph P Q : H →L[ℂ] H} {e e' : ℂ} (hUPr : U * Pr = A + B)
    (hUW : U * W = A - (A + B) * y) (hA : ph * A = e • A) (hB : ph * B = e' • B) :
    ph * U * (Pr * P + W * Q) = A * (e • (P + Q - y * Q)) + B * (e' • (P - y * Q)) := by
  calc ph * U * (Pr * P + W * Q) = ph * ((U * Pr) * P + (U * W) * Q) := by noncomm_ring
    _ = ph * A * P + ph * B * P + ph * A * Q - ph * A * (y * Q) - ph * B * (y * Q) := by
        rw [hUPr, hUW]; noncomm_ring
    _ = _ := by
        rw [hA, hB]
        simp only [smul_mul_assoc, mul_smul_comm, mul_add, mul_sub]
        module

theorem odd_core {Ud Pr A B W y ph P Q : H →L[ℂ] H} {e e' : ℂ} (hUA : Ud * A = y + W)
    (hUB : Ud * B = Pr - y - W) (hPy : Pr * y = y) (hPr : ph * Pr = e • Pr)
    (hW : ph * W = e' • W) :
    ph * Ud * (A * P + B * Q) = Pr * (e • (y * (P - Q) + Q)) + W * (e' • (P - Q)) := by
  have hy : ph * y = e • y := by rw [← hPy, ← mul_assoc, hPr, smul_mul_assoc]
  calc ph * Ud * (A * P + B * Q) = ph * ((Ud * A) * P + (Ud * B) * Q) := by noncomm_ring
    _ = ph * y * P + ph * W * P + ph * Pr * Q - ph * y * Q - ph * W * Q := by
        rw [hUA, hUB]; noncomm_ring
    _ = e • (y * P) + e' • (W * P) + e • (Pr * Q) - e • (y * Q) - e' • (W * Q) := by
        rw [hy, hW, hPr]; simp only [smul_mul_assoc]
    _ = _ := by
        simp only [mul_smul_comm, mul_add, mul_sub, ← mul_assoc, hPy]
        module

theorem shape_step {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr) (hPr' : IsProj Pr')
    {k : ℕ} {V : H →L[ℂ] H} {st : ℂ[X] × ℂ[X]} (h : Shape U Pr Pr' k V st) (φ : ℝ) :
    Shape U Pr Pr' (k + 1) (stepOp U Pr Pr' k φ ∘L V) (pqStep k φ st) := by
  unfold Shape at h ⊢
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have hk1 : ¬ (k + 1) % 2 = 0 := by omega
    rw [ite_eq_left hk] at h
    rw [ite_eq_right hk1, stepOp, ite_eq_left hk, pqStep, ite_eq_left hk]
    simp only [map_mul, map_add, map_sub, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    rw [ContinuousLinearMap.comp_assoc _ V Pr, h]
    exact even_core (mul_proj_eq U Pr Pr') (mul_encW hU hPr hPr')
      (phaseOp_mul_of_mul_eq φ (proj_mul_enc hPr'))
      (phaseOp_mul_of_mul_eq_zero φ (proj_mul_encC hPr'))
  · have hk0 : ¬ k % 2 = 0 := by omega
    have hk1 : (k + 1) % 2 = 0 := by omega
    rw [ite_eq_right hk0] at h
    rw [ite_eq_left hk1, stepOp, ite_eq_right hk0, pqStep, ite_eq_right hk0]
    simp only [map_mul, map_add, map_sub, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
    rw [ContinuousLinearMap.comp_assoc _ V Pr, h]
    exact odd_core (adjoint_mul_enc hPr hPr') (adjoint_mul_encC hU hPr hPr')
      (proj_mul_adjoint_enc_comp_enc hPr hPr') (phaseOp_mul_of_mul_eq (P := Pr) (X := Pr) φ hPr.2)
      (phaseOp_mul_of_mul_eq_zero φ (proj_mul_encW hPr))

theorem shape_altFrom {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) {k : ℕ} {V : H →L[ℂ] H} {st : ℂ[X] × ℂ[X]}
    (h : Shape U Pr Pr' k V st) :
    Shape U Pr Pr' (k + Φ.length) (altFrom U Pr Pr' Φ k V) (pqFrom Φ k st) := by
  induction Φ generalizing k V st with
  | nil => simpa only [altFrom, pqFrom, List.length_nil, Nat.add_zero] using h
  | cons φ Φ ih =>
    rw [altFrom, pqFrom, List.length_cons, show k + (Φ.length + 1) = k + 1 + Φ.length by omega]
    exact ih (shape_step hU hPr hPr' h φ)

theorem shape_one {U Pr Pr' : H →L[ℂ] H} (hPr : IsProj Pr) : Shape U Pr Pr' 0 1 (1, 0) := by
  -- `hPr` is not needed: `1 ∘L Pr = Pr ∘L 1 + W ∘L 0` holds for any `Pr`.
  have _ := hPr
  unfold Shape
  rw [ite_eq_left rfl]
  simp only [map_one, map_zero, comp_one, ContinuousLinearMap.comp_zero, add_zero, one_comp]

theorem proj_mul_add_mul {X A B P Q : H →L[ℂ] H} (hA : X * A = A) (hB : X * B = 0) :
    X * (A * P + B * Q) = A * P := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, hA, hB, zero_mul, add_zero]

theorem proj_mul_mul_proj {Pr V W P Q : H →L[ℂ] H} (hP : Pr * Pr = Pr) (hW : Pr * W = 0)
    (hV : V * Pr = Pr * P + W * Q) : Pr * (V * Pr) = Pr * (P * Pr) := by
  calc Pr * (V * Pr) = Pr * ((V * Pr) * Pr) := by rw [mul_assoc V, hP]
    _ = Pr * ((Pr * P + W * Q) * Pr) := by rw [hV]
    _ = (Pr * Pr) * P * Pr + (Pr * W) * Q * Pr := by noncomm_ring
    _ = Pr * (P * Pr) := by rw [hP, hW, zero_mul, zero_mul, add_zero, mul_assoc]

/-- QSVT-3 (GSLW Thm 17, odd case). For an odd number of phases,
`Pr' U_Φ Pr = A ∘ p_Φ(A†A)`: the singular value transformation of `A` by `x ↦ x p_Φ(x²)`. -/
theorem proj_UΦ_proj_odd {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 1) :
    Pr' ∘L UΦ U Pr Pr' Φ ∘L Pr =
      enc U Pr Pr' ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (pqΦ Φ).1 := by
  have hs := shape_altFrom hU hPr hPr' Φ (shape_one (U := U) (Pr' := Pr') hPr)
  unfold Shape at hs
  rw [zero_add, ite_eq_right (by omega : ¬ Φ.length % 2 = 0)] at hs
  rw [UΦ, pqΦ, hs]
  exact proj_mul_add_mul (proj_mul_enc hPr') (proj_mul_encC hPr')

/-- QSVT-3 (GSLW Thm 17, even case). For an even number of phases,
`Pr U_Φ Pr = Pr ∘ p_Φ(A†A) ∘ Pr`: the SVT of `A` by the even polynomial `x ↦ p_Φ(x²)`. -/
theorem proj_UΦ_proj_even {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 0) :
    Pr ∘L UΦ U Pr Pr' Φ ∘L Pr =
      Pr ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (pqΦ Φ).1 ∘L Pr := by
  have hs := shape_altFrom hU hPr hPr' Φ (shape_one (U := U) (Pr' := Pr') hPr)
  unfold Shape at hs
  rw [zero_add, ite_eq_left hΦ] at hs
  exact proj_mul_mul_proj hPr.2 (proj_mul_encW hPr) hs

/-- GSLW Cor 18 (conjugation): negating all phases conjugates the polynomial pair. -/
theorem pqStep_neg (k : ℕ) (φ : ℝ) (st : ℂ[X] × ℂ[X]) :
    pqStep k (-φ) (st.1.map (starRingEnd ℂ), st.2.map (starRingEnd ℂ)) =
      ((pqStep k φ st).1.map (starRingEnd ℂ), (pqStep k φ st).2.map (starRingEnd ℂ)) := by
  have h1 : (starRingEnd ℂ) (Complex.exp (φ * Complex.I)) =
      Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  have h2 : (starRingEnd ℂ) (Complex.exp (-(φ * Complex.I))) =
      Complex.exp (-(((-φ : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal, Complex.conj_I]
  unfold pqStep
  split_ifs <;> simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_X, h1, h2]

theorem pqFrom_neg (Φ : List ℝ) (k : ℕ) (st : ℂ[X] × ℂ[X]) :
    pqFrom (Φ.map Neg.neg) k (st.1.map (starRingEnd ℂ), st.2.map (starRingEnd ℂ)) =
      ((pqFrom Φ k st).1.map (starRingEnd ℂ), (pqFrom Φ k st).2.map (starRingEnd ℂ)) := by
  induction Φ generalizing k st with
  | nil => rfl
  | cons φ Φ ih =>
    simp only [List.map_cons, pqFrom]
    rw [pqStep_neg, ih]

theorem pqΦ_neg (Φ : List ℝ) :
    pqΦ (Φ.map Neg.neg) = ((pqΦ Φ).1.map (starRingEnd ℂ), (pqΦ Φ).2.map (starRingEnd ℂ)) := by
  have := pqFrom_neg Φ 0 (1, 0)
  simp only [Polynomial.map_one, Polynomial.map_zero] at this
  exact this

/-- The degree of `p_Φ` is at most `⌊|Φ|/2⌋` (so `P(x) = x^{n mod 2} p(x²)` has degree ≤ `n`). -/
theorem natDegree_X_mul_le' (f : ℂ[X]) : (X * f).natDegree ≤ f.natDegree + 1 := by
  have h1 := natDegree_X_le (R := ℂ)
  have h2 := natDegree_mul_le (p := X) (q := f)
  omega

theorem natDegree_pqStep_le {k : ℕ} (hk : 1 ≤ k) (φ : ℝ) {st : ℂ[X] × ℂ[X]}
    (h1 : st.1.natDegree ≤ k / 2) (h2 : st.2.natDegree ≤ (k - 1) / 2) :
    (pqStep k φ st).1.natDegree ≤ (k + 1) / 2 ∧ (pqStep k φ st).2.natDegree ≤ k / 2 := by
  have hX := natDegree_X_mul_le' st.2
  have hX' := natDegree_X_mul_le' (st.1 - st.2)
  have hs := natDegree_sub_le st.1 st.2
  unfold pqStep
  split_ifs <;> dsimp only
  · have ha := natDegree_add_le st.1 st.2
    have hb := natDegree_sub_le (st.1 + st.2) (X * st.2)
    have hc := natDegree_sub_le st.1 (X * st.2)
    have hd := natDegree_C_mul_le (Complex.exp (φ * Complex.I)) (st.1 + st.2 - X * st.2)
    have he := natDegree_C_mul_le (Complex.exp (-(φ * Complex.I))) (st.1 - X * st.2)
    constructor <;> omega
  · have ha := natDegree_add_le (X * (st.1 - st.2)) st.2
    have hd := natDegree_C_mul_le (Complex.exp (φ * Complex.I)) (X * (st.1 - st.2) + st.2)
    have he := natDegree_C_mul_le (Complex.exp (-(φ * Complex.I))) (st.1 - st.2)
    constructor <;> omega

theorem natDegree_pqFrom_le (Φ : List ℝ) {k : ℕ} (hk : 1 ≤ k) {st : ℂ[X] × ℂ[X]}
    (h1 : st.1.natDegree ≤ k / 2) (h2 : st.2.natDegree ≤ (k - 1) / 2) :
    (pqFrom Φ k st).1.natDegree ≤ (k + Φ.length) / 2 ∧
      (pqFrom Φ k st).2.natDegree ≤ (k + Φ.length - 1) / 2 := by
  induction Φ generalizing k st with
  | nil => simpa only [pqFrom, List.length_nil, Nat.add_zero] using ⟨h1, h2⟩
  | cons φ Φ ih =>
    obtain ⟨h1', h2'⟩ := natDegree_pqStep_le hk φ h1 h2
    have := ih (k := k + 1) (by omega) h1' (by omega)
    rw [pqFrom, List.length_cons, show k + (Φ.length + 1) = k + 1 + Φ.length by omega]
    exact this

theorem natDegree_pqΦ_fst_le (Φ : List ℝ) : (pqΦ Φ).1.natDegree ≤ Φ.length / 2 := by
  cases Φ with
  | nil => simp [pqΦ, pqFrom]
  | cons φ Φ =>
    have h1 : (pqStep 0 φ (1, 0)).1.natDegree ≤ 1 / 2 := by simp [pqStep]
    have h2 : (pqStep 0 φ (1, 0)).2.natDegree ≤ (1 - 1) / 2 := by simp [pqStep]
    have := (natDegree_pqFrom_le Φ le_rfl h1 h2).1
    rw [pqΦ, pqFrom, List.length_cons]
    rw [Nat.add_comm] at this
    exact this

end QSVT

end MQSP
