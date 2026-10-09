/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import MQSP.QSP.Structure

/-!
# Existence of QSP phases, reflection convention (lean-qsvt QSP-7c; GSLW Thm 3 "⇐", Cor 8)

Adapted from lean-qsvt (MIT, shosonoda), `QSVT/QSP/Existence.lean`.  lean-qsvt proves the
existence of phases in the rotation convention (`qspPolyW`) and transports it to the reflection
convention through GSLW Cor 8 at the matrix level; here the degree-lowering induction
(GSLW eqs. (6)–(8)) is carried out *directly* in the reflection convention on the polynomial
recursion `qspPoly`, which avoids the rotation convention altogether.

Given `P, Q ∈ ℂ[X]` with (i) `deg P ≤ k`, `deg Q ≤ k - 1` (`Q = 0` for `k = 0`), (ii) parity
`P ≡ k`, `Q ≡ k - 1 (mod 2)`, (iii) `P P^* + (1 - X²) Q Q^* = 1`:

* `exists_phases_R_unimodular`: there are `θ` and `Φ` of length `k` with
  `qspPoly Φ = e^{iθ} (P, Q)`.  Induction on `k`; for `k = n + 1` the inverse step
  `unstepR φ (P, Q) = (e^{-iφ} X P + e^{iφ} (1 - X²) Q, e^{-iφ} P - e^{iφ} X Q)`
  (`stepR φ ∘ unstepR φ = id`, `stepR_unstepR`) preserves (iii) (`unstepR_unit`), shifts the
  parities, and with `e^{-iφ} p_{n+1} = e^{iφ} q_n` (`exists_phase_coeff`) lowers the degrees.
  The base case `k = 0` is `(P, Q) = (e^{iθ}, 0)`; the reflection convention has no free leading
  phase, which is why a unimodular factor is carried along.
* `exists_phases_R_poly`: for `k ≥ 1` the factor is absorbed into the head (latest) phase, which
  multiplies `P` by `e^{iθ}` and `Q` by `e^{-iθ}`: `(qspPoly Φ).1 = P` and
  `(qspPoly Φ).2 = e^{iθ'} Q`.  (For `k = 0` only `P = 1` is realisable.)
* `exists_phases_R`: the matrix form `(seqR Φ x) 0 0 = P(x)` on `[-1, 1]` (lean-qsvt's
  `exists_phases_R`).
-/

open Polynomial

namespace MQSP.QSP

open Complex

/-! ### One reflection step and its inverse -/

/-- One reflection-convention step `e^{iφσ_z} R(x)` on the polynomial pair (the recursion of
`qspPoly`): `(P, Q) ↦ (e^{iφ} (X P + (1 - X²) Q), e^{-iφ} (P - X Q))`. -/
noncomputable def stepR (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (Complex.I * φ)) * (X * PQ.1 + (1 - X ^ 2) * PQ.2),
    C (Complex.exp (-(Complex.I * φ))) * (PQ.1 - X * PQ.2))

theorem qspPoly_cons_eq_stepR (φ : ℝ) (Φ : List ℝ) : qspPoly (φ :: Φ) = stepR φ (qspPoly Φ) :=
  rfl

/-- QSP-7. The inverse of `stepR φ`, `R(x) e^{-iφσ_z}` on the first column:
`(P, Q) ↦ (e^{-iφ} X P + e^{iφ} (1 - X²) Q, e^{-iφ} P - e^{iφ} X Q)`. -/
noncomputable def unstepR (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (-(Complex.I * φ))) * (X * PQ.1) +
      C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * PQ.2),
    C (Complex.exp (-(Complex.I * φ))) * PQ.1 - C (Complex.exp (Complex.I * φ)) * (X * PQ.2))

theorem unstepR_fst (φ : ℝ) (P Q : ℂ[X]) :
    (unstepR φ (P, Q)).1 =
      C (Complex.exp (-(Complex.I * φ))) * (X * P) +
        C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * Q) := rfl

theorem unstepR_snd (φ : ℝ) (P Q : ℂ[X]) :
    (unstepR φ (P, Q)).2 =
      C (Complex.exp (-(Complex.I * φ))) * P - C (Complex.exp (Complex.I * φ)) * (X * Q) := rfl

/-- QSP-7. `stepR φ ∘ unstepR φ = id`. -/
theorem stepR_unstepR (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : stepR φ (unstepR φ PQ) = PQ := by
  have h := C_exp_mul_C_exp_neg φ
  obtain ⟨P, Q⟩ := PQ
  simp only [stepR, unstepR, Prod.mk.injEq]
  constructor
  · linear_combination P * h
  · linear_combination Q * h

/-- `stepR φ` is `ℂ`-linear: it commutes with a scalar factor. -/
theorem stepR_C_mul (φ : ℝ) (c : ℂ) (PQ : ℂ[X] × ℂ[X]) :
    stepR φ (C c * PQ.1, C c * PQ.2) = (C c * (stepR φ PQ).1, C c * (stepR φ PQ).2) := by
  simp only [stepR, Prod.mk.injEq]
  constructor <;> ring

/-- QSP-7. `unstepR φ` preserves `P P^* + (1 - X²) Q Q^*`. -/
theorem unstepR_unit (φ : ℝ) (P Q : ℂ[X]) :
    (unstepR φ (P, Q)).1 * conjP (unstepR φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepR φ (P, Q)).2 * conjP (unstepR φ (P, Q)).2 =
      P * conjP P + (1 - X ^ 2) * Q * conjP Q := by
  have h := C_exp_mul_C_exp_neg φ
  rw [unstepR_fst, unstepR_snd]
  simp only [conjP_mul, conjP_C, conjP_add, conjP_sub, conjP_X, conjP_pow, conjP_one,
    conj_exp_I_mul, conj_exp_neg_I_mul]
  linear_combination (P * conjP P + (1 - X ^ 2) * Q * conjP Q) * h

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the first component of `unstepR φ (P, Q)` has parity `n`. -/
theorem unstepR_fst_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepR φ (P, Q)).1 n := by
  rw [unstepR_fst]
  exact (hP.X_mul.of_add_two.C_mul _).add (hQ.one_sub_X_sq_mul.C_mul _)

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the second component of `unstepR φ (P, Q)` has parity
`n + 1`. -/
theorem unstepR_snd_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepR φ (P, Q)).2 (n + 1) := by
  rw [unstepR_snd]
  exact (hP.C_mul _).sub (hQ.X_mul.C_mul _)

/-- Crude degree bound for the first component of `unstepR`. -/
theorem natDegree_unstepR_fst_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepR φ (P, Q)).1.natDegree ≤ n + 1 + 1 := by
  have h1X2 : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 := by compute_degree
  rw [unstepR_fst]
  refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans ?_)
  · exact (natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega)
  · exact (natDegree_mul_le_of_le h1X2 hQ).trans (by omega)

/-- Crude degree bound for the second component of `unstepR`. -/
theorem natDegree_unstepR_snd_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepR φ (P, Q)).2.natDegree ≤ n + 1 := by
  rw [unstepR_snd]
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hP)
    ((natDegree_C_mul_le _ _).trans ?_))
  exact (natDegree_mul_le_of_le natDegree_X_le hQ).trans (by omega)

/-- The top coefficient of the first component of `unstepR φ (P, Q)` for `deg Q ≤ n`:
`e^{-iφ} p_{n+1} - e^{iφ} q_n`. -/
theorem coeff_unstepR_fst {P Q : ℂ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) (φ : ℝ) :
    (unstepR φ (P, Q)).1.coeff (n + 1 + 1) =
      Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) -
        Complex.exp (Complex.I * φ) * Q.coeff n := by
  rw [unstepR_fst, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, sub_mul, one_mul, coeff_sub,
    coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n + 1 + 1),
    show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul]
  ring

/-- The top coefficient of the second component of `unstepR φ (P, Q)`:
`e^{-iφ} p_{n+1} - e^{iφ} q_n`. -/
theorem coeff_unstepR_snd (P Q : ℂ[X]) (n : ℕ) (φ : ℝ) :
    (unstepR φ (P, Q)).2.coeff (n + 1) =
      Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) -
        Complex.exp (Complex.I * φ) * Q.coeff n := by
  rw [unstepR_snd, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-! ### The top coefficients -/

/-- QSP-7. The `X^{2n+2}` coefficient of `P P^* + (1 - X²) Q Q^* = 1` for `deg P ≤ n + 1`,
`deg Q ≤ n`: `p_{n+1} p̄_{n+1} = q_n q̄_n`. -/
theorem coeff_top_mul_conj_eq {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    P.coeff (n + 1) * (starRingEnd ℂ) (P.coeff (n + 1)) =
      Q.coeff n * (starRingEnd ℂ) (Q.coeff n) := by
  have h := congrArg (fun R : ℂ[X] => R.coeff (n + 1 + (n + 1))) hunit
  have hQQ : (Q * conjP Q).natDegree ≤ n + n :=
    natDegree_mul_le_of_le hQ ((natDegree_conjP_le Q).trans hQ)
  have h0 : (Q * conjP Q).coeff (n + 1 + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : (1 : ℂ[X]).coeff (n + 1 + (n + 1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by rw [natDegree_one]; omega)
  rw [coeff_add, coeff_mul_add_eq_of_natDegree_le hP ((natDegree_conjP_le P).trans hP),
    coeff_conjP, show (1 - X ^ 2) * Q * conjP Q = Q * conjP Q - X ^ 2 * (Q * conjP Q) by ring,
    coeff_sub, h0, h1, show n + 1 + (n + 1) = n + n + 2 by ring, coeff_X_pow_mul,
    coeff_mul_add_eq_of_natDegree_le hQ ((natDegree_conjP_le Q).trans hQ), coeff_conjP] at h
  linear_combination h

/-- QSP-7. Given `p p̄ = q q̄`, there is a phase `φ` with `e^{-iφ} p = e^{iφ} q`
(`φ = arg (p / q) / 2` if `q ≠ 0`, else `φ = 0`). -/
theorem exists_phase_coeff {p q : ℂ} (h : p * (starRingEnd ℂ) p = q * (starRingEnd ℂ) q) :
    ∃ φ : ℝ, Complex.exp (-(Complex.I * φ)) * p = Complex.exp (Complex.I * φ) * q := by
  by_cases hq : q = 0
  · refine ⟨0, ?_⟩
    have hp : p = 0 := by
      rw [hq, zero_mul, Complex.mul_conj] at h
      exact Complex.normSq_eq_zero.mp (by exact_mod_cast h)
    rw [hp, hq, mul_zero, mul_zero]
  · have hnorm : ‖p / q‖ = 1 := by
      rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hq)]
      rw [Complex.mul_conj', Complex.mul_conj'] at h
      exact (sq_eq_sq₀ (norm_nonneg p) (norm_nonneg q)).mp (by exact_mod_cast h)
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (p / q)).mp hnorm
    refine ⟨θ / 2, ?_⟩
    have hp : p = p / q * q := (div_mul_cancel₀ p hq).symm
    have hee : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) = p / q := by
      rw [← Complex.exp_add, ← hθ]
      congr 1
      push_cast
      ring
    have h1 := exp_I_mul_mul_exp_neg (θ / 2)
    linear_combination Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) * hp -
      (Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) * q) * hee +
      (Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) * q) * h1

/-! ### The existence theorem -/

/-- QSP-7c (reflection convention, up to a unimodular factor).  If (i) `deg P ≤ k`,
`deg Q ≤ k - 1` (with `Q = 0` for `k = 0`), (ii) `P` has parity `k` and `Q` parity `k - 1`, and
(iii) `P P^* + (1 - X²) Q Q^* = 1`, then there are `θ : ℝ` and `Φ : List ℝ` of length `k` with
`e^{iθ} qspPoly Φ = (P, Q)`. -/
theorem exists_phases_R_unimodular (k : ℕ) (P Q : ℂ[X]) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k - 1) (hQ0 : k = 0 → Q = 0) (hPpar : HasParity P k)
    (hQpar : HasParity Q (k - 1)) (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ θ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧
      (C (Complex.exp (Complex.I * θ)) * (qspPoly Φ).1,
        C (Complex.exp (Complex.I * θ)) * (qspPoly Φ).2) = (P, Q) := by
  induction k generalizing P Q with
  | zero =>
    obtain rfl := hQ0 rfl
    rw [eq_C_of_natDegree_le_zero hP] at hunit ⊢
    have hc : P.coeff 0 * (starRingEnd ℂ) (P.coeff 0) = 1 := by
      rw [conjP_C, conjP_zero, mul_zero, add_zero, ← C_mul, ← C_1, C_inj] at hunit
      exact hunit
    have hnorm : ‖P.coeff 0‖ = 1 := by
      rw [Complex.mul_conj'] at hc
      exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [one_pow]; exact_mod_cast hc)
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff _).mp hnorm
    refine ⟨θ, [], rfl, ?_⟩
    rw [qspPoly_nil, mul_one, mul_zero, ← hθ, mul_comm]
  | succ n ih =>
    rw [Nat.add_sub_cancel] at hQ hQpar
    obtain ⟨φ, hφ⟩ := exists_phase_coeff (coeff_top_mul_conj_eq hP hQ hunit)
    -- the lowered pair `(P̃, Q̃) = unstepR φ (P, Q)`
    have hPpar' : HasParity (unstepR φ (P, Q)).1 n := unstepR_fst_hasParity hPpar hQpar φ
    have hQpar' : HasParity (unstepR φ (P, Q)).2 (n + 1) := unstepR_snd_hasParity hPpar hQpar φ
    have hP' : (unstepR φ (P, Q)).1.natDegree ≤ n := by
      have h2 : (unstepR φ (P, Q)).1.natDegree ≤ n + 1 + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepR_fst_le hP hQ φ)
          (by rw [coeff_unstepR_fst hQ]; linear_combination hφ)
      rw [Nat.add_sub_cancel] at h2
      have h1 := natDegree_le_pred h2 (hPpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩)
      rwa [Nat.add_sub_cancel] at h1
    have hQn : (unstepR φ (P, Q)).2.coeff n = 0 :=
      hQpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩
    have hQ'' : (unstepR φ (P, Q)).2.natDegree ≤ n := by
      have h1 : (unstepR φ (P, Q)).2.natDegree ≤ n + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepR_snd_le hP hQ φ)
          (by rw [coeff_unstepR_snd]; linear_combination hφ)
      rwa [Nat.add_sub_cancel] at h1
    have hQ' : (unstepR φ (P, Q)).2.natDegree ≤ n - 1 := natDegree_le_pred hQ'' hQn
    have hQ0' : n = 0 → (unstepR φ (P, Q)).2 = 0 := by
      rintro rfl
      rw [eq_C_of_natDegree_le_zero hQ'', hQn, C_0]
    have hQpar'' : HasParity (unstepR φ (P, Q)).2 (n - 1) := by
      rcases n with _ | m
      · rw [hQ0' rfl]
        exact hasParity_zero _
      · rw [Nat.add_sub_cancel]
        exact hQpar'.of_add_two
    have hunit' : (unstepR φ (P, Q)).1 * conjP (unstepR φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepR φ (P, Q)).2 * conjP (unstepR φ (P, Q)).2 = 1 := by
      rw [unstepR_unit, hunit]
    obtain ⟨θ, Φ, hlen, hΦ⟩ := ih _ _ hP' hQ' hQ0' hPpar' hQpar'' hunit'
    refine ⟨θ, φ :: Φ, by rw [List.length_cons, hlen], ?_⟩
    rw [qspPoly_cons_eq_stepR, ← stepR_C_mul, hΦ]
    exact stepR_unstepR φ (P, Q)

/-- Adding `θ` to the head (latest) phase multiplies `P` by `e^{iθ}` and `Q` by `e^{-iθ}`. -/
theorem qspPoly_cons_add (φ θ : ℝ) (Φ : List ℝ) :
    qspPoly ((φ + θ) :: Φ) =
      (C (Complex.exp (Complex.I * θ)) * (qspPoly (φ :: Φ)).1,
        C (Complex.exp (-(Complex.I * θ))) * (qspPoly (φ :: Φ)).2) := by
  have h1 : Complex.exp (Complex.I * ((φ + θ : ℝ) : ℂ)) =
      Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * φ) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (-(Complex.I * ((φ + θ : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * θ)) * Complex.exp (-(Complex.I * φ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [qspPoly_cons, qspPoly_cons, h1, h2, C_mul, C_mul, mul_assoc, mul_assoc]

/-- QSP-7c (reflection convention, polynomial form).  For `k ≥ 1` and `(P, Q)` satisfying
(i)–(iii) of `exists_phases_R_unimodular`, there is a reflection-convention phase list `Φ` of
length `k` with `(qspPoly Φ).1 = P`; its second polynomial is `Q` up to a unimodular constant. -/
theorem exists_phases_R_poly (k : ℕ) (hk : 1 ≤ k) (P Q : ℂ[X]) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k - 1) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ Φ : List ℝ, Φ.length = k ∧ (qspPoly Φ).1 = P ∧
      ∃ θ : ℝ, (qspPoly Φ).2 = C (Complex.exp (Complex.I * θ)) * Q := by
  obtain ⟨θ, Φ, hlen, hΦ⟩ :=
    exists_phases_R_unimodular k P Q hP hQ (fun h => absurd h (by omega)) hPpar hQpar hunit
  obtain ⟨hΦ1, hΦ2⟩ := Prod.mk.inj hΦ
  obtain _ | ⟨φ, Ψ⟩ := Φ
  · rw [List.length_nil] at hlen
    omega
  refine ⟨(φ + θ) :: Ψ, by rw [List.length_cons, ← hlen, List.length_cons], ?_, -(2 * θ), ?_⟩
  · rw [qspPoly_cons_add, hΦ1]
  · have he : Complex.exp (-(Complex.I * θ)) =
        Complex.exp (Complex.I * ((-(2 * θ) : ℝ) : ℂ)) * Complex.exp (Complex.I * θ) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [qspPoly_cons_add, ← hΦ2, he, C_mul, mul_assoc]

/-- QSP-7c (reflection convention, matrix form; lean-qsvt `exists_phases_R`).  For `k ≥ 1` and
`(P, Q)` satisfying (i)–(iii), there is a phase list `Φ` of length `k` with
`(seqR Φ x) 0 0 = P(x)` for all `x ∈ [-1, 1]`. -/
theorem exists_phases_R (k : ℕ) (hk : 1 ≤ k) (P Q : ℂ[X]) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k - 1) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ Φ : List ℝ, Φ.length = k ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, (seqR Φ x) 0 0 = P.eval (x : ℂ) := by
  obtain ⟨Φ, hlen, hΦ, -⟩ := exists_phases_R_poly k hk P Q hP hQ hPpar hQpar hunit
  exact ⟨Φ, hlen, fun x hx => by rw [seqR_apply_zero_zero hx, hΦ]⟩

end MQSP.QSP
