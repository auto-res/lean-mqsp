/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.QSP.Complementary
import MQSP.QSP.Conversion
import MQSP.QSP.PolyW

/-!
# Existence of QSP phases, rotation convention (lean-qsvt QSP-7c/7d; GSLW Thm 3 "⇐", Cor 10)

Adapted from lean-qsvt (MIT, shosonoda), `QSVT/QSP/Existence.lean` (rotation-convention part)
and the rotation-convention corollary `exists_phases_real` of `QSVT/QSP/Complementary.lean`.

Given polynomials `P, Q ∈ ℂ[X]` with (i) `deg P ≤ k`, `deg Q ≤ k - 1`, (ii) parity `P ≡ k`,
`Q ≡ k - 1 (mod 2)`, and (iii) the polynomial identity `P P^* + (1 - X²) Q Q^* = 1`, there are
phases `φ₀` and `Φ = [φ₁, …, φ_k]` with `qspPolyW φ₀ Φ = (P, Q)`, i.e. by `seqW_eval`
`e^{iφ₀σ_z} ∏_j W(x) e^{iφ_jσ_z} = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]`
(`exists_phases_W`, lean-qsvt `exists_phases`).  The proof is GSLW's degree-lowering induction
(eqs. (6)–(8)) with the inverse step `unstepW`; the top-coefficient lemmas
`coeff_top_mul_conj_eq` and `exists_phase_coeff` are shared with the reflection-convention
proof in `MQSP.QSP.Existence`.

* `exists_phases_R_of_W` transports the result to the reflection convention through GSLW Cor 8
  (`seqW_apply_zero_zero_eq`; lean-qsvt `exists_phases_R`); `MQSP.QSP.exists_phases_R` is the
  direct proof.
* `exists_phases_W_real` (GSLW Cor 10, rotation convention; lean-qsvt `exists_phases_real`).
-/

open Polynomial

namespace MQSP.QSP

open Complex

/-! ### The inverse step (GSLW eqs. (7)–(8)) -/

/-- QSP-7. The inverse of `stepW φ` (GSLW eqs. (7)–(8)):
`(P, Q) ↦ (e^{-iφ} X P + e^{iφ} (1 - X²) Q, e^{iφ} X Q - e^{-iφ} P)`.  For every `φ`,
`stepW φ (unstepW φ (P, Q)) = (P, Q)` (`stepW_unstepW`). -/
noncomputable def unstepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  (C (Complex.exp (-(Complex.I * φ))) * (X * PQ.1) +
      C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * PQ.2),
    C (Complex.exp (Complex.I * φ)) * (X * PQ.2) - C (Complex.exp (-(Complex.I * φ))) * PQ.1)

theorem unstepW_fst (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).1 =
      C (Complex.exp (-(Complex.I * φ))) * (X * P) +
        C (Complex.exp (Complex.I * φ)) * ((1 - X ^ 2) * Q) := rfl

theorem unstepW_snd (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).2 =
      C (Complex.exp (Complex.I * φ)) * (X * Q) - C (Complex.exp (-(Complex.I * φ))) * P := rfl

/-- QSP-7. `stepW φ ∘ unstepW φ = id` (uses only `e^{iφ} e^{-iφ} = 1`, i.e. `x² + (1 - x²) = 1`
after expanding). -/
theorem stepW_unstepW (φ : ℝ) (PQ : ℂ[X] × ℂ[X]) : stepW φ (unstepW φ PQ) = PQ := by
  have h := C_exp_mul_C_exp_neg φ
  obtain ⟨P, Q⟩ := PQ
  simp only [stepW, unstepW, Prod.mk.injEq]
  constructor
  · linear_combination P * h
  · linear_combination Q * h

/-- QSP-7. `unstepW φ` preserves `P P^* + (1 - X²) Q Q^*`. -/
theorem unstepW_unit (φ : ℝ) (P Q : ℂ[X]) :
    (unstepW φ (P, Q)).1 * conjP (unstepW φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepW φ (P, Q)).2 * conjP (unstepW φ (P, Q)).2 =
      P * conjP P + (1 - X ^ 2) * Q * conjP Q := by
  have h := C_exp_mul_C_exp_neg φ
  rw [unstepW_fst, unstepW_snd]
  simp only [conjP_mul, conjP_C, conjP_add, conjP_sub, conjP_X, conjP_pow, conjP_one,
    conj_exp_I_mul, conj_exp_neg_I_mul]
  linear_combination (P * conjP P + (1 - X ^ 2) * Q * conjP Q) * h

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the first component of `unstepW φ (P, Q)` has parity `n`. -/
theorem unstepW_fst_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepW φ (P, Q)).1 n := by
  rw [unstepW_fst]
  exact (hP.X_mul.of_add_two.C_mul _).add (hQ.one_sub_X_sq_mul.C_mul _)

/-- QSP-7. If `P ≡ n + 1` and `Q ≡ n`, the second component of `unstepW φ (P, Q)` has parity
`n + 1`. -/
theorem unstepW_snd_hasParity {P Q : ℂ[X]} {n : ℕ} (hP : HasParity P (n + 1))
    (hQ : HasParity Q n) (φ : ℝ) : HasParity (unstepW φ (P, Q)).2 (n + 1) := by
  rw [unstepW_snd]
  exact (hQ.X_mul.C_mul _).sub (hP.C_mul _)

/-- Crude degree bound for the first component of `unstepW`. -/
theorem natDegree_unstepW_fst_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepW φ (P, Q)).1.natDegree ≤ n + 1 + 1 := by
  have h1X2 : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 := by compute_degree
  rw [unstepW_fst]
  refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans ?_)
  · exact (natDegree_mul_le_of_le natDegree_X_le hP).trans (by omega)
  · exact (natDegree_mul_le_of_le h1X2 hQ).trans (by omega)

/-- Crude degree bound for the second component of `unstepW`. -/
theorem natDegree_unstepW_snd_le {P Q : ℂ[X]} {n : ℕ} (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (φ : ℝ) : (unstepW φ (P, Q)).2.natDegree ≤ n + 1 := by
  rw [unstepW_snd]
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans ?_)
    ((natDegree_C_mul_le _ _).trans hP))
  exact (natDegree_mul_le_of_le natDegree_X_le hQ).trans (by omega)

/-- The top coefficient of the first component of `unstepW φ (P, Q)` for `deg Q ≤ n`:
`e^{-iφ} p_{n+1} - e^{iφ} q_n`. -/
theorem coeff_unstepW_fst {P Q : ℂ[X]} {n : ℕ} (hQ : Q.natDegree ≤ n) (φ : ℝ) :
    (unstepW φ (P, Q)).1.coeff (n + 1 + 1) =
      Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) -
        Complex.exp (Complex.I * φ) * Q.coeff n := by
  rw [unstepW_fst, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul, sub_mul, one_mul, coeff_sub,
    coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n + 1 + 1),
    show n + 1 + 1 = n + 2 from rfl, coeff_X_pow_mul]
  ring

/-- The top coefficient of the second component of `unstepW φ (P, Q)`:
`e^{iφ} q_n - e^{-iφ} p_{n+1}`. -/
theorem coeff_unstepW_snd (P Q : ℂ[X]) (n : ℕ) (φ : ℝ) :
    (unstepW φ (P, Q)).2.coeff (n + 1) =
      Complex.exp (Complex.I * φ) * Q.coeff n -
        Complex.exp (-(Complex.I * φ)) * P.coeff (n + 1) := by
  rw [unstepW_snd, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_X_mul]

/-! ### The existence theorem -/

/-- QSP-7c. Existence of QSP phases (GSLW Theorem 3, "⇐", rotation convention; lean-qsvt
`exists_phases`).  If
(i) `deg P ≤ k`, `deg Q ≤ k - 1` (with `Q = 0` for `k = 0`), (ii) `P` has parity `k` and `Q`
parity `k - 1`, and (iii) `P P^* + (1 - X²) Q Q^* = 1`, then there are `φ₀ : ℝ` and
`Φ : List ℝ` of length `k` with `qspPolyW φ₀ Φ = (P, Q)`; by `seqW_eval`,
`seqW φ₀ Φ x = [[P(x), i Q(x) s], [i Q^*(x) s, P^*(x)]]` on `[-1, 1]`. -/
theorem exists_phases_W (k : ℕ) (P Q : ℂ[X]) (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ k - 1)
    (hQ0 : k = 0 → Q = 0) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧ qspPolyW φ₀ Φ = (P, Q) := by
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
    exact ⟨θ, [], rfl, by rw [qspPolyW_nil, ← hθ, mul_comm]⟩
  | succ n ih =>
    rw [Nat.add_sub_cancel] at hQ hQpar
    obtain ⟨φ, hφ⟩ := exists_phase_coeff (coeff_top_mul_conj_eq hP hQ hunit)
    -- the lowered pair `(P̃, Q̃) = unstepW φ (P, Q)`
    have hPpar' : HasParity (unstepW φ (P, Q)).1 n := unstepW_fst_hasParity hPpar hQpar φ
    have hQpar' : HasParity (unstepW φ (P, Q)).2 (n + 1) := unstepW_snd_hasParity hPpar hQpar φ
    have hP' : (unstepW φ (P, Q)).1.natDegree ≤ n := by
      have h2 : (unstepW φ (P, Q)).1.natDegree ≤ n + 1 + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepW_fst_le hP hQ φ)
          (by rw [coeff_unstepW_fst hQ]; linear_combination hφ)
      rw [Nat.add_sub_cancel] at h2
      have h1 := natDegree_le_pred h2 (hPpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩)
      rwa [Nat.add_sub_cancel] at h1
    have hQn : (unstepW φ (P, Q)).2.coeff n = 0 :=
      hQpar'.coeff_eq_zero_of_odd_add ⟨n, by ring⟩
    have hQ'' : (unstepW φ (P, Q)).2.natDegree ≤ n := by
      have h1 : (unstepW φ (P, Q)).2.natDegree ≤ n + 1 - 1 :=
        natDegree_le_pred (natDegree_unstepW_snd_le hP hQ φ)
          (by rw [coeff_unstepW_snd]; linear_combination -hφ)
      rwa [Nat.add_sub_cancel] at h1
    have hQ' : (unstepW φ (P, Q)).2.natDegree ≤ n - 1 := natDegree_le_pred hQ'' hQn
    have hQ0' : n = 0 → (unstepW φ (P, Q)).2 = 0 := by
      rintro rfl
      rw [eq_C_of_natDegree_le_zero hQ'', hQn, C_0]
    have hQpar'' : HasParity (unstepW φ (P, Q)).2 (n - 1) := by
      rcases n with _ | m
      · rw [hQ0' rfl]
        exact hasParity_zero _
      · rw [Nat.add_sub_cancel]
        exact hQpar'.of_add_two
    have hunit' : (unstepW φ (P, Q)).1 * conjP (unstepW φ (P, Q)).1 +
        (1 - X ^ 2) * (unstepW φ (P, Q)).2 * conjP (unstepW φ (P, Q)).2 = 1 := by
      rw [unstepW_unit, hunit]
    obtain ⟨φ₀, Φ, hlen, hΦ⟩ := ih _ _ hP' hQ' hQ0' hPpar' hQpar'' hunit'
    refine ⟨φ₀, Φ ++ [φ], by rw [List.length_append, List.length_singleton, hlen], ?_⟩
    rw [qspPolyW_concat, hΦ]
    exact stepW_unstepW φ (P, Q)

/-! ### Transport to the reflection convention (GSLW Cor 8) -/

/-- QSP-7c, reflection convention via GSLW Cor 8 (`seqW_apply_zero_zero_eq`; lean-qsvt
`exists_phases_R`, here an alternative to the direct `MQSP.QSP.exists_phases_R`).  For `k ≥ 1` and
`(P, Q)` satisfying (i)–(iii) of `exists_phases`, there is a reflection-convention phase list
`Φ` of length `k` with `(seqR Φ x) 0 0 = P(x)` for all `x ∈ [-1, 1]`. -/
theorem exists_phases_R_of_W (k : ℕ) (hk : 1 ≤ k) (P Q : ℂ[X]) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k - 1) (hPpar : HasParity P k) (hQpar : HasParity Q (k - 1))
    (hunit : P * conjP P + (1 - X ^ 2) * Q * conjP Q = 1) :
    ∃ Φ : List ℝ, Φ.length = k ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, (seqR Φ x) 0 0 = P.eval (x : ℂ) := by
  obtain ⟨φ₀, Φ', hlen, hΦ'⟩ :=
    exists_phases_W k P Q hP hQ (fun h => absurd h (by omega)) hPpar hQpar hunit
  have hne : Φ' ≠ [] := by
    rintro rfl
    rw [List.length_nil] at hlen
    omega
  refine ⟨cor8Phases φ₀ Φ' hne, by rw [cor8Phases_length, hlen], fun x hx => ?_⟩
  rw [← seqW_apply_zero_zero_eq, seqW_apply_zero_zero hx, hΦ']

/-- QSP-7d (GSLW Cor 10, rotation convention; lean-qsvt `exists_phases_real`).  A real
polynomial `P̃` of degree `≤ k`, parity `k`, and `|P̃| ≤ 1` on `[-1, 1]` is the real part of the
QSP polynomial of some phase list `(φ₀, Φ)` of length `k`: `Re[(qspPolyW φ₀ Φ).1] = P̃`. -/
theorem exists_phases_W_real (k : ℕ) (Pr : ℝ[X]) (hP : Pr.natDegree ≤ k)
    (hPpar : HasParity (Pr.map (algebraMap ℝ ℂ)) k)
    (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pr.eval x ^ 2 ≤ 1) :
    ∃ φ₀ : ℝ, ∃ Φ : List ℝ, Φ.length = k ∧
      QSVT.rePoly (qspPolyW φ₀ Φ).1 = Pr.map (algebraMap ℝ ℂ) := by
  obtain ⟨P, Q, hPd, hQd, hQ0, hPp, hQp, hunit, hre⟩ := exists_complement k Pr hP hPpar hbound
  obtain ⟨φ₀, Φ, hlen, hΦ⟩ := exists_phases_W k P Q hPd hQd hQ0 hPp hQp hunit
  exact ⟨φ₀, Φ, hlen, by rw [hΦ]; exact hre⟩

end MQSP.QSP
