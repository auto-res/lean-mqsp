/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Poly.Basic
import MQSP.QSP.Chebyshev
import MQSP.QSP.ExistenceW

/-!
# Synthesis of QSVT phases (QSVT-2; GSLW Thm 3/4/5, Cor 8, Cor 10)

The converse of QSVT-3: every real polynomial `P` of parity `n mod 2`, degree `≤ n ≥ 1` and
`|P| ≤ 1` on `[-1, 1]` is the real part of the QSP polynomial of a phase list of length `n`
in the conventions of `MQSP.QSVT.Core` (`exists_phases`).

**Bridge to the reflection convention (no phase conversion).**  In the scalar case
`H = ℂ²`, `Pr = Pr' = |0⟩⟨0|`, `U = R(x) = [[x, s], [s, -x]]` (`s = √(1-x²)`), the phase
operator is `e^{iφ(2Pr-1)} = e^{iφσ_z}` and `U† = U`, so every step of `U_Φ` is `e^{iφσ_z} R(x)`
and `U_Φ = seqR Φ.reverse x` (time order reversed: the head of a `seqR` list is the latest
factor).  The two-block shape of `MQSP.QSVT.Shape` reads `V|0⟩ = p(x²)|0⟩ + x q(x²) s|1⟩` after
an even and `V|0⟩ = x p(x²)|0⟩ + q(x²) s|1⟩` after an odd number of steps.  Accordingly,
`liftPQ k (p, q)` is `(p(X²), X q(X²))` for even `k` and `(X p(X²), q(X²))` for odd `k`, and
the `y = x²` recursion `pqStep` is intertwined with the reflection step `MQSP.QSP.stepR`
(`liftPQ_pqStep`), with *the same phases*; hence (`qspPoly_reverse`)

  `qspPoly Φ.reverse = liftPQ |Φ| (pqΦ Φ)`,

so `(qspPoly Φ.reverse).1 = X^{|Φ| mod 2} p_Φ(X²)` and `(seqR Φ.reverse x)₀₀ = x^{|Φ| mod 2}
p_Φ(x²)` on `[-1, 1]` (`seqR_reverse_apply_zero_zero`), with real part
`x^{|Φ| mod 2} Re[p_Φ](x²)` (`re_seqR_reverse_apply_zero_zero`).

Further consequences in our conventions: `|P_Φ| ≤ 1` on `[-1, 1]`
(`norm_eval_qspScalar_le_one`, GSLW Thm 3 "⇒"); the time-ordered Chebyshev phases
`(π/2, …, π/2, (1-d)π/2)` realise `T_d` (`qspScalar_chebPhases_reverse`, GSLW Lemma 9);
rotation-convention phases `(φ₀; Φ')` (the output of the usual phase solvers) are turned into
ours by `(cor8Phases φ₀ Φ').reverse` (`qspScalar_cor8Phases_reverse`, GSLW Cor 8: the
conversion `W(x) = i e^{-iπσ_z/4} R(x) e^{-iπσ_z/4}` shifts the phases by `-π/2`, the first one
by `φ₀ + φ'_d + (d-1)π/2`).

**Synthesis.**  `MQSP.QSP.exists_phases_R_poly_real` (GSLW Cor 10 via Lemma 6 and Thm 5, ported
from lean-qsvt) gives `Ψ` with `Re[(qspPoly Ψ).1] = P`; `Φ := Ψ.reverse` works
(`exists_phases`; scalar forms `exists_phases_eval`, `exists_phases_seqR`).  Combined with
GSLW Cor 18 (`proj_average_proj_odd/even`) this is the QSVT of a projected unitary encoding by
an arbitrary real polynomial of definite parity bounded by `1`
(`exists_phases_proj_average_proj_odd/even`).

The hypothesis `1 ≤ n` is necessary (as in GSLW Cor 10): with no phases `p_Φ = 1`
(`not_exists_phases_zero`).
-/

namespace MQSP

open Polynomial

namespace QSVT

/-! ### The bridge between the `y = x²` recursion and the reflection convention -/

/-- The reflection-convention pair `(P, Q)` attached to the pair `(p, q)` in `y = x²` after `k`
steps: `(p(X²), X q(X²))` for even `k`, `(X p(X²), q(X²))` for odd `k`. -/
noncomputable def liftPQ (k : ℕ) (st : ℂ[X] × ℂ[X]) : ℂ[X] × ℂ[X] :=
  if k % 2 = 0 then (st.1.comp (X ^ 2), X * st.2.comp (X ^ 2))
  else (X * st.1.comp (X ^ 2), st.2.comp (X ^ 2))

/-- QSVT-2 (bridge). One step of the `y = x²` recursion is one reflection step, same phase. -/
theorem liftPQ_pqStep (k : ℕ) (φ : ℝ) (st : ℂ[X] × ℂ[X]) :
    liftPQ (k + 1) (pqStep k φ st) = QSP.stepR φ (liftPQ k st) := by
  have he : Complex.exp (φ * Complex.I) = Complex.exp (Complex.I * φ) := by rw [mul_comm]
  have he' : Complex.exp (-(φ * Complex.I)) = Complex.exp (-(Complex.I * φ)) := by
    rw [mul_comm]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have hk1 : ¬ (k + 1) % 2 = 0 := by omega
    rw [liftPQ, liftPQ, ite_eq_right hk1, ite_eq_left hk, pqStep, ite_eq_left hk]
    simp only [QSP.stepR, he, he', mul_comp, add_comp, sub_comp, C_comp, X_comp, Prod.mk.injEq]
    constructor <;> ring
  · have hk0 : ¬ k % 2 = 0 := by omega
    have hk1 : (k + 1) % 2 = 0 := by omega
    rw [liftPQ, liftPQ, ite_eq_left hk1, ite_eq_right hk0, pqStep, ite_eq_right hk0]
    simp only [QSP.stepR, he, he', mul_comp, add_comp, sub_comp, C_comp, X_comp, Prod.mk.injEq]
    constructor <;> ring

theorem qspPoly_reverse_append (Φ : List ℝ) :
    ∀ (k : ℕ) (st : ℂ[X] × ℂ[X]) (L : List ℝ), QSP.qspPoly L = liftPQ k st →
      QSP.qspPoly (Φ.reverse ++ L) = liftPQ (k + Φ.length) (pqFrom Φ k st) := by
  induction Φ with
  | nil =>
    intro k st L h
    rw [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero, pqFrom]
    exact h
  | cons φ Φ ih =>
    intro k st L h
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, pqFrom, List.length_cons,
      show k + (Φ.length + 1) = k + 1 + Φ.length by omega]
    exact ih (k + 1) _ (φ :: L) (by rw [QSP.qspPoly_cons_eq_stepR, h, liftPQ_pqStep])

/-- QSVT-2 (bridge, GSLW Cor 8 in our conventions). The reflection-convention polynomials of the
reversed phase list are the lift of `pqΦ Φ`: `qspPoly Φ.reverse = liftPQ |Φ| (pqΦ Φ)`. -/
theorem qspPoly_reverse (Φ : List ℝ) : QSP.qspPoly Φ.reverse = liftPQ Φ.length (pqΦ Φ) := by
  have h := qspPoly_reverse_append Φ 0 (1, 0) [] (by simp [liftPQ])
  rwa [List.append_nil, Nat.zero_add] at h

/-- QSVT-2. The scalar polynomial realised by `Φ`: `P_Φ(x) = x^{|Φ| mod 2} p_Φ(x²)`
(the singular value transformation of `proj_UΦ_proj_odd` / `proj_UΦ_proj_even`). -/
noncomputable def qspScalar (Φ : List ℝ) : ℂ[X] := X ^ (Φ.length % 2) * (pqΦ Φ).1.comp (X ^ 2)

theorem liftPQ_fst (k : ℕ) (st : ℂ[X] × ℂ[X]) :
    (liftPQ k st).1 = X ^ (k % 2) * st.1.comp (X ^ 2) := by
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · rw [liftPQ, ite_eq_left hk, hk, pow_zero, one_mul]
  · rw [liftPQ, ite_eq_right (by omega), hk, pow_one]

/-- QSVT-2 (forward identification). `(qspPoly Φ.reverse).1 = P_Φ`. -/
theorem qspPoly_reverse_fst (Φ : List ℝ) : (QSP.qspPoly Φ.reverse).1 = qspScalar Φ := by
  rw [qspPoly_reverse, liftPQ_fst, qspScalar]

theorem eval_qspScalar (Φ : List ℝ) (z : ℂ) :
    (qspScalar Φ).eval z = z ^ (Φ.length % 2) * (pqΦ Φ).1.eval (z ^ 2) := by
  rw [qspScalar, eval_mul, eval_pow, eval_X, eval_comp, eval_pow, eval_X]

/-- QSVT-2 (forward identification, matrix form). The top-left entry of the
reflection-convention product `∏ e^{iφ_j σ_z} R(x)` over the reversed list is
`x^{|Φ| mod 2} p_Φ(x²)`. -/
theorem seqR_reverse_apply_zero_zero (Φ : List ℝ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    QSP.seqR Φ.reverse x 0 0 = (x : ℂ) ^ (Φ.length % 2) * (pqΦ Φ).1.eval ((x : ℂ) ^ 2) := by
  rw [QSP.seqR_apply_zero_zero hx, qspPoly_reverse_fst, eval_qspScalar]

/-- `Re` commutes with `p ↦ p(X²)`. -/
theorem rePoly_comp_X_sq (p : ℂ[X]) : rePoly (p.comp (X ^ 2)) = (rePoly p).comp (X ^ 2) := by
  rw [rePoly, rePoly, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X, mul_comp,
    C_comp, add_comp]

/-- `Re` commutes with multiplication by `X`. -/
theorem rePoly_X_pow_mul (m : ℕ) (p : ℂ[X]) : rePoly (X ^ m * p) = X ^ m * rePoly p := by
  rw [rePoly, rePoly, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  ring

theorem rePoly_qspScalar (Φ : List ℝ) :
    rePoly (qspScalar Φ) = X ^ (Φ.length % 2) * (rePoly (pqΦ Φ).1).comp (X ^ 2) := by
  rw [qspScalar, rePoly_X_pow_mul, rePoly_comp_X_sq]

/-- QSVT-2 (forward identification, real part). Our `rePoly (pqΦ Φ).1` is the real part of the
top-left entry of the reflection-convention product over the reversed list:
`Re (seqR Φ.reverse x)₀₀ = x^{|Φ| mod 2} Re[p_Φ](x²)` on `[-1, 1]`. -/
theorem re_seqR_reverse_apply_zero_zero (Φ : List ℝ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (((QSP.seqR Φ.reverse x 0 0).re : ℝ) : ℂ) =
      (x : ℂ) ^ (Φ.length % 2) * (rePoly (pqΦ Φ).1).eval ((x : ℂ) ^ 2) := by
  rw [QSP.seqR_apply_zero_zero hx, qspPoly_reverse_fst, ← QSP.eval_rePoly_ofReal,
    rePoly_qspScalar, eval_mul, eval_pow, eval_X, eval_comp, eval_pow, eval_X]

/-- Two complex polynomials agreeing at the real points of `[-1, 1]` are equal. -/
theorem eq_of_eval_Icc {p q : ℂ[X]}
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p.eval (x : ℂ) = q.eval (x : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono ?_ (Set.Infinite.image Complex.ofReal_injective.injOn
    (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)))
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

/-- QSVT-2 (GSLW Cor 8 in our conventions: rotation-convention phases). Rotation-convention
phases `(φ₀; φ'_1, …, φ'_d)`, `d ≥ 1` (the output format of the usual phase solvers), give the
time-ordered phase list `(cor8Phases φ₀ Φ').reverse` of our convention with the same scalar
polynomial: `P_Φ = (qspPolyW φ₀ Φ').1`. -/
theorem qspScalar_cor8Phases_reverse (φ₀ : ℝ) {Φ' : List ℝ} (hΦ : Φ' ≠ []) :
    qspScalar (QSP.cor8Phases φ₀ Φ' hΦ).reverse = (QSP.qspPolyW φ₀ Φ').1 := by
  rw [← qspPoly_reverse_fst, List.reverse_reverse]
  refine eq_of_eval_Icc fun x hx => ?_
  rw [← QSP.seqR_apply_zero_zero hx, ← QSP.seqW_apply_zero_zero_eq, QSP.seqW_apply_zero_zero hx]

/-! ### Consequences in our conventions: the bound and the Chebyshev phases -/

/-- QSVT-2 (GSLW Thm 3 "⇒", bound). `|P_Φ(x)| ≤ 1` on `[-1, 1]`, from the unit identity
`|P(x)|² + (1 - x²)|Q(x)|² = 1` of the reflection convention. -/
theorem norm_eval_qspScalar_le_one (Φ : List ℝ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(qspScalar Φ).eval (x : ℂ)‖ ≤ 1 := by
  have h := QSP.norm_identity hx Φ.reverse
  rw [qspPoly_reverse_fst] at h
  have h0 : 0 ≤ (1 - x ^ 2) * ‖(QSP.qspPoly Φ.reverse).2.eval (x : ℂ)‖ ^ 2 :=
    mul_nonneg (by nlinarith [hx.1, hx.2]) (sq_nonneg _)
  nlinarith [norm_nonneg ((qspScalar Φ).eval (x : ℂ))]

/-- QSVT-2 (GSLW Lemma 9 in our conventions). The time-ordered phases
`(π/2, …, π/2, (1-d)π/2)` (the reversal of `QSP.chebPhases d`) realise the Chebyshev polynomial:
`P_Φ = x^{d mod 2} p_Φ(x²) = T_d`. -/
theorem qspScalar_chebPhases_reverse (d : ℕ) :
    qspScalar (QSP.chebPhases d).reverse = Chebyshev.T ℂ d := by
  rw [← qspPoly_reverse_fst, List.reverse_reverse]
  exact eq_of_eval_Icc fun x hx => by rw [← QSP.seqR_apply_zero_zero hx, QSP.seqR_chebPhases hx]

/-! ### Real polynomials with parity -/

theorem isEven_map_of_isEven {P : ℝ[X]} (h : MQSP.Poly.IsEven P) :
    QSP.IsEven (P.map (algebraMap ℝ ℂ)) := fun k hk => by
  rw [coeff_map, h k (Nat.odd_iff.mp hk), map_zero]

theorem isOdd_map_of_isOdd {P : ℝ[X]} (h : MQSP.Poly.IsOdd P) :
    QSP.IsOdd (P.map (algebraMap ℝ ℂ)) := fun k hk => by
  rw [coeff_map, h k (Nat.even_iff.mp hk), map_zero]

theorem eq_evenCore_comp {P : ℝ[X]} (h : MQSP.Poly.IsEven P) :
    P = (MQSP.Poly.evenCore P).comp (X ^ 2) :=
  Polynomial.funext fun x => by rw [eval_comp, eval_pow, eval_X, MQSP.Poly.IsEven.eval_eq P h]

theorem eq_X_mul_oddCore_comp {P : ℝ[X]} (h : MQSP.Poly.IsOdd P) :
    P = X * (MQSP.Poly.oddCore P).comp (X ^ 2) :=
  Polynomial.funext fun x => by
    rw [eval_mul, eval_X, eval_comp, eval_pow, eval_X, MQSP.Poly.IsOdd.eval_eq P h]

theorem map_comp_X_sq (p : ℝ[X]) :
    (p.comp (X ^ 2)).map (algebraMap ℝ ℂ) = (p.map (algebraMap ℝ ℂ)).comp (X ^ 2) := by
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]

theorem comp_X_sq_injective {p q : ℂ[X]} (h : p.comp (X ^ 2) = q.comp (X ^ 2)) : p = q := by
  rw [← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow] at h
  exact expand_injective two_pos h

/-! ### The synthesis theorem -/

/-- QSVT-2 (GSLW Cor 10 / Thm 5): every real polynomial of parity `n mod 2`, degree `≤ n`,
bounded by `1` on `[-1, 1]`, is the real part of the QSP polynomial of some phase list of
length `n`.  The hypothesis `1 ≤ n` (as in GSLW Cor 10) cannot be dropped
(`not_exists_phases_zero`). -/
theorem exists_phases (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) (hdeg : P.natDegree ≤ n)
    (hpar : if n % 2 = 0 then MQSP.Poly.IsEven P else MQSP.Poly.IsOdd P)
    (hb : MQSP.Poly.BoundedOn P (Set.Icc (-1) 1) 1) :
    ∃ Φ : List ℝ, Φ.length = n ∧
      rePoly (pqΦ Φ).1 =
        (if n % 2 = 0 then MQSP.Poly.evenCore P else MQSP.Poly.oddCore P).map (algebraMap ℝ ℂ) := by
  have hpar' : QSP.HasParity (P.map (algebraMap ℝ ℂ)) n := by
    split_ifs at hpar with hn2
    · exact (isEven_map_of_isEven hpar).hasParity (Nat.even_iff.mpr hn2)
    · exact (isOdd_map_of_isOdd hpar).hasParity (Nat.odd_iff.mpr (by omega))
  have hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, P.eval x ^ 2 ≤ 1 := by
    intro x hx
    have h := abs_le.mp (hb x hx)
    nlinarith [h.1, h.2]
  obtain ⟨Ψ, hlen, hΨ⟩ := QSP.exists_phases_R_poly_real n hn P hdeg hpar' hbound
  refine ⟨Ψ.reverse, by rw [List.length_reverse, hlen], ?_⟩
  rw [← List.reverse_reverse Ψ, qspPoly_reverse_fst, rePoly_qspScalar, List.length_reverse,
    hlen] at hΨ
  split_ifs at hpar ⊢ with hn2
  · rw [hn2, pow_zero, one_mul] at hΨ
    rw [eq_evenCore_comp hpar, map_comp_X_sq] at hΨ
    exact comp_X_sq_injective hΨ
  · rw [show n % 2 = 1 by omega, pow_one] at hΨ
    rw [eq_X_mul_oddCore_comp hpar, Polynomial.map_mul, Polynomial.map_X, map_comp_X_sq] at hΨ
    exact comp_X_sq_injective (mul_left_cancel₀ X_ne_zero hΨ)

/-- QSVT-2, scalar form: for the phases of `exists_phases`,
`Re P_Φ(x) = x^{n mod 2} Re[p_Φ](x²) = P(x)` on `[-1, 1]` (indeed on all of `ℝ`). -/
theorem exists_phases_eval (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) (hdeg : P.natDegree ≤ n)
    (hpar : if n % 2 = 0 then MQSP.Poly.IsEven P else MQSP.Poly.IsOdd P)
    (hb : MQSP.Poly.BoundedOn P (Set.Icc (-1) 1) 1) :
    ∃ Φ : List ℝ, Φ.length = n ∧ ∀ x : ℝ,
      (x : ℂ) ^ (n % 2) * (rePoly (pqΦ Φ).1).eval ((x : ℂ) ^ 2) = ((P.eval x : ℝ) : ℂ) := by
  obtain ⟨Φ, hlen, hΦ⟩ := exists_phases P n hn hdeg hpar hb
  refine ⟨Φ, hlen, fun x => ?_⟩
  have hmap : ∀ p : ℝ[X],
      (p.map (algebraMap ℝ ℂ)).eval ((x : ℂ) ^ 2) = ((p.eval (x ^ 2) : ℝ) : ℂ) :=
    fun p => by rw [← Complex.ofReal_pow, QSP.eval_map_algebraMap_ofReal]
  rw [hΦ]
  split_ifs at hpar ⊢ with hn2
  · rw [hn2, pow_zero, one_mul, hmap, ← MQSP.Poly.IsEven.eval_eq P hpar]
  · rw [show n % 2 = 1 by omega, pow_one, hmap, MQSP.Poly.IsOdd.eval_eq P hpar,
      Complex.ofReal_mul]

/-- QSVT-2 (forward identification of the synthesised phases): the reflection-convention
product over the reversed list has `Re (seqR Φ.reverse x)₀₀ = P(x)` on `[-1, 1]`. -/
theorem exists_phases_seqR (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n) (hdeg : P.natDegree ≤ n)
    (hpar : if n % 2 = 0 then MQSP.Poly.IsEven P else MQSP.Poly.IsOdd P)
    (hb : MQSP.Poly.BoundedOn P (Set.Icc (-1) 1) 1) :
    ∃ Φ : List ℝ, Φ.length = n ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (QSP.seqR Φ.reverse x 0 0).re = P.eval x := by
  obtain ⟨Φ, hlen, hΦ⟩ := exists_phases_eval P n hn hdeg hpar hb
  refine ⟨Φ, hlen, fun x hx => ?_⟩
  have h := re_seqR_reverse_apply_zero_zero Φ hx
  rw [hlen, hΦ x] at h
  exact_mod_cast h

/-- The hypothesis `1 ≤ n` of `exists_phases` is necessary: for `n = 0` the only phase list is
`[]`, with `p_Φ = 1`, so the constant `1/2` is not realised. -/
theorem not_exists_phases_zero :
    ¬ ∃ Φ : List ℝ, Φ.length = 0 ∧
      rePoly (pqΦ Φ).1 = (MQSP.Poly.evenCore (C (1 / 2 : ℝ))).map (algebraMap ℝ ℂ) := by
  rintro ⟨Φ, hlen, h⟩
  rw [List.length_eq_zero_iff] at hlen
  subst hlen
  have h0 := congrArg (fun p : ℂ[X] => p.coeff 0) h
  simp [pqΦ, pqFrom, rePoly, MQSP.Poly.evenCore] at h0

/-! ### Operator form: QSVT by an arbitrary real polynomial (GSLW Cor 10 + Cor 18 + Thm 17) -/

section Operator

universe u

variable {H : Type u} [HSpace H]

/-- QSVT-2 + QSVT-3 (odd case). For a projected unitary encoding `A = Pr' U Pr` and a real odd
polynomial `P` of degree `≤ n` (`n` odd) with `|P| ≤ 1` on `[-1, 1]`, there are `n` phases with
`Pr' (U_Φ + U_{-Φ})/2 Pr = A ∘ p(A†A)`, `P(x) = x p(x²)`: the singular value transformation
of `A` by `P`. -/
theorem exists_phases_proj_average_proj_odd {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U)
    (hPr : IsProj Pr) (hPr' : IsProj Pr') (P : Polynomial ℝ) (n : ℕ) (hn : n % 2 = 1)
    (hdeg : P.natDegree ≤ n) (hpar : MQSP.Poly.IsOdd P)
    (hb : MQSP.Poly.BoundedOn P (Set.Icc (-1) 1) 1) :
    ∃ Φ : List ℝ, Φ.length = n ∧
      Pr' ∘L ((2 : ℂ)⁻¹ • (UΦ U Pr Pr' Φ + UΦ U Pr Pr' (Φ.map Neg.neg))) ∘L Pr =
        enc U Pr Pr' ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr')
          ((MQSP.Poly.oddCore P).map (algebraMap ℝ ℂ)) := by
  have hn0 : ¬ n % 2 = 0 := by omega
  obtain ⟨Φ, hlen, hΦ⟩ :=
    exists_phases P n (by omega) hdeg (by rw [ite_eq_right hn0]; exact hpar) hb
  rw [ite_eq_right hn0] at hΦ
  refine ⟨Φ, hlen, ?_⟩
  rw [proj_average_proj_odd hU hPr hPr' Φ (by rw [hlen]; exact hn), hΦ]

/-- QSVT-2 + QSVT-3 (even case). For a real even polynomial `P` of degree `≤ n` (`n ≥ 2` even)
with `|P| ≤ 1` on `[-1, 1]`, there are `n` phases with
`Pr (U_Φ + U_{-Φ})/2 Pr = Pr ∘ p(A†A) ∘ Pr`, `P(x) = p(x²)`. -/
theorem exists_phases_proj_average_proj_even {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U)
    (hPr : IsProj Pr) (hPr' : IsProj Pr') (P : Polynomial ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hn2 : n % 2 = 0) (hdeg : P.natDegree ≤ n) (hpar : MQSP.Poly.IsEven P)
    (hb : MQSP.Poly.BoundedOn P (Set.Icc (-1) 1) 1) :
    ∃ Φ : List ℝ, Φ.length = n ∧
      Pr ∘L ((2 : ℂ)⁻¹ • (UΦ U Pr Pr' Φ + UΦ U Pr Pr' (Φ.map Neg.neg))) ∘L Pr =
        Pr ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr')
          ((MQSP.Poly.evenCore P).map (algebraMap ℝ ℂ)) ∘L Pr := by
  obtain ⟨Φ, hlen, hΦ⟩ := exists_phases P n hn hdeg (by rw [ite_eq_left hn2]; exact hpar) hb
  rw [ite_eq_left hn2] at hΦ
  refine ⟨Φ, hlen, ?_⟩
  rw [proj_average_proj_even hU hPr hPr' Φ (by rw [hlen]; exact hn2), hΦ]

end Operator

end QSVT

end MQSP
