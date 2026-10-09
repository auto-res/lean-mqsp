/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.CPE.Signal
import MQSP.CPE.Stitch
import MQSP.Poly.Approx

/-!
# Estimator specifications and one-bit extraction (CPE-0, CPE-2; Rall Def 1, 2, Lemma 10/11)

* `RoundingPromise n α θ`: the phase `θ/(2π) ∈ [0,1)` is `α`-far from every `n`-bit rounding
  boundary (Rall Def 1): the `k`-th bit of `θ/(2π)` is well defined for every `k < n`.
* `bit k θ`: the `k`-th binary digit of `θ/(2π)`.
* One-bit extraction: with the amplifying polynomial `A_{η→δ}` applied through the QSVT of the
  phase signal of `U^{2^{n-k-1}}` (whose eigenphase is `2^{n-k-1} θ`), each eigenvector is sent
  to itself times a scalar which is `≥ 1 - δ` or `≤ δ` according to the bit; this is the
  per-eigenspace content of Rall Lemma 10/11, stated here from `CPE.proj_UΦ_plus_eigen` and
  `Poly.exists_amplifier`.
-/

namespace MQSP

universe u

open Polynomial

namespace CPE

/-- The fractional phase `θ/(2π) mod 1`. -/
noncomputable def frac (θ : ℝ) : ℝ := Int.fract (θ / (2 * Real.pi))

/-- The `k`-th binary digit (`k = 0` is the most significant) of the fractional phase, in the
rounding convention (the bits of the nearest `(k+1)`-bit rounding of `frac θ`). -/
noncomputable def bit (k : ℕ) (θ : ℝ) : ℕ := ⌊frac θ * 2 ^ (k + 1) + 1 / 2⌋₊ % 2

/-- CPE-0 (Rall Def 1). The `n`-bit rounding promise with margin `α`: the fractional phase is
at distance at least `α / 2^n` from every multiple of `2^{-n}`… in the form used by the bit
extraction: for every `k < n`, `2^k · frac θ` is at distance `≥ α/2` from `ℤ + 1/2`. -/
def RoundingPromise (n : ℕ) (α θ : ℝ) : Prop :=
  ∀ k < n, ∀ m : ℤ, α ≤ |2 ^ (k + 1) * frac θ - (m + 1 / 2)|

/-- The `cos²` signal in rounding-parity form: if `2x` is `α`-far from `ℤ + 1/2` (`α ≥ 0`), then
`cos²(π x) ≥ 1/2 + sin(πα)/2` when the integer nearest to `2x` is even and
`cos²(π x) ≤ 1/2 - sin(πα)/2` when it is odd. -/
theorem cos_sq_of_round_parity {α x : ℝ} (hα : 0 ≤ α) (hp : ∀ m : ℤ, α ≤ |2 * x - (m + 1 / 2)|) :
    (round (2 * x) % 2 = 0 → 1 / 2 + Real.sin (Real.pi * α) / 2 ≤ Real.cos (Real.pi * x) ^ 2) ∧
    (round (2 * x) % 2 = 1 →
      Real.cos (Real.pi * x) ^ 2 ≤ 1 / 2 - Real.sin (Real.pi * α) / 2) := by
  set r := round (2 * x)
  have hd1 : |2 * x - r| ≤ 1 / 2 := abs_sub_round _
  have h1 := hp r
  have h2 := hp (r - 1)
  have e1 : 2 * x - ((r : ℝ) + 1 / 2) = (2 * x - r) - 1 / 2 := by ring
  have e2 : 2 * x - (((r - 1 : ℤ) : ℝ) + 1 / 2) = (2 * x - r) + 1 / 2 := by push_cast; ring
  rw [abs_le] at hd1
  rw [e1, abs_of_nonpos (by linarith)] at h1
  rw [e2, abs_of_nonneg (by linarith)] at h2
  have hd2 : |2 * x - r| ≤ 1 / 2 - α := abs_le.2 ⟨by linarith, by linarith⟩
  have hc : Real.sin (Real.pi * α) ≤ Real.cos (Real.pi * (2 * x - r)) := by
    rw [← Real.cos_abs, abs_mul, abs_of_pos Real.pi_pos, ← Real.cos_pi_div_two_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi * x) ^ 2 =
      1 / 2 + (-1) ^ r * Real.cos (Real.pi * (2 * x - r)) / 2 := by
    rw [Real.cos_sq, ← Real.cos_add_int_mul_pi]
    congr 3
    ring
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcos, (Int.even_iff.2 h).neg_one_zpow]
    linarith
  · rw [hcos, (Int.odd_iff.2 h).neg_one_zpow]
    linarith

/-- The signal `cos²(π 2^k frac θ)` is the `cos²(2^k θ / 2)` read by `bit_extraction`. -/
theorem cos_sq_frac (k : ℕ) (θ : ℝ) :
    Real.cos (Real.pi * 2 ^ k * frac θ) ^ 2 = Real.cos (2 ^ k * θ / 2) ^ 2 := by
  rw [Real.cos_sq, Real.cos_sq]
  have h : 2 * (Real.pi * 2 ^ k * frac θ) =
      2 * (2 ^ k * θ / 2) - ((2 ^ k * ⌊θ / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [frac, Int.fract]
    push_cast
    field_simp
  rw [h, Real.cos_sub_int_mul_two_pi]

/-- Corrected form of `cos_sq_of_bit` (the version below is false as stated, see its
docstring): with the *rounded* bit `⌊2^{k+1} frac θ + 1/2⌋ mod 2` (parity of the integer nearest
to `2^{k+1} frac θ`) and the promise that `2^{k+1} frac θ` is `α`-far from `ℤ + 1/2`,
`cos²(π 2^k frac θ)` is `≥ 1/2 + sin(πα)/2` for bit `0` and `≤ 1/2 - sin(πα)/2` for bit `1`. -/
theorem cos_sq_of_bit_round {n : ℕ} {α θ : ℝ} (hα : 0 ≤ α)
    (hp : ∀ k < n, ∀ m : ℤ, α ≤ |2 ^ (k + 1) * frac θ - (m + 1 / 2)|) {k : ℕ} (hk : k < n) :
    (⌊frac θ * 2 ^ (k + 1) + 1 / 2⌋₊ % 2 = 0 →
      1 / 2 + Real.sin (Real.pi * α) / 2 ≤ Real.cos (Real.pi * 2 ^ k * frac θ) ^ 2) ∧
    (⌊frac θ * 2 ^ (k + 1) + 1 / 2⌋₊ % 2 = 1 →
      Real.cos (Real.pi * 2 ^ k * frac θ) ^ 2 ≤ 1 / 2 - Real.sin (Real.pi * α) / 2) := by
  have h2 : 2 * (2 ^ k * frac θ) = frac θ * 2 ^ (k + 1) := by ring
  have hf : 0 ≤ frac θ := Int.fract_nonneg _
  have hr : round (2 * (2 ^ k * frac θ)) = (⌊frac θ * 2 ^ (k + 1) + 1 / 2⌋₊ : ℤ) := by
    rw [round_eq, h2, Int.natCast_floor_eq_floor (by positivity)]
  have H := cos_sq_of_round_parity (x := 2 ^ k * frac θ) hα (fun m => by
    rw [h2, mul_comm]; exact hp k hk m)
  rw [hr, ← mul_assoc] at H
  exact ⟨fun h => H.1 (by omega), fun h => H.2 (by omega)⟩

/-- Under the promise, `cos²(π 2^k frac θ)` is bounded away from `1/2` on the side of the bit:
`bit k θ = 0 → cos² ≥ 1/2 + η`, `bit k θ = 1 → cos² ≤ 1/2 - η` for `η = sin(π α)/2`
(the signal of the `k`-th bit).

WIP (`sorry`): false as stated. Counterexample `n = 1`, `k = 0`, `α = 1/2`, `θ = π/2`:
`frac θ = 1/4`, the promise holds (`|m + 1/4| ≥ 1/4`), `bit 0 θ = ⌊1/2⌋ % 2 = 0`, but
`cos²(π/4) = 1/2 < 1 = 1/2 + sin(π/2)/2`. The floor bit flips at `frac(2^k frac θ) = 0`, which the
promise does not exclude, while `cos²` only sees the rounded bit; see `cos_sq_of_bit_round`. -/
theorem cos_sq_of_bit {n : ℕ} {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 2)
    (hp : RoundingPromise n α θ) {k : ℕ} (hk : k < n) :
    (bit k θ = 0 → 1 / 2 + Real.sin (Real.pi * α) / 2 ≤ Real.cos (Real.pi * 2 ^ k * frac θ) ^ 2) ∧
    (bit k θ = 1 →
      Real.cos (Real.pi * 2 ^ k * frac θ) ^ 2 ≤ 1 / 2 - Real.sin (Real.pi * α) / 2) := by
  have _ := hα1
  exact cos_sq_of_bit_round hα.le hp hk

variable {H : Type u} [HSpace H]

/-- The eigenphase of `U^{2^k}` on an eigenvector of `U` with eigenphase `θ`. -/
theorem pow_apply_eigen (U : H →L[ℂ] H) {ψ : H} {θ : ℝ}
    (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) (m : ℕ) :
    ((U ^ m : H →L[ℂ] H)) ψ = Complex.exp ((m * θ) * Complex.I) • ψ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hψ, smul_smul,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- CPE-2 (per-eigenspace bit extraction, Rall Lemma 10/11 content). For a QSP polynomial pair
with `(pqΦ Φ).1 = A_amp` an amplifying polynomial (`0 ≤ A ≤ 1` on `[0,1]`, `A ≥ 1 - δ` on
`[0, 1/2 - η]`, `A ≤ δ` on `[1/2 + η, 1]`), the projected QSVT of the phase signal of `U^{2^k}`
acts on `plus ψ` by a scalar `s` with `|s| ≥ 1 - δ` if `bit k θ = 1`… (the bit is encoded in
whether `cos²(2^k θ/2)` lies below or above `1/2`). -/
theorem bit_extraction {U : H →L[ℂ] H} (hU : IsUnitary U) (Φ : List ℝ) (hΦ : Φ.length % 2 = 0)
    {A : ℝ[X]} (hpq : (QSVT.pqΦ Φ).1 = A.map (algebraMap ℝ ℂ)) {η δ : ℝ}
    (hA1 : ∀ y ∈ Set.Icc (1 / 2 + η) (1 : ℝ), A.eval y ≤ δ)
    (hA0 : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2 - η), 1 - δ ≤ A.eval y)
    {ψ : H} {θ : ℝ} (hψ : U ψ = Complex.exp (θ * Complex.I) • ψ) (k : ℕ) :
    ∃ s : ℝ, (plusProj ∘L QSVT.UΦ (phaseSignal (U ^ 2 ^ k)) plusProj plusProj Φ ∘L plusProj)
        (DSum.plus ψ) = (s : ℂ) • DSum.plus ψ ∧
      s = A.eval (Real.cos (2 ^ k * θ / 2) ^ 2) ∧
      (Real.cos (2 ^ k * θ / 2) ^ 2 ≤ 1 / 2 - η → 1 - δ ≤ s) ∧
      (1 / 2 + η ≤ Real.cos (2 ^ k * θ / 2) ^ 2 → s ≤ δ) := by
  have hUk : IsUnitary (U ^ 2 ^ k) := by
    rw [isUnitary_iff_mem_unitary] at hU ⊢
    exact pow_mem hU _
  have hψk : (U ^ 2 ^ k) ψ = Complex.exp (((2 ^ k * θ : ℝ) : ℂ) * Complex.I) • ψ := by
    rw [pow_apply_eigen U hψ]
    push_cast
    rfl
  have hc0 : 0 ≤ Real.cos (2 ^ k * θ / 2) ^ 2 := sq_nonneg _
  have hc1 : Real.cos (2 ^ k * θ / 2) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  refine ⟨A.eval (Real.cos (2 ^ k * θ / 2) ^ 2), ?_, rfl, fun h => hA0 _ ⟨hc0, h⟩,
    fun h => hA1 _ ⟨h, hc1⟩⟩
  rw [proj_UΦ_plus_eigen hUk Φ hΦ hψk, hpq, Polynomial.eval_map_algebraMap]
  exact congrArg (· • DSum.plus ψ)
    (Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) _ A)

end CPE

end MQSP
