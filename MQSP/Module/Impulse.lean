/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Defs

/-!
# Time-domain impulse response of a junction (MOD-3)

The delayed impulse response `G n : P →L[ℂ] P` of a junction with port delays `r j`
(mQSP Eq. (2.20)–(2.21), with the delay convention of Thm 2.2): for the public impulse
`u₀ = ψ`, `uₖ = 0 (k > 0)`, the private state written at time `k` is `g k` and the feedback
vector read at time `k` is

  `fb k = ∑ⱼ (π j)† (O j) (π j) (g (k - r j))`  (terms with `k < r j` vanish),

so that `g k = [k = 0] C + D (fb k)` and `y k = G k = [k = 0] A + B (fb k)`.
Port `j` stores its amplitude for `r j` steps and passes through `O j` exactly once in between.

For unit delays this is the familiar `G 0 = A`, `G (n+1) = B Q (D Q)ⁿ C` (Eq. (2.21)).
The unitary Toeplitz lift (`MQSP.Compile.Lift`) block-encodes the Toeplitz matrix of these
coefficients; in particular they are contractions.
-/

namespace MQSP

universe u v w x

open Finset

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (O : OracleTuple K)

/-- MOD-3. The private state `g k : P →L L` written at time `k` for the public impulse at
time `0` (mQSP Eq. (2.20) with delays). -/
noncomputable def gseq : ℕ → (P →L[ℂ] L)
  | k =>
    (if k = 0 then M.C else 0) +
      M.D ∘L ∑ j, (if _h : M.delay j ≤ k then
        (M.ports.π j)† ∘L O j ∘L M.ports.π j ∘L gseq (k - M.delay j) else 0)
termination_by k => k
decreasing_by
  all_goals
    have := M.one_le_delay j
    omega

/-- MOD-3. The feedback vector read at time `k`: `∑ⱼ (π j)† (O j) (π j) g (k - r j)`. -/
noncomputable def fb (k : ℕ) : P →L[ℂ] L :=
  ∑ j, (if M.delay j ≤ k then
    (M.ports.π j)† ∘L O j ∘L M.ports.π j ∘L M.gseq O (k - M.delay j) else 0)

theorem gseq_eq (k : ℕ) : M.gseq O k = (if k = 0 then M.C else 0) + M.D ∘L M.fb O k := by
  rw [gseq, fb]
  congr 2

/-- MOD-3 (mQSP Eq. (2.21) generalised). The impulse response `G k = [k = 0] A + B (fb k)`. -/
noncomputable def G (k : ℕ) : P →L[ℂ] P :=
  (if k = 0 then M.A else 0) + M.B ∘L M.fb O k

@[simp] theorem fb_zero : M.fb O 0 = 0 := by
  unfold fb
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have := M.one_le_delay j
  split_ifs with hj
  · omega
  · rfl

@[simp] theorem gseq_zero : M.gseq O 0 = M.C := by
  rw [gseq_eq, fb_zero]; simp

@[simp] theorem G_zero : M.G O 0 = M.A := by
  rw [G, fb_zero]; simp

theorem gseq_succ (k : ℕ) : M.gseq O (k + 1) = M.D ∘L M.fb O (k + 1) := by
  rw [gseq_eq]; simp

theorem G_succ (k : ℕ) : M.G O (k + 1) = M.B ∘L M.fb O (k + 1) := by
  rw [G]; simp

/-- With unit delays the feedback at time `k + 1` is `Q g k`. -/
theorem fb_succ_of_delay_eq_one (h : ∀ j, M.delay j = 1) (k : ℕ) :
    M.fb O (k + 1) = M.Q O ∘L M.gseq O k := by
  rw [fb, Q, Ports.feedback, ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ite_eq_left (by rw [h j]; omega), h j, Nat.add_sub_cancel]
  simp only [ContinuousLinearMap.comp_assoc]

/-- mQSP Eq. (2.21): with unit delays, `G (n + 1) = B Q (D Q)ⁿ C`. -/
theorem G_succ_of_delay_eq_one (h : ∀ j, M.delay j = 1) (n : ℕ) :
    M.G O (n + 1) = M.B ∘L M.Q O ∘L (((M.D ∘L M.Q O) ^ n : L →L[ℂ] L) ∘L M.C) := by
  have hg : ∀ m, M.gseq O m = ((M.D ∘L M.Q O) ^ m : L →L[ℂ] L) ∘L M.C := by
    intro m
    induction m with
    | zero => rw [gseq_zero, pow_zero, one_comp]
    | succ m ih =>
      rw [gseq_succ, fb_succ_of_delay_eq_one M O h, ih, pow_succ', ContinuousLinearMap.mul_def]
      simp only [ContinuousLinearMap.comp_assoc]
  rw [G_succ, fb_succ_of_delay_eq_one M O h, hg]

end Junction

end MQSP
