/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Impulse

/-!
# Step responses, transients and the clock error identity (CLK-1; mQSP §3.1, Eq. (1.12))

For a junction with impulse response `G n` and (regular) steady value `F`, the *step response*
`Y n = ∑_{k ≤ n} G k` is the public output at time `n` of the zero-catalyst circuit driven by a
constant input, and the *transient* is `K n = F† (F - Y n)`. For clock weights
`c : ℕ → ℂ` with `c N = 0`, Abel summation gives the exact error identity (mQSP Eq. (1.12))

  `F† (F - ∑_{n<N} c n • G n) = (1 - c 0) • 1 + ∑_{n<N} (c n - c (n+1)) • K n`,

hence the clock error bound (S1)

  `‖F - ∑_{n<N} c n • G n‖ ≤ |1 - c 0| + ∑_{n<N} |c n - c (n+1)| ‖K n‖`.

Clock shaping (§3.2–3.3) chooses `c` so that the right-hand side is small: adjacent weights
agree on a plateau (cancelling the transient) and the transient decays at the edges.
-/

namespace MQSP

universe u v w x

open Finset

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (O : OracleTuple K)

/-- CLK-1. The step response `Y n = ∑_{k ≤ n} G k`. -/
noncomputable def stepResp (n : ℕ) : P →L[ℂ] P := ∑ k ∈ Finset.range (n + 1), M.G O k

/-- CLK-1. The transient `K n = F† (F - Y n)`. -/
noncomputable def transient (n : ℕ) : P →L[ℂ] P :=
  (M.steady O)† ∘L (M.steady O - M.stepResp O n)

/-- The clock-weighted finite response `G̃_N = ∑_{n<N} c n • G n` (mQSP Eq. (2.1)). -/
noncomputable def weighted (c : ℕ → ℂ) (N : ℕ) : P →L[ℂ] P :=
  ∑ n ∈ Finset.range N, c n • M.G O n

theorem stepResp_zero : M.stepResp O 0 = M.G O 0 := by
  rw [stepResp, Finset.sum_range_one]

theorem stepResp_succ (n : ℕ) : M.stepResp O (n + 1) = M.stepResp O n + M.G O (n + 1) := by
  rw [stepResp, stepResp, Finset.sum_range_succ]

/-- Abel summation without the boundary condition:
`∑_{n ≤ N} c n • G n = ∑_{n<N} (c n - c (n+1)) • Y n + c N • Y N`. -/
theorem sum_range_succ_smul_G (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), c n • M.G O n =
      ∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.stepResp O n + c N • M.stepResp O N := by
  induction N with
  | zero => simp [stepResp_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (n := N), stepResp_succ, sub_smul,
      smul_add]
    abel

/-- Abel summation: `∑_{n<N} c n • G n = c 0 • Y 0 + ∑_{0<n<N} …` in the form
`∑_{n<N} c n • G n = ∑_{n<N} (c n - c (n+1)) • Y n` when `c N = 0`. -/
theorem weighted_eq_sum_stepResp (c : ℕ → ℂ) (N : ℕ) (hc : c N = 0) :
    M.weighted O c N = ∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.stepResp O n := by
  cases N with
  | zero => simp [weighted]
  | succ N =>
    rw [weighted, sum_range_succ_smul_G, Finset.sum_range_succ (n := N), hc, sub_zero]

/-- CLK-1 (mQSP Eq. (1.12)). The exact clock error identity, for a unitary steady value. -/
theorem steady_adj_sub_weighted (hO : O.IsUnitary) (h : M.IsRegular O) (c : ℕ → ℂ) (N : ℕ)
    (hc : c N = 0) :
    (M.steady O)† ∘L (M.steady O - M.weighted O c N) =
      (1 - c 0) • (1 : P →L[ℂ] P) +
        ∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.transient O n := by
  have hF : (M.steady O)† ∘L M.steady O = 1 := (M.isUnitary_steady hO h).1
  have hsum : ∑ n ∈ Finset.range N, (c n - c (n + 1)) = c 0 := by
    rw [Finset.sum_range_sub', hc, sub_zero]
  have hT : ∀ n, M.transient O n = 1 - (M.steady O)† ∘L M.stepResp O n := by
    intro n; rw [transient, ContinuousLinearMap.comp_sub, hF]
  rw [weighted_eq_sum_stepResp M O c N hc, ContinuousLinearMap.comp_sub, hF,
    ContinuousLinearMap.comp_finsetSum]
  simp_rw [hT, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum,
    ContinuousLinearMap.comp_smul]
  rw [sub_smul, one_smul]
  abel

/-- CLK-1 (S1). The clock error bound
`‖F - G̃_N‖ ≤ |1 - c 0| + ∑_{n<N} |c n - c (n+1)| ‖K n‖`. -/
theorem norm_steady_sub_weighted_le (hO : O.IsUnitary) (h : M.IsRegular O) (c : ℕ → ℂ) (N : ℕ)
    (hc : c N = 0) :
    ‖M.steady O - M.weighted O c N‖ ≤
      ‖1 - c 0‖ + ∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖ * ‖M.transient O n‖ := by
  have hU := M.isUnitary_steady hO h
  have heq : M.steady O - M.weighted O c N =
      M.steady O ∘L ((M.steady O)† ∘L (M.steady O - M.weighted O c N)) := by
    rw [← ContinuousLinearMap.comp_assoc, hU.2, one_comp]
  have h1 : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  rw [heq, steady_adj_sub_weighted M O hO h c N hc]
  calc _ ≤ ‖M.steady O‖ * ‖(1 - c 0) • (1 : P →L[ℂ] P) +
        ∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.transient O n‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖(1 - c 0) • (1 : P →L[ℂ] P)‖ +
        ‖∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.transient O n‖) := by
      gcongr
      · exact hU.opNorm_le_one
      · exact norm_add_le _ _
    _ ≤ 1 * (‖1 - c 0‖ * 1 +
        ∑ n ∈ Finset.range N, ‖c n - c (n + 1)‖ * ‖M.transient O n‖) := by
      gcongr
      · rw [norm_smul]; gcongr
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [norm_smul]
    _ = _ := by ring

/-- Where adjacent weights agree the transient does not contribute: on a plateau
`c n = c (n+1)` the `n`-th term vanishes (immediate from the identity; recorded for use). -/
theorem transient_term_eq_zero_of_eq (c : ℕ → ℂ) (n : ℕ) (hn : c n = c (n + 1)) :
    (c n - c (n + 1)) • M.transient O n = 0 := by
  rw [hn, sub_self, zero_smul]

end Junction

end MQSP
