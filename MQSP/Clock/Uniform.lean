/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Clock.Transient
import MQSP.Clock.Flat
import MQSP.Compile.Lift

/-!
# The uniform clock: polynomial-precision compilation (CLK-2; mQSP Thm 3.2, Lemma 3.3)

For a module with unit delays, the step response is `Y n = F - B Q (D Q)ⁿ Γ` (Lemma 3.3:
the terminal formula, the missing catalyst after `n` rounds), and unitarity of `S` gives the
energy inequality `∑_{n<N} ‖B Q (DQ)ⁿ v‖² ≤ ‖v‖²`. The *uniform clock* (the normalised box of
width `N` paired with itself) has weights `cₙ = (N - n)/N`, so the clock-error identity and
Cauchy–Schwarz give the baseline (mQSP Thm 3.2, [BJY24])

  `‖(F - G̃_N) ψ‖ ≤ ‖Γ ψ‖ / √N`,   `‖F - G̃_N‖ ≤ ‖Γ‖ / √N`,

i.e. horizon `N = O(W/ε²)` for catalyst weight `W = ‖Γ‖²`. Combined with the Toeplitz lift
and the box clock this is an end-to-end compilation theorem with normalization `1`
(`isEncodingOf_uniform`): every regular unit-delay module compiles to a circuit of
`N - 1` queries per port encoding an operator within `‖Γ‖/√N` of its steady value.
-/

namespace MQSP

universe u v w x

open Finset

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (O : OracleTuple K)

/-- The loop power `(D Q)ⁿ`. -/
noncomputable abbrev loopPow (n : ℕ) : L →L[ℂ] L := ((M.D ∘L M.Q O) ^ n : L →L[ℂ] L)

omit [DecidableEq ι] in
/-- CLK-2 (mQSP Lemma 3.3, unit delays). The step response misses the catalyst after `n`
rounds: `Y n = F - B Q (D Q)ⁿ Γ`. -/
theorem stepResp_eq (hd : ∀ j, M.delay j = 1) (h : M.IsRegular O) (n : ℕ) :
    M.stepResp O n = M.steady O - M.B ∘L M.Q O ∘L M.loopPow O n ∘L M.catalyst O := by
  have hTΓ : (M.D ∘L M.Q O) ∘L M.catalyst O = M.catalyst O - M.C := by
    rw [ContinuousLinearMap.comp_assoc]
    conv_rhs => rw [M.catalyst_eq h]
    abel
  induction n with
  | zero =>
    rw [stepResp_zero, G_zero, loopPow, pow_zero, one_comp, steady]
    abel
  | succ n ih =>
    have hstep : ((M.D ∘L M.Q O) ^ (n + 1) : L →L[ℂ] L) ∘L M.catalyst O =
        ((M.D ∘L M.Q O) ^ n : L →L[ℂ] L) ∘L M.catalyst O -
          ((M.D ∘L M.Q O) ^ n : L →L[ℂ] L) ∘L M.C := by
      rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, hTΓ,
        ContinuousLinearMap.comp_sub]
    rw [stepResp_succ, ih, G_succ_of_delay_eq_one M O hd, loopPow, loopPow, hstep]
    simp only [ContinuousLinearMap.comp_sub]
    abel

omit [DecidableEq ι] in
/-- The energy inequality: the public amplitude leaving in the first `N` rounds is bounded by
the initial private amplitude. -/
theorem sum_norm_sq_B_Q_loopPow_le (hO : O.IsUnitary) (v : L) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖M.B (M.Q O (M.loopPow O n v))‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have key : ∀ w : L, ‖M.B (M.Q O w)‖ ^ 2 = ‖w‖ ^ 2 - ‖(M.D ∘L M.Q O) w‖ ^ 2 := by
    intro w
    have h1 := M.isUnitary_S.isIsometry.norm_map (DSum.mk 0 (M.Q O w))
    have h2 := congrArg (fun t : ℝ => t ^ 2) h1
    simp only [DSum.norm_sq_eq, S_apply, DSum.fst_mk, DSum.snd_mk, map_zero, zero_add,
      norm_zero] at h2
    rw [(M.isUnitary_Q hO).isIsometry.norm_map] at h2
    rw [ContinuousLinearMap.comp_apply]
    nlinarith [h2]
  calc ∑ n ∈ Finset.range N, ‖M.B (M.Q O (M.loopPow O n v))‖ ^ 2
      = ∑ n ∈ Finset.range N, (‖M.loopPow O n v‖ ^ 2 - ‖M.loopPow O (n + 1) v‖ ^ 2) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [key, loopPow, loopPow, pow_succ' (M.D ∘L M.Q O) n, mul_apply_eq_comp]
    _ = ‖v‖ ^ 2 - ‖M.loopPow O N v‖ ^ 2 := by
        rw [Finset.sum_range_sub', loopPow, pow_zero, one_apply_eq_self]
    _ ≤ ‖v‖ ^ 2 := sub_le_self _ (sq_nonneg _)

/-- The uniform clock weights `cₙ = (N - n)/N` (as complex numbers), zero for `n ≥ N`. -/
noncomputable def uniformWeights (N : ℕ) (n : ℕ) : ℂ := (((N - n : ℕ) : ℝ) / N : ℝ)

/-- The uniform weights are those of the normalised box of width `N` paired with itself. -/
theorem weights_box_self (N : ℕ) (hN : 0 < N) (n : ℕ) :
    Clock.weights (Clock.clockX (Clock.box N N) (Clock.box N N)) n = uniformWeights N n := by
  have h := Clock.weights_box_eq N N 0 n hN (by omega)
  simp only [Nat.cast_zero, add_zero] at h
  rw [h, uniformWeights, min_eq_right (Nat.sub_le N n),
    Real.mul_self_sqrt (Nat.cast_nonneg N)]

omit [DecidableEq ι] in
/-- CLK-2 (mQSP Thm 3.2, vector form). With the uniform clock, `‖(F - G̃_N) ψ‖ ≤ ‖Γ ψ‖/√N`. -/
theorem norm_steady_sub_weighted_uniform_apply (hd : ∀ j, M.delay j = 1) (hO : O.IsUnitary)
    (h : M.IsRegular O) (N : ℕ) (hN : 0 < N) (ψ : P) :
    ‖(M.steady O - M.weighted O (uniformWeights N) N) ψ‖ ≤ ‖M.catalyst O ψ‖ / Real.sqrt N := by
  set c := uniformWeights N with hc
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : c N = 0 := by
    rw [hc, uniformWeights, Nat.sub_self, Nat.cast_zero, zero_div, Complex.ofReal_zero]
  have hc0 : c 0 = 1 := by
    rw [hc, uniformWeights, Nat.sub_zero, div_self hNr.ne', Complex.ofReal_one]
  have hcd : ∀ n ∈ Finset.range N, c n - c (n + 1) = ((1 / N : ℝ) : ℂ) := by
    intro n hn
    have hn' : N - n = (N - (n + 1)) + 1 := by have := Finset.mem_range.1 hn; omega
    rw [hc, uniformWeights, uniformWeights, ← Complex.ofReal_sub, ← sub_div, hn', Nat.cast_add,
      Nat.cast_one, add_sub_cancel_left]
  have hU := M.isUnitary_steady hO h
  have hK : ∀ n, ‖M.transient O n ψ‖ = ‖M.B (M.Q O (M.loopPow O n (M.catalyst O ψ)))‖ := by
    intro n
    rw [transient, stepResp_eq M O hd h n, sub_sub_cancel, ContinuousLinearMap.comp_apply,
      hU.adjoint.isIsometry.norm_map]
    rfl
  have hid := M.steady_adj_sub_weighted O hO h c N hcN
  rw [hc0, sub_self, zero_smul, zero_add] at hid
  have h1 : (M.steady O)† ((M.steady O - M.weighted O c N) ψ) =
      ∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.transient O n ψ := by
    rw [show (M.steady O)† ((M.steady O - M.weighted O c N) ψ) =
      ((M.steady O)† ∘L (M.steady O - M.weighted O c N)) ψ from rfl, hid]
    simp only [_root_.sum_apply, smul_apply]
  have hs1 : ∑ n ∈ Finset.range N, (1 : ℝ) ^ 2 = N := by simp
  have hs2 : Real.sqrt (∑ n ∈ Finset.range N,
      ‖M.B (M.Q O (M.loopPow O n (M.catalyst O ψ)))‖ ^ 2) ≤ ‖M.catalyst O ψ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (M.catalyst O ψ))]
    exact Real.sqrt_le_sqrt (M.sum_norm_sq_B_Q_loopPow_le O hO _ N)
  calc ‖(M.steady O - M.weighted O c N) ψ‖
      = ‖∑ n ∈ Finset.range N, (c n - c (n + 1)) • M.transient O n ψ‖ := by
        rw [← h1, hU.adjoint.isIsometry.norm_map]
    _ ≤ ∑ n ∈ Finset.range N, ‖(c n - c (n + 1)) • M.transient O n ψ‖ := norm_sum_le _ _
    _ = (1 / N) * ∑ n ∈ Finset.range N,
          1 * ‖M.B (M.Q O (M.loopPow O n (M.catalyst O ψ)))‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [norm_smul, hcd n hn, hK, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          one_mul]
    _ ≤ (1 / N) * (Real.sqrt (∑ n ∈ Finset.range N, (1 : ℝ) ^ 2) * Real.sqrt (∑ n ∈
          Finset.range N, ‖M.B (M.Q O (M.loopPow O n (M.catalyst O ψ)))‖ ^ 2)) := by
        gcongr
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ (1 / N) * (Real.sqrt N * ‖M.catalyst O ψ‖) := by
        rw [hs1]
        gcongr
    _ = ‖M.catalyst O ψ‖ / Real.sqrt N := by
        have hp : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
        field_simp
        rw [Real.sq_sqrt hNr.le]

omit [DecidableEq ι] in
/-- CLK-2 (mQSP Thm 3.2). `‖F - G̃_N‖ ≤ ‖Γ‖/√N` for the uniform clock. -/
theorem norm_steady_sub_weighted_uniform (hd : ∀ j, M.delay j = 1) (hO : O.IsUnitary)
    (h : M.IsRegular O) (N : ℕ) (hN : 0 < N) :
    ‖M.steady O - M.weighted O (uniformWeights N) N‖ ≤ ‖M.catalyst O‖ / Real.sqrt N := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) fun ψ => ?_
  calc ‖(M.steady O - M.weighted O (uniformWeights N) N) ψ‖
      ≤ ‖M.catalyst O ψ‖ / Real.sqrt N :=
        M.norm_steady_sub_weighted_uniform_apply O hd hO h N hN ψ
    _ ≤ ‖M.catalyst O‖ * ‖ψ‖ / Real.sqrt N := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖M.catalyst O‖ / Real.sqrt N * ‖ψ‖ := by ring

/-- CLK-2 (end-to-end). The lift of horizon `N` with the uniform box clock encodes `G̃_N`,
which is within `‖Γ‖/√N` of the steady value, at normalization `1`. -/
theorem isEncodingOf_uniform (hd : ∀ j, M.delay j = 1) (hO : O.IsUnitary) (h : M.IsRegular O)
    (N : ℕ) (hN : 0 < N) :
    IsEncodingOf (Reg.map (M.lift O N)) (Clock.clockIn (Clock.box N N))
        (Clock.clockIn (Clock.box N N)) (M.weighted O (uniformWeights N) N) ∧
      ‖M.steady O - M.weighted O (uniformWeights N) N‖ ≤ ‖M.catalyst O‖ / Real.sqrt N := by
  refine ⟨?_, M.norm_steady_sub_weighted_uniform O hd hO h N hN⟩
  have hk : Clock.kernel (M.lift O N) =
      fun (o i : Fin N) => if (i : ℕ) ≤ o then M.G O ((o : ℕ) - i) else 0 := by
    funext o i
    exact M.toeplitz_block O N hO i o
  have hW := Clock.isEncodingOf_quditize (M.isUnitary_lift O N hO)
    (Clock.isNormalized_box N N hN le_rfl) (Clock.isNormalized_box N N hN le_rfl)
  rw [hk, Clock.extract_toeplitz] at hW
  simp only [weights_box_self N hN] at hW
  exact hW

end Junction

end MQSP
