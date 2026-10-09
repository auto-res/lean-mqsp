/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Defs

/-!
# Comparing two oracle substitutions (MOD-5; mQSP Thm 2.1 Eq. (2.14))

For the same junction evaluated on two unitary oracle tuples `O`, `O'` (both regular), the
steady-state equations and unitarity of `S` give the two-point identity

  `1 - F'† F = Γ'† (1 - Q'† Q) Γ`

(mQSP Eq. (2.14); the private contribution is `Q'† Q = ⊕ⱼ O'ⱼ† Oⱼ`). Consequently
`F' - F = F' Γ'† Q'† (Q' - Q) Γ` and the *query-Lipschitz bound*

  `‖F - F'‖ ≤ ‖Γ'‖ ‖Q - Q'‖ ‖Γ‖`,

which specialises to the familiar "`d` queries ⟹ `d`-fold error amplification" for finite
query circuits (GSLW Lemmas 22/23, Thm 73) since a chain of `d` queries has `‖Γ‖ = √d`.
-/

namespace MQSP

universe u v w x

open scoped InnerProductSpace

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-- The steady-state equation in operator form: `S (inl + inr Q Γ) = inl F + inr Γ`. -/
theorem steady_state_op {O : OracleTuple K} (h : M.IsRegular O) :
    M.S ∘L (DSum.inl + DSum.inr ∘L M.Q O ∘L M.catalyst O) =
      DSum.inl ∘L M.steady O + DSum.inr ∘L M.catalyst O := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  simp only [ContinuousLinearMap.comp_apply, add_apply]
  rw [← DSum.mk_eq_inl_add_inr, ← DSum.mk_eq_inl_add_inr]
  exact M.steady_state_eq h ψ

/-- `X'† X = (fst X')† (fst X) + (snd X')† (snd X)` for operators into a direct sum. -/
theorem adjoint_comp_eq_fst_add_snd {E : Type*} [HSpace E] (X X' : E →L[ℂ] P ⊕ₕ L) :
    X'† ∘L X = (DSum.fst ∘L X')† ∘L (DSum.fst ∘L X) + (DSum.snd ∘L X')† ∘L (DSum.snd ∘L X) := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, DSum.adjoint_fst,
    DSum.adjoint_snd]
  conv_lhs => rw [← one_comp X, ← DSum.inl_fst_add_inr_snd]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc]

/-- MOD-5 (mQSP Eq. (2.14)). The two-point identity `1 - F'† F = Γ'† (1 - Q'† Q) Γ`. -/
theorem one_sub_steady_adj_steady {O O' : OracleTuple K} (h : M.IsRegular O)
    (h' : M.IsRegular O') :
    1 - (M.steady O')† ∘L M.steady O =
      (M.catalyst O')† ∘L (1 - (M.Q O')† ∘L M.Q O) ∘L M.catalyst O := by
  set X : P →L[ℂ] P ⊕ₕ L := DSum.inl + DSum.inr ∘L M.Q O ∘L M.catalyst O with hX
  set X' : P →L[ℂ] P ⊕ₕ L := DSum.inl + DSum.inr ∘L M.Q O' ∘L M.catalyst O' with hX'
  set Y : P →L[ℂ] P ⊕ₕ L := DSum.inl ∘L M.steady O + DSum.inr ∘L M.catalyst O with hY
  set Y' : P →L[ℂ] P ⊕ₕ L := DSum.inl ∘L M.steady O' + DSum.inr ∘L M.catalyst O' with hY'
  have hSX : M.S ∘L X = Y := M.steady_state_op h
  have hSX' : M.S ∘L X' = Y' := M.steady_state_op h'
  have key : X'† ∘L X = Y'† ∘L Y := by
    rw [← hSX, ← hSX', ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc (M.S†), M.isUnitary_S.1, one_comp]
  have h1 : DSum.fst ∘L X = 1 := by ext ψ; simp [hX]
  have h2 : DSum.snd ∘L X = M.Q O ∘L M.catalyst O := by ext ψ; simp [hX]
  have h1' : DSum.fst ∘L X' = 1 := by ext ψ; simp [hX']
  have h2' : DSum.snd ∘L X' = M.Q O' ∘L M.catalyst O' := by ext ψ; simp [hX']
  have h3 : DSum.fst ∘L Y = M.steady O := by ext ψ; simp [hY]
  have h4 : DSum.snd ∘L Y = M.catalyst O := by ext ψ; simp [hY]
  have h3' : DSum.fst ∘L Y' = M.steady O' := by ext ψ; simp [hY']
  have h4' : DSum.snd ∘L Y' = M.catalyst O' := by ext ψ; simp [hY']
  rw [adjoint_comp_eq_fst_add_snd, adjoint_comp_eq_fst_add_snd, h1, h2, h1', h2', h3, h4, h3',
    h4', adjoint_one, one_comp, ContinuousLinearMap.adjoint_comp] at key
  simp only [ContinuousLinearMap.comp_assoc] at key
  rw [ContinuousLinearMap.sub_comp, one_comp, ContinuousLinearMap.comp_sub,
    sub_eq_sub_iff_add_eq_add]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [key, add_comm]

/-- `F' - F = F' Γ'† Q'† (Q' - Q) Γ` for unitary oracles. -/
theorem steady_sub_steady {O O' : OracleTuple K} (hO : O.IsUnitary) (hO' : O'.IsUnitary)
    (h : M.IsRegular O) (h' : M.IsRegular O') :
    M.steady O' - M.steady O =
      M.steady O' ∘L (M.catalyst O')† ∘L (M.Q O')† ∘L (M.Q O' - M.Q O) ∘L M.catalyst O := by
  -- only the unitarity of `O'` is needed; `hO` is kept for symmetry of the statement
  have _ := hO
  have e1 : M.steady O' ∘L (1 - (M.steady O')† ∘L M.steady O) = M.steady O' - M.steady O := by
    rw [ContinuousLinearMap.comp_sub, comp_one, ← ContinuousLinearMap.comp_assoc,
      (M.isUnitary_steady hO' h').2, one_comp]
  have e2 : (1 - (M.Q O')† ∘L M.Q O) = (M.Q O')† ∘L (M.Q O' - M.Q O) := by
    rw [ContinuousLinearMap.comp_sub, (M.isUnitary_Q hO').1]
  rw [← e1, M.one_sub_steady_adj_steady h h', e2]
  simp only [ContinuousLinearMap.comp_assoc]

/-- MOD-5. The query-Lipschitz bound `‖F - F'‖ ≤ ‖Γ'‖ ‖Q - Q'‖ ‖Γ‖`. -/
theorem norm_steady_sub_steady_le {O O' : OracleTuple K} (hO : O.IsUnitary)
    (hO' : O'.IsUnitary) (h : M.IsRegular O) (h' : M.IsRegular O') :
    ‖M.steady O - M.steady O'‖ ≤ ‖M.catalyst O'‖ * ‖M.Q O - M.Q O'‖ * ‖M.catalyst O‖ := by
  rw [norm_sub_rev, M.steady_sub_steady hO hO' h h', norm_sub_rev (M.Q O)]
  have hF : ‖M.steady O'‖ ≤ 1 := (M.isUnitary_steady hO' h').opNorm_le_one
  have hQ : ‖(M.Q O')†‖ ≤ 1 := (M.isUnitary_Q hO').adjoint.opNorm_le_one
  have hΓ : ‖(M.catalyst O')†‖ = ‖M.catalyst O'‖ := LinearIsometryEquiv.norm_map _ _
  calc ‖M.steady O' ∘L (M.catalyst O')† ∘L (M.Q O')† ∘L (M.Q O' - M.Q O) ∘L M.catalyst O‖
      ≤ ‖M.steady O'‖ * (‖(M.catalyst O')†‖ * (‖(M.Q O')†‖ *
          (‖M.Q O' - M.Q O‖ * ‖M.catalyst O‖))) := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖M.catalyst O'‖ * (1 * (‖M.Q O' - M.Q O‖ * ‖M.catalyst O‖))) := by
        rw [hΓ]; gcongr
    _ = ‖M.catalyst O'‖ * ‖M.Q O' - M.Q O‖ * ‖M.catalyst O‖ := by ring

/-- The feedback difference is bounded by the largest port difference:
`‖Q O - Q O'‖ ≤ sup_j ‖O j - O' j‖` (stated with an explicit bound). -/
theorem norm_Q_sub_Q_le {O O' : OracleTuple K} {ε : ℝ} (hε : ∀ j, ‖O j - O' j‖ ≤ ε) (h0 : 0 ≤ ε) :
    ‖M.Q O - M.Q O'‖ ≤ ε := by
  have hdiff : M.Q O - M.Q O' = M.ports.feedback (fun j => O j - O' j) := by
    simp only [Q, Ports.feedback, ← Finset.sum_sub_distrib, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp]
  rw [hdiff]
  refine ContinuousLinearMap.opNorm_le_bound _ h0 (fun v => ?_)
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)), mul_pow,
    M.ports.norm_sq_eq, M.ports.norm_sq_eq v, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Ports.π_feedback_apply, ← mul_pow]
  have := (O j - O' j).le_opNorm (M.ports.π j v)
  have h2 : ‖(O j - O' j) (M.ports.π j v)‖ ≤ ε * ‖M.ports.π j v‖ :=
    this.trans (by gcongr; exact hε j)
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

end Junction

end MQSP
