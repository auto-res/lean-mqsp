/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Defs

/-!
# The steady state without a regularity hypothesis (MOD-2b)

For a unitary junction `S` and unitary feedback `Q` in finite dimension, the steady-state
equation `Γ = C + D Q Γ` always has a solution, and the transfer value `F = A + B Q Γ` does
not depend on which solution is chosen. Indeed, with `T = D Q` (a contraction):

* `ker (1 - T) = ker (1 - T†)` (a contraction fixes `v` iff its adjoint does);
* if `v = D Q v` then `B Q v = 0` (unitarity of `S` on `0 ⊕ Q v`), and if `h = Q† D† h` then
  `C† h = 0` (unitarity of `S†`); hence `ran C ⊆ (ker (1 - T†))ᗮ = ran (1 - T)`.

The canonical choice is the *minimum-norm* solution `Γ₀`, characterised by
`(1 - D Q) Γ₀ = C` and `ran Γ₀ ⊥ ker (1 - D Q)`; it agrees with `(1 - D Q)⁻¹ C` on regular
loops and with the Abel/analytic-continuation catalyst of mQSP. `steady₀ = A + B Q Γ₀` is
always unitary (mQSP Prop 5.1 without the regularity proviso).
-/

namespace MQSP

universe u v w x

open scoped InnerProductSpace

/-- A contraction fixes `v` only if its adjoint does. -/
theorem adjoint_apply_eq_of_apply_eq {E : Type*} [HSpace E] {T : E →L[ℂ] E}
    (hT : ‖T‖ ≤ 1) {v : E} (hv : T v = v) : T† v = v := by
  have h1 : ‖T† v‖ ≤ ‖v‖ := by
    calc ‖T† v‖ ≤ ‖T†‖ * ‖v‖ := (T†).le_opNorm v
      _ ≤ 1 * ‖v‖ := by
        gcongr
        rw [ContinuousLinearMap.adjoint.norm_map]
        exact hT
      _ = ‖v‖ := one_mul _
  have h2 : RCLike.re ⟪T† v, v⟫_ℂ = ‖v‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_left, hv, inner_self_eq_norm_sq]
  have h3 : ‖T† v - v‖ ^ 2 = ‖T† v‖ ^ 2 - 2 * ‖v‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [@norm_sub_sq ℂ, h2]
  have h4 : ‖T† v - v‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (T† v), norm_nonneg v]
  have h5 : ‖T† v - v‖ = 0 := by nlinarith [norm_nonneg (T† v - v)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h5)

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-- The loop operator `T = D Q`. -/
noncomputable abbrev loopOp (O : OracleTuple K) : L →L[ℂ] L := M.D ∘L M.Q O

/-- Vectors fixed by the loop: `ker (1 - D Q)`. -/
noncomputable abbrev fixedSpace (O : OracleTuple K) : Submodule ℂ L :=
  LinearMap.ker ((1 - M.loopOp O : L →L[ℂ] L) : L →ₗ[ℂ] L)

/-- A loop-fixed vector is invisible to the public output: `v = D Q v → B Q v = 0`. -/
theorem B_Q_eq_zero_of_fixed {O : OracleTuple K} (hO : O.IsUnitary) {v : L}
    (hv : v = M.D (M.Q O v)) : M.B (M.Q O v) = 0 := by
  have h1 := M.isUnitary_S.isIsometry.norm_map (DSum.mk 0 (M.Q O v))
  rw [S_apply, DSum.fst_mk, DSum.snd_mk, map_zero, map_zero, zero_add, zero_add, ← hv] at h1
  have h2 := congrArg (fun t : ℝ => t ^ 2) h1
  simp only [DSum.norm_sq_eq, DSum.fst_mk, DSum.snd_mk, (M.isUnitary_Q hO).isIsometry.norm_map,
    norm_zero] at h2
  have h3 : ‖M.B (M.Q O v)‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- The loop operator is a contraction. -/
theorem opNorm_loopOp_le_one {O : OracleTuple K} (hO : O.IsUnitary) : ‖M.loopOp O‖ ≤ 1 :=
  calc ‖M.loopOp O‖ ≤ ‖M.D‖ * ‖M.Q O‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      gcongr
      · exact M.opNorm_D_le_one
      · exact (M.isUnitary_Q hO).opNorm_le_one
    _ = 1 := one_mul _

/-- The adjoint loop has the same fixed vectors. -/
theorem fixed_adjoint_iff {O : OracleTuple K} (hO : O.IsUnitary) (v : L) :
    (M.loopOp O)† v = v ↔ M.loopOp O v = v := by
  have hT := M.opNorm_loopOp_le_one hO
  refine ⟨fun h => ?_, adjoint_apply_eq_of_apply_eq hT⟩
  have hT' : ‖(M.loopOp O)†‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hT
  have := adjoint_apply_eq_of_apply_eq hT' h
  rwa [ContinuousLinearMap.adjoint_adjoint] at this

/-- A vector fixed by the adjoint loop is orthogonal to the range of `C`: `C† h = 0`. -/
theorem C_adj_eq_zero_of_fixed_adjoint {O : OracleTuple K} (hO : O.IsUnitary) {h : L}
    (hh : (M.loopOp O)† h = h) : M.C† h = 0 := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply] at hh
  have hD : ‖M.D† h‖ = ‖h‖ := by
    rw [← (M.isUnitary_Q hO).adjoint.isIsometry.norm_map (M.D† h), hh]
  have h1 := M.isUnitary_S.adjoint.isIsometry.norm_map (DSum.mk 0 h)
  rw [S_eq_block, DSum.adjoint_block, DSum.block_apply, DSum.fst_mk, DSum.snd_mk, map_zero,
    map_zero, zero_add, zero_add] at h1
  have h2 := congrArg (fun t : ℝ => t ^ 2) h1
  simp only [DSum.norm_sq_eq, DSum.fst_mk, DSum.snd_mk, hD, norm_zero] at h2
  have h3 : ‖M.C† h‖ ^ 2 = 0 := by linarith
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- MOD-2b. The steady-state equation always has a solution orthogonal to the fixed space:
for every `ψ` there is a unique `g ⊥ ker (1 - D Q)` with `(1 - D Q) g = C ψ`. -/
theorem existsUnique_steady_solution {O : OracleTuple K} (hO : O.IsUnitary) (ψ : P) :
    ∃! g : L, (1 - M.loopOp O) g = M.C ψ ∧ g ∈ (M.fixedSpace O)ᗮ := by
  set W : L →L[ℂ] L := 1 - M.loopOp O with hW
  set N := M.fixedSpace O with hN
  have hmem : M.C ψ ∈ LinearMap.range (W : L →ₗ[ℂ] L) := by
    rw [← Submodule.orthogonal_orthogonal (LinearMap.range (W : L →ₗ[ℂ] L)),
      ContinuousLinearMap.orthogonal_range, Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hW, map_sub, adjoint_one, sub_apply,
      one_apply_eq_self, sub_eq_zero] at hu
    rw [← ContinuousLinearMap.adjoint_inner_left,
      M.C_adj_eq_zero_of_fixed_adjoint hO hu.symm, inner_zero_left]
  obtain ⟨g₀, hg₀⟩ := hmem
  rw [ContinuousLinearMap.coe_coe] at hg₀
  refine ⟨g₀ - N.starProjection g₀, ⟨?_, N.sub_starProjection_mem_orthogonal g₀⟩, ?_⟩
  · have h0 : W (N.starProjection g₀) = 0 := N.starProjection_apply_mem g₀
    rw [map_sub, h0, sub_zero, hg₀]
  · rintro g ⟨hg1, hg2⟩
    have hker : g - (g₀ - N.starProjection g₀) ∈ N := by
      have h0 : W (N.starProjection g₀) = 0 := N.starProjection_apply_mem g₀
      change W (g - (g₀ - N.starProjection g₀)) = 0
      rw [map_sub, map_sub, h0, sub_zero, hg₀, hg1, sub_self]
    have hperp : g - (g₀ - N.starProjection g₀) ∈ Nᗮ :=
      Nᗮ.sub_mem hg2 (N.sub_starProjection_mem_orthogonal g₀)
    have h := Submodule.mem_inf.2 ⟨hker, hperp⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
    exact sub_eq_zero.1 h

/-- MOD-2b. The minimum-norm catalyst `Γ₀`. -/
noncomputable def catalyst₀ {O : OracleTuple K} (hO : O.IsUnitary) : P →L[ℂ] L :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ => Classical.choose (M.existsUnique_steady_solution hO ψ).exists
      map_add' := by
        intro x y
        have hx := Classical.choose_spec (M.existsUnique_steady_solution hO x).exists
        have hy := Classical.choose_spec (M.existsUnique_steady_solution hO y).exists
        have hxy := Classical.choose_spec (M.existsUnique_steady_solution hO (x + y)).exists
        refine (M.existsUnique_steady_solution hO (x + y)).unique hxy ⟨?_, ?_⟩
        · rw [map_add, hx.1, hy.1, map_add]
        · exact Submodule.add_mem _ hx.2 hy.2
      map_smul' := by
        intro c x
        have hx := Classical.choose_spec (M.existsUnique_steady_solution hO x).exists
        have hcx := Classical.choose_spec (M.existsUnique_steady_solution hO (c • x)).exists
        refine (M.existsUnique_steady_solution hO (c • x)).unique hcx ⟨?_, ?_⟩
        · rw [RingHom.id_apply, map_smul, hx.1, map_smul]
        · exact Submodule.smul_mem _ c hx.2 }

theorem catalyst₀_spec {O : OracleTuple K} (hO : O.IsUnitary) (ψ : P) :
    (1 - M.loopOp O) (M.catalyst₀ hO ψ) = M.C ψ ∧ M.catalyst₀ hO ψ ∈ (M.fixedSpace O)ᗮ :=
  Classical.choose_spec (M.existsUnique_steady_solution hO ψ).exists

/-- A solution of the fixed-point equation solves `(1 - D Q) Γ ψ = C ψ`. -/
theorem one_sub_loopOp_apply_of_eq {O : OracleTuple K} {Γ : P →L[ℂ] L}
    (hΓ : Γ = M.C + M.D ∘L M.Q O ∘L Γ) (ψ : P) : (1 - M.loopOp O) (Γ ψ) = M.C ψ := by
  have hψ := congrArg (fun T : P →L[ℂ] L => T ψ) hΓ
  simp only [add_apply, ContinuousLinearMap.comp_apply] at hψ
  rw [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, sub_eq_iff_eq_add]
  exact hψ

/-- The minimum-norm catalyst satisfies the fixed-point equation `Γ₀ = C + D Q Γ₀`. -/
theorem catalyst₀_eq {O : OracleTuple K} (hO : O.IsUnitary) :
    M.catalyst₀ hO = M.C + M.D ∘L M.Q O ∘L M.catalyst₀ hO := by
  ext ψ
  have h := (M.catalyst₀_spec hO ψ).1
  rw [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, sub_eq_iff_eq_add] at h
  rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact h

/-- Any solution of the fixed-point equation with range orthogonal to the fixed space is
the minimum-norm catalyst. -/
theorem catalyst₀_unique {O : OracleTuple K} (hO : O.IsUnitary) {Γ : P →L[ℂ] L}
    (hΓ : Γ = M.C + M.D ∘L M.Q O ∘L Γ) (hperp : ∀ ψ, Γ ψ ∈ (M.fixedSpace O)ᗮ) :
    Γ = M.catalyst₀ hO := by
  ext ψ
  exact (M.existsUnique_steady_solution hO ψ).unique
    ⟨M.one_sub_loopOp_apply_of_eq hΓ ψ, hperp ψ⟩ (M.catalyst₀_spec hO ψ)

/-- On a regular loop the minimum-norm catalyst is the inverse-based one. -/
theorem catalyst₀_eq_catalyst {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    M.catalyst₀ hO = M.catalyst O := by
  have hinj := (M.isRegular_iff_injective O).1 h
  have hN : M.fixedSpace O = ⊥ := LinearMap.ker_eq_bot.2 hinj
  refine (M.catalyst₀_unique hO (M.catalyst_eq h) (fun ψ => ?_)).symm
  rw [hN, Submodule.bot_orthogonal_eq_top]
  exact Submodule.mem_top

/-- MOD-2b. The transfer value `F = A + B Q Γ₀`. -/
noncomputable def steady₀ {O : OracleTuple K} (hO : O.IsUnitary) : P →L[ℂ] P :=
  M.A + M.B ∘L M.Q O ∘L M.catalyst₀ hO

/-- The steady-state equation for the minimum-norm catalyst:
`S (ψ ⊕ Q Γ₀ ψ) = F ψ ⊕ Γ₀ ψ` (mQSP Eq. (2.7)). -/
theorem steady₀_state_eq {O : OracleTuple K} (hO : O.IsUnitary) (ψ : P) :
    M.S (DSum.mk ψ (M.Q O (M.catalyst₀ hO ψ))) =
      DSum.mk (M.steady₀ hO ψ) (M.catalyst₀ hO ψ) := by
  rw [S_apply, DSum.fst_mk, DSum.snd_mk]
  have h1 : M.A ψ + M.B (M.Q O (M.catalyst₀ hO ψ)) = M.steady₀ hO ψ := rfl
  have h2 : M.C ψ + M.D (M.Q O (M.catalyst₀ hO ψ)) = M.catalyst₀ hO ψ := by
    conv_rhs => rw [catalyst₀_eq M hO]
    rfl
  rw [h1, h2]

/-- The transfer value does not depend on the solution of the fixed-point equation. -/
theorem steady₀_eq_of_solution {O : OracleTuple K} (hO : O.IsUnitary) {Γ : P →L[ℂ] L}
    (hΓ : Γ = M.C + M.D ∘L M.Q O ∘L Γ) :
    M.steady₀ hO = M.A + M.B ∘L M.Q O ∘L Γ := by
  have key : M.B ∘L M.Q O ∘L M.catalyst₀ hO = M.B ∘L M.Q O ∘L Γ := by
    ext ψ
    have e1 := congrArg (fun T : P →L[ℂ] L => T ψ) hΓ
    have e2 := congrArg (fun T : P →L[ℂ] L => T ψ) (M.catalyst₀_eq hO)
    simp only [add_apply, ContinuousLinearMap.comp_apply] at e1 e2
    have hδ : Γ ψ - M.catalyst₀ hO ψ = M.D (M.Q O (Γ ψ - M.catalyst₀ hO ψ)) := by
      calc Γ ψ - M.catalyst₀ hO ψ
          = (M.C ψ + M.D (M.Q O (Γ ψ))) - (M.C ψ + M.D (M.Q O (M.catalyst₀ hO ψ))) := by
            rw [← e1, ← e2]
        _ = M.D (M.Q O (Γ ψ - M.catalyst₀ hO ψ)) := by
            rw [add_sub_add_left_eq_sub, map_sub, map_sub]
    have h0 := M.B_Q_eq_zero_of_fixed hO hδ
    rw [map_sub, map_sub, sub_eq_zero] at h0
    simp only [ContinuousLinearMap.comp_apply]
    exact h0.symm
  rw [steady₀, key]

theorem steady₀_eq_steady {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    M.steady₀ hO = M.steady O :=
  M.steady₀_eq_of_solution hO (M.catalyst_eq h)

/-- MOD-2b (mQSP Prop 5.1, Thm 2.1): the transfer value is always unitary. -/
theorem isUnitary_steady₀ {O : OracleTuple K} (hO : O.IsUnitary) : IsUnitary (M.steady₀ hO) := by
  apply isUnitary_of_isIsometry
  apply isIsometry_of_norm
  intro ψ
  have h1 := M.isUnitary_S.isIsometry.norm_map (DSum.mk ψ (M.Q O (M.catalyst₀ hO ψ)))
  rw [M.steady₀_state_eq hO] at h1
  have h2 := congrArg (fun t : ℝ => t ^ 2) h1
  simp only [DSum.norm_sq_eq, DSum.fst_mk, DSum.snd_mk,
    (M.isUnitary_Q hO).isIsometry.norm_map] at h2
  have h3 : ‖M.steady₀ hO ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

end Junction

end MQSP
