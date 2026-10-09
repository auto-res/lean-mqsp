/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Extend
import MQSP.Module.Defs

/-!
# Series connection of junctions (COMP-2)

mQSP §5.2 (Series) and Eq. (4.102)–(4.103), (5.15): connecting the public output of `M₁` to the
public input of `M₂` gives a junction on the public space `P` with private space `L₁ ⊕ₕ L₂`,
ports `ι₁ ⊕ ι₂`, system matrix `(S₂ ⊕ 1_{L₁}) ∘ (S₁ ⊕ 1_{L₂})`, and

* transfer value `F₂₁ = F₂ F₁`,
* catalyst `Γ₂₁ ψ = Γ₁ ψ ⊕ Γ₂ (F₁ ψ)`,
* weights `W₂₁ = W₁ + F₁† W₂ F₁` (thrifty composition).

Regularity of the composite follows from regularity of the parts (the composite loop operator
is block lower-triangular).
-/

namespace MQSP

universe u₁ u₂ v₁ v₂ w x

open scoped InnerProductSpace
open Finset

/-- `HSpace` instance for the port family of a sum of port index types. -/
instance instHSpaceSumElim {ι₁ : Type u₁} {ι₂ : Type u₂} {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w}
    [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)] : ∀ i : ι₁ ⊕ ι₂, HSpace (Sum.elim K₁ K₂ i)
  | Sum.inl i => inferInstanceAs (HSpace (K₁ i))
  | Sum.inr i => inferInstanceAs (HSpace (K₂ i))

/-- Restrict an oracle tuple on `ι₁ ⊕ ι₂` to the left ports. -/
abbrev OracleTuple.left {ι₁ : Type u₁} {ι₂ : Type u₂} {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w}
    [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)] (O : OracleTuple (Sum.elim K₁ K₂)) :
    OracleTuple K₁ :=
  fun i => O (Sum.inl i)

/-- Restrict an oracle tuple on `ι₁ ⊕ ι₂` to the right ports. -/
abbrev OracleTuple.right {ι₁ : Type u₁} {ι₂ : Type u₂} {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w}
    [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)] (O : OracleTuple (Sum.elim K₁ K₂)) :
    OracleTuple K₂ :=
  fun i => O (Sum.inr i)

/-- Glue two oracle tuples. -/
def OracleTuple.sum {ι₁ : Type u₁} {ι₂ : Type u₂} {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w}
    [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)] (O₁ : OracleTuple K₁) (O₂ : OracleTuple K₂) :
    OracleTuple (Sum.elim K₁ K₂)
  | Sum.inl i => O₁ i
  | Sum.inr i => O₂ i

theorem OracleTuple.IsUnitary.left {ι₁ : Type u₁} {ι₂ : Type u₂} {K₁ : ι₁ → Type w}
    {K₂ : ι₂ → Type w} [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)]
    {O : OracleTuple (Sum.elim K₁ K₂)} (h : O.IsUnitary) : O.left.IsUnitary :=
  fun i => h (Sum.inl i)

theorem OracleTuple.IsUnitary.right {ι₁ : Type u₁} {ι₂ : Type u₂} {K₁ : ι₁ → Type w}
    {K₂ : ι₂ → Type w} [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)]
    {O : OracleTuple (Sum.elim K₁ K₂)} (h : O.IsUnitary) : O.right.IsUnitary :=
  fun i => h (Sum.inr i)

namespace Ports

variable {L₁ : Type v₁} {L₂ : Type v₂} [HSpace L₁] [HSpace L₂]
variable {ι₁ : Type u₁} {ι₂ : Type u₂} [Fintype ι₁] [Fintype ι₂]
variable {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w} [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)]

section Helpers

/-! Auxiliary identities for operators precomposed with `DSum.fst` / `DSum.snd`. Stated with the
plain port types `K i`, they are applied to `Ports.sum` by definitional unfolding (simp lemmas do
not see through the `Sum.elim` instances). -/

variable {E : Type*} {F : Type*} [HSpace E] [HSpace F]

theorem fst_comp_adj_fst (f : L₁ →L[ℂ] E) (g : L₁ →L[ℂ] F) :
    (f ∘L (DSum.fst : L₁ ⊕ₕ L₂ →L[ℂ] L₁)) ∘L (g ∘L DSum.fst)† = f ∘L g† := by
  rw [ContinuousLinearMap.adjoint_comp, DSum.adjoint_fst]
  ext x; simp

theorem snd_comp_adj_snd (f : L₂ →L[ℂ] E) (g : L₂ →L[ℂ] F) :
    (f ∘L (DSum.snd : L₁ ⊕ₕ L₂ →L[ℂ] L₂)) ∘L (g ∘L DSum.snd)† = f ∘L g† := by
  rw [ContinuousLinearMap.adjoint_comp, DSum.adjoint_snd]
  ext x; simp

theorem fst_comp_adj_snd (f : L₁ →L[ℂ] E) (g : L₂ →L[ℂ] F) :
    (f ∘L (DSum.fst : L₁ ⊕ₕ L₂ →L[ℂ] L₁)) ∘L (g ∘L DSum.snd)† = 0 := by
  rw [ContinuousLinearMap.adjoint_comp, DSum.adjoint_snd]
  ext x; simp

theorem snd_comp_adj_fst (f : L₂ →L[ℂ] E) (g : L₁ →L[ℂ] F) :
    (f ∘L (DSum.snd : L₁ ⊕ₕ L₂ →L[ℂ] L₂)) ∘L (g ∘L DSum.fst)† = 0 := by
  rw [ContinuousLinearMap.adjoint_comp, DSum.adjoint_fst]
  ext x; simp

variable {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, HSpace (K i)]

theorem feedback_comp_fst (p : Ports L₁ K) (O : OracleTuple K) :
    ∑ i, (p.π i ∘L (DSum.fst : L₁ ⊕ₕ L₂ →L[ℂ] L₁))† ∘L O i ∘L
      (p.π i ∘L (DSum.fst : L₁ ⊕ₕ L₂ →L[ℂ] L₁)) =
      (DSum.inl : L₁ →L[ℂ] L₁ ⊕ₕ L₂) ∘L p.feedback O ∘L DSum.fst := by
  ext v <;> simp [_root_.sum_apply, map_sum, ContinuousLinearMap.adjoint_comp, feedback_apply]

theorem feedback_comp_snd (p : Ports L₂ K) (O : OracleTuple K) :
    ∑ i, (p.π i ∘L (DSum.snd : L₁ ⊕ₕ L₂ →L[ℂ] L₂))† ∘L O i ∘L
      (p.π i ∘L (DSum.snd : L₁ ⊕ₕ L₂ →L[ℂ] L₂)) =
      (DSum.inr : L₂ →L[ℂ] L₁ ⊕ₕ L₂) ∘L p.feedback O ∘L DSum.snd := by
  ext v <;> simp [_root_.sum_apply, map_sum, ContinuousLinearMap.adjoint_comp, feedback_apply]

theorem sum_adj_comp_fst (p : Ports L₁ K) :
    ∑ i, (p.π i ∘L (DSum.fst : L₁ ⊕ₕ L₂ →L[ℂ] L₁))† ∘L
      (p.π i ∘L (DSum.fst : L₁ ⊕ₕ L₂ →L[ℂ] L₁)) =
      (DSum.inl : L₁ →L[ℂ] L₁ ⊕ₕ L₂) ∘L DSum.fst := by
  ext v <;> simp [_root_.sum_apply, map_sum, ContinuousLinearMap.adjoint_comp, p.sum_adj_apply]

theorem sum_adj_comp_snd (p : Ports L₂ K) :
    ∑ i, (p.π i ∘L (DSum.snd : L₁ ⊕ₕ L₂ →L[ℂ] L₂))† ∘L
      (p.π i ∘L (DSum.snd : L₁ ⊕ₕ L₂ →L[ℂ] L₂)) =
      (DSum.inr : L₂ →L[ℂ] L₁ ⊕ₕ L₂) ∘L DSum.snd := by
  ext v <;> simp [_root_.sum_apply, map_sum, ContinuousLinearMap.adjoint_comp, p.sum_adj_apply]

end Helpers

/-- COMP-1. Ports of a direct sum of private spaces, indexed by `ι₁ ⊕ ι₂`. -/
noncomputable def sum (p₁ : Ports L₁ K₁) (p₂ : Ports L₂ K₂) :
    Ports (L₁ ⊕ₕ L₂) (Sum.elim K₁ K₂) where
  π
    | Sum.inl i => p₁.π i ∘L DSum.fst
    | Sum.inr i => p₂.π i ∘L DSum.snd
  π_comp_adj_self := by
    rintro (i | i)
    · exact (fst_comp_adj_fst _ _).trans (p₁.π_comp_adj_self i)
    · exact (snd_comp_adj_snd _ _).trans (p₂.π_comp_adj_self i)
  π_comp_adj_ne := by
    rintro (i | i) (j | j) h
    · exact (fst_comp_adj_fst _ _).trans (p₁.π_comp_adj_ne i j fun e => h (congrArg Sum.inl e))
    · exact fst_comp_adj_snd _ _
    · exact snd_comp_adj_fst _ _
    · exact (snd_comp_adj_snd _ _).trans (p₂.π_comp_adj_ne i j fun e => h (congrArg Sum.inr e))
  sum_adj_comp := by
    rw [Fintype.sum_sum_type]
    exact (congrArg₂ (· + ·) (sum_adj_comp_fst p₁) (sum_adj_comp_snd p₂)).trans
      DSum.inl_fst_add_inr_snd

@[simp] theorem sum_π_inl (p₁ : Ports L₁ K₁) (p₂ : Ports L₂ K₂) (i : ι₁) :
    (p₁.sum p₂).π (Sum.inl i) = p₁.π i ∘L DSum.fst := rfl

@[simp] theorem sum_π_inr (p₁ : Ports L₁ K₁) (p₂ : Ports L₂ K₂) (i : ι₂) :
    (p₁.sum p₂).π (Sum.inr i) = p₂.π i ∘L DSum.snd := rfl

/-- The feedback of glued ports is the direct sum of the feedbacks. -/
theorem sum_feedback (p₁ : Ports L₁ K₁) (p₂ : Ports L₂ K₂) (O : OracleTuple (Sum.elim K₁ K₂)) :
    (p₁.sum p₂).feedback O = DSum.block (p₁.feedback O.left) 0 0 (p₂.feedback O.right) := by
  rw [feedback, Fintype.sum_sum_type]
  refine (congrArg₂ (· + ·) (feedback_comp_fst p₁ O.left) (feedback_comp_snd p₂ O.right)).trans ?_
  ext v <;> simp

end Ports

namespace Junction

variable {P : Type x} [HSpace P]
variable {L₁ : Type v₁} {L₂ : Type v₂} [HSpace L₁] [HSpace L₂]
variable {ι₁ : Type u₁} {ι₂ : Type u₂} [Fintype ι₁] [Fintype ι₂]
variable {K₁ : ι₁ → Type w} {K₂ : ι₂ → Type w} [∀ i, HSpace (K₁ i)] [∀ i, HSpace (K₂ i)]

/-- COMP-2 (mQSP §5.2 Series). The series connection `M₂ ∘ M₁` (execute `M₁` first). -/
noncomputable def series (M₁ : Junction P L₁ K₁) (M₂ : Junction P L₂ K₂) :
    Junction P (L₁ ⊕ₕ L₂) (Sum.elim K₁ K₂) where
  S := DSum.extendL L₁ M₂.S ∘L DSum.extendR L₂ M₁.S
  isUnitary_S :=
    (DSum.isUnitary_extendL M₂.isUnitary_S).comp (DSum.isUnitary_extendR M₁.isUnitary_S)
  ports := M₁.ports.sum M₂.ports
  delay
    | Sum.inl i => M₁.delay i
    | Sum.inr i => M₂.delay i
  one_le_delay
    | Sum.inl i => M₁.one_le_delay i
    | Sum.inr i => M₂.one_le_delay i

variable (M₁ : Junction P L₁ K₁) (M₂ : Junction P L₂ K₂)

/-- The series system matrix on triples. -/
theorem series_S_apply (x : P) (y : L₁) (z : L₂) :
    (M₁.series M₂).S (DSum.mk x (DSum.mk y z)) =
      DSum.mk (M₂.A (M₁.A x + M₁.B y) + M₂.B z)
        (DSum.mk (M₁.C x + M₁.D y) (M₂.C (M₁.A x + M₁.B y) + M₂.D z)) := by
  simp only [series, ContinuousLinearMap.comp_apply, DSum.extendR_apply, DSum.extendL_apply,
    S_apply, DSum.fst_mk, DSum.snd_mk]

/-- The series system matrix in blocks. -/
theorem series_S_eq_block :
    (M₁.series M₂).S = DSum.block (M₂.A ∘L M₁.A) (M₂.A ∘L M₁.B ∘L DSum.fst + M₂.B ∘L DSum.snd)
      (DSum.inl ∘L M₁.C + DSum.inr ∘L M₂.C ∘L M₁.A) (DSum.block M₁.D 0 (M₂.C ∘L M₁.B) M₂.D) := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨x, y, z, rfl⟩ := DSum.exists_eq_mk_mk v
  rw [series_S_apply]
  ext <;> simp [DSum.block_apply, map_add] <;> abel

/-- Blocks of the series system matrix. -/
theorem series_A : (M₁.series M₂).A = M₂.A ∘L M₁.A := by
  rw [A, series_S_eq_block, DSum.fst_block_inl]

theorem series_B : (M₁.series M₂).B = M₂.A ∘L M₁.B ∘L DSum.fst + M₂.B ∘L DSum.snd := by
  rw [B, series_S_eq_block, DSum.fst_block_inr]

theorem series_C : (M₁.series M₂).C = DSum.inl ∘L M₁.C + DSum.inr ∘L M₂.C ∘L M₁.A := by
  rw [C, series_S_eq_block, DSum.snd_block_inl]

theorem series_D :
    (M₁.series M₂).D = DSum.block M₁.D 0 (M₂.C ∘L M₁.B) M₂.D := by
  rw [D, series_S_eq_block, DSum.snd_block_inr]

/-- The feedback of the series connection is block diagonal. -/
theorem series_Q (O : OracleTuple (Sum.elim K₁ K₂)) :
    (M₁.series M₂).Q O = DSum.block (M₁.Q O.left) 0 0 (M₂.Q O.right) :=
  Ports.sum_feedback _ _ _

/-- COMP-2. Regularity is inherited by the series connection. -/
theorem series_isRegular {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) : (M₁.series M₂).IsRegular O := by
  rw [isRegular_iff_injective] at h₁ h₂ ⊢
  rw [series_D, series_Q]
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  have e1 := congrArg DSum.fst hv
  have e2 := congrArg DSum.snd hv
  simp only [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, map_sub,
    DSum.fst_block_apply, DSum.snd_block_apply, zero_apply, add_zero, zero_add,
    map_zero] at e1 e2
  have g1 : DSum.fst v = 0 := h₁ <| by
    rw [map_zero, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
    exact e1
  rw [g1, map_zero, map_zero, map_zero, zero_add] at e2
  have g2 : DSum.snd v = 0 := h₂ <| by
    rw [map_zero, sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply]
    exact e2
  exact DSum.ext (g1.trans (map_zero _).symm) (g2.trans (map_zero _).symm)

/-- COMP-2 (mQSP Eq. (4.103)). The catalyst of the series connection is `Γ₁ ψ ⊕ Γ₂ (F₁ ψ)`. -/
theorem series_catalyst {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.series M₂).catalyst O =
      DSum.inl ∘L M₁.catalyst O.left + DSum.inr ∘L M₂.catalyst O.right ∘L M₁.steady O.left := by
  have hc₁ : ∀ ψ, M₁.catalyst O.left ψ =
      M₁.C ψ + M₁.D (M₁.Q O.left (M₁.catalyst O.left ψ)) :=
    fun ψ => congrArg (fun T : P →L[ℂ] L₁ => T ψ) (M₁.catalyst_eq h₁)
  have hc₂ : ∀ φ, M₂.catalyst O.right φ =
      M₂.C φ + M₂.D (M₂.Q O.right (M₂.catalyst O.right φ)) :=
    fun φ => congrArg (fun T : P →L[ℂ] L₂ => T φ) (M₂.catalyst_eq h₂)
  have hF₁ : ∀ ψ, M₁.steady O.left ψ = M₁.A ψ + M₁.B (M₁.Q O.left (M₁.catalyst O.left ψ)) :=
    fun _ => rfl
  symm
  refine catalyst_unique _ (M₁.series_isRegular M₂ h₁ h₂) ?_
  rw [series_C, series_D, series_Q]
  ext ψ
  · simp only [add_apply, ContinuousLinearMap.comp_apply, DSum.inl_apply, DSum.inr_apply,
      map_add, DSum.fst_mk, add_zero, ContinuousLinearMap.comp_add, DSum.block_apply,
      DSum.snd_mk, zero_apply, map_zero, zero_add]
    exact hc₁ ψ
  · simp only [add_apply, ContinuousLinearMap.comp_apply, DSum.inl_apply, DSum.inr_apply,
      map_add, DSum.snd_mk, zero_add, ContinuousLinearMap.comp_add, DSum.block_apply,
      DSum.fst_mk, zero_apply, add_zero, map_zero]
    exact (hc₂ _).trans (by rw [hF₁ ψ, map_add M₂.C, add_assoc])

/-- COMP-2 (mQSP Eq. (4.102)). The transfer value of the series connection is `F₂ F₁`. -/
theorem series_steady {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) :
    (M₁.series M₂).steady O = M₂.steady O.right ∘L M₁.steady O.left := by
  have hF₁ : ∀ ψ, M₁.steady O.left ψ = M₁.A ψ + M₁.B (M₁.Q O.left (M₁.catalyst O.left ψ)) :=
    fun _ => rfl
  have hF₂ : ∀ φ, M₂.steady O.right φ =
      M₂.A φ + M₂.B (M₂.Q O.right (M₂.catalyst O.right φ)) :=
    fun _ => rfl
  conv_lhs => rw [steady]
  rw [series_A, series_B, series_Q, series_catalyst M₁ M₂ h₁ h₂]
  ext ψ
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, add_apply,
    ContinuousLinearMap.comp_apply, DSum.inl_apply, DSum.block_apply, DSum.fst_mk, DSum.snd_mk,
    zero_apply, add_zero, map_zero, DSum.inr_apply, zero_add]
  rw [hF₂, ← add_assoc, ← map_add M₂.A, ← hF₁ ψ]

/-- COMP-2 (mQSP Eq. (5.15)). Weights of the left ports are those of `M₁`. -/
theorem series_weight_inl {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) (i : ι₁) (ψ : P) :
    (M₁.series M₂).weight O (Sum.inl i) ψ = M₁.weight O.left i ψ := by
  have h : DSum.fst ((M₁.series M₂).catalyst O ψ) = M₁.catalyst O.left ψ := by
    rw [series_catalyst M₁ M₂ h₁ h₂]
    simp
  change ‖M₁.ports.π i (DSum.fst ((M₁.series M₂).catalyst O ψ))‖ ^ 2 = _
  rw [h]
  rfl

/-- COMP-2 (mQSP Eq. (5.15)). Weights of the right ports are those of `M₂` on the transmitted
state `F₁ ψ`. -/
theorem series_weight_inr {O : OracleTuple (Sum.elim K₁ K₂)}
    (h₁ : M₁.IsRegular O.left) (h₂ : M₂.IsRegular O.right) (i : ι₂) (ψ : P) :
    (M₁.series M₂).weight O (Sum.inr i) ψ = M₂.weight O.right i (M₁.steady O.left ψ) := by
  have h : DSum.snd ((M₁.series M₂).catalyst O ψ) =
      M₂.catalyst O.right (M₁.steady O.left ψ) := by
    rw [series_catalyst M₁ M₂ h₁ h₂]
    simp
  change ‖M₂.ports.π i (DSum.snd ((M₁.series M₂).catalyst O ψ))‖ ^ 2 = _
  rw [h]
  rfl

end Junction

end MQSP
