/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.DSum

/-!
# Extending operators by the identity on an extra private summand (CORE-4)

For the connection rules of mQSP §5.2 a system matrix `S` on `P ⊕ₕ L₁` must act on the
enlarged space `P ⊕ₕ (L₁ ⊕ₕ L₂)` as `S ⊕ 1_{L₂}` ("extend each known system by identity on the
other's private space", Series rule). We define

* `extendR S` for `S : P ⊕ₕ L₁ →L P ⊕ₕ L₁` (identity on the right summand `L₂`),
* `extendL S` for `S : P ⊕ₕ L₂ →L P ⊕ₕ L₂` (identity on the left summand `L₁`),

prove their action on triples, norm preservation and unitarity, and the algebra
`extendR (S ∘ T) = extendR S ∘ extendR T`.
-/

namespace MQSP

universe u v w

open scoped InnerProductSpace

namespace DSum

variable {P : Type u} {L₁ : Type v} {L₂ : Type w} [HSpace P] [HSpace L₁] [HSpace L₂]

/-- CORE-4. `S ⊕ 1_{L₂}` on `P ⊕ₕ (L₁ ⊕ₕ L₂)`. -/
noncomputable def extendR (L₂ : Type w) [HSpace L₂] (S : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁) :
    P ⊕ₕ (L₁ ⊕ₕ L₂) →L[ℂ] P ⊕ₕ (L₁ ⊕ₕ L₂) :=
  block (fst ∘L S ∘L inl) (fst ∘L S ∘L inr ∘L fst) (inl ∘L snd ∘L S ∘L inl)
    (block (snd ∘L S ∘L inr) 0 0 1)

/-- CORE-4. `S ⊕ 1_{L₁}` on `P ⊕ₕ (L₁ ⊕ₕ L₂)` for `S` on `P ⊕ₕ L₂`. -/
noncomputable def extendL (L₁ : Type v) [HSpace L₁] (S : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂) :
    P ⊕ₕ (L₁ ⊕ₕ L₂) →L[ℂ] P ⊕ₕ (L₁ ⊕ₕ L₂) :=
  block (fst ∘L S ∘L inl) (fst ∘L S ∘L inr ∘L snd) (inr ∘L snd ∘L S ∘L inl)
    (block 1 0 0 (snd ∘L S ∘L inr))

/-- Every vector of `P ⊕ₕ (L₁ ⊕ₕ L₂)` is a triple. -/
theorem exists_eq_mk_mk (v : P ⊕ₕ (L₁ ⊕ₕ L₂)) : ∃ x y z, v = mk x (mk y z) :=
  ⟨fst v, fst (snd v), snd (snd v), rfl⟩

theorem extendR_apply (S : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁) (x : P) (y : L₁) (z : L₂) :
    extendR L₂ S (mk x (mk y z)) =
      mk (fst (S (mk x y))) (mk (snd (S (mk x y))) z) := by
  have h : S (mk x y) = S (inl x) + S (inr y) := by rw [mk_eq_inl_add_inr, map_add]
  rw [h]
  ext <;> simp [extendR, block_apply]

theorem extendL_apply (S : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂) (x : P) (y : L₁) (z : L₂) :
    extendL L₁ S (mk x (mk y z)) =
      mk (fst (S (mk x z))) (mk y (snd (S (mk x z)))) := by
  have h : S (mk x z) = S (inl x) + S (inr z) := by rw [mk_eq_inl_add_inr, map_add]
  rw [h]
  ext <;> simp [extendL, block_apply]

theorem norm_extendR_apply (S : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁) (x : P) (y : L₁) (z : L₂) :
    ‖extendR L₂ S (mk x (mk y z))‖ ^ 2 = ‖S (mk x y)‖ ^ 2 + ‖z‖ ^ 2 := by
  have h := norm_sq_eq (mk (snd (S (mk x y))) z)
  rw [extendR_apply, norm_sq_eq, norm_sq_eq (S (mk x y))]
  simp only [fst_mk, snd_mk] at h ⊢
  rw [h, add_assoc]

theorem norm_extendL_apply (S : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂) (x : P) (y : L₁) (z : L₂) :
    ‖extendL L₁ S (mk x (mk y z))‖ ^ 2 = ‖S (mk x z)‖ ^ 2 + ‖y‖ ^ 2 := by
  have h := norm_sq_eq (mk y (snd (S (mk x z))))
  rw [extendL_apply, norm_sq_eq, norm_sq_eq (S (mk x z))]
  simp only [fst_mk, snd_mk] at h ⊢
  rw [h]
  ring

theorem isUnitary_extendR {S : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁} (h : IsUnitary S) :
    IsUnitary (extendR L₂ S) := by
  refine isUnitary_of_isIsometry (isIsometry_of_norm fun v => ?_)
  obtain ⟨x, y, z, rfl⟩ := exists_eq_mk_mk v
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_extendR_apply, h.isIsometry.norm_map,
    norm_sq_eq (mk x y), norm_sq_eq (mk x (mk y z))]
  have h' := norm_sq_eq (mk y z)
  simp only [fst_mk, snd_mk] at h' ⊢
  rw [h']
  ring

theorem isUnitary_extendL {S : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂} (h : IsUnitary S) :
    IsUnitary (extendL L₁ S) := by
  refine isUnitary_of_isIsometry (isIsometry_of_norm fun v => ?_)
  obtain ⟨x, y, z, rfl⟩ := exists_eq_mk_mk v
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_extendL_apply, h.isIsometry.norm_map,
    norm_sq_eq (mk x z), norm_sq_eq (mk x (mk y z))]
  have h' := norm_sq_eq (mk y z)
  simp only [fst_mk, snd_mk] at h' ⊢
  rw [h']
  ring

theorem extendR_comp (S T : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁) :
    extendR L₂ (S ∘L T) = extendR L₂ S ∘L extendR L₂ T := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨x, y, z, rfl⟩ := exists_eq_mk_mk v
  simp only [ContinuousLinearMap.comp_apply, extendR_apply, mk_fst_snd]

theorem extendL_comp (S T : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂) :
    extendL L₁ (S ∘L T) = extendL L₁ S ∘L extendL L₁ T := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨x, y, z, rfl⟩ := exists_eq_mk_mk v
  simp only [ContinuousLinearMap.comp_apply, extendL_apply, mk_fst_snd]

@[simp] theorem extendR_one : extendR L₂ (1 : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨x, y, z, rfl⟩ := exists_eq_mk_mk v
  simp only [extendR_apply, one_apply_eq_self, fst_mk, snd_mk]

@[simp] theorem extendL_one : extendL L₁ (1 : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨x, y, z, rfl⟩ := exists_eq_mk_mk v
  simp only [extendL_apply, one_apply_eq_self, fst_mk, snd_mk]

theorem adjoint_extendR (S : P ⊕ₕ L₁ →L[ℂ] P ⊕ₕ L₁) :
    (extendR L₂ S)† = extendR L₂ (S†) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  obtain ⟨a, b, c, rfl⟩ := exists_eq_mk_mk v
  obtain ⟨a', b', c', rfl⟩ := exists_eq_mk_mk w
  have h := ContinuousLinearMap.adjoint_inner_left S (mk a' b') (mk a b)
  rw [← mk_fst_snd (S† (mk a b)), ← mk_fst_snd (S (mk a' b')), inner_mk_mk,
    inner_mk_mk] at h
  rw [extendR_apply, extendR_apply, inner_mk_mk, inner_mk_mk, inner_mk_mk, inner_mk_mk,
    ← add_assoc, ← add_assoc, h]

theorem adjoint_extendL (S : P ⊕ₕ L₂ →L[ℂ] P ⊕ₕ L₂) :
    (extendL L₁ S)† = extendL L₁ (S†) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  obtain ⟨a, b, c, rfl⟩ := exists_eq_mk_mk v
  obtain ⟨a', b', c', rfl⟩ := exists_eq_mk_mk w
  have h := ContinuousLinearMap.adjoint_inner_left S (mk a' c') (mk a c)
  rw [← mk_fst_snd (S† (mk a c)), ← mk_fst_snd (S (mk a' c')), inner_mk_mk,
    inner_mk_mk] at h
  rw [extendL_apply, extendL_apply, inner_mk_mk, inner_mk_mk, inner_mk_mk, inner_mk_mk]
  linear_combination h

end DSum

end MQSP
