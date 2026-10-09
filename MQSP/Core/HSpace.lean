/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Star.Unitary

/-!
# Finite-dimensional Hilbert spaces and operators (CORE-1)

The whole library works with finite-dimensional complex Hilbert spaces (`HSpace`) and bounded
operators between them (`E →L[ℂ] F`). Direct sums are `WithLp 2 (E × F)` (`E ⊕ₕ F`) and
indexed direct sums are `PiLp 2 K`; a register of dimension `N` attached to `E` is the
indexed direct sum `PiLp 2 (fun _ : Fin N => E)` ("`Fin N ⊗ E`").

## Main definitions

* `MQSP.HSpace E`: bundled class (normed, inner product over `ℂ`, complete, finite-dimensional).
* `MQSP.DSum E F` (notation `E ⊕ₕ F`) and `MQSP.PiSum K`: direct sums with the `L²` inner product.
* `A†` for the adjoint `ContinuousLinearMap.adjoint A` of a rectangular operator.
* `MQSP.IsUnitary U`, `MQSP.IsProj P` (orthogonal projection), `MQSP.IsIsometry V`.

## Mathlib facts used

`star` on `E →L[ℂ] E` is the adjoint (`ContinuousLinearMap.star_eq_adjoint`), so for square
operators `IsSelfAdjoint`, `unitary (E →L[ℂ] E)` and `IsStarProjection` are available.
-/

namespace MQSP

universe u v w

/-- CORE-1. A finite-dimensional complex Hilbert space. -/
class HSpace (E : Type u) extends
  NormedAddCommGroup E, InnerProductSpace ℂ E, CompleteSpace E, FiniteDimensional ℂ E

/-- The Hilbert-space direct sum `E ⊕ F` with the `L²` inner product. -/
abbrev DSum (E : Type u) (F : Type v) : Type max u v := WithLp 2 (E × F)

@[inherit_doc] infixr:30 " ⊕ₕ " => DSum

/-- The indexed Hilbert-space direct sum `⊕ᵢ K i` with the `L²` inner product. -/
abbrev PiSum {ι : Type u} (K : ι → Type v) : Type max u v := PiLp 2 K

/-- The register `Fin N ⊗ E`, modelled as `N` copies of `E` in direct sum. -/
abbrev Reg (N : ℕ) (E : Type u) : Type u := PiLp 2 (fun _ : Fin N => E)

noncomputable instance instHSpaceDSum (E : Type u) (F : Type v) [HSpace E] [HSpace F] :
    HSpace (E ⊕ₕ F) := {}

noncomputable instance instHSpacePiSum {ι : Type u} [Fintype ι] (K : ι → Type v)
    [∀ i, HSpace (K i)] : HSpace (PiSum K) := {}

noncomputable instance instHSpaceReg (N : ℕ) (E : Type u) [HSpace E] : HSpace (Reg N E) := {}

noncomputable instance instHSpaceComplex : HSpace ℂ := {}

/-- The adjoint of a (rectangular) bounded operator. -/
notation:max A "†" => ContinuousLinearMap.adjoint A

section Predicates

open scoped InnerProductSpace

variable {E : Type u} {F : Type v} [HSpace E] [HSpace F]

@[simp] theorem adjoint_one : (1 : E →L[ℂ] E)† = 1 := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.adjoint_id]

@[simp] theorem one_comp (f : E →L[ℂ] F) : (1 : F →L[ℂ] F) ∘L f = f := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

@[simp] theorem comp_one (f : E →L[ℂ] F) : f ∘L (1 : E →L[ℂ] E) = f := by
  rw [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

theorem star_two : star (2 : ℂ) = 2 := by rw [Complex.star_def, map_ofNat]

/-- `U` is unitary: `U† U = 1` and `U U† = 1`. For square operators this is
`U ∈ unitary (E →L[ℂ] E)`. -/
def IsUnitary (U : E →L[ℂ] F) : Prop := U† ∘L U = 1 ∧ U ∘L U† = 1

/-- `V` is an isometry: `V† V = 1`. -/
def IsIsometry (V : E →L[ℂ] F) : Prop := V† ∘L V = 1

/-- `P` is an orthogonal projection: self-adjoint and idempotent. -/
def IsProj (P : E →L[ℂ] E) : Prop := P† = P ∧ P ∘L P = P

theorem isUnitary_iff_mem_unitary (U : E →L[ℂ] E) : IsUnitary U ↔ U ∈ unitary (E →L[ℂ] E) := by
  simp only [IsUnitary, unitary, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]

theorem IsUnitary.isIsometry {U : E →L[ℂ] F} (h : IsUnitary U) : IsIsometry U := h.1

theorem IsUnitary.adjoint {U : E →L[ℂ] F} (h : IsUnitary U) : IsUnitary (U†) := by
  refine ⟨?_, ?_⟩ <;> simp only [ContinuousLinearMap.adjoint_adjoint, h.1, h.2]

theorem IsUnitary.comp {G : Type w} [HSpace G] {U : F →L[ℂ] G} {V : E →L[ℂ] F}
    (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U ∘L V) := by
  refine ⟨?_, ?_⟩
  · rw [ContinuousLinearMap.adjoint_comp]
    calc V† ∘L U† ∘L (U ∘L V) = V† ∘L (U† ∘L U) ∘L V := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = 1 := by rw [hU.1, one_comp]; exact hV.1
  · rw [ContinuousLinearMap.adjoint_comp]
    calc U ∘L V ∘L (V† ∘L U†) = U ∘L (V ∘L V†) ∘L U† := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = 1 := by rw [hV.2, one_comp]; exact hU.2

theorem isUnitary_one : IsUnitary (1 : E →L[ℂ] E) := by
  constructor <;> simp only [adjoint_one, one_comp]

theorem IsIsometry.apply_adjoint_apply {V : E →L[ℂ] F} (h : IsIsometry V) (x : E) :
    V† (V x) = x := by
  have := congrArg (fun T : E →L[ℂ] E => T x) h
  simpa using this

theorem IsIsometry.inner_map_map {V : E →L[ℂ] F} (h : IsIsometry V) (x y : E) :
    ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, h.apply_adjoint_apply]

theorem IsIsometry.norm_map {V : E →L[ℂ] F} (h : IsIsometry V) (x : E) : ‖V x‖ = ‖x‖ := by
  have h1 := h.inner_map_map x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖V x‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem IsIsometry.opNorm_le_one {V : E →L[ℂ] F} (h : IsIsometry V) : ‖V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [h.norm_map, one_mul])

theorem IsUnitary.opNorm_le_one {U : E →L[ℂ] F} (h : IsUnitary U) : ‖U‖ ≤ 1 :=
  h.isIsometry.opNorm_le_one

/-- In finite dimension an isometric endomorphism is unitary. -/
theorem isUnitary_of_isIsometry {U : E →L[ℂ] E} (h : IsIsometry U) : IsUnitary U := by
  refine ⟨h, ?_⟩
  have hinj : Function.Injective (U : E →ₗ[ℂ] E) := by
    intro x y hxy
    have := congrArg (U†) hxy
    simpa [h.apply_adjoint_apply] using this
  have hsurj : Function.Surjective (U : E →ₗ[ℂ] E) := LinearMap.injective_iff_surjective.1 hinj
  ext y
  obtain ⟨x, hx⟩ := hsurj y
  simp only [ContinuousLinearMap.coe_coe] at hx
  rw [← hx]
  simp [h.apply_adjoint_apply]

/-- An operator preserving inner products is an isometry. -/
theorem isIsometry_of_inner {V : E →L[ℂ] F} (h : ∀ x y, ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ) :
    IsIsometry V := by
  ext x
  apply ext_inner_left ℂ
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, h,
    one_apply_eq_self]

/-- An operator preserving norms is an isometry (polarization). -/
theorem isIsometry_of_norm {V : E →L[ℂ] F} (h : ∀ x, ‖V x‖ = ‖x‖) : IsIsometry V := by
  let Vi : E →ₗᵢ[ℂ] F := ⟨V.toLinearMap, h⟩
  exact isIsometry_of_inner (fun x y => Vi.inner_map_map x y)

theorem IsProj.isSelfAdjoint {P : E →L[ℂ] E} (h : IsProj P) : IsSelfAdjoint P := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]; exact h.1

theorem IsProj.one_sub {P : E →L[ℂ] E} (h : IsProj P) : IsProj (1 - P) := by
  refine ⟨?_, ?_⟩
  · rw [map_sub, adjoint_one, h.1]
  · simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, h.2]
    abel

theorem isProj_one : IsProj (1 : E →L[ℂ] E) := by
  constructor
  · exact adjoint_one
  · simp

theorem isProj_zero : IsProj (0 : E →L[ℂ] E) := by
  constructor <;> simp

/-- The reflection `2P - 1` about the range of a projection. -/
noncomputable def reflection (P : E →L[ℂ] E) : E →L[ℂ] E := (2 : ℂ) • P - 1

theorem IsProj.reflection_adjoint {P : E →L[ℂ] E} (h : IsProj P) :
    (reflection P)† = reflection P := by
  rw [reflection, ← ContinuousLinearMap.star_eq_adjoint, star_sub, star_smul, star_one,
    ContinuousLinearMap.star_eq_adjoint, h.1, star_two]

theorem IsProj.reflection_sq {P : E →L[ℂ] E} (h : IsProj P) :
    reflection P ∘L reflection P = 1 := by
  simp only [reflection, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, one_comp, comp_one, h.2]
  module

/-- The reflection about the range of a projection is unitary. -/
theorem IsProj.reflection_isUnitary {P : E →L[ℂ] E} (h : IsProj P) :
    IsUnitary (reflection P) :=
  ⟨by rw [h.reflection_adjoint, h.reflection_sq], by rw [h.reflection_adjoint, h.reflection_sq]⟩

end Predicates

end MQSP
