/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg
import MQSP.Core.BlockEncoding
import MQSP.Modules.Signals

/-!
# The preparation query (LIB-2; mQSP Eq. (5.14), (5.58))

State-preparation access `U |0⟩ = |ψ⟩` (with inverse access) has a canonical bidirectional
query: on a direction qubit, `V_U = |0⟩⟨1| ⊗ U† + |1⟩⟨0| ⊗ U` is self-inverse (a reflection),
so it supplies a Hermitian signal on the doubled space `Reg 2 E`; its off-diagonal blocks are
`U` and `U†`. Each use costs one `U` and one `U†`. The weighted state-preparation algorithm
(mQSP §6.2, Cor 5.8) feeds these into the weighted Cayley junction.
-/

namespace MQSP

universe u

namespace Signals

variable {E : Type u} [HSpace E]

/-- LIB-2 (mQSP Eq. (5.14)). The preparation query `V_U = |0⟩⟨1| ⊗ U† + |1⟩⟨0| ⊗ U`. -/
noncomputable def prepQuery (U : E →L[ℂ] E) : Reg 2 E →L[ℂ] Reg 2 E :=
  Reg.single 0 ∘L U† ∘L Reg.proj 1 + Reg.single 1 ∘L U ∘L Reg.proj 0

theorem prepQuery_adjoint (U : E →L[ℂ] E) : (prepQuery U)† = prepQuery U := by
  simp only [prepQuery, map_add, ContinuousLinearMap.adjoint_comp, Reg.adjoint_single,
    Reg.adjoint_proj, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  exact add_comm _ _

theorem prepQuery_sq {U : E →L[ℂ] E} (hU : IsUnitary U) : prepQuery U ∘L prepQuery U = 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hUU : ∀ f : Reg 2 E →L[ℂ] E, U† ∘L U ∘L f = f := fun f => by
    rw [← ContinuousLinearMap.comp_assoc, hU.1, one_comp]
  have hUU' : ∀ f : Reg 2 E →L[ℂ] E, U ∘L U† ∘L f = f := fun f => by
    rw [← ContinuousLinearMap.comp_assoc, hU.2, one_comp]
  have hsum := Reg.sum_single_proj (n := 2) (E := E)
  rw [Fin.sum_univ_two] at hsum
  simp only [prepQuery, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc, proj_comp_single_same_comp, hUU, hUU',
    proj_comp_single_of_ne_comp h10, proj_comp_single_of_ne_comp h10.symm,
    ContinuousLinearMap.comp_zero, zero_add, add_zero]
  exact (add_comm _ _).trans hsum

theorem isUnitary_prepQuery {U : E →L[ℂ] E} (hU : IsUnitary U) : IsUnitary (prepQuery U) := by
  rw [IsUnitary, prepQuery_adjoint]
  exact ⟨prepQuery_sq hU, prepQuery_sq hU⟩

/-- The `(1, 0)` block of the preparation query is `U`: it is an encoding of `U` between the
isometries `|0⟩ ⊗ ·` and `|1⟩ ⊗ ·`. -/
theorem isEncodingOf_prepQuery {U : E →L[ℂ] E} (hU : IsUnitary U) :
    IsEncodingOf (prepQuery U) (Reg.single 0) (Reg.single 1) U := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine ⟨isUnitary_prepQuery hU, Reg.isIsometry_single 0, Reg.isIsometry_single 1, ?_⟩
  simp only [prepQuery, Reg.adjoint_single, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc, proj_comp_single_same_comp,
    proj_comp_single_of_ne_comp h10, proj_comp_single_same, comp_one,
    zero_add]

/-- The `(0, 1)` block is `U†`. -/
theorem proj_zero_prepQuery_single_one (U : E →L[ℂ] E) :
    Reg.proj 0 ∘L prepQuery U ∘L Reg.single 1 = U† := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [prepQuery, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, proj_comp_single_same_comp,
    proj_comp_single_of_ne_comp h10.symm, proj_comp_single_same, comp_one,
    add_zero]

/-- The diagonal blocks vanish. -/
theorem proj_zero_prepQuery_single_zero (U : E →L[ℂ] E) :
    Reg.proj 0 ∘L prepQuery U ∘L Reg.single 0 = 0 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h : (Reg.proj 1 : Reg 2 E →L[ℂ] E) ∘L Reg.single 0 = 0 :=
    ContinuousLinearMap.ext fun x => by simp [Reg.proj_single_of_ne h10]
  simp only [prepQuery, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_assoc, proj_comp_single_of_ne_comp h10.symm, h,
    ContinuousLinearMap.comp_zero, add_zero]

end Signals

end MQSP
