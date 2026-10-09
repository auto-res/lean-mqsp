/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg
import MQSP.Core.BlockEncoding

/-!
# Signal normalisation of oracle access (LIB-2; mQSP §5.1 Eq. (5.11)–(5.14))

Different access models supply different signals. Given a block encoding `V` of `A/λ` with
signal injection `s = |0⟩ₐ ⊗ I` (so `A/λ = s† V s`), the following known constructions turn
it into the canonical signals used by the modules:

* **direct projected query** (5.11): `s† V s = A/λ`;
* **Hermitian dilation** (5.12): on a direction qubit, `J_V = |0⟩⟨1| ⊗ V† + |1⟩⟨0| ⊗ V` is
  self-inverse and `(|0⟩⟨0| ⊗ s† ⊕ |1⟩⟨1| ⊗ s†) J_V (…) = [[0, A†/λ], [A/λ, 0]]`;
* **reflection walk** (5.13): `R = V† (2Π_out - 1) V` satisfies `s† R s = 2 A†A/λ² - 1`
  (the degree-two Chebyshev transformation of the singular values);
* **preparation query** (5.14): for `U|0⟩ = |ψ⟩`, `V_U = |0⟩⟨1| ⊗ U† + |1⟩⟨0| ⊗ U` is a
  self-inverse Hermitian signal on a doubled space.
-/

namespace MQSP

universe u

open scoped InnerProductSpace

namespace Signals

variable {E : Type u} [HSpace E]

/-- The signal injection `|0⟩ₐ ⊗ I : E → Reg 2 E`. -/
noncomputable abbrev s : E →L[ℂ] Reg 2 E := Reg.single 0

/-- The signal projector `Π = |0⟩⟨0|ₐ ⊗ I`. -/
noncomputable abbrev sigProj : Reg 2 E →L[ℂ] Reg 2 E := Reg.single 0 ∘L Reg.proj 0

/-- The encoded block `s† V s`. -/
noncomputable abbrev blk (V : Reg 2 E →L[ℂ] Reg 2 E) : E →L[ℂ] E := Reg.proj 0 ∘L V ∘L Reg.single 0

/-- LIB-2 (mQSP Eq. (5.13)). The reflection walk `R = V† (2Π - 1) V`. -/
noncomputable def reflWalk (V : Reg 2 E →L[ℂ] Reg 2 E) : Reg 2 E →L[ℂ] Reg 2 E :=
  V† ∘L reflection (sigProj (E := E)) ∘L V

/-- `⟨i| ∘ |i⟩ = 1`, composed on the right with an arbitrary operator. -/
theorem proj_comp_single_same_comp {n : ℕ} {F : Type*} [HSpace F] (i : Fin n)
    (f : F →L[ℂ] E) : Reg.proj i ∘L Reg.single i ∘L f = f :=
  ContinuousLinearMap.ext fun x => by simp

/-- `⟨t| ∘ |s⟩ = 0` for `t ≠ s`, composed on the right with an arbitrary operator. -/
theorem proj_comp_single_of_ne_comp {n : ℕ} {F : Type*} [HSpace F] {s t : Fin n} (h : t ≠ s)
    (f : F →L[ℂ] E) : Reg.proj t ∘L Reg.single s ∘L f = 0 :=
  ContinuousLinearMap.ext fun x => by simp [Reg.proj_single_of_ne h]

theorem proj_comp_single_same {n : ℕ} (i : Fin n) :
    (Reg.proj i : Reg n E →L[ℂ] E) ∘L Reg.single i = 1 :=
  ContinuousLinearMap.ext fun x => by simp

theorem isProj_sigProj : IsProj (sigProj (E := E)) := by
  refine ⟨?_, ?_⟩
  · simp only [sigProj, ContinuousLinearMap.adjoint_comp, Reg.adjoint_single, Reg.adjoint_proj]
  · simp only [sigProj, ContinuousLinearMap.comp_assoc, proj_comp_single_same_comp]

theorem isUnitary_reflWalk {V : Reg 2 E →L[ℂ] Reg 2 E} (hV : IsUnitary V) :
    IsUnitary (reflWalk V) :=
  hV.adjoint.comp (isProj_sigProj.reflection_isUnitary.comp hV)

/-- LIB-2 (mQSP Eq. (5.13)). The reflection walk block-encodes `2 A†A - 1`
(`A = s† V s`): `s† R s = 2 A† A - 1`. -/
theorem blk_reflWalk {V : Reg 2 E →L[ℂ] Reg 2 E} (hV : IsUnitary V) :
    blk (reflWalk V) = (2 : ℂ) • ((blk V)† ∘L blk V) - 1 := by
  have hVV : ∀ {F : Type u} [HSpace F] (f : F →L[ℂ] Reg 2 E), V† ∘L V ∘L f = f := fun f => by
    rw [← ContinuousLinearMap.comp_assoc, hV.1, one_comp]
  simp only [blk, reflWalk, reflection, sigProj, ContinuousLinearMap.adjoint_comp,
    Reg.adjoint_single, Reg.adjoint_proj, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    one_comp, ContinuousLinearMap.comp_assoc, hVV, proj_comp_single_same]

/-- LIB-2 (mQSP Eq. (5.12)). The Hermitian dilation on a direction qubit:
`J = |0⟩⟨1| ⊗ V† + |1⟩⟨0| ⊗ V` on `Reg 2 (Reg 2 E)`. -/
noncomputable def hermDilation (V : Reg 2 E →L[ℂ] Reg 2 E) :
    Reg 2 (Reg 2 E) →L[ℂ] Reg 2 (Reg 2 E) :=
  Reg.single 0 ∘L V† ∘L Reg.proj 1 + Reg.single 1 ∘L V ∘L Reg.proj 0

theorem hermDilation_adjoint (V : Reg 2 E →L[ℂ] Reg 2 E) :
    (hermDilation V)† = hermDilation V := by
  simp only [hermDilation, map_add, ContinuousLinearMap.adjoint_comp, Reg.adjoint_single,
    Reg.adjoint_proj, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  exact add_comm _ _

theorem hermDilation_sq {V : Reg 2 E →L[ℂ] Reg 2 E} (hV : IsUnitary V) :
    hermDilation V ∘L hermDilation V = 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hVV : ∀ f : Reg 2 (Reg 2 E) →L[ℂ] Reg 2 E, V† ∘L V ∘L f = f := fun f => by
    rw [← ContinuousLinearMap.comp_assoc, hV.1, one_comp]
  have hVV' : ∀ f : Reg 2 (Reg 2 E) →L[ℂ] Reg 2 E, V ∘L V† ∘L f = f := fun f => by
    rw [← ContinuousLinearMap.comp_assoc, hV.2, one_comp]
  have hsum := Reg.sum_single_proj (n := 2) (E := Reg 2 E)
  rw [Fin.sum_univ_two] at hsum
  simp only [hermDilation, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_assoc, proj_comp_single_same_comp, hVV, hVV',
    proj_comp_single_of_ne_comp h10, proj_comp_single_of_ne_comp h10.symm,
    ContinuousLinearMap.comp_zero, zero_add, add_zero]
  exact (add_comm _ _).trans hsum

end Signals

end MQSP
