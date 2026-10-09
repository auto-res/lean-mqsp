/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.PiSum

/-!
# Registers `Fin n ⊗ E` (CORE-5)

`Reg n E = PiLp 2 (fun _ : Fin n => E)` models a register of dimension `n` attached to `E`
(clock registers, delay buffers, ancilla qubits). This file specialises the `PiSum` API:
`Reg.single s : E →L Reg n E` ("`|s⟩ ⊗ ·`"), `Reg.proj s` ("`⟨s| ⊗ ·`"), and
`Reg.map T = 1 ⊗ T` (apply `T` on every slot).
-/

namespace MQSP

universe u

open scoped InnerProductSpace

namespace Reg

variable {E : Type u} [HSpace E] {n : ℕ}

/-- `|s⟩ ⊗ x`. -/
noncomputable abbrev single (s : Fin n) : E →L[ℂ] Reg n E := PiSum.single (K := fun _ => E) s

/-- `⟨s| ⊗ ·`. -/
noncomputable abbrev proj (s : Fin n) : Reg n E →L[ℂ] E := PiSum.proj (K := fun _ => E) s

/-- `1 ⊗ T`: apply `T` on every slot. -/
noncomputable abbrev map (T : E →L[ℂ] E) : Reg n E →L[ℂ] Reg n E :=
  PiSum.diag (K := fun _ => E) (fun _ => T)

@[simp] theorem proj_single_same (s : Fin n) (x : E) : proj s (single s x) = x :=
  PiSum.proj_single_same (K := fun _ => E) s x

@[simp] theorem proj_single_of_ne {s t : Fin n} (h : t ≠ s) (x : E) : proj t (single s x) = 0 :=
  PiSum.proj_single_of_ne (K := fun _ => E) h x

@[ext] theorem ext {v w : Reg n E} (h : ∀ s, proj s v = proj s w) : v = w := PiSum.ext h

@[simp] theorem adjoint_single (s : Fin n) : (single s : E →L[ℂ] Reg n E)† = proj s :=
  PiSum.adjoint_single s

@[simp] theorem adjoint_proj (s : Fin n) : (proj s : Reg n E →L[ℂ] E)† = single s :=
  PiSum.adjoint_proj s

theorem isIsometry_single (s : Fin n) : IsIsometry (single s : E →L[ℂ] Reg n E) :=
  PiSum.isIsometry_single s

theorem sum_single_proj : ∑ s, (single s ∘L proj s : Reg n E →L[ℂ] Reg n E) = 1 :=
  PiSum.sum_single_proj

theorem norm_sq_eq (v : Reg n E) : ‖v‖ ^ 2 = ∑ s, ‖proj s v‖ ^ 2 := PiSum.norm_sq_eq v

@[simp] theorem proj_map (T : E →L[ℂ] E) (s : Fin n) (v : Reg n E) :
    proj s (map T v) = T (proj s v) :=
  PiSum.proj_diag_apply _ s v

@[simp] theorem map_single (T : E →L[ℂ] E) (s : Fin n) (x : E) :
    map T (single s x) = single s (T x) := by
  ext t
  by_cases h : t = s
  · subst h; simp
  · simp [proj_single_of_ne h]

theorem map_comp_map (T T' : E →L[ℂ] E) : map T ∘L map T' = map (n := n) (T ∘L T') :=
  PiSum.diag_comp_diag _ _

theorem adjoint_map (T : E →L[ℂ] E) : (map (n := n) T)† = map (T†) := PiSum.adjoint_diag _

@[simp] theorem map_one : map (n := n) (1 : E →L[ℂ] E) = 1 := PiSum.diag_one

theorem isUnitary_map {T : E →L[ℂ] E} (h : IsUnitary T) : IsUnitary (map (n := n) T) :=
  PiSum.isUnitary_diag (fun _ => h)

end Reg

end MQSP
