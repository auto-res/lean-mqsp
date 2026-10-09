/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg
import MQSP.Module.Defs

/-!
# Spectator registers (COMP-5; mQSP §5.2 Spectator)

A register `Fin n` carried through unchanged tensors every space of a junction: public
`Reg n P`, private `Reg n L`, ports `Reg n (K j)` on which the oracles act as `1 ⊗ O j`.
The transfer value becomes `1 ⊗ F` (`Reg.map F`), and the rule holds for entangled inputs.
-/

namespace MQSP

universe u v w x

open Finset

namespace Reg

variable {E : Type u} {F : Type v} [HSpace E] [HSpace F] {n : ℕ}

/-- `1 ⊗ T` for a rectangular `T : E → F`: apply `T` on every slot. -/
noncomputable def mapTo (T : E →L[ℂ] F) : Reg n E →L[ℂ] Reg n F :=
  ∑ s, single s ∘L T ∘L proj s

@[simp] theorem proj_mapTo (T : E →L[ℂ] F) (s : Fin n) (v : Reg n E) :
    proj s (mapTo T v) = T (proj s v) := by
  simp only [mapTo, _root_.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single s]
  · rw [proj_single_same]
  · intro t _ hts; rw [proj_single_of_ne (Ne.symm hts)]
  · intro h; exact absurd (Finset.mem_univ s) h

theorem mapTo_single (T : E →L[ℂ] F) (s : Fin n) (x : E) :
    mapTo T (single s x) = single s (T x) := by
  refine Reg.ext fun t => ?_
  by_cases h : t = s
  · subst h; simp
  · simp [proj_single_of_ne h]

theorem mapTo_comp {G : Type w} [HSpace G] (T : F →L[ℂ] G) (T' : E →L[ℂ] F) :
    mapTo (n := n) (T ∘L T') = mapTo T ∘L mapTo T' :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

theorem adjoint_mapTo (T : E →L[ℂ] F) : (mapTo (n := n) T)† = mapTo (T†) := by
  simp only [mapTo, map_sum, ContinuousLinearMap.adjoint_comp, adjoint_single, adjoint_proj,
    ContinuousLinearMap.comp_assoc]

theorem mapTo_add (T T' : E →L[ℂ] F) : mapTo (n := n) (T + T') = mapTo T + mapTo T' :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

theorem mapTo_sub (T T' : E →L[ℂ] F) : mapTo (n := n) (T - T') = mapTo T - mapTo T' :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

theorem mapTo_sum {ι : Type*} (t : Finset ι) (T : ι → E →L[ℂ] F) :
    mapTo (n := n) (∑ i ∈ t, T i) = ∑ i ∈ t, mapTo (T i) :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp [_root_.sum_apply, map_sum]

@[simp] theorem mapTo_one : mapTo (n := n) (1 : E →L[ℂ] E) = 1 :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

@[simp] theorem mapTo_zero : mapTo (n := n) (0 : E →L[ℂ] F) = 0 :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

theorem mapTo_eq_map (T : E →L[ℂ] E) : mapTo (n := n) T = map T :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

theorem one_sub_mapTo_comp_map (T T' : E →L[ℂ] E) :
    (1 : Reg n E →L[ℂ] Reg n E) - mapTo T ∘L map T' = mapTo (1 - T ∘L T') :=
  ContinuousLinearMap.ext fun v => Reg.ext fun s => by simp

/-- `1 ⊗ T` is injective iff `T` is, or the register is empty. -/
theorem injective_mapTo_iff (T : E →L[ℂ] F) :
    Function.Injective (mapTo (n := n) T) ↔ n = 0 ∨ Function.Injective T := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · refine Or.inr fun x y hxy => ?_
      have := h (a₁ := single ⟨0, hn⟩ x) (a₂ := single ⟨0, hn⟩ y)
        (by rw [mapTo_single, mapTo_single, hxy])
      simpa using congrArg (proj ⟨0, hn⟩) this
  · rintro (hn | hT) v w hvw
    · subst hn
      exact Reg.ext fun s => s.elim0
    · refine Reg.ext fun s => hT ?_
      rw [← proj_mapTo, ← proj_mapTo, hvw]

end Reg

namespace Ports

variable {L : Type v} [HSpace L] {ι : Type u} [Fintype ι] {K : ι → Type w} [∀ i, HSpace (K i)]

/-- Ports of `Reg n L` with port spaces `Reg n (K j)`. -/
noncomputable def reg (n : ℕ) (ps : Ports L K) : Ports (Reg n L) (fun j => Reg n (K j)) where
  π j := Reg.mapTo (ps.π j)
  π_comp_adj_self j := by
    rw [Reg.adjoint_mapTo, ← Reg.mapTo_comp, ps.π_comp_adj_self, Reg.mapTo_one]
  π_comp_adj_ne i j h := by
    rw [Reg.adjoint_mapTo, ← Reg.mapTo_comp, ps.π_comp_adj_ne i j h, Reg.mapTo_zero]
  sum_adj_comp := by
    simp only [Reg.adjoint_mapTo, ← Reg.mapTo_comp]
    rw [← Reg.mapTo_sum, ps.sum_adj_comp, Reg.mapTo_one]

end Ports

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (n : ℕ)

/-- COMP-5. The junction with a spectator register `Fin n` tensored on every space. -/
noncomputable def spectator : Junction (Reg n P) (Reg n L) (fun j => Reg n (K j)) where
  S := DSum.block (Reg.mapTo M.A) (Reg.mapTo M.B) (Reg.mapTo M.C) (Reg.mapTo M.D)
  isUnitary_S := by
    obtain ⟨h1, h2, h3, h4⟩ := M.adj_mul_blocks
    obtain ⟨k1, k2, k3, k4⟩ := M.mul_adj_blocks
    constructor
    · rw [DSum.adjoint_block, DSum.block_comp_block]
      simp only [Reg.adjoint_mapTo, ← Reg.mapTo_comp, ← Reg.mapTo_add, h1, h2, h3, h4,
        Reg.mapTo_one, Reg.mapTo_zero, DSum.block_one_zero_zero_one]
    · rw [DSum.adjoint_block, DSum.block_comp_block]
      simp only [Reg.adjoint_mapTo, ← Reg.mapTo_comp, ← Reg.mapTo_add, k1, k2, k3, k4,
        Reg.mapTo_one, Reg.mapTo_zero, DSum.block_one_zero_zero_one]
  ports := M.ports.reg n
  delay := M.delay
  one_le_delay := M.one_le_delay

/-- The spectator oracle tuple `j ↦ 1 ⊗ O j`. -/
noncomputable def OracleTuple.reg {ι : Type u} {K : ι → Type w} [∀ i, HSpace (K i)] (n : ℕ)
    (O : OracleTuple K) : OracleTuple (fun j => Reg n (K j)) :=
  fun j => Reg.map (O j)

theorem spectator_A : (M.spectator n).A = Reg.mapTo M.A := DSum.fst_block_inl _ _ _ _
theorem spectator_B : (M.spectator n).B = Reg.mapTo M.B := DSum.fst_block_inr _ _ _ _
theorem spectator_C : (M.spectator n).C = Reg.mapTo M.C := DSum.snd_block_inl _ _ _ _
theorem spectator_D : (M.spectator n).D = Reg.mapTo M.D := DSum.snd_block_inr _ _ _ _

theorem spectator_Q (O : OracleTuple K) :
    (M.spectator n).Q (OracleTuple.reg n O) = Reg.map (M.Q O) := by
  change ∑ j, (Reg.mapTo (M.ports.π j))† ∘L Reg.map (O j) ∘L Reg.mapTo (M.ports.π j) =
    Reg.map (M.ports.feedback O)
  simp only [← Reg.mapTo_eq_map, Reg.adjoint_mapTo, ← Reg.mapTo_comp, ← Reg.mapTo_sum]
  rfl

theorem spectator_isRegular_iff (O : OracleTuple K) :
    (M.spectator n).IsRegular (OracleTuple.reg n O) ↔ (n = 0 ∨ M.IsRegular O) := by
  rw [isRegular_iff_injective, isRegular_iff_injective, spectator_D, spectator_Q,
    Reg.one_sub_mapTo_comp_map]
  exact Reg.injective_mapTo_iff _

theorem spectator_catalyst {O : OracleTuple K} (h : M.IsRegular O) :
    (M.spectator n).catalyst (OracleTuple.reg n O) = Reg.mapTo (M.catalyst O) := by
  symm
  refine catalyst_unique _ ((M.spectator_isRegular_iff n O).2 (Or.inr h)) ?_
  rw [spectator_C, spectator_D, spectator_Q, ← Reg.mapTo_eq_map, ← Reg.mapTo_comp,
    ← Reg.mapTo_comp, ← Reg.mapTo_add]
  exact congrArg Reg.mapTo (M.catalyst_eq h)

/-- COMP-5. The transfer value with a spectator register is `1 ⊗ F`. -/
theorem spectator_steady {O : OracleTuple K} (h : M.IsRegular O) :
    (M.spectator n).steady (OracleTuple.reg n O) = Reg.map (M.steady O) := by
  conv_lhs => rw [steady]
  rw [spectator_A, spectator_B, spectator_Q, spectator_catalyst M n h]
  simp only [← Reg.mapTo_eq_map]
  rw [← Reg.mapTo_comp, ← Reg.mapTo_comp, ← Reg.mapTo_add]
  rfl

end Junction

end MQSP
