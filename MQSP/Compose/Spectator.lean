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
    proj s (mapTo T v) = T (proj s v) := by sorry

theorem mapTo_single (T : E →L[ℂ] F) (s : Fin n) (x : E) :
    mapTo T (single s x) = single s (T x) := by sorry

theorem mapTo_comp {G : Type w} [HSpace G] (T : F →L[ℂ] G) (T' : E →L[ℂ] F) :
    mapTo (n := n) (T ∘L T') = mapTo T ∘L mapTo T' := by sorry

theorem adjoint_mapTo (T : E →L[ℂ] F) : (mapTo (n := n) T)† = mapTo (T†) := by sorry

theorem mapTo_add (T T' : E →L[ℂ] F) : mapTo (n := n) (T + T') = mapTo T + mapTo T' := by sorry

@[simp] theorem mapTo_one : mapTo (n := n) (1 : E →L[ℂ] E) = 1 := by sorry

@[simp] theorem mapTo_zero : mapTo (n := n) (0 : E →L[ℂ] F) = 0 := by sorry

theorem mapTo_eq_map (T : E →L[ℂ] E) : mapTo (n := n) T = map T := by sorry

end Reg

namespace Ports

variable {L : Type v} [HSpace L] {ι : Type u} [Fintype ι] {K : ι → Type w} [∀ i, HSpace (K i)]

/-- Ports of `Reg n L` with port spaces `Reg n (K j)`. -/
noncomputable def reg (n : ℕ) (ps : Ports L K) : Ports (Reg n L) (fun j => Reg n (K j)) where
  π j := Reg.mapTo (ps.π j)
  π_comp_adj_self j := by sorry
  π_comp_adj_ne i j h := by sorry
  sum_adj_comp := by sorry

end Ports

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (n : ℕ)

/-- COMP-5. The junction with a spectator register `Fin n` tensored on every space. -/
noncomputable def spectator : Junction (Reg n P) (Reg n L) (fun j => Reg n (K j)) where
  S := DSum.block (Reg.mapTo M.A) (Reg.mapTo M.B) (Reg.mapTo M.C) (Reg.mapTo M.D)
  isUnitary_S := by sorry
  ports := M.ports.reg n
  delay := M.delay
  one_le_delay := M.one_le_delay

/-- The spectator oracle tuple `j ↦ 1 ⊗ O j`. -/
noncomputable def OracleTuple.reg {ι : Type u} {K : ι → Type w} [∀ i, HSpace (K i)] (n : ℕ)
    (O : OracleTuple K) : OracleTuple (fun j => Reg n (K j)) :=
  fun j => Reg.map (O j)

theorem spectator_A : (M.spectator n).A = Reg.mapTo M.A := by sorry
theorem spectator_B : (M.spectator n).B = Reg.mapTo M.B := by sorry
theorem spectator_C : (M.spectator n).C = Reg.mapTo M.C := by sorry
theorem spectator_D : (M.spectator n).D = Reg.mapTo M.D := by sorry

theorem spectator_Q (O : OracleTuple K) :
    (M.spectator n).Q (OracleTuple.reg n O) = Reg.map (M.Q O) := by sorry

theorem spectator_isRegular_iff (O : OracleTuple K) :
    (M.spectator n).IsRegular (OracleTuple.reg n O) ↔ (n = 0 ∨ M.IsRegular O) := by sorry

theorem spectator_catalyst {O : OracleTuple K} (h : M.IsRegular O) :
    (M.spectator n).catalyst (OracleTuple.reg n O) = Reg.mapTo (M.catalyst O) := by sorry

/-- COMP-5. The transfer value with a spectator register is `1 ⊗ F`. -/
theorem spectator_steady {O : OracleTuple K} (h : M.IsRegular O) :
    (M.spectator n).steady (OracleTuple.reg n O) = Reg.map (M.steady O) := by sorry

end Junction

end MQSP
