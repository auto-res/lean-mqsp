/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Defs

/-!
# Known public gates (COMP-3; mQSP §5.2 Wire)

A known unitary `V` on the public space applied before a module changes the transfer value
to `F V` (and the catalyst to `Γ V`); applied after, to `V F` (catalyst unchanged).
The system matrices are `S (V ⊕ 1)` and `(V ⊕ 1) S`.
-/

namespace MQSP

universe u v w x

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-- The block-diagonal operator `V ⊕ 1` is unitary when `V` is. -/
theorem isUnitary_block_one {V : P →L[ℂ] P} (hV : IsUnitary V) :
    IsUnitary (DSum.block V 0 0 (1 : L →L[ℂ] L)) := by
  constructor <;>
  · rw [DSum.adjoint_block, DSum.block_comp_block]
    simp [hV.1, hV.2]

/-- COMP-3. Apply the known unitary `V` to the public input before the module. -/
noncomputable def wireBefore (V : P →L[ℂ] P) (hV : IsUnitary V) : Junction P L K where
  S := M.S ∘L DSum.block V 0 0 1
  isUnitary_S := M.isUnitary_S.comp (isUnitary_block_one hV)
  ports := M.ports
  delay := M.delay
  one_le_delay := M.one_le_delay

/-- COMP-3. Apply the known unitary `V` to the public output after the module. -/
noncomputable def wireAfter (V : P →L[ℂ] P) (hV : IsUnitary V) : Junction P L K where
  S := DSum.block V 0 0 1 ∘L M.S
  isUnitary_S := (isUnitary_block_one hV).comp M.isUnitary_S
  ports := M.ports
  delay := M.delay
  one_le_delay := M.one_le_delay

variable (V : P →L[ℂ] P) (hV : IsUnitary V) (O : OracleTuple K)

theorem wireBefore_A : (M.wireBefore V hV).A = M.A ∘L V := by
  change DSum.fst ∘L (M.S ∘L DSum.block V 0 0 1) ∘L DSum.inl = _
  rw [S_eq_block, DSum.block_comp_block, DSum.fst_block_inl]; simp
theorem wireBefore_B : (M.wireBefore V hV).B = M.B := by
  change DSum.fst ∘L (M.S ∘L DSum.block V 0 0 1) ∘L DSum.inr = _
  rw [S_eq_block, DSum.block_comp_block, DSum.fst_block_inr]; simp
theorem wireBefore_C : (M.wireBefore V hV).C = M.C ∘L V := by
  change DSum.snd ∘L (M.S ∘L DSum.block V 0 0 1) ∘L DSum.inl = _
  rw [S_eq_block, DSum.block_comp_block, DSum.snd_block_inl]; simp
theorem wireBefore_D : (M.wireBefore V hV).D = M.D := by
  change DSum.snd ∘L (M.S ∘L DSum.block V 0 0 1) ∘L DSum.inr = _
  rw [S_eq_block, DSum.block_comp_block, DSum.snd_block_inr]; simp
theorem wireAfter_A : (M.wireAfter V hV).A = V ∘L M.A := by
  change DSum.fst ∘L (DSum.block V 0 0 1 ∘L M.S) ∘L DSum.inl = _
  rw [S_eq_block, DSum.block_comp_block, DSum.fst_block_inl]; simp
theorem wireAfter_B : (M.wireAfter V hV).B = V ∘L M.B := by
  change DSum.fst ∘L (DSum.block V 0 0 1 ∘L M.S) ∘L DSum.inr = _
  rw [S_eq_block, DSum.block_comp_block, DSum.fst_block_inr]; simp
theorem wireAfter_C : (M.wireAfter V hV).C = M.C := by
  change DSum.snd ∘L (DSum.block V 0 0 1 ∘L M.S) ∘L DSum.inl = _
  rw [S_eq_block, DSum.block_comp_block, DSum.snd_block_inl]; simp
theorem wireAfter_D : (M.wireAfter V hV).D = M.D := by
  change DSum.snd ∘L (DSum.block V 0 0 1 ∘L M.S) ∘L DSum.inr = _
  rw [S_eq_block, DSum.block_comp_block, DSum.snd_block_inr]; simp

theorem wireBefore_Q : (M.wireBefore V hV).Q O = M.Q O := rfl
theorem wireAfter_Q : (M.wireAfter V hV).Q O = M.Q O := rfl

theorem wireBefore_isRegular_iff : (M.wireBefore V hV).IsRegular O ↔ M.IsRegular O := by
  rw [IsRegular, IsRegular, wireBefore_D, wireBefore_Q]
theorem wireAfter_isRegular_iff : (M.wireAfter V hV).IsRegular O ↔ M.IsRegular O := by
  rw [IsRegular, IsRegular, wireAfter_D, wireAfter_Q]

theorem wireBefore_catalyst : (M.wireBefore V hV).catalyst O = M.catalyst O ∘L V := by
  rw [catalyst, catalyst, wireBefore_D, wireBefore_Q, wireBefore_C,
    ContinuousLinearMap.comp_assoc]
theorem wireAfter_catalyst : (M.wireAfter V hV).catalyst O = M.catalyst O := by
  rw [catalyst, catalyst, wireAfter_D, wireAfter_Q, wireAfter_C]

/-- COMP-3. `F (V ⊕ 1)`-wiring gives transfer value `F V`. -/
theorem wireBefore_steady : (M.wireBefore V hV).steady O = M.steady O ∘L V := by
  rw [steady, steady, wireBefore_A, wireBefore_B, wireBefore_Q, wireBefore_catalyst,
    ContinuousLinearMap.add_comp]
  simp only [ContinuousLinearMap.comp_assoc]

/-- COMP-3. `(V ⊕ 1) S`-wiring gives transfer value `V F`. -/
theorem wireAfter_steady : (M.wireAfter V hV).steady O = V ∘L M.steady O := by
  rw [steady, steady, wireAfter_A, wireAfter_B, wireAfter_Q, wireAfter_catalyst,
    ContinuousLinearMap.comp_add]
  simp only [ContinuousLinearMap.comp_assoc]

theorem wireBefore_weight (i : ι) (ψ : P) :
    (M.wireBefore V hV).weight O i ψ = M.weight O i (V ψ) := by
  rw [weight, weight, wireBefore_catalyst]
  rfl

theorem wireAfter_weight (i : ι) (ψ : P) :
    (M.wireAfter V hV).weight O i ψ = M.weight O i ψ := by
  rw [weight, weight, wireAfter_catalyst]
  rfl

end Junction

end MQSP
