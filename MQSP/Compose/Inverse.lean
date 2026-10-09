/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Defs

/-!
# The inverse of a junction (COMP-8; mQSP §5.2 Inverse)

Reversing the known system (`S†`) and using inverse oracle feedback connections (`O j†`)
implements the adjoint transfer value `F†` at `z = 1`, with the same catalyst norm on the
corresponding output state: `Γ_inv = Q Γ F†`.
-/

namespace MQSP

universe u v w x

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K)

/-- COMP-8. The inverse junction: system matrix `S†`, same ports and delays. -/
noncomputable def inverse : Junction P L K where
  S := M.S†
  isUnitary_S := M.isUnitary_S.adjoint
  ports := M.ports
  delay := M.delay
  one_le_delay := M.one_le_delay

/-- The inverse oracle tuple `j ↦ (O j)†`. -/
noncomputable def OracleTuple.inv' {ι : Type u} {K : ι → Type w} [∀ i, HSpace (K i)]
    (O : OracleTuple K) : OracleTuple K :=
  fun j => (O j)†

theorem inverse_A : M.inverse.A = M.A† := by
  change DSum.fst ∘L M.S† ∘L DSum.inl = _
  rw [S_eq_block, DSum.adjoint_block, DSum.fst_block_inl]

theorem inverse_B : M.inverse.B = M.C† := by
  change DSum.fst ∘L M.S† ∘L DSum.inr = _
  rw [S_eq_block, DSum.adjoint_block, DSum.fst_block_inr]

theorem inverse_C : M.inverse.C = M.B† := by
  change DSum.snd ∘L M.S† ∘L DSum.inl = _
  rw [S_eq_block, DSum.adjoint_block, DSum.snd_block_inl]

theorem inverse_D : M.inverse.D = M.D† := by
  change DSum.snd ∘L M.S† ∘L DSum.inr = _
  rw [S_eq_block, DSum.adjoint_block, DSum.snd_block_inr]

theorem inverse_Q (O : OracleTuple K) : M.inverse.Q (OracleTuple.inv' O) = (M.Q O)† :=
  (M.ports.adjoint_feedback O).symm

/-- COMP-8. The inverse loop is regular iff the original loop is. -/
theorem inverse_isRegular_iff {O : OracleTuple K} (hO : O.IsUnitary) :
    M.inverse.IsRegular (OracleTuple.inv' O) ↔ M.IsRegular O := by
  have hQ := M.isUnitary_Q hO
  have hQQ : M.Q O * (M.Q O)† = 1 := hQ.2
  -- `Q` is a unit, and `1 - Q D = Q (1 - D Q) Q⁻¹`, whose adjoint is `1 - D† Q†`.
  let u : (L →L[ℂ] L)ˣ := ⟨M.Q O, (M.Q O)†, hQ.2, hQ.1⟩
  have h1 : (↑u * (1 - M.D * M.Q O) * ↑u⁻¹ : L →L[ℂ] L) = 1 - M.Q O * M.D := by
    change M.Q O * (1 - M.D * M.Q O) * (M.Q O)† = _
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hQQ]
  have e : 1 - M.inverse.D ∘L M.inverse.Q (OracleTuple.inv' O) =
      star (↑u * (1 - M.D * M.Q O) * ↑u⁻¹) := by
    rw [h1, inverse_D, inverse_Q, star_sub, star_one, star_mul,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def]
  rw [IsRegular, IsRegular, e, isUnit_star, Units.isUnit_mul_units, Units.isUnit_units_mul]
  rfl

/-- The steady-state equation read backwards through `S†`:
`A† F ψ + C† Γ ψ = ψ` and `B† F ψ + D† Γ ψ = Q Γ ψ`. -/
theorem adjoint_steady_state_eq {O : OracleTuple K} (h : M.IsRegular O) (ψ : P) :
    M.A† (M.steady O ψ) + M.C† (M.catalyst O ψ) = ψ ∧
      M.B† (M.steady O ψ) + M.D† (M.catalyst O ψ) = M.Q O (M.catalyst O ψ) := by
  have h1 := M.isUnitary_S.isIsometry.apply_adjoint_apply
    (DSum.mk ψ (M.Q O (M.catalyst O ψ)))
  rw [steady_state_eq M h, S_eq_block, DSum.adjoint_block, DSum.block_apply] at h1
  exact ⟨congrArg DSum.fst h1, congrArg DSum.snd h1⟩

/-- COMP-8. The catalyst of the inverse junction is `Q Γ F†`. -/
theorem inverse_catalyst {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    M.inverse.catalyst (OracleTuple.inv' O) = M.Q O ∘L M.catalyst O ∘L (M.steady O)† := by
  have hF : ∀ χ, M.steady O ((M.steady O)† χ) = χ := fun χ => by
    simpa using congrArg (fun T : P →L[ℂ] P => T χ) (M.isUnitary_steady hO h).2
  symm
  refine catalyst_unique _ ((M.inverse_isRegular_iff hO).2 h) ?_
  rw [inverse_C, inverse_D, inverse_Q]
  ext χ
  have key := (M.adjoint_steady_state_eq h ((M.steady O)† χ)).2
  rw [hF] at key
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    (M.isUnitary_Q hO).isIsometry.apply_adjoint_apply]
  exact key.symm

/-- COMP-8 (mQSP §5.2 Inverse). The transfer value of the inverse junction is `F†`. -/
theorem inverse_steady {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    M.inverse.steady (OracleTuple.inv' O) = (M.steady O)† := by
  have hF : ∀ χ, M.steady O ((M.steady O)† χ) = χ := fun χ => by
    simpa using congrArg (fun T : P →L[ℂ] P => T χ) (M.isUnitary_steady hO h).2
  conv_lhs => rw [steady]
  rw [inverse_A, inverse_B, inverse_Q, inverse_catalyst M hO h]
  ext χ
  have key := (M.adjoint_steady_state_eq h ((M.steady O)† χ)).1
  rw [hF] at key
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    (M.isUnitary_Q hO).isIsometry.apply_adjoint_apply]
  exact key

end Junction

end MQSP
