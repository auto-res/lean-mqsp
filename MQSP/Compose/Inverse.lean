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
noncomputable def OracleTuple.inv' {ι : Type u} {K : ι → Type w} [∀ i, HSpace (K i)] (O : OracleTuple K) :
    OracleTuple K :=
  fun j => (O j)†

theorem inverse_A : M.inverse.A = M.A† := by sorry
theorem inverse_B : M.inverse.B = M.C† := by sorry
theorem inverse_C : M.inverse.C = M.B† := by sorry
theorem inverse_D : M.inverse.D = M.D† := by sorry

theorem inverse_Q (O : OracleTuple K) : M.inverse.Q (OracleTuple.inv' O) = (M.Q O)† := by sorry

/-- COMP-8. The inverse loop is regular iff the original loop is. -/
theorem inverse_isRegular_iff {O : OracleTuple K} (hO : O.IsUnitary) :
    M.inverse.IsRegular (OracleTuple.inv' O) ↔ M.IsRegular O := by sorry

/-- COMP-8. The catalyst of the inverse junction is `Q Γ F†`. -/
theorem inverse_catalyst {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    M.inverse.catalyst (OracleTuple.inv' O) = M.Q O ∘L M.catalyst O ∘L (M.steady O)† := by
  sorry

/-- COMP-8 (mQSP §5.2 Inverse). The transfer value of the inverse junction is `F†`. -/
theorem inverse_steady {O : OracleTuple K} (hO : O.IsUnitary) (h : M.IsRegular O) :
    M.inverse.steady (OracleTuple.inv' O) = (M.steady O)† := by
  sorry

end Junction

end MQSP
