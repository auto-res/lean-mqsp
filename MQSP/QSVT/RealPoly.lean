/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.QSVT.Core
import MQSP.Compose.Project

/-!
# Real polynomials by phase conjugation (QSVT-3; GSLW Cor 18)

Negating all phases conjugates the QSP polynomial pair (`pqΦ_neg`), so the average of `U_Φ`
and `U_{-Φ}` — the direct sum of the two chains flagged by `|+⟩` (an LCU) — implements the
singular value transformation by the *real part* `(p + p̄)/2` of `p_Φ`. In particular every
QSVT with a real polynomial is the `|+⟩`-projection of `U_Φ ⊕ U_{-Φ}` (GSLW Cor 18); the two
branches share the same query schedule, so in a circuit they are merged into one controlled
sequence with the same number of queries (GSLW Lemma 19).
-/

namespace MQSP

universe u

open Polynomial

namespace QSVT

variable {H : Type u} [HSpace H]

/-- The real part of a complex polynomial, as a complex polynomial: `(p + p̄)/2`. -/
noncomputable def rePoly (p : ℂ[X]) : ℂ[X] := C ((2 : ℂ)⁻¹) * (p + p.map (starRingEnd ℂ))

theorem rePoly_coeff (p : ℂ[X]) (k : ℕ) : (rePoly p).coeff k = ((p.coeff k).re : ℂ) := by
  rw [rePoly, coeff_C_mul, coeff_add, coeff_map, Complex.add_conj, Complex.ofReal_mul,
    Complex.ofReal_ofNat, ← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]

/-- `c • q(y) = (C c * q)(y)`. -/
theorem smul_aeval (y : H →L[ℂ] H) (c : ℂ) (q : ℂ[X]) : c • aeval y q = aeval y (C c * q) := by
  rw [aeval_mul, aeval_C, Algebra.smul_def]

/-- The block-diagonal operator `U ⊕ V` of two unitaries is unitary. -/
theorem isUnitary_block_diag {U V : H →L[ℂ] H} (hU : IsUnitary U) (hV : IsUnitary V) :
    IsUnitary (DSum.block U 0 0 V) := by
  constructor <;>
  · rw [DSum.adjoint_block, DSum.block_comp_block]
    simp [hU.1, hU.2, hV.1, hV.2]

/-- GSLW Cor 18 (odd case): `Π' (U_Φ + U_{-Φ})/2 Π = A ∘ Re(p_Φ)(A†A)`. -/
theorem proj_average_proj_odd {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 1) :
    Pr' ∘L ((2 : ℂ)⁻¹ • (UΦ U Pr Pr' Φ + UΦ U Pr Pr' (Φ.map Neg.neg))) ∘L Pr =
      enc U Pr Pr' ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (rePoly (pqΦ Φ).1) := by
  have hΦ' : (Φ.map Neg.neg).length % 2 = 1 := by rwa [List.length_map]
  have hneg := congrArg Prod.fst (pqΦ_neg Φ)
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    proj_UΦ_proj_odd hU hPr hPr' Φ hΦ, proj_UΦ_proj_odd hU hPr hPr' _ hΦ', hneg,
    ← ContinuousLinearMap.comp_add, ← map_add, ← ContinuousLinearMap.comp_smul, smul_aeval,
    rePoly]

/-- GSLW Cor 18 (even case). -/
theorem proj_average_proj_even {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 0) :
    Pr ∘L ((2 : ℂ)⁻¹ • (UΦ U Pr Pr' Φ + UΦ U Pr Pr' (Φ.map Neg.neg))) ∘L Pr =
      Pr ∘L aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (rePoly (pqΦ Φ).1) ∘L Pr := by
  have hΦ' : (Φ.map Neg.neg).length % 2 = 0 := by rwa [List.length_map]
  have hneg := congrArg Prod.fst (pqΦ_neg Φ)
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    proj_UΦ_proj_even hU hPr hPr' Φ hΦ, proj_UΦ_proj_even hU hPr hPr' _ hΦ', hneg,
    ← ContinuousLinearMap.comp_add, ← ContinuousLinearMap.add_comp, ← map_add,
    ← ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.smul_comp, smul_aeval, rePoly]

/-- The average `(U_Φ + U_{-Φ})/2` is the `|+⟩`-block of `U_Φ ⊕ U_{-Φ}`: an encoding. -/
theorem isEncodingOf_average {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) :
    IsEncodingOf (DSum.block (UΦ U Pr Pr' Φ) 0 0 (UΦ U Pr Pr' (Φ.map Neg.neg))) DSum.plus
      DSum.plus ((2 : ℂ)⁻¹ • (UΦ U Pr Pr' Φ + UΦ U Pr Pr' (Φ.map Neg.neg))) :=
  ⟨isUnitary_block_diag (isUnitary_UΦ hU hPr hPr' Φ) (isUnitary_UΦ hU hPr hPr' _),
    DSum.isIsometry_plus, DSum.isIsometry_plus, DSum.plus_adj_block_plus _ _⟩

end QSVT

end MQSP
