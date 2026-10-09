/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.QSVT.Core
import MQSP.Modules.Chain

/-!
# The QSP/QSVT phase sequence as an mQSP module (QSVT-1)

The alternating phase sequence `U_Φ` (GSLW Def 15) is the chain junction whose known unitaries
are the phase operators `e^{iφₖ(2Π-1)}` / `e^{iφₖ(2Π̃-1)}` and whose oracles alternate `U`, `U†`.
In the language of mQSP: `qsp Φ U = Series_k (Query (U or U†) ; Wire (phaseOp …))`, a
feedback-free module (`D` nilpotent) with transfer function `z^d U_Φ`, catalyst weight `1` per
port (`d` in total), impulse response concentrated at delay `d`, and steady value `U_Φ`.
Composing with the SVD-free QSVT theorem (`MQSP.QSVT.proj_UΦ_proj_odd/even`) gives the
singular value transformation as the projected steady value of this module; compiling it
with the endpoint clock (`MQSP.Compile.Endpoint`) reproduces the QSVT circuit.
-/

namespace MQSP

universe u

namespace QSVT

variable {H : Type u} [HSpace H]

/-- The known unitaries of the QSP chain: `V 0 = 1`, `V (k+1) = phaseOp (Π̃ or Π) φₖ`
(after an even step `k` the projector is `Π̃`, after an odd step it is `Π`). -/
noncomputable def chainData (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr) (hPr' : IsProj Pr')
    (Φ : List ℝ) : Junction.ChainData H Φ.length where
  V k := if h : (k : ℕ) = 0 then 1 else
    if (k - 1) % 2 = 0 then phaseOp Pr' (Φ.getD (k - 1) 0) else phaseOp Pr (Φ.getD (k - 1) 0)
  isUnitary_V k := by
    split_ifs
    · exact isUnitary_one
    · exact isUnitary_phaseOp hPr' _
    · exact isUnitary_phaseOp hPr _

/-- The alternating oracles `U, U†, U, …` of the QSP chain. -/
noncomputable def chainOracles (U : H →L[ℂ] H) (d : ℕ) : Fin d → (H →L[ℂ] H) :=
  fun k => if (k : ℕ) % 2 = 0 then U else U†

/-- QSVT-1. The QSP phase-sequence module. -/
noncomputable def qsp (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr) (hPr' : IsProj Pr') (Φ : List ℝ) :
    Junction H (Reg Φ.length H) (Junction.chainPorts H Φ.length) :=
  (chainData Pr Pr' hPr hPr' Φ).junction

/-- Appending a phase appends one step to the alternating sequence. -/
theorem altFrom_append_singleton (U Pr Pr' : H →L[ℂ] H) (φ : ℝ) :
    ∀ (Φ : List ℝ) (k : ℕ) (V : H →L[ℂ] H),
      altFrom U Pr Pr' (Φ ++ [φ]) k V = stepOp U Pr Pr' (k + Φ.length) φ ∘L altFrom U Pr Pr' Φ k V
  | [], k, V => by simp [altFrom]
  | ψ :: Φ, k, V => by
    simp only [List.cons_append, altFrom, List.length_cons]
    rw [altFrom_append_singleton U Pr Pr' φ Φ, show k + 1 + Φ.length = k + (Φ.length + 1) by omega]

/-- Parity of the predecessor of `k + 1` in `Fin (d + 1)` (the convention of `chainData`). -/
theorem fin_sub_one_mod_two_eq_zero_iff {d k : ℕ} (hk : k + 1 < d + 1) :
    ((⟨k + 1, hk⟩ : Fin (d + 1)) - 1) % 2 = 0 ↔ k % 2 = 0 := by
  have h1 : ((⟨k + 1, hk⟩ : Fin (d + 1)) - 1) = ⟨k, by omega⟩ := by
    ext
    rw [Fin.coe_sub_one]
    simp
  rw [h1, Fin.ext_iff, Fin.val_mod, Fin.val_zero]
  rcases Nat.lt_or_ge d 2 with hd | hd
  · obtain rfl : k = 0 := by omega
    simp
  · have h2 : ((2 : Fin (d + 1)) : ℕ) = 2 := Nat.mod_eq_of_lt (a := 2) (b := d + 1) (by omega)
    rw [h2]

/-- The QSP chain after `k` steps (followed by the next phase operator `V k`) is the
alternating sequence of the first `k` phases. -/
theorem chainData_V_comp_go (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr) (hPr' : IsProj Pr')
    (U : H →L[ℂ] H) (Φ : List ℝ) (k : ℕ) (hk : k ≤ Φ.length) :
    (chainData Pr Pr' hPr hPr' Φ).V ⟨k, by omega⟩ ∘L
      Junction.ChainData.circuit.go (chainData Pr Pr' hPr hPr' Φ) (chainOracles U Φ.length) k hk =
      altFrom U Pr Pr' (Φ.take k) 0 1 := by
  induction k with
  | zero => simp [chainData, Junction.ChainData.circuit.go, altFrom]
  | succ k ih =>
    have hk' : k < Φ.length := by omega
    rw [Junction.ChainData.circuit.go, ih (by omega), List.take_succ_eq_append_getElem hk',
      altFrom_append_singleton, List.length_take, min_eq_left (by omega), zero_add,
      ← ContinuousLinearMap.comp_assoc]
    congr 1
    simp only [chainData, chainOracles, stepOp, Nat.add_one_ne_zero, ↓reduceDIte,
      Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk',
      Option.getD_some, fin_sub_one_mod_two_eq_zero_iff]
    split_ifs <;> rfl

/-- The chain circuit of the QSP data is the alternating phase sequence `U_Φ`. -/
theorem chainData_circuit (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr) (hPr' : IsProj Pr')
    (U : H →L[ℂ] H) (Φ : List ℝ) :
    (chainData Pr Pr' hPr hPr' Φ).circuit (chainOracles U Φ.length) = UΦ U Pr Pr' Φ := by
  have h := chainData_V_comp_go Pr Pr' hPr hPr' U Φ Φ.length le_rfl
  rw [List.take_length] at h
  rw [Junction.ChainData.circuit, UΦ]
  exact h

/-- QSVT-1. The steady value of the QSP module is `U_Φ`. -/
theorem qsp_steady (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr) (hPr' : IsProj Pr') (U : H →L[ℂ] H)
    (Φ : List ℝ) :
    (qsp Pr Pr' hPr hPr' Φ).steady (Junction.ChainData.oracles (chainOracles U Φ.length)) =
      UΦ U Pr Pr' Φ := by
  rw [qsp, Junction.ChainData.steady_eq_circuit, chainData_circuit]

/-- QSVT-3 as a statement about the module: for an odd number of phases the projected steady
value is the singular value transformation `A ∘ p_Φ(A†A)`. -/
theorem proj_qsp_steady_proj_odd {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) (hΦ : Φ.length % 2 = 1) :
    Pr' ∘L (qsp Pr Pr' hPr hPr' Φ).steady (Junction.ChainData.oracles (chainOracles U Φ.length))
      ∘L Pr = enc U Pr Pr' ∘L Polynomial.aeval ((enc U Pr Pr')† ∘L enc U Pr Pr') (pqΦ Φ).1 := by
  rw [qsp_steady]
  exact proj_UΦ_proj_odd hU hPr hPr' Φ hΦ

/-- QSVT-1. Every port of the QSP module has catalyst weight `‖ψ‖²`: the module makes one
query per step, `|Φ|` in total. -/
theorem qsp_weight {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U) (hPr : IsProj Pr) (hPr' : IsProj Pr')
    (Φ : List ℝ) (k : Fin Φ.length) (ψ : H) :
    (qsp Pr Pr' hPr hPr' Φ).weight (Junction.ChainData.oracles (chainOracles U Φ.length)) k ψ =
      ‖ψ‖ ^ 2 := by
  have _ := hPr
  have _ := hPr'
  refine Junction.ChainData.weight_eq _ _ (fun j => ?_) k ψ
  unfold chainOracles
  split_ifs
  · exact hU
  · exact hU.adjoint

end QSVT

end MQSP
