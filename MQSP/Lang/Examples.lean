/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Lang.Prog
import MQSP.QSVT.Module

/-!
# Example programs (LANG-1)

Operator-level programs written in the surface language, with the theorems the language
attaches to them.

1. `cayleyTwice E`: the Cayley module applied twice in series. Its steady value is the square
   of the Cayley transform `((1 - iA)(1 + iA)⁻¹)²`, i.e. `e^{-4i arctan A}`, using two
   queries per traversal (one per port); the weight of the second port is evaluated on the
   transmitted state.
2. `qspProg`: a QSP phase sequence as a chain program; its steady value is `U_Φ` and its
   projected block is the singular value transformation.
3. `nested`: a Cayley module whose oracle is implemented by an inverse direct query — module
   substitution; the steady value is the Cayley transform of the inverse oracle.
-/

namespace MQSP

universe u

open Prog

namespace Examples

variable {E : Type u} [HSpace E]

/-- Two Cayley modules in series (two ports, each a self-inverse block encoding). -/
noncomputable def cayleyTwice (E : Type u) [HSpace E] :
    Prog E ((PortFamily.one (Reg 2 E)).sum (PortFamily.one (Reg 2 E))) :=
  cayley E ;; cayley E

/-- The steady value of `cayleyTwice` on the same self-inverse encoding `O` at both ports is
the square of the Cayley transform. -/
theorem cayleyTwice_steady {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : Junction.IsSelfInverse O) :
    steady (cayleyTwice E) (OracleTuple.sum (oneOracle O) (oneOracle O)) =
      let W := (1 - Complex.I • Junction.encoded O) ∘L
        Ring.inverse (1 + Complex.I • Junction.encoded O)
      W ∘L W := by
  have hreg : IsRegular (cayley E) (oneOracle O) := Junction.cayley_isRegular hO
  have hl : (OracleTuple.sum (oneOracle O) (oneOracle O)).left = oneOracle O :=
    funext fun _ => rfl
  have hr : (OracleTuple.sum (oneOracle O) (oneOracle O)).right = oneOracle O :=
    funext fun _ => rfl
  unfold cayleyTwice
  rw [steady_series (cayley E) (cayley E) (hl ▸ hreg) (hr ▸ hreg), hl, hr, steady_cayley hO]

/-- The QSP program of a phase list: a chain. -/
noncomputable def qspProg {H : Type u} [HSpace H] (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (Φ : List ℝ) : Prog H (PortFamily.chain H Φ.length) :=
  chain (QSVT.chainData Pr Pr' hPr hPr' Φ)

theorem qspProg_steady {H : Type u} [HSpace H] (Pr Pr' : H →L[ℂ] H) (hPr : IsProj Pr)
    (hPr' : IsProj Pr') (U : H →L[ℂ] H) (Φ : List ℝ) :
    steady (qspProg Pr Pr' hPr hPr' Φ)
        (Junction.ChainData.oracles (QSVT.chainOracles U Φ.length)) = QSVT.UΦ U Pr Pr' Φ :=
  QSVT.qsp_steady Pr Pr' hPr hPr' U Φ

/-- Every port of the QSP program is queried once per traversal. -/
theorem qspProg_weight {H : Type u} [HSpace H] {U Pr Pr' : H →L[ℂ] H} (hU : IsUnitary U)
    (hPr : IsProj Pr) (hPr' : IsProj Pr') (Φ : List ℝ) (k : Fin Φ.length) (ψ : H) :
    weight (qspProg Pr Pr' hPr hPr' Φ)
      (Junction.ChainData.oracles (QSVT.chainOracles U Φ.length)) k ψ = ‖ψ‖ ^ 2 :=
  QSVT.qsp_weight hU hPr hPr' Φ k ψ

/-- The Cayley module with its oracle implemented by the inverse of a direct query. -/
noncomputable def nested (E : Type u) [HSpace E] :
    Prog E ((PortFamily.one (Reg 2 E)).sum (PortFamily.one (Reg 2 E))) :=
  (cayley E)[() ≔ inverse (query (Reg 2 E))]

/-- The nested program's steady value is the Cayley transform of `O†` (here `O† = O`). -/
theorem nested_steady {O : Reg 2 E →L[ℂ] Reg 2 E} (hO : Junction.IsSelfInverse O)
    (hU : IsUnitary O) :
    steady (nested E) (OracleTuple.sum (oneOracle 1) (Junction.OracleTuple.inv' (oneOracle O))) =
      (1 - Complex.I • Junction.encoded O) ∘L
        Ring.inverse (1 + Complex.I • Junction.encoded O) := by
  have hO' : (oneOracle O).IsUnitary := fun _ => hU
  have hqO : IsRegular (query (Reg 2 E)) (oneOracle O) := Junction.query_isRegular O
  have hr : (OracleTuple.sum (oneOracle (1 : Reg 2 E →L[ℂ] Reg 2 E))
      (Junction.OracleTuple.inv' (oneOracle O))).right =
      Junction.OracleTuple.inv' (oneOracle O) := funext fun _ => rfl
  have hq : IsRegular (inverse (query (Reg 2 E))) (Junction.OracleTuple.inv' (oneOracle O)) :=
    (Junction.inverse_isRegular_iff _ hO').2 hqO
  have hs : steady (inverse (query _)) (Junction.OracleTuple.inv' (oneOracle O)) = O := by
    rw [steady_inverse (query _) hO' hqO, steady_query, hO.adjoint_eq]
  have hupd : Function.update
      (OracleTuple.sum (oneOracle (1 : Reg 2 E →L[ℂ] Reg 2 E))
        (Junction.OracleTuple.inv' (oneOracle O))).left ()
      (steady (inverse (query (Reg 2 E))) (Junction.OracleTuple.inv' (oneOracle O))) =
      oneOracle O := by
    funext i
    rw [hs, Function.update_self]
    rfl
  unfold nested
  rw [steady_subst (cayley E) () (inverse (query (Reg 2 E))) rfl (hr ▸ hq)
    (by rw [hr, hupd]; exact Junction.cayley_isRegular hO), hr, hupd, steady_cayley hO]

end Examples

end MQSP
