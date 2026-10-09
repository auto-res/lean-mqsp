/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Lang.Prog

/-!
# `#mqsp_info`: inspect a program (LANG-1)

`#mqsp_info p` elaborates the program `p : Prog P pf` and prints its network structure
(connection rules and leaves) together with the number of oracle ports, by inspecting the
elaborated term — programs are noncomputable (they contain operators), so this works at the
meta level rather than by evaluation.
-/

namespace MQSP.Prog

open Lean Elab Command Term Meta

/-- Try to evaluate a natural-number expression to a numeral (after reduction). -/
private def natOf? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n ← evalNat e then return some n
  try
    let e' ← withTransparency .all (reduce e)
    evalNat e'
  catch _ => return none

/-- Count the elements of a finite index type built from `Unit`/`One`, `Fin n` and `Sum`. -/
private partial def cardOf? (ι : Expr) : MetaM (Option Nat) := do
  let ι ← whnfR ι
  match ι.getAppFn with
  | .const ``Unit _ => return some 1
  | .const ``PUnit _ => return some 1
  | .const ``MQSP.One _ => return some 1
  | .const ``Fin _ => natOf? ι.getAppArgs[0]!
  | .const ``Sum _ =>
    let a ← cardOf? ι.getAppArgs[0]!
    let b ← cardOf? ι.getAppArgs[1]!
    return do pure ((← a) + (← b))
  | _ =>
    let ι' ← withTransparency .all (whnf ι)
    if ι' == ι then return none else cardOf? ι'

/-- Describe the structure of an elaborated program term. -/
private partial def describeExpr (e : Expr) : MetaM String := do
  let e ← whnf e
  let args := e.getAppArgs
  match e.getAppFn with
  | .const ``Prog.prim _ =>
    -- prim {P L} [HSpace P] [HSpace L] {pf} (M)
    let pf := args[4]!
    let ι ← withTransparency .all (reduce (← mkProjection pf `ι))
    match ← cardOf? ι with
    | some n => return s!"prim[{n} ports]"
    | none => return "prim"
  | .const ``Prog.series _ =>
    -- series {P} [HSpace P] {pf₁ pf₂} (p) (q)
    return s!"({← describeExpr args[4]!} ;; {← describeExpr args[5]!})"
  | .const ``Prog.wireBefore _ =>
    -- wireBefore {P} [HSpace P] {pf} (V) (hV) (p)
    return s!"(V ◁ {← describeExpr args[5]!})"
  | .const ``Prog.wireAfter _ =>
    return s!"({← describeExpr args[5]!} ▷ V)"
  | .const ``Prog.dsum _ =>
    -- dsum {P₁ P₂} [HSpace P₁] [HSpace P₂] {pf₁ pf₂} (p) (q)
    return s!"({← describeExpr args[6]!} ⊕ {← describeExpr args[7]!})"
  | .const ``Prog.spectator _ =>
    -- spectator {P} [HSpace P] {pf} (n) (p)
    let ns := match ← natOf? args[3]! with | some k => toString k | none => "n"
    return s!"(spectator {ns} {← describeExpr args[4]!})"
  | .const ``Prog.inverse _ =>
    -- inverse {P} [HSpace P] {pf} (p)
    return s!"({← describeExpr args[3]!})⁻¹"
  | .const ``Prog.subst _ =>
    -- subst {P} [HSpace P] {pf pf'} (p) (j) (q)
    return s!"({← describeExpr args[4]!} ⇐[_] {← describeExpr args[6]!})"
  | _ => return "?"

/-- `#mqsp_info p` prints the network structure of the program `p` and its number of ports. -/
elab "#mqsp_info " t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← inferType e
  let ty ← whnf ty
  let desc ← describeExpr e
  let ports ← match ty.getAppFn with
    | .const ``Prog _ =>
      let pf := ty.getAppArgs[2]!
      let ι ← withTransparency .all (reduce (← mkProjection pf `ι))
      match ← cardOf? ι with
      | some n => pure s!"{n}"
      | none => pure "?"
    | _ => pure "?"
  logInfo m!"network: {desc}\nports: {ports}"

end MQSP.Prog
