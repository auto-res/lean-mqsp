import MQSP

/-! Smoke tests for the surface language: programs describe themselves, and `#check` of the
compositional semantics. -/

open MQSP MQSP.Prog

-- A program: the Cayley module followed by an inverse direct query, with a spectator register.
noncomputable example (E : Type) [HSpace E] :
    Prog (Reg 2 E) ((PortFamily.one (Reg 2 (Reg 2 E))).sum (PortFamily.one (Reg 2 E))) :=
  spectator 2 (cayley E) ;; inverse (query (Reg 2 E))

example : describe (spectator 2 (cayley ℂ) ;; inverse (query (Reg 2 ℂ))) =
    "((spectator 2 prim[1 ports]) ;; (prim[1 ports])⁻¹)" := by
  decide

example : numPorts (spectator 2 (cayley ℂ) ;; inverse (query (Reg 2 ℂ))) = 2 := by
  decide

-- The compositional semantics is available by name.
#check @MQSP.Prog.steady_series
#check @MQSP.Prog.steady_subst
#check @MQSP.Prog.toeplitz_block

/--
info: network: ((spectator 2 prim[1 ports]) ;; (prim[1 ports])⁻¹)
ports: 2
-/
#guard_msgs in
#mqsp_info (spectator 2 (cayley ℂ) ;; inverse (query (Reg 2 ℂ)))

/--
info: network: (prim[1 ports] ⇐[_] (prim[1 ports])⁻¹)
ports: 2
-/
#guard_msgs in
#mqsp_info (Examples.nested ℂ)
