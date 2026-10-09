/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Extend
import MQSP.Compose.Series
import MQSP.Compose.Substitute
import MQSP.Modules.Query

/-!
# Closing a public sector (COMP-6; mQSP §5.2 Close)

For a junction whose public space splits as `P ⊕ₕ E`, feeding the public output in the sector
`E` back to its input through a known unitary `V` moves `E` from the public port into memory:
the result is a junction with public space `P` and private space `E ⊕ₕ L`, whose sector `E` is
a *known port* carrying `V` (an identity-cost feedback connection). In our port formalism
`close M` is therefore the same system matrix regrouped, with one extra port of space `E`
whose oracle is `V`; its steady value is the Schur complement

  `F_pp + F_pe V (1 - F_ee V)⁻¹ F_ep`

of the blocks of the open transfer value `F = M.steady O` (mQSP §5.2), whenever `1 - F_ee V`
is invertible (regular internal feedback).
-/

namespace MQSP

universe u v w x

open scoped InnerProductSpace

namespace Ports

/-- The feedback of the one-port structure is its single oracle. -/
theorem one_feedback_apply {E : Type w} [HSpace E] (U : OracleTuple (onePort E)) (e : E) :
    (Ports.one E).feedback U e = U () e := by
  rw [feedback_apply, Fintype.sum_unique]
  change (1 : E →L[ℂ] E)† (U () ((1 : E →L[ℂ] E) e)) = U () e
  rw [adjoint_one, one_apply_eq_self, one_apply_eq_self]

end Ports

namespace Junction

section Generic

variable {P' : Type*} {L' : Type*} [HSpace P'] [HSpace L'] {ι' : Type*} [Fintype ι']
variable {K' : ι' → Type*} [∀ i, HSpace (K' i)]

/-- A pointwise steady-state equation `S (x ⊕ Q g) = y ⊕ g` of a regular junction determines
its steady value: `F x = y` (and `g = Γ x`). -/
theorem steady_apply_of_S_eq (M : Junction P' L' K') {O : OracleTuple K'} (h : M.IsRegular O)
    {x y : P'} {g : L'} (hg : M.S (DSum.mk x (M.Q O g)) = DSum.mk y g) : M.steady O x = y := by
  have h2 := congrArg DSum.snd hg
  rw [snd_S_mk, DSum.snd_mk] at h2
  obtain rfl := M.eq_catalyst_apply h h2
  have h1 := congrArg DSum.fst hg
  rw [fst_S_mk, DSum.fst_mk] at h1
  exact h1

/-- If `1 - T` is invertible, `e = (1 - T)⁻¹ c` solves `e = c + T e`. -/
private theorem add_apply_inverse_one_sub {X : Type*} [HSpace X] {T : X →L[ℂ] X}
    (hT : IsUnit (1 - T)) (c : X) :
    c + T (Ring.inverse (1 - T) c) = Ring.inverse (1 - T) c := by
  have h := congrArg (fun S : X →L[ℂ] X => S c) (Ring.mul_inverse_cancel _ hT)
  change Ring.inverse (1 - T) c - T (Ring.inverse (1 - T) c) = c at h
  exact (sub_eq_iff_eq_add.1 h).symm

/-- If `1 - T` is invertible, `T e = e` forces `e = 0`. -/
private theorem eq_zero_of_apply_eq_self {X : Type*} [HSpace X] {T : X →L[ℂ] X}
    (hT : IsUnit (1 - T)) {e : X} (he : T e = e) : e = 0 := by
  have h := congrArg (fun S : X →L[ℂ] X => S e) (Ring.inverse_mul_cancel _ hT)
  change Ring.inverse (1 - T) (e - T e) = e at h
  rw [he, sub_self, map_zero] at h
  exact h.symm

end Generic

variable {P : Type x} {E : Type w} {L : Type v} [HSpace P] [HSpace E] [HSpace L]
variable {ι : Type u} [Fintype ι] {K : ι → Type w} [∀ i, HSpace (K i)]

/-- The regrouping isometry `(P ⊕ₕ E) ⊕ₕ L ≃ P ⊕ₕ (E ⊕ₕ L)` (as an explicit operator). -/
noncomputable def regroup : (P ⊕ₕ E) ⊕ₕ L →L[ℂ] P ⊕ₕ (E ⊕ₕ L) :=
  DSum.inl ∘L DSum.fst ∘L DSum.fst +
    DSum.inr ∘L (DSum.inl ∘L DSum.snd ∘L DSum.fst + DSum.inr ∘L DSum.snd)

theorem regroup_apply (x : P) (e : E) (l : L) :
    regroup (DSum.mk (DSum.mk x e) l) = DSum.mk x (DSum.mk e l) := by
  refine DSum.ext ?_ (DSum.ext ?_ ?_) <;> simp [regroup]

theorem regroup_mk (w : P ⊕ₕ E) (l : L) :
    regroup (DSum.mk w l) = DSum.mk (DSum.fst w) (DSum.mk (DSum.snd w) l) :=
  regroup_apply _ _ _

theorem regroup_apply' (v : (P ⊕ₕ E) ⊕ₕ L) :
    regroup v =
      DSum.mk (DSum.fst (DSum.fst v)) (DSum.mk (DSum.snd (DSum.fst v)) (DSum.snd v)) :=
  regroup_apply _ _ _

theorem isUnitary_regroup : IsUnitary (regroup : (P ⊕ₕ E) ⊕ₕ L →L[ℂ] P ⊕ₕ (E ⊕ₕ L)) := by
  have hI : IsIsometry (regroup : (P ⊕ₕ E) ⊕ₕ L →L[ℂ] P ⊕ₕ (E ⊕ₕ L)) := by
    refine isIsometry_of_norm fun v => ?_
    obtain ⟨x, e, l, rfl⟩ : ∃ (x : P) (e : E) (l : L), v = DSum.mk (DSum.mk x e) l :=
      ⟨_, _, _, rfl⟩
    rw [regroup_apply]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    simp only [DSum.norm_sq_eq, DSum.fst_mk, DSum.snd_mk]
    ring
  refine ⟨hI, ContinuousLinearMap.ext fun w => ?_⟩
  obtain ⟨x, e, l, rfl⟩ := DSum.exists_eq_mk_mk w
  rw [ContinuousLinearMap.comp_apply, ← regroup_apply, hI.apply_adjoint_apply,
    one_apply_eq_self]

theorem adjoint_regroup_apply (x : P) (e : E) (l : L) :
    regroup† (DSum.mk x (DSum.mk e l)) = DSum.mk (DSum.mk x e) l := by
  rw [← regroup_apply x e l, isUnitary_regroup.isIsometry.apply_adjoint_apply]

/-- COMP-6 (mQSP §5.2 Close). Close the public sector `E` of `M` into a known port. -/
noncomputable def close (M : Junction (P ⊕ₕ E) L K) :
    Junction P (E ⊕ₕ L) (Sum.elim (onePort E) K) where
  S := regroup ∘L M.S ∘L regroup†
  isUnitary_S := isUnitary_regroup.comp (M.isUnitary_S.comp isUnitary_regroup.adjoint)
  ports := (Ports.one E).sum M.ports
  delay
    | Sum.inl _ => 1
    | Sum.inr i => M.delay i
  one_le_delay
    | Sum.inl _ => le_rfl
    | Sum.inr i => M.one_le_delay i

variable (M : Junction (P ⊕ₕ E) L K)

/-- The blocks of the open transfer value `F = M.steady O` on `P ⊕ₕ E`. -/
noncomputable abbrev Fpp (O : OracleTuple K) : P →L[ℂ] P := DSum.fst ∘L M.steady O ∘L DSum.inl
noncomputable abbrev Fpe (O : OracleTuple K) : E →L[ℂ] P := DSum.fst ∘L M.steady O ∘L DSum.inr
noncomputable abbrev Fep (O : OracleTuple K) : P →L[ℂ] E := DSum.snd ∘L M.steady O ∘L DSum.inl
noncomputable abbrev Fee (O : OracleTuple K) : E →L[ℂ] E := DSum.snd ∘L M.steady O ∘L DSum.inr

theorem fst_steady_mk (O : OracleTuple K) (x : P) (y : E) :
    DSum.fst (M.steady O (DSum.mk x y)) = M.Fpp O x + M.Fpe O y := by
  rw [DSum.mk_eq_inl_add_inr, map_add, map_add]
  rfl

theorem snd_steady_mk (O : OracleTuple K) (x : P) (y : E) :
    DSum.snd (M.steady O (DSum.mk x y)) = M.Fep O x + M.Fee O y := by
  rw [DSum.mk_eq_inl_add_inr, map_add, map_add]
  rfl

theorem close_S_apply (x : P) (e : E) (l : L) :
    (close M).S (DSum.mk x (DSum.mk e l)) = regroup (M.S (DSum.mk (DSum.mk x e) l)) := by
  change regroup (M.S (regroup† (DSum.mk x (DSum.mk e l)))) = _
  rw [adjoint_regroup_apply]

/-- The feedback of the closed junction: `V` on the sector `E`, the old feedback on `L`. -/
theorem close_Q_apply (O : OracleTuple (Sum.elim (onePort E) K)) (e : E) (l : L) :
    (close M).Q O (DSum.mk e l) = DSum.mk (O.left () e) (M.Q O.right l) := by
  change ((Ports.one E).sum M.ports).feedback O (DSum.mk e l) = _
  rw [Ports.sum_feedback, DSum.block_apply]
  simp only [DSum.fst_mk, DSum.snd_mk, zero_apply, add_zero, zero_add]
  rw [Ports.one_feedback_apply]
  rfl

/-- The closed system matrix on a feedback state whose old ports carry the open catalyst. -/
theorem close_S_Q_catalyst {O : OracleTuple (Sum.elim (onePort E) K)} (h : M.IsRegular O.right)
    (x : P) (e : E) :
    (close M).S (DSum.mk x ((close M).Q O
        (DSum.mk e (M.catalyst O.right (DSum.mk x (O.left () e)))))) =
      DSum.mk (M.Fpp O.right x + M.Fpe O.right (O.left () e))
        (DSum.mk (M.Fep O.right x + M.Fee O.right (O.left () e))
          (M.catalyst O.right (DSum.mk x (O.left () e)))) := by
  rw [close_Q_apply, close_S_apply, M.steady_state_eq h, regroup_mk, fst_steady_mk,
    snd_steady_mk]

/-- COMP-6. The closed loop is regular when the open loop is regular and the internal feedback
`1 - F_ee V` is invertible. -/
theorem close_isRegular {O : OracleTuple (Sum.elim (onePort E) K)} (hO : O.IsUnitary)
    (h : M.IsRegular O.right) (hV : IsUnit (1 - M.Fee O.right ∘L O.left ())) :
    (close M).IsRegular O := by
  have _ := hO
  rw [isRegular_iff_injective]
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  obtain ⟨e, l, rfl⟩ : ∃ (e : E) (l : L), v = DSum.mk e l := ⟨_, _, rfl⟩
  rw [sub_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply, sub_eq_zero] at hv
  have hv' : DSum.snd ((close M).S (DSum.mk 0 ((close M).Q O (DSum.mk e l)))) =
      DSum.mk e l := hv.symm
  rw [close_Q_apply, close_S_apply, regroup_apply', DSum.snd_mk] at hv'
  have h2 : DSum.snd (M.S (DSum.mk (DSum.mk 0 (O.left () e)) (M.Q O.right l))) = l :=
    congrArg DSum.snd hv'
  rw [snd_S_mk] at h2
  obtain rfl := M.eq_catalyst_apply h h2
  have h1 : DSum.snd (DSum.fst (M.S (DSum.mk (DSum.mk 0 (O.left () e))
      (M.Q O.right (M.catalyst O.right (DSum.mk 0 (O.left () e))))))) = e :=
    congrArg DSum.fst hv'
  rw [M.steady_state_eq h, DSum.fst_mk, snd_steady_mk, map_zero, zero_add] at h1
  obtain rfl : e = 0 := eq_zero_of_apply_eq_self hV h1
  simp

/-- COMP-6 (mQSP §5.2 Close). The steady value of the closed junction is the Schur complement
`F_pp + F_pe V (1 - F_ee V)⁻¹ F_ep` with `V = O.left ()`. -/
theorem close_steady {O : OracleTuple (Sum.elim (onePort E) K)} (hO : O.IsUnitary)
    (h : M.IsRegular O.right) (hV : IsUnit (1 - M.Fee O.right ∘L O.left ())) :
    (close M).steady O =
      M.Fpp O.right + M.Fpe O.right ∘L O.left () ∘L
        Ring.inverse (1 - M.Fee O.right ∘L O.left ()) ∘L M.Fep O.right := by
  refine ContinuousLinearMap.ext fun x => ?_
  have he : M.Fep O.right x + M.Fee O.right (O.left ()
      (Ring.inverse (1 - M.Fee O.right ∘L O.left ()) (M.Fep O.right x))) =
      Ring.inverse (1 - M.Fee O.right ∘L O.left ()) (M.Fep O.right x) :=
    add_apply_inverse_one_sub hV _
  have hS := close_S_Q_catalyst M h x
    (Ring.inverse (1 - M.Fee O.right ∘L O.left ()) (M.Fep O.right x))
  rw [he] at hS
  exact steady_apply_of_S_eq (close M) (close_isRegular M hO h hV) hS

end Junction

end MQSP
