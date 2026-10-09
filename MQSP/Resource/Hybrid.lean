/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.HSpace

/-!
# The hybrid argument (RES-2; mQSP Eq. (A.13))

Errors of approximate operations add along a circuit: for contractions `Ũₖ, Uₖ`,

  `‖Ũₙ ⋯ Ũ₁ - Uₙ ⋯ U₁‖ ≤ ∑ₖ ‖Ũₖ - Uₖ‖`

(telescoping). This is the error-budget rule behind mQSP Eq. (A.13): an operation executed
`q` times with error `η` contributes `q η`. Here for lists of operators composed in order.
-/

namespace MQSP

universe u

namespace Resource

variable {H : Type u} [HSpace H]

/-- Compose a list of operators in order (the head is applied first). -/
noncomputable def compList : List (H →L[ℂ] H) → (H →L[ℂ] H)
  | [] => 1
  | U :: Us => compList Us ∘L U

theorem compList_cons (U : H →L[ℂ] H) (Us : List (H →L[ℂ] H)) :
    compList (U :: Us) = compList Us ∘L U := rfl

theorem norm_compList_le_one {Us : List (H →L[ℂ] H)} (h : ∀ U ∈ Us, ‖U‖ ≤ 1) :
    ‖compList Us‖ ≤ 1 := by
  induction Us with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons U Us ih =>
    rw [List.forall_mem_cons] at h
    rw [compList_cons]
    calc ‖compList Us ∘L U‖ ≤ ‖compList Us‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul (ih h.2) h.1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- RES-2 (hybrid argument). For contractions, the error of a composition is at most the sum
of the errors of the factors. -/
theorem norm_compList_sub_compList_le {Us Vs : List (H →L[ℂ] H)} (hlen : Us.length = Vs.length)
    (hU : ∀ U ∈ Us, ‖U‖ ≤ 1) (hV : ∀ V ∈ Vs, ‖V‖ ≤ 1) :
    ‖compList Us - compList Vs‖ ≤ (List.zipWith (fun U V => ‖U - V‖) Us Vs).sum := by
  induction Us generalizing Vs with
  | nil =>
    cases Vs with
    | nil => simp
    | cons V Vs => simp at hlen
  | cons U Us ih =>
    cases Vs with
    | nil => simp at hlen
    | cons V Vs =>
      rw [List.forall_mem_cons] at hU hV
      have hlen' : Us.length = Vs.length := by simpa using hlen
      have key : compList (U :: Us) - compList (V :: Vs) =
          compList Us ∘L (U - V) + (compList Us - compList Vs) ∘L V := by
        rw [compList_cons, compList_cons, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.sub_comp, sub_add_sub_cancel]
      rw [key, List.zipWith_cons_cons, List.sum_cons]
      have hC := norm_compList_le_one hU.2
      have ih' := ih hlen' hU.2 hV.2
      calc ‖compList Us ∘L (U - V) + (compList Us - compList Vs) ∘L V‖
          ≤ ‖compList Us ∘L (U - V)‖ + ‖(compList Us - compList Vs) ∘L V‖ := norm_add_le _ _
        _ ≤ ‖compList Us‖ * ‖U - V‖ + ‖compList Us - compList Vs‖ * ‖V‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ 1 * ‖U - V‖ + ‖compList Us - compList Vs‖ * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hV.1 (norm_nonneg _))
        _ ≤ ‖U - V‖ + (List.zipWith (fun U V => ‖U - V‖) Us Vs).sum := by
          rw [one_mul, mul_one]; exact add_le_add_right ih' _

/-- An operation executed `q` times with error `η` contributes `q η`: the error of `Ũ^q`
against `U^q` is at most `q ‖Ũ - U‖` for contractions. -/
theorem norm_pow_sub_pow_le {Ut U : H →L[ℂ] H} (hUt : ‖Ut‖ ≤ 1) (hU : ‖U‖ ≤ 1) (q : ℕ) :
    ‖(Ut ^ q : H →L[ℂ] H) - U ^ q‖ ≤ q * ‖Ut - U‖ := by
  have hpow : ∀ n : ℕ, ‖(Ut ^ n : H →L[ℂ] H)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ n ihn =>
      rw [pow_succ]
      calc ‖Ut ^ n * Ut‖ ≤ ‖Ut ^ n‖ * ‖Ut‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul ihn hUt (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  induction q with
  | zero => simp
  | succ n ih =>
    have key : (Ut ^ (n + 1) : H →L[ℂ] H) - U ^ (n + 1) =
        Ut ^ n * (Ut - U) + (Ut ^ n - U ^ n) * U := by
      rw [pow_succ, pow_succ, mul_sub, sub_mul, sub_add_sub_cancel]
    rw [key, Nat.cast_succ]
    calc ‖Ut ^ n * (Ut - U) + (Ut ^ n - U ^ n) * U‖
        ≤ ‖Ut ^ n * (Ut - U)‖ + ‖(Ut ^ n - U ^ n) * U‖ := norm_add_le _ _
      _ ≤ ‖Ut ^ n‖ * ‖Ut - U‖ + ‖Ut ^ n - U ^ n‖ * ‖U‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1 * ‖Ut - U‖ + ‖Ut ^ n - U ^ n‖ * 1 :=
        add_le_add (mul_le_mul_of_nonneg_right (hpow n) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hU (norm_nonneg _))
      _ ≤ (n + 1) * ‖Ut - U‖ := by linarith

end Resource

end MQSP
