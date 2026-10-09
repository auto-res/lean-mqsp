/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Module.Impulse

/-!
# The direct query module (LIB-1; mQSP Eq. (2.4), (5.4))

`Query E` exchanges the public space `E` with one private copy of `E` through the swap
system matrix `S = [[0, 1], [1, 0]]`. Its single port carries the oracle `O`; the transfer
function is `z O`, the catalyst is `Γ = 1`, the steady value is `O` and the catalyst weight is
`‖ψ‖²` (one query per traversal).
-/

namespace MQSP

universe u

/-- The single-port index. -/
abbrev One : Type := Unit

/-- The constant port family with one port of space `E`. -/
abbrev onePort (E : Type u) : One → Type u := fun _ => E

instance instHSpaceOnePort (E : Type u) [HSpace E] : ∀ i, HSpace (onePort E i) := fun _ =>
  inferInstanceAs (HSpace E)

/-- The oracle tuple with the single oracle `U`. -/
def oneOracle {E : Type u} [HSpace E] (U : E →L[ℂ] E) : OracleTuple (onePort E) := fun _ => U

namespace Ports

/-- The trivial port structure of `E` with one port. -/
noncomputable def one (E : Type u) [HSpace E] : Ports E (onePort E) where
  π _ := 1
  π_comp_adj_self _ := by simp
  π_comp_adj_ne i j h := absurd (Subsingleton.elim i j) h
  sum_adj_comp := by simp

end Ports

namespace Junction

variable (E : Type u) [HSpace E]

/-- LIB-1 (mQSP Eq. (5.4)). The direct query module: `S = swap`, one port, unit delay. -/
noncomputable def query : Junction E E (onePort E) where
  S := DSum.block 0 1 1 0
  isUnitary_S := by
    constructor <;>
    · rw [DSum.adjoint_block, DSum.block_comp_block]
      simp
  ports := Ports.one E
  delay _ := 1
  one_le_delay _ := le_rfl

variable {E}

@[simp] theorem query_A : (query E).A = 0 := DSum.fst_block_inl _ _ _ _
@[simp] theorem query_B : (query E).B = 1 := DSum.fst_block_inr _ _ _ _
@[simp] theorem query_C : (query E).C = 1 := DSum.snd_block_inl _ _ _ _
@[simp] theorem query_D : (query E).D = 0 := DSum.snd_block_inr _ _ _ _

@[simp] theorem query_delay (i : One) : (query E).delay i = 1 := rfl
@[simp] theorem query_π (i : One) : (query E).ports.π i = 1 := rfl

theorem query_Q (U : E →L[ℂ] E) : (query E).Q (oneOracle U) = U := by
  rw [Q, Ports.feedback, Fintype.sum_unique]
  simp only [query_π, adjoint_one, one_comp, comp_one]
  rfl

theorem query_isRegular (U : E →L[ℂ] E) : (query E).IsRegular (oneOracle U) :=
  (query E).isRegular_of_D_eq_zero query_D _

/-- The catalyst of a direct query is the identity. -/
theorem query_catalyst (U : E →L[ℂ] E) : (query E).catalyst (oneOracle U) = 1 := by
  rw [catalyst_of_D_eq_zero _ query_D, query_C]

/-- LIB-1. The steady value of a direct query is the oracle itself. -/
theorem query_steady (U : E →L[ℂ] E) : (query E).steady (oneOracle U) = U := by
  rw [steady_of_D_eq_zero _ query_D, query_A, query_B, query_C, query_Q]
  simp

/-- The catalyst weight of a direct query is `‖ψ‖²`. -/
theorem query_weight (U : E →L[ℂ] E) (ψ : E) : (query E).weight (oneOracle U) () ψ = ‖ψ‖ ^ 2 := by
  rw [weight, query_catalyst, query_π]
  rfl

theorem query_fb_succ (U : E →L[ℂ] E) (k : ℕ) :
    (query E).fb (oneOracle U) (k + 1) = U ∘L (query E).gseq (oneOracle U) k := by
  rw [fb, Fintype.sum_unique]
  simp only [query_delay, query_π, adjoint_one, one_comp, Nat.add_sub_cancel,
    le_add_iff_nonneg_left, zero_le, ↓reduceIte]
  rfl

/-- The impulse response of a direct query: `G 1 = U` and `G n = 0` otherwise. -/
theorem query_G (U : E →L[ℂ] E) (n : ℕ) :
    (query E).G (oneOracle U) n = if n = 1 then U else 0 := by
  rcases n with _ | _ | k
  · simp
  · rw [G_succ, query_fb_succ, gseq_zero]; simp
  · rw [G_succ, query_fb_succ, gseq_succ, query_D]; simp

end Junction

end MQSP
