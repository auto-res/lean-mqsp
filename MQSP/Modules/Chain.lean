/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import Mathlib.RingTheory.Nilpotent.Basic
import MQSP.Core.Reg
import MQSP.Module.Impulse

/-!
# Chain junctions: finite query circuits as modules (LIB-0; mQSP Thm 4.4 / 4.8)

A *chain* is the module of a finite causally ordered query circuit
`V_d ∘ O_{d-1} ∘ V_{d-1} ∘ ⋯ ∘ O_0 ∘ V_0` with known unitaries `V_k` on `H` and one oracle
call per step: the public input passes through `V_0` into port `0`, the output of port `k`
passes through `V_{k+1}` into port `k+1`, and the output of the last port passes through
`V_d` to the public output. Its private space is `Reg d H` (one slot per step), its ports are
`Fin d` (all with space `H`, unit delays), and its system matrix is

  `S = [[0, V_d ⟨d-1|], [|0⟩ V_0, ∑_{k+1<d} |k+1⟩ V_{k+1} ⟨k|]]`.

The private-to-private block `D` is nilpotent, so the loop is regular with catalyst
`Γ = ∑_k (D Q)^k C` (each slot holds one unit-norm copy of the signal: catalyst weight `1`
per port, total `d`), the transfer function is `z^d · (V_d O_{d-1} ⋯ O_0 V_0)`
(impulse response `G d = product`, `G n = 0` otherwise), and the steady value is the circuit.
The QSP/QSVT alternating phase sequence is the chain with `V_k` the phase operators and the
oracles alternating `U`, `U†`. mQSP Thm 4.4 says every finite query circuit is of this form;
compiling a chain with horizon `d + 1` and the endpoint clock `X = |d⟩⟨0|` reproduces the
circuit exactly (mQSP Thm 4.8).
-/

namespace MQSP

universe u

open Finset

namespace Junction

variable {H : Type u} [HSpace H]

/-- The constant port family `Fin d → H`. -/
abbrev chainPorts (H : Type u) (d : ℕ) : Fin d → Type u := fun _ => H

instance instHSpaceChainPorts (d : ℕ) : ∀ i, HSpace (chainPorts H d i) := fun _ =>
  inferInstanceAs (HSpace H)

/-- The step unitaries of a chain of `d` queries: `V 0, …, V d`. -/
structure ChainData (H : Type u) [HSpace H] (d : ℕ) where
  /-- The known unitaries between the queries. -/
  V : Fin (d + 1) → (H →L[ℂ] H)
  /-- Each one is unitary. -/
  isUnitary_V : ∀ k, IsUnitary (V k)

namespace ChainData

variable {d : ℕ} (cd : ChainData H d)

/-- The private-to-private block: slot `k` goes through `V (k+1)` into slot `k+1`. -/
noncomputable def Dblk : Reg d H →L[ℂ] Reg d H :=
  ∑ k : Fin d, ∑ k' : Fin d, if (k' : ℕ) = k + 1 then
    Reg.single k' ∘L cd.V ⟨k + 1, by omega⟩ ∘L Reg.proj k else 0

/-- The public-to-private block: the input goes through `V 0` into slot `0`. -/
noncomputable def Cblk : H →L[ℂ] Reg d H :=
  ∑ k : Fin d, if (k : ℕ) = 0 then Reg.single k ∘L cd.V 0 else 0

/-- The private-to-public block: slot `d-1` goes through `V d` to the output. -/
noncomputable def Bblk : Reg d H →L[ℂ] H :=
  ∑ k : Fin d, if (k : ℕ) + 1 = d then cd.V (Fin.last d) ∘L Reg.proj k else 0

/-- The public-to-public block: the bypass `V 0` when `d = 0` (no queries), zero otherwise. -/
noncomputable def Ablk : H →L[ℂ] H := if d = 0 then cd.V 0 else 0

/-! ### Slot structure of the blocks -/

theorem proj_Cblk_apply (s : Fin d) (x : H) :
    Reg.proj s (cd.Cblk x) = if (s : ℕ) = 0 then cd.V 0 x else 0 := by
  simp only [Cblk, _root_.sum_apply, map_sum]
  rw [Finset.sum_eq_single s]
  · split_ifs <;> simp
  · intro k _ hks
    split_ifs <;> simp [Reg.proj_single_of_ne (Ne.symm hks)]
  · intro h; exact absurd (Finset.mem_univ s) h

theorem proj_Cblk_of_val_eq_zero (s : Fin d) (hs : (s : ℕ) = 0) (x : H) :
    Reg.proj s (cd.Cblk x) = cd.V 0 x := by
  simp [proj_Cblk_apply, hs]

theorem proj_Cblk_of_val_ne_zero (s : Fin d) (hs : (s : ℕ) ≠ 0) (x : H) :
    Reg.proj s (cd.Cblk x) = 0 := by
  simp [proj_Cblk_apply, hs]

theorem proj_Dblk_apply (s : Fin d) (w : Reg d H) :
    Reg.proj s (cd.Dblk w) = ∑ k : Fin d,
      if (s : ℕ) = k + 1 then cd.V ⟨k + 1, by omega⟩ (Reg.proj k w) else 0 := by
  simp only [Dblk, _root_.sum_apply, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single s]
  · split_ifs <;> simp
  · intro k' _ hk's
    split_ifs <;> simp [Reg.proj_single_of_ne (Ne.symm hk's)]
  · intro h; exact absurd (Finset.mem_univ s) h

theorem proj_Dblk_of_val_eq_zero (s : Fin d) (hs : (s : ℕ) = 0) (w : Reg d H) :
    Reg.proj s (cd.Dblk w) = 0 := by
  rw [proj_Dblk_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  split_ifs with h
  · omega
  · rfl

theorem proj_Dblk_of_val_eq_succ (s : Fin d) (m : ℕ) (hs : (s : ℕ) = m + 1) (w : Reg d H) :
    Reg.proj s (cd.Dblk w) = cd.V ⟨s, by omega⟩ (Reg.proj ⟨m, by omega⟩ w) := by
  rw [proj_Dblk_apply, Finset.sum_eq_single ⟨m, by omega⟩]
  · rw [ite_eq_left hs]
    have e : (⟨m + 1, by omega⟩ : Fin (d + 1)) = ⟨s, by omega⟩ := Fin.ext hs.symm
    exact congrArg (fun i => cd.V i (Reg.proj ⟨m, by omega⟩ w)) e
  · intro k _ hk
    have : (k : ℕ) ≠ m := fun e => hk (Fin.ext e)
    split_ifs with h'
    · omega
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem Bblk_apply_of_eq (k : Fin d) (hk : (k : ℕ) + 1 = d) (w : Reg d H) :
    cd.Bblk w = cd.V (Fin.last d) (Reg.proj k w) := by
  simp only [Bblk, _root_.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [ite_eq_left hk]; rfl
  · intro k' _ hk'
    have : (k' : ℕ) ≠ k := fun e => hk' (Fin.ext e)
    split_ifs with h'
    · omega
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The system matrix of a chain preserves norms. -/
theorem norm_block_apply (v : H ⊕ₕ Reg d H) :
    ‖DSum.block cd.Ablk cd.Bblk cd.Cblk cd.Dblk v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), DSum.norm_sq_eq, DSum.norm_sq_eq v,
    DSum.fst_block_apply, DSum.snd_block_apply, Reg.norm_sq_eq, Reg.norm_sq_eq (DSum.snd v)]
  cases d with
  | zero => simp [Ablk, Bblk, (cd.isUnitary_V 0).isIsometry.norm_map]
  | succ n =>
    have hA : cd.Ablk = 0 := by simp [Ablk]
    have hs : ∀ i : Fin n, ‖Reg.proj i.succ (cd.Cblk (DSum.fst v) + cd.Dblk (DSum.snd v))‖ ^ 2 =
        ‖Reg.proj i.castSucc (DSum.snd v)‖ ^ 2 := by
      intro i
      rw [map_add, cd.proj_Cblk_of_val_ne_zero _ (by simp),
        cd.proj_Dblk_of_val_eq_succ i.succ i (by simp), zero_add,
        (cd.isUnitary_V _).isIsometry.norm_map]
      rfl
    rw [hA, zero_apply, zero_add, cd.Bblk_apply_of_eq (Fin.last n) rfl,
      (cd.isUnitary_V _).isIsometry.norm_map, Fin.sum_univ_succ, Fin.sum_univ_castSucc,
      Finset.sum_congr rfl (fun i _ => hs i), map_add, cd.proj_Cblk_of_val_eq_zero 0 (by simp),
      cd.proj_Dblk_of_val_eq_zero 0 (by simp), add_zero, (cd.isUnitary_V _).isIsometry.norm_map]
    ring

/-- LIB-0. The chain junction. -/
noncomputable def junction : Junction H (Reg d H) (chainPorts H d) where
  S := DSum.block cd.Ablk cd.Bblk cd.Cblk cd.Dblk
  isUnitary_S := isUnitary_of_isIsometry (isIsometry_of_norm cd.norm_block_apply)
  ports := Ports.pi
  delay _ := 1
  one_le_delay _ := le_rfl

/-- The oracle tuple of a chain: oracle `O k` at step `k`. -/
def oracles (O : Fin d → (H →L[ℂ] H)) : OracleTuple (chainPorts H d) := O

/-- The circuit `V d ∘ O (d-1) ∘ V (d-1) ∘ ⋯ ∘ O 0 ∘ V 0` (defined by recursion on the steps). -/
noncomputable def circuit (O : Fin d → (H →L[ℂ] H)) : H →L[ℂ] H :=
  cd.V (Fin.last d) ∘L go d (le_refl d)
where
  /-- `go k : = O (k-1) ∘ V (k-1) ∘ ⋯ ∘ O 0 ∘ V 0`, the first `k` oracle steps. -/
  go : (k : ℕ) → k ≤ d → (H →L[ℂ] H)
    | 0, _ => 1
    | k + 1, hk => O ⟨k, by omega⟩ ∘L cd.V ⟨k, by omega⟩ ∘L go k (by omega)

@[simp] theorem junction_A : cd.junction.A = cd.Ablk := DSum.fst_block_inl _ _ _ _
@[simp] theorem junction_B : cd.junction.B = cd.Bblk := DSum.fst_block_inr _ _ _ _
@[simp] theorem junction_C : cd.junction.C = cd.Cblk := DSum.snd_block_inl _ _ _ _
@[simp] theorem junction_D : cd.junction.D = cd.Dblk := DSum.snd_block_inr _ _ _ _

theorem junction_delay (j : Fin d) : cd.junction.delay j = 1 := rfl

/-- The feedback of a chain acts slot-wise. -/
theorem proj_Q_apply (O : Fin d → (H →L[ℂ] H)) (s : Fin d) (w : Reg d H) :
    Reg.proj s (cd.junction.Q (oracles O) w) = O s (Reg.proj s w) :=
  cd.junction.ports.π_feedback_apply (oracles O) s w

theorem proj_DQ_of_val_eq_zero (O : Fin d → (H →L[ℂ] H)) (s : Fin d) (hs : (s : ℕ) = 0)
    (w : Reg d H) : Reg.proj s (cd.junction.D (cd.junction.Q (oracles O) w)) = 0 := by
  rw [junction_D, cd.proj_Dblk_of_val_eq_zero s hs]

theorem proj_DQ_of_val_eq_succ (O : Fin d → (H →L[ℂ] H)) (s : Fin d) (m : ℕ)
    (hs : (s : ℕ) = m + 1) (w : Reg d H) :
    Reg.proj s (cd.junction.D (cd.junction.Q (oracles O) w)) =
      cd.V ⟨s, by omega⟩ (O ⟨m, by omega⟩ (Reg.proj ⟨m, by omega⟩ w)) := by
  rw [junction_D, cd.proj_Dblk_of_val_eq_succ s m hs, proj_Q_apply]

theorem proj_loop_pow_apply_eq_zero (O : Fin d → (H →L[ℂ] H)) (m : ℕ) (w : Reg d H) (s : Fin d)
    (hs : (s : ℕ) < m) :
    Reg.proj s (((cd.junction.D ∘L cd.junction.Q (oracles O)) ^ m :
      Reg d H →L[ℂ] Reg d H) w) = 0 := by
  induction m generalizing s with
  | zero => omega
  | succ m ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    rcases Nat.eq_zero_or_pos (s : ℕ) with h | h
    · exact cd.proj_DQ_of_val_eq_zero O s h _
    · obtain ⟨k, hk⟩ : ∃ k, (s : ℕ) = k + 1 := ⟨s - 1, by omega⟩
      rw [cd.proj_DQ_of_val_eq_succ O s k hk, ih ⟨k, by omega⟩ (by simp only; omega), map_zero,
        map_zero]

/-- The loop operator of a chain is nilpotent: `(D Q)^d = 0`. -/
theorem loop_pow_eq_zero (O : Fin d → (H →L[ℂ] H)) :
    ((cd.junction.D ∘L cd.junction.Q (oracles O)) ^ d : Reg d H →L[ℂ] Reg d H) = 0 := by
  refine ContinuousLinearMap.ext fun w => Reg.ext fun s => ?_
  rw [zero_apply, map_zero]
  exact cd.proj_loop_pow_apply_eq_zero O d w s s.isLt

/-- LIB-0. A chain is always regular. -/
theorem isRegular (O : Fin d → (H →L[ℂ] H)) : cd.junction.IsRegular (oracles O) :=
  IsNilpotent.isUnit_one_sub ⟨d, cd.loop_pow_eq_zero O⟩

theorem catalyst_apply_eq (O : Fin d → (H →L[ℂ] H)) (ψ : H) :
    cd.junction.catalyst (oracles O) ψ =
      cd.Cblk ψ + cd.Dblk (cd.junction.Q (oracles O) (cd.junction.catalyst (oracles O) ψ)) := by
  conv_lhs => rw [cd.junction.catalyst_eq (cd.isRegular O)]
  rw [junction_C, junction_D]
  rfl

theorem proj_catalyst_apply (O : Fin d → (H →L[ℂ] H)) (m : ℕ) (hm : m < d) (ψ : H) :
    Reg.proj ⟨m, hm⟩ (cd.junction.catalyst (oracles O) ψ) =
      cd.V ⟨m, by omega⟩ (circuit.go cd O m (by omega) ψ) := by
  induction m with
  | zero =>
    rw [catalyst_apply_eq, map_add, cd.proj_Cblk_of_val_eq_zero _ rfl,
      cd.proj_Dblk_of_val_eq_zero _ rfl, add_zero]
    rfl
  | succ m ih =>
    rw [catalyst_apply_eq, map_add, cd.proj_Cblk_of_val_ne_zero _ (by simp),
      cd.proj_Dblk_of_val_eq_succ _ m rfl, zero_add, proj_Q_apply, ih (by omega)]
    rfl

/-- The catalyst stores the intermediate states: slot `k` holds `O (k-1) V (k-1) ⋯ O 0 V 0 ψ`
after the first `k` steps and before `V k`… precisely `proj k (Γ ψ) = V k (go k ψ)`. -/
theorem proj_catalyst (O : Fin d → (H →L[ℂ] H)) (k : Fin d) :
    Reg.proj k ∘L cd.junction.catalyst (oracles O) =
      cd.V ⟨k, by omega⟩ ∘L circuit.go cd O k (by omega) :=
  ContinuousLinearMap.ext fun ψ => cd.proj_catalyst_apply O k k.isLt ψ

/-- LIB-0. The steady value of a chain is the circuit `V d ∘ O (d-1) ∘ ⋯ ∘ O 0 ∘ V 0`. -/
theorem steady_eq_circuit (O : Fin d → (H →L[ℂ] H)) :
    cd.junction.steady (oracles O) = cd.circuit O := by
  cases d with
  | zero =>
    rw [steady, junction_A, junction_B]
    simp [Ablk, Bblk, circuit, circuit.go]
  | succ n =>
    refine ContinuousLinearMap.ext fun ψ => ?_
    rw [steady, junction_A, junction_B, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, cd.Bblk_apply_of_eq (Fin.last n) rfl, proj_Q_apply]
    have h := cd.proj_catalyst_apply O n (by omega) ψ
    simp only [Ablk, Nat.add_one_ne_zero, ↓reduceIte, zero_apply, zero_add]
    rw [show (Fin.last n : Fin (n + 1)) = ⟨n, by omega⟩ from rfl, h]
    rfl

theorem norm_go_apply (O : Fin d → (H →L[ℂ] H)) (hO : ∀ k, IsUnitary (O k)) (m : ℕ)
    (hm : m ≤ d) (ψ : H) : ‖circuit.go cd O m hm ψ‖ = ‖ψ‖ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [circuit.go, ContinuousLinearMap.comp_apply]
    rw [(hO _).isIsometry.norm_map, (cd.isUnitary_V _).isIsometry.norm_map, ih]

/-- LIB-0. Every port of a chain has catalyst weight `‖ψ‖²` on unitary oracles
(one query per traversal), so the total weight is `d ‖ψ‖²`. -/
theorem weight_eq (O : Fin d → (H →L[ℂ] H)) (hO : ∀ k, IsUnitary (O k)) (k : Fin d) (ψ : H) :
    cd.junction.weight (oracles O) k ψ = ‖ψ‖ ^ 2 := by
  have h : Reg.proj k (cd.junction.catalyst (oracles O) ψ) =
      cd.V ⟨k, by omega⟩ (circuit.go cd O k (by omega) ψ) :=
    cd.proj_catalyst_apply O k k.isLt ψ
  rw [weight]
  change ‖Reg.proj k (cd.junction.catalyst (oracles O) ψ)‖ ^ 2 = _
  rw [h, (cd.isUnitary_V _).isIsometry.norm_map, cd.norm_go_apply O hO]

/-- The state after `n` loop steps from the impulse sits in slot `n`. -/
theorem proj_loop_pow_C_apply (O : Fin d → (H →L[ℂ] H)) (n : ℕ) (ψ : H) (m : ℕ) (hm : m < d) :
    Reg.proj ⟨m, hm⟩ (((cd.junction.D ∘L cd.junction.Q (oracles O)) ^ n :
      Reg d H →L[ℂ] Reg d H) (cd.junction.C ψ)) =
      if m = n then cd.V ⟨m, by omega⟩ (circuit.go cd O m (by omega) ψ) else 0 := by
  induction n generalizing m with
  | zero =>
    rw [pow_zero, one_apply_eq_self, junction_C]
    rcases m with _ | m
    · rw [cd.proj_Cblk_of_val_eq_zero _ rfl]; rfl
    · rw [cd.proj_Cblk_of_val_ne_zero _ (by simp)]; simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
    rcases m with _ | m
    · rw [cd.proj_DQ_of_val_eq_zero O _ rfl]; simp
    · rw [cd.proj_DQ_of_val_eq_succ O _ m rfl, ih m (by omega)]
      by_cases h : m = n
      · subst h; simp only [↓reduceIte]; rfl
      · simp [h]

/-- LIB-0. The impulse response of a chain is concentrated at delay `d`: `G d = circuit` and
`G n = 0` for `n ≠ d`. -/
theorem G_eq (O : Fin d → (H →L[ℂ] H)) (n : ℕ) :
    cd.junction.G (oracles O) n = if n = d then cd.circuit O else 0 := by
  rcases n with _ | n
  · rw [G_zero, junction_A]
    cases d with
    | zero => simp [Ablk, circuit, circuit.go]
    | succ d => simp [Ablk]
  · rw [G_succ_of_delay_eq_one _ _ cd.junction_delay]
    cases d with
    | zero =>
      rw [junction_B]
      simp [Bblk]
    | succ d =>
      refine ContinuousLinearMap.ext fun ψ => ?_
      simp only [ContinuousLinearMap.comp_apply, junction_B]
      rw [cd.Bblk_apply_of_eq (Fin.last d) rfl, proj_Q_apply,
        show (Fin.last d : Fin (d + 1)) = ⟨d, by omega⟩ from rfl, cd.proj_loop_pow_C_apply]
      by_cases h : d = n
      · subst h; simp only [↓reduceIte]; rfl
      · rw [ite_eq_right h, ite_eq_right (by omega), map_zero, map_zero, zero_apply]

end ChainData

end Junction

end MQSP
