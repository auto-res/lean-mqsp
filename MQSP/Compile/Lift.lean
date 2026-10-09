/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Core.Reg
import MQSP.Module.Impulse

/-!
# The unitary Toeplitz lift (COMP-C1; mQSP Thm 2.2)

Quditization unrolls a junction to a finite horizon `N`. The lift acts on

  `LiftSpace = Reg N P ⊕ₕ Mem`,  `Mem = ⊕ⱼ Reg (r j) (K j)`

(clock register `|k⟩ ⊗ P` and, for every port, a buffer of `r j` slots). At step `k`
(`0 ≤ k < N`):

1. `oracleAt k`: for every port `j` with `0 < k` and `r j ∣ k`, apply `O j` on all slots of
   the buffer of `j` (one controlled query);
2. `step k`: apply the system matrix `S` on the subspace `(|k⟩ ⊗ P) ⊕ ⊕ⱼ (|k mod r j⟩ ⊗ K j)`
   through the isometry `J k`, and the identity on its orthogonal complement.

`lift = step (N-1) ∘ oracleAt (N-1) ∘ ⋯ ∘ step 0 ∘ oracleAt 0` is unitary; its public block
is the lower-triangular Toeplitz matrix `T_N[G]` of the impulse response (`toeplitz_block`),
it makes `⌊(N-1)/r j⌋` queries to port `j` (`queries_eq`), and the coefficients `G n` are
contractions (`norm_G_le_one`, Eq. (2.26)).
-/

namespace MQSP

universe u v w x

open Finset

section Aux

variable {X : Type*} {Y : Type*} [HSpace X] [HSpace Y]

/-- If `V` is an isometry and `S` is unitary, then `V S V† + (1 - V V†)` is unitary. -/
theorem isUnitary_conj_add_one_sub {V : X →L[ℂ] Y} (hV : IsIsometry V) {S : X →L[ℂ] X}
    (hS : IsUnitary S) : IsUnitary (V ∘L S ∘L V† + (1 - V ∘L V†)) := by
  apply isUnitary_of_isIsometry
  refine ContinuousLinearMap.ext (fun y => ?_)
  have h1 := hV.apply_adjoint_apply
  have h2 := hS.isIsometry.apply_adjoint_apply
  simp only [map_add, map_sub, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, adjoint_one, ContinuousLinearMap.comp_apply,
    add_apply, sub_apply, one_apply_eq_self, h1, h2, sub_self, add_zero]
  abel

theorem comp_opNorm_le_one {Z : Type*} [HSpace Z] {f : Y →L[ℂ] Z} {g : X →L[ℂ] Y}
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) : ‖f ∘L g‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le f g).trans (by nlinarith [norm_nonneg f, norm_nonneg g])

/-- `(k + 1) mod r` either increments `k mod r` or wraps around to `0`. -/
theorem succ_mod_cases {k r : ℕ} (hr : 0 < r) :
    ((k + 1) % r = k % r + 1 ∧ k % r + 1 < r) ∨ ((k + 1) % r = 0 ∧ k % r + 1 = r) := by
  have hlt := Nat.mod_lt k hr
  have hk : k + 1 = r * (k / r) + (k % r + 1) := by have := Nat.div_add_mod k r; omega
  rw [hk, Nat.mul_add_mod]
  rcases Nat.lt_or_ge (k % r + 1) r with h | h
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have h' : k % r + 1 = r := by omega
    refine Or.inr ⟨?_, h'⟩
    rw [h', Nat.mod_self]

end Aux

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (O : OracleTuple K) (N : ℕ)

/-- The delay memory `⊕ⱼ Reg (r j) (K j)`. -/
abbrev Mem : Type max u w := PiSum (fun j => Reg (M.delay j) (K j))

/-- The lift space `H_{N,r} = Reg N P ⊕ₕ Mem` (mQSP Eq. (2.22)). -/
abbrev LiftSpace : Type max u w x := Reg N P ⊕ₕ M.Mem

/-- The buffer slot `k mod r j` of port `j` used at time `k`. -/
def slot (j : ι) (k : ℕ) : Fin (M.delay j) :=
  ⟨k % M.delay j, Nat.mod_lt _ (M.one_le_delay j)⟩

/-- Embedding of the private space into the memory at time `k`: port `j` goes to slot
`k mod r j`. -/
noncomputable def embedL (k : ℕ) : L →L[ℂ] M.Mem :=
  ∑ j, PiSum.single j ∘L Reg.single (M.slot j k) ∘L M.ports.π j

/-- The isometry `J k` of mQSP Eq. (2.25). -/
noncomputable def J (k : Fin N) : P ⊕ₕ L →L[ℂ] M.LiftSpace N :=
  DSum.block (Reg.single k) 0 0 (M.embedL k)

/-- `S^{(k)} = J k S (J k)† + (1 - J k (J k)†)`. -/
noncomputable def step (k : Fin N) : M.LiftSpace N →L[ℂ] M.LiftSpace N :=
  M.J N k ∘L M.S ∘L (M.J N k)† + (1 - M.J N k ∘L (M.J N k)†)

/-- The scheduled oracle calls at time `k`: port `j` is queried iff `0 < k` and `r j ∣ k`. -/
noncomputable def oracleAt (k : ℕ) : M.LiftSpace N →L[ℂ] M.LiftSpace N :=
  DSum.block 1 0 0
    (PiSum.diag (fun j => if 0 < k ∧ M.delay j ∣ k then Reg.map (O j) else 1))

/-- The lift after the first `k` steps. -/
noncomputable def liftUpTo : ℕ → (M.LiftSpace N →L[ℂ] M.LiftSpace N)
  | 0 => 1
  | k + 1 =>
    (if h : k < N then M.step N ⟨k, h⟩ ∘L M.oracleAt O N k else 1) ∘L liftUpTo k

/-- COMP-C1 (mQSP Thm 2.2). The unitary Toeplitz lift `W_N[G]`. -/
noncomputable def lift : M.LiftSpace N →L[ℂ] M.LiftSpace N := M.liftUpTo O N N

/-- The number of controlled queries to port `j` made by the lift. -/
def queries (j : ι) : ℕ := ((Finset.range N).filter (fun k => 0 < k ∧ M.delay j ∣ k)).card

/-! ### Pointwise formulas -/

theorem proj_embedL (k : ℕ) (j : ι) (v : L) :
    PiSum.proj j (M.embedL k v) = Reg.single (M.slot j k) (M.ports.π j v) := by
  simp only [embedL, _root_.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  rw [Finset.sum_eq_single j]
  · rw [PiSum.proj_single_same]
  · intro i _ hij; rw [PiSum.proj_single_of_ne (Ne.symm hij)]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem adjoint_embedL_apply (k : ℕ) (m : M.Mem) :
    (M.embedL k)† m = ∑ j, (M.ports.π j)† (Reg.proj (M.slot j k) (PiSum.proj j m)) := by
  simp only [embedL, map_sum, ContinuousLinearMap.adjoint_comp, _root_.sum_apply,
    ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [PiSum.adjoint_single, Reg.adjoint_single]

theorem π_adjoint_embedL_apply (k : ℕ) (m : M.Mem) (j : ι) :
    M.ports.π j ((M.embedL k)† m) = Reg.proj (M.slot j k) (PiSum.proj j m) := by
  rw [adjoint_embedL_apply, map_sum, Finset.sum_eq_single j]
  · rw [Ports.π_adj_apply_self]
  · intro i _ hij; rw [Ports.π_adj_apply_ne _ (Ne.symm hij)]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem J_apply (k : Fin N) (x : P ⊕ₕ L) :
    M.J N k x = DSum.mk (Reg.single k (DSum.fst x)) (M.embedL k (DSum.snd x)) := by
  simp [J, DSum.block_apply]

theorem adjoint_J_apply (k : Fin N) (y : M.LiftSpace N) :
    (M.J N k)† y = DSum.mk (Reg.proj k (DSum.fst y)) ((M.embedL k)† (DSum.snd y)) := by
  simp [J, DSum.adjoint_block, DSum.block_apply]

theorem step_apply (k : Fin N) (y : M.LiftSpace N) :
    M.step N k y = M.J N k (M.S ((M.J N k)† y)) + (y - M.J N k ((M.J N k)† y)) := rfl

/-- The public slot `o` after `step k`: only slot `k` changes. -/
theorem proj_fst_step (k : Fin N) (y : M.LiftSpace N) (o : Fin N) :
    Reg.proj o (DSum.fst (M.step N k y)) =
      if (o : ℕ) = k then DSum.fst (M.S ((M.J N k)† y)) else Reg.proj o (DSum.fst y) := by
  simp only [step_apply, J_apply, map_add, map_sub, DSum.fst_mk, adjoint_J_apply]
  split_ifs with h
  · have h' : o = k := Fin.ext h
    subst h'; simp
  · have h' : o ≠ k := fun h' => h (congrArg Fin.val h')
    simp [Reg.proj_single_of_ne h']

/-- Memory slot `s` of port `j` after `step k`: only slot `k mod r j` changes. -/
theorem proj_snd_step (k : Fin N) (y : M.LiftSpace N) (j : ι) (s : Fin (M.delay j)) :
    Reg.proj s (PiSum.proj j (DSum.snd (M.step N k y))) =
      if (s : ℕ) = k % M.delay j then M.ports.π j (DSum.snd (M.S ((M.J N k)† y)))
      else Reg.proj s (PiSum.proj j (DSum.snd y)) := by
  simp only [step_apply, J_apply, map_add, map_sub, DSum.snd_mk, proj_embedL, adjoint_J_apply,
    π_adjoint_embedL_apply]
  split_ifs with h
  · have h' : s = M.slot j k := Fin.ext h
    subst h'; simp
  · have h' : s ≠ M.slot j k := fun h' => h (congrArg Fin.val h')
    simp [Reg.proj_single_of_ne h']

theorem fst_oracleAt (k : ℕ) (y : M.LiftSpace N) :
    DSum.fst (M.oracleAt O N k y) = DSum.fst y := by
  simp [oracleAt, DSum.block_apply]

theorem proj_snd_oracleAt (k : ℕ) (y : M.LiftSpace N) (j : ι) (s : Fin (M.delay j)) :
    Reg.proj s (PiSum.proj j (DSum.snd (M.oracleAt O N k y))) =
      if 0 < k ∧ M.delay j ∣ k then O j (Reg.proj s (PiSum.proj j (DSum.snd y)))
      else Reg.proj s (PiSum.proj j (DSum.snd y)) := by
  simp only [oracleAt, DSum.snd_block_apply, zero_apply, zero_add,
    PiSum.proj_diag_apply]
  split_ifs <;> simp

theorem oracleAt_inl (k : ℕ) (x : Reg N P) :
    M.oracleAt O N k (DSum.inl x) = DSum.inl x := by
  simp [oracleAt, DSum.block_apply]

/-! ### Unitarity -/

theorem isIsometry_embedL (k : ℕ) : IsIsometry (M.embedL k) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.comp_apply, adjoint_embedL_apply, one_apply_eq_self]
  simp only [proj_embedL, Reg.proj_single_same]
  exact M.ports.sum_adj_apply v

theorem isIsometry_J (k : Fin N) : IsIsometry (M.J N k) := by
  refine ContinuousLinearMap.ext (fun x => ?_)
  rw [ContinuousLinearMap.comp_apply, adjoint_J_apply, J_apply, DSum.fst_mk, DSum.snd_mk,
    Reg.proj_single_same, (M.isIsometry_embedL k).apply_adjoint_apply]
  rfl

theorem isUnitary_step (k : Fin N) : IsUnitary (M.step N k) :=
  isUnitary_conj_add_one_sub (M.isIsometry_J N k) M.isUnitary_S

theorem isUnitary_oracleAt (hO : O.IsUnitary) (k : ℕ) : IsUnitary (M.oracleAt O N k) := by
  have hU : IsUnitary (PiSum.diag (K := fun j => Reg (M.delay j) (K j))
      (fun j => if 0 < k ∧ M.delay j ∣ k then Reg.map (O j) else 1)) := by
    apply PiSum.isUnitary_diag
    intro j
    split_ifs
    · exact Reg.isUnitary_map (hO j)
    · exact isUnitary_one
  constructor
  · rw [oracleAt, DSum.adjoint_block, DSum.block_comp_block, hU.1]; simp
  · rw [oracleAt, DSum.adjoint_block, DSum.block_comp_block, hU.2]; simp

theorem isUnitary_liftUpTo (hO : O.IsUnitary) (k : ℕ) : IsUnitary (M.liftUpTo O N k) := by
  induction k with
  | zero => exact isUnitary_one
  | succ k ih =>
    rw [liftUpTo]
    refine IsUnitary.comp ?_ ih
    split_ifs with h
    · exact (M.isUnitary_step N ⟨k, h⟩).comp (M.isUnitary_oracleAt O N hO k)
    · exact isUnitary_one

theorem isUnitary_lift (hO : O.IsUnitary) : IsUnitary (M.lift O N) :=
  M.isUnitary_liftUpTo O N hO N

/-! ### Query count (mQSP Eq. (2.24)) -/

omit [DecidableEq ι] in
theorem queries_eq (j : ι) : M.queries N j = (N - 1) / M.delay j := by
  rw [queries, ← Nat.Ioc_filter_dvd_card_eq_div]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h1, h3⟩

/-! ### The Toeplitz block (mQSP Eq. (2.23)) -/

/-- Age of slot `s` of the buffer of port `j` after time `k`: the number of steps since it
was last written (if it was written at all). -/
def age (j : ι) (k s : ℕ) : ℕ :=
  if s ≤ k % M.delay j then k % M.delay j - s else k % M.delay j + M.delay j - s

/-- The amplitude written into port `j` at relative time `n` for the impulse `ψ`. -/
noncomputable def wr (ψ : P) (j : ι) (n : ℕ) : K j := M.ports.π j (M.gseq O n ψ)

/-- Content of slot `s` of the buffer of port `j` after time `k`, for the impulse `ψ`
injected at time `i`: the amplitude written `age` steps ago, which has passed through `O j`
iff a multiple of `r j` lies in between (iff `k mod r j < s`). -/
noncomputable def cell (i k : ℕ) (ψ : P) (j : ι) (s : ℕ) : K j :=
  if M.age j k s ≤ k - i then
    (if k % M.delay j < s then O j (M.wr O ψ j (k - i - M.age j k s))
      else M.wr O ψ j (k - i - M.age j k s))
  else 0

/-- The clock register after time `k` for the impulse `ψ` injected at time `i`. -/
noncomputable def pubState (i k : ℕ) (ψ : P) : Reg N P :=
  WithLp.toLp 2 (fun o : Fin N => if i ≤ (o : ℕ) ∧ (o : ℕ) ≤ k then M.G O (o - i) ψ else 0)

/-- The delay memory after time `k` for the impulse `ψ` injected at time `i`. -/
noncomputable def memState (i k : ℕ) (ψ : P) : M.Mem :=
  WithLp.toLp 2 (fun j =>
    (WithLp.toLp 2 (fun s : Fin (M.delay j) => M.cell O i k ψ j s) : Reg (M.delay j) (K j)))

omit [DecidableEq ι] in
theorem proj_pubState (i k : ℕ) (ψ : P) (o : Fin N) :
    Reg.proj o (M.pubState O N i k ψ) =
      if i ≤ (o : ℕ) ∧ (o : ℕ) ≤ k then M.G O (o - i) ψ else 0 := rfl

omit [DecidableEq ι] in
theorem proj_memState (i k : ℕ) (ψ : P) (j : ι) (s : Fin (M.delay j)) :
    Reg.proj s (PiSum.proj j (M.memState O i k ψ)) = M.cell O i k ψ j s := rfl

omit [DecidableEq ι] in
theorem cell_base (i : ℕ) (ψ : P) (j : ι) (s : ℕ) (hs : s < M.delay j) :
    M.cell O i i ψ j s = if s = i % M.delay j then M.wr O ψ j 0 else 0 := by
  have hm := Nat.mod_lt i (M.one_le_delay j)
  simp only [cell, age]
  split_ifs <;> first | omega | rfl | (congr 1; omega)

omit [DecidableEq ι] in
theorem cell_mod (i k : ℕ) (ψ : P) (j : ι) :
    M.cell O i k ψ j (k % M.delay j) = M.wr O ψ j (k - i) := by
  simp [cell, age]

omit [DecidableEq ι] in
theorem cell_succ_of_ne (i k : ℕ) (ψ : P) (j : ι) (s : ℕ) (hs : s < M.delay j)
    (hne : s ≠ (k + 1) % M.delay j) :
    M.cell O i (k + 1) ψ j s =
      if 0 < k + 1 ∧ M.delay j ∣ k + 1 then O j (M.cell O i k ψ j s) else M.cell O i k ψ j s := by
  have hr := M.one_le_delay j
  have hm := Nat.mod_lt k (M.one_le_delay j)
  simp only [cell, age, Nat.dvd_iff_mod_eq_zero]
  rcases succ_mod_cases (k := k) (M.one_le_delay j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  split_ifs <;> (try first | omega | rfl | simp | (congr 2; omega) | (congr 1; omega))

omit [DecidableEq ι] in
/-- The slot read at time `k + 1` (after the oracle at time `k + 1`). -/
theorem cell_read (i k : ℕ) (hik : i ≤ k) (ψ : P) (j : ι) :
    (if 0 < k + 1 ∧ M.delay j ∣ k + 1 then O j (M.cell O i k ψ j ((k + 1) % M.delay j))
      else M.cell O i k ψ j ((k + 1) % M.delay j)) =
    if M.delay j ≤ k + 1 - i then O j (M.wr O ψ j (k + 1 - i - M.delay j)) else 0 := by
  have hr := M.one_le_delay j
  have hm := Nat.mod_lt k (M.one_le_delay j)
  simp only [cell, age, Nat.dvd_iff_mod_eq_zero]
  rcases succ_mod_cases (k := k) (M.one_le_delay j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  split_ifs <;> first | omega | rfl | simp | (congr 2; omega) | (congr 1; omega)

/-- Before the impulse time nothing happens. -/
theorem liftUpTo_apply_of_le (i : Fin N) (ψ : P) :
    ∀ n, n ≤ (i : ℕ) →
      M.liftUpTo O N n (DSum.inl (Reg.single i ψ)) = DSum.inl (Reg.single i ψ)
  | 0, _ => rfl
  | n + 1, h => by
    have hn : n < N := by omega
    have hne : (⟨n, hn⟩ : Fin N) ≠ i := fun h' => by
      have := congrArg Fin.val h'; simp only at this; omega
    rw [liftUpTo, dite_eq_left hn, ContinuousLinearMap.comp_apply,
      M.liftUpTo_apply_of_le i ψ n (by omega), ContinuousLinearMap.comp_apply, oracleAt_inl]
    have h2 : (M.J N ⟨n, hn⟩)† (DSum.inl (Reg.single i ψ)) = 0 := by
      rw [adjoint_J_apply]; simp [Reg.proj_single_of_ne hne]
    rw [step_apply, h2]; simp

/-- The full state of the lift after time `k ≥ i` for the impulse `ψ` injected at time `i`. -/
theorem liftUpTo_succ_apply (i : Fin N) (ψ : P) (k : ℕ) (hik : (i : ℕ) ≤ k) (hk : k < N) :
    M.liftUpTo O N (k + 1) (DSum.inl (Reg.single i ψ)) =
      DSum.mk (M.pubState O N i k ψ) (M.memState O i k ψ) := by
  induction k, hik using Nat.le_induction with
  | base =>
    rw [liftUpTo, dite_eq_left hk, ContinuousLinearMap.comp_apply,
      M.liftUpTo_apply_of_le O N i ψ i le_rfl, ContinuousLinearMap.comp_apply, oracleAt_inl]
    have h2 : (M.J N ⟨i, hk⟩)† (DSum.inl (Reg.single i ψ)) = DSum.mk ψ 0 := by
      rw [adjoint_J_apply]; simp
    have h3 : M.S (DSum.mk ψ 0) = DSum.mk (M.A ψ) (M.C ψ) := by rw [S_apply]; simp
    refine DSum.ext (Reg.ext fun o => ?_) (PiSum.ext fun j => Reg.ext fun s => ?_)
    · rw [proj_fst_step, h2, h3, DSum.fst_mk, proj_pubState]
      split_ifs with h4 h5 h5
      · have : o = i := Fin.ext h4
        subst this; simp
      · omega
      · omega
      · have : o ≠ i := fun h' => h4 (congrArg Fin.val h')
        simp [Reg.proj_single_of_ne this]
    · rw [proj_snd_step, h2, h3, DSum.snd_mk, proj_memState, M.cell_base O i ψ j s s.isLt]
      split_ifs
      · simp [wr]
      · simp
  | succ k hik ih =>
    have hk' : k < N := by omega
    rw [liftUpTo, dite_eq_left hk, ContinuousLinearMap.comp_apply, ih hk',
      ContinuousLinearMap.comp_apply]
    set Y := M.oracleAt O N (k + 1) (DSum.mk (M.pubState O N i k ψ) (M.memState O i k ψ))
      with hY
    have hfb : M.fb O (k + 1 - i) ψ = ∑ j, (M.ports.π j)†
        (if M.delay j ≤ k + 1 - i then O j (M.wr O ψ j (k + 1 - i - M.delay j)) else 0) := by
      rw [fb, _root_.sum_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs <;> simp [wr]
    have h2 : (M.J N ⟨k + 1, hk⟩)† Y = DSum.mk 0 (M.fb O (k + 1 - i) ψ) := by
      rw [adjoint_J_apply, hfb]
      congr 1
      · rw [hY, fst_oracleAt, DSum.fst_mk, proj_pubState, ite_eq_right (by simp)]
      · rw [adjoint_embedL_apply]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hY, proj_snd_oracleAt, DSum.snd_mk, proj_memState]
        congr 1
        exact M.cell_read O i k hik ψ j
    have hg : k + 1 - i = (k - i) + 1 := by omega
    have h3 : M.S (DSum.mk 0 (M.fb O (k + 1 - i) ψ)) =
        DSum.mk (M.G O (k + 1 - i) ψ) (M.gseq O (k + 1 - i) ψ) := by
      rw [S_apply]
      simp only [DSum.fst_mk, DSum.snd_mk, map_zero, zero_add]
      rw [hg, G_succ, gseq_succ]
      rfl
    refine DSum.ext (Reg.ext fun o => ?_) (PiSum.ext fun j => Reg.ext fun s => ?_)
    · rw [proj_fst_step, h2, h3, DSum.fst_mk, hY, fst_oracleAt, DSum.fst_mk, proj_pubState,
        proj_pubState]
      split_ifs <;> first | omega | rfl | (congr 2; omega)
    · rw [proj_snd_step, h2, h3, DSum.snd_mk, hY, proj_snd_oracleAt, DSum.snd_mk, proj_memState,
        proj_memState]
      split_ifs with hs
      · rw [hs, cell_mod]; rfl
      · exact (M.cell_succ_of_ne O i k ψ j s s.isLt hs).symm

/-- COMP-C1 (mQSP Thm 2.2). The public block of the lift is the lower-triangular Toeplitz
matrix of the impulse response: entry `(o, i)` is `G (o - i)` for `i ≤ o` and `0` otherwise. -/
theorem toeplitz_block (hO : O.IsUnitary) (i o : Fin N) :
    Reg.proj o ∘L DSum.fst ∘L M.lift O N ∘L DSum.inl ∘L Reg.single i =
      if (i : ℕ) ≤ o then M.G O (o - i) else 0 := by
  refine ContinuousLinearMap.ext (fun ψ => ?_)
  have h := M.liftUpTo_succ_apply O N i ψ (N - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at h
  simp only [ContinuousLinearMap.comp_apply, lift, h, DSum.fst_mk, proj_pubState]
  split_ifs with h1 h2 h2
  · rfl
  · omega
  · omega
  · rfl

/-- mQSP Eq. (2.26): every impulse-response coefficient is a contraction. -/
theorem norm_G_le_one (hO : O.IsUnitary) (n : ℕ) : ‖M.G O n‖ ≤ 1 := by
  have h := M.toeplitz_block O (n + 1) hO 0 (Fin.last n)
  rw [ite_eq_left (by simp), Fin.val_last, Fin.val_zero, Nat.sub_zero] at h
  rw [← h]
  exact comp_opNorm_le_one (PiSum.opNorm_proj_le _) (comp_opNorm_le_one DSum.opNorm_fst_le
    (comp_opNorm_le_one (M.isUnitary_lift O (n + 1) hO).opNorm_le_one
      (comp_opNorm_le_one DSum.isIsometry_inl.opNorm_le_one
        (Reg.isIsometry_single _).opNorm_le_one)))

end Junction

end MQSP
