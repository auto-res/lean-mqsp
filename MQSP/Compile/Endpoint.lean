/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Compile.Lift
import MQSP.Compile.Clock
import MQSP.Modules.Chain

/-!
# Endpoint clocks and exact compilation of finite query circuits (COMP-C4; mQSP Thm 4.4/4.8)

If the impulse response of a junction is concentrated at a single delay `T` (`G T = V`,
`G n = 0` otherwise) — e.g. a chain of `T` queries — then the lift of horizon `T + 1` with the
endpoint clock `cin = |0⟩`, `cout = |T⟩` (one label) selects the block `kernel (lift) T 0 = V`
exactly, with normalization `1`: `1_R ⊗ lift` is an encoding of `V` (mQSP Eq. (4.76)).
For a chain this reproduces the circuit `V_T O_{T-1} ⋯ O_0 V_0` with `T` queries: the
QSVT circuit is the quditization of its chain module with the endpoint clock.
-/

namespace MQSP

universe u v w x

open Finset

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (O : OracleTuple K)

/-- The endpoint clock state `|k⟩` with a single label. -/
def endpointClock (N : ℕ) (k : Fin N) : Fin 1 → Fin N → ℂ := fun _ i => if i = k then 1 else 0

theorem isNormalized_endpointClock (N : ℕ) (k : Fin N) :
    Clock.IsNormalized (endpointClock N k) := by
  simp [Clock.IsNormalized, endpointClock, apply_ite]

/-- The clock matrix of the endpoint pair `(|0⟩, |T⟩)` is `|T⟩⟨0|`. -/
theorem clockX_endpoint (N : ℕ) (i o : Fin N) :
    Clock.clockX (endpointClock N i) (endpointClock N o) =
      fun o' i' => if o' = o ∧ i' = i then 1 else 0 := by
  funext o' i'
  by_cases ho : o' = o <;> by_cases hi : i' = i <;> simp [Clock.clockX, endpointClock, ho, hi]

/-- COMP-C4 (mQSP Eq. (4.76)). The endpoint-clock block of the lift is `G (o - i)`. -/
theorem extract_endpoint (hO : O.IsUnitary) (N : ℕ) (i o : Fin N) (hio : (i : ℕ) ≤ o) :
    Clock.extract (Clock.clockX (endpointClock N i) (endpointClock N o))
      (Clock.kernel (M.lift O N)) = M.G O (o - i) := by
  rw [clockX_endpoint]
  simp only [Clock.extract, ite_and, ite_smul, one_smul, zero_smul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Clock.kernel, M.toeplitz_block O N hO i o, ite_eq_left hio]

/-- COMP-C4. The lift with the endpoint clock `(|0⟩, |T⟩)` encodes `G T` exactly. -/
theorem isEncodingOf_endpoint (hO : O.IsUnitary) (T : ℕ) :
    IsEncodingOf (Reg.map (M.lift O (T + 1)))
      (Clock.clockIn (endpointClock (T + 1) 0))
      (Clock.clockIn (endpointClock (T + 1) (Fin.last T))) (M.G O T) := by
  have h := Clock.isEncodingOf_quditize (Mm := M.Mem) (M.isUnitary_lift O (T + 1) hO)
    (isNormalized_endpointClock (T + 1) 0) (isNormalized_endpointClock (T + 1) (Fin.last T))
  rw [M.extract_endpoint O hO (T + 1) 0 (Fin.last T) (by simp), Fin.val_last, Fin.val_zero,
    Nat.sub_zero] at h
  exact h

end Junction

namespace Junction.ChainData

variable {H : Type u} [HSpace H] {d : ℕ} (cd : ChainData H d) (O : Fin d → (H →L[ℂ] H))

/-- COMP-C4 (mQSP Thm 4.4/4.8 for chains). Compiling a chain of `d` queries at horizon
`d + 1` with the endpoint clock yields an exact encoding of the circuit. Note that the
generic Toeplitz lift unrolls the chain for *every* clock input and therefore calls each of
the `d` ports `d` times (`queries (d+1) j = d`); the circuit itself (`compileFIR`) uses one
call per port. The lift is the uniform compilation route shared with IIR modules; for
feedback-free modules the direct route below is the one that reproduces GSLW Lemma 19. -/
theorem isEncodingOf_chain_endpoint (hO : ∀ k, IsUnitary (O k)) :
    IsEncodingOf (Reg.map (cd.junction.lift (oracles O) (d + 1)))
      (Clock.clockIn (endpointClock (d + 1) 0))
      (Clock.clockIn (endpointClock (d + 1) (Fin.last d))) (cd.circuit O) := by
  have h := cd.junction.isEncodingOf_endpoint (oracles O) hO d
  rw [cd.G_eq, ite_eq_left rfl] at h
  exact h

/-- The first `m` steps of a chain with unitary oracles form a unitary. -/
theorem isUnitary_go (hO : ∀ k, IsUnitary (O k)) (m : ℕ) (hm : m ≤ d) :
    IsUnitary (circuit.go cd O m hm) := by
  induction m with
  | zero => exact isUnitary_one
  | succ m ih => exact (hO _).comp ((cd.isUnitary_V _).comp (ih (by omega)))

/-- A chain circuit with unitary oracles is unitary. -/
theorem isUnitary_circuit (hO : ∀ k, IsUnitary (O k)) : IsUnitary (cd.circuit O) :=
  (cd.isUnitary_V _).comp (cd.isUnitary_go O hO d le_rfl)

/-- COMP-C4. The direct compilation of a feedback-free module: the circuit itself, which is
trivially an encoding of itself (no clock, no ancilla, one call per port). -/
theorem isEncodingOf_circuit (hO : ∀ k, IsUnitary (O k)) :
    IsEncodingOf (cd.circuit O) 1 1 (cd.circuit O) :=
  ⟨cd.isUnitary_circuit O hO, isUnitary_one.isIsometry, isUnitary_one.isIsometry, by simp⟩

end Junction.ChainData

end MQSP
