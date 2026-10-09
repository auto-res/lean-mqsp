/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Compile.Lift

/-!
# Resource accounting (RES-1; mQSP Def A.1)

Ports are backed by *oracle types*: a port `j` calls oracle type `typ j` (forward or inverse
access, possibly on several copies at once); one port call is one controlled invocation of
that oracle and costs `cost (typ j)`. The lift of horizon `N` makes `queries N j` calls to
port `j`, so the weighted query cost is `⟨C, q⟩ = ∑ⱼ cost (typ j) * queries N j`
(mQSP Eq. (1.18)) and the number of invocations of oracle type `t` is
`∑_{j : typ j = t} queries N j`. Identity wires are ports with cost `0`.
-/

namespace MQSP

universe u v w x

open Finset

/-- RES-1. An assignment of oracle types and costs to the ports of a junction. -/
structure CostModel (ι : Type u) (τ : Type v) where
  /-- The oracle type called at each port. -/
  typ : ι → τ
  /-- The cost of one call of each oracle type. -/
  cost : τ → ℝ
  /-- Costs are nonnegative. -/
  cost_nonneg : ∀ t, 0 ≤ cost t

namespace Junction

variable {P : Type x} {L : Type v} [HSpace P] [HSpace L] {ι : Type u} [Fintype ι]
  [DecidableEq ι] {K : ι → Type w} [∀ i, HSpace (K i)]
variable (M : Junction P L K) (N : ℕ) {τ : Type*} [DecidableEq τ] (cm : CostModel ι τ)

/-- RES-1 (mQSP Eq. (1.18)). The weighted query cost `⟨C, q⟩` of the lift of horizon `N`. -/
noncomputable def weightedCost : ℝ := ∑ j, cm.cost (cm.typ j) * (M.queries N j : ℝ)

/-- The number of invocations of oracle type `t` in the lift of horizon `N`. -/
def invocations (t : τ) : ℕ := ∑ j ∈ Finset.univ.filter (fun j => cm.typ j = t), M.queries N j

omit [DecidableEq ι] in
/-- The weighted cost is the cost-weighted sum of invocations per type. -/
theorem weightedCost_eq_sum_invocations [Fintype τ] :
    M.weightedCost N cm = ∑ t, cm.cost t * (M.invocations N cm t : ℝ) := by
  simp only [weightedCost, invocations, Nat.cast_sum, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ cm.typ]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.1 hj).2]

omit [DecidableEq ι] [DecidableEq τ] in
/-- Upper bound `⟨C, q⟩ ≤ ∑ⱼ C_j (N - 1) / r_j` (mQSP Eq. (1.18) context). -/
theorem weightedCost_eq :
    M.weightedCost N cm = ∑ j, cm.cost (cm.typ j) * (((N - 1) / M.delay j : ℕ) : ℝ) := by
  simp only [weightedCost, queries_eq]

end Junction

end MQSP
