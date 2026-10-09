/-
Copyright (c) 2026 shosonoda. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: shosonoda
-/
import MQSP.Compose.Series
import MQSP.Compose.Wire
import MQSP.Compose.DirectSum
import MQSP.Compose.Spectator
import MQSP.Compose.Inverse
import MQSP.Compose.Substitute
import MQSP.Compose.Delay
import MQSP.Compile.Lift
import MQSP.Clock.Uniform
import MQSP.Modules.Query
import MQSP.Modules.Cayley
import MQSP.Modules.Chain

/-!
# The surface language: programs as module networks (LANG-1)

A *program* is a syntax tree whose leaves are library modules (or raw unitary junctions) and
whose nodes are the connection rules of mQSP §5.2. It is indexed by its public space `P` and
its *port family* `pf` (the oracle ports it exposes), so that substitution of a program into a
port of another is well typed. The private space is *not* an index: it is computed by the
denotation `denote : Prog P pf → Den P pf` (a junction on some private space).

```
p, q ::= prim M                      -- a unitary junction (Prop 5.1); library modules
       | query E                     -- the direct query of an oracle on E
       | cayley E                    -- the Cayley module
       | p ;; q                      -- Series   (p first, then q)
       | V ◁ p | p ▷ V               -- Wire     (known unitary before / after)
       | p ⊕ q                       -- DirectSum
       | spectator n p               -- Spectator register `Fin n`
       | p⁻¹                         -- Inverse  (reversed system, inverse oracles)
       | p ⇐[j] q                    -- Substitute q for the oracle at port j of p
       | withDelay r hr p            -- Delay: change the query schedule of p
```

Semantics of a program on an oracle tuple `O` for its ports: steady value
`steady p O`, catalyst weights `weight p O j ψ`, impulse response `G p O n`, and the compiled
circuit `lift p O N` with `queries p N j = ⌊(N-1)/rⱼ⌋` calls to port `j`. The theorems
`steady_series`, `steady_wireAfter`, …, `steady_subst` are the compositional semantics: the
steady value of a program is computed from the steady values of its parts.
-/

namespace MQSP

universe u

/-- A bundled family of oracle ports: a finite index type and a Hilbert space per port. -/
structure PortFamily : Type (u + 1) where
  /-- The port index type (small). -/
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  /-- The port spaces. -/
  K : ι → Type u
  [inst : ∀ i, HSpace (K i)]

attribute [instance] PortFamily.fin PortFamily.dec PortFamily.inst

namespace PortFamily

/-- The port family with one port of space `E`. -/
abbrev one (E : Type u) [HSpace E] : PortFamily where
  ι := One
  K := onePort E

/-- Disjoint union of two port families. -/
abbrev sum (pf₁ pf₂ : PortFamily.{u}) : PortFamily where
  ι := pf₁.ι ⊕ pf₂.ι
  K := Sum.elim pf₁.K pf₂.K

/-- The ports of a chain of `d` queries on `H`. -/
abbrev chain (H : Type u) [HSpace H] (d : ℕ) : PortFamily where
  ι := Fin d
  K := Junction.chainPorts H d

/-- Tensoring every port with a spectator register. -/
noncomputable abbrev reg (n : ℕ) (pf : PortFamily.{u}) : PortFamily where
  ι := pf.ι
  K := fun j => Reg n (pf.K j)

end PortFamily

/-- LANG-1. Programs: module networks indexed by public space and port family. -/
inductive Prog : (P : Type u) → [HSpace P] → PortFamily.{u} → Type (u + 1)
  /-- A raw unitary junction (mQSP Prop 5.1). Library modules enter through this leaf. -/
  | prim {P L : Type u} [HSpace P] [HSpace L] {pf : PortFamily} (M : Junction P L pf.K) :
      Prog P pf
  /-- Series connection: `p` first, then `q` (mQSP §5.2 Series). -/
  | series {P : Type u} [HSpace P] {pf₁ pf₂ : PortFamily} (p : Prog P pf₁) (q : Prog P pf₂) :
      Prog P (pf₁.sum pf₂)
  /-- A known unitary applied to the public input before `p`. -/
  | wireBefore {P : Type u} [HSpace P] {pf : PortFamily} (V : P →L[ℂ] P) (hV : IsUnitary V)
      (p : Prog P pf) : Prog P pf
  /-- A known unitary applied to the public output after `p`. -/
  | wireAfter {P : Type u} [HSpace P] {pf : PortFamily} (V : P →L[ℂ] P) (hV : IsUnitary V)
      (p : Prog P pf) : Prog P pf
  /-- Orthogonal branches (mQSP §5.2 DirectSum). -/
  | dsum {P₁ P₂ : Type u} [HSpace P₁] [HSpace P₂] {pf₁ pf₂ : PortFamily} (p : Prog P₁ pf₁)
      (q : Prog P₂ pf₂) : Prog (P₁ ⊕ₕ P₂) (pf₁.sum pf₂)
  /-- A spectator register `Fin n` (mQSP §5.2 Spectator). -/
  | spectator {P : Type u} [HSpace P] {pf : PortFamily} (n : ℕ) (p : Prog P pf) :
      Prog (Reg n P) (pf.reg n)
  /-- The inverse network (mQSP §5.2 Inverse). -/
  | inverse {P : Type u} [HSpace P] {pf : PortFamily} (p : Prog P pf) : Prog P pf
  /-- Substitute `q` for the oracle at port `j` of `p` (mQSP §5.2 Substitute). -/
  | subst {P : Type u} [HSpace P] {pf pf' : PortFamily} (p : Prog P pf) (j : pf.ι)
      (q : Prog (pf.K j) pf') : Prog P (pf.sum pf')
  /-- Change the port delays (query schedule) of `p` (mQSP §5.2 Delay). -/
  | withDelay {P : Type u} [HSpace P] {pf : PortFamily} (r : pf.ι → ℕ) (hr : ∀ j, 1 ≤ r j)
      (p : Prog P pf) : Prog P pf

namespace Prog

/-- The denotation of a program: a junction on some private space. -/
structure Den (P : Type u) [HSpace P] (pf : PortFamily.{u}) : Type (u + 1) where
  /-- The private space. -/
  L : Type u
  [inst : HSpace L]
  /-- The junction. -/
  M : Junction P L pf.K

attribute [instance] Den.inst

/-- LANG-1. The denotation `denote : Prog P pf → Den P pf`. -/
noncomputable def denote : {P : Type u} → [HSpace P] → {pf : PortFamily} → Prog P pf → Den P pf
  | _, _, _, prim M => ⟨_, M⟩
  | _, _, _, series p q => ⟨_, (denote p).M.series (denote q).M⟩
  | _, _, _, wireBefore V hV p => ⟨_, (denote p).M.wireBefore V hV⟩
  | _, _, _, wireAfter V hV p => ⟨_, (denote p).M.wireAfter V hV⟩
  | _, _, _, dsum p q => ⟨_, (denote p).M.directSum (denote q).M⟩
  | _, _, _, spectator n p => ⟨_, (denote p).M.spectator n⟩
  | _, _, _, inverse p => ⟨_, (denote p).M.inverse⟩
  | _, _, _, subst p j q => ⟨_, (denote p).M.subst j (denote q).M⟩
  | _, _, _, withDelay r hr p => ⟨_, (denote p).M.withDelay r hr⟩

variable {P : Type u} [HSpace P] {pf : PortFamily.{u}}

/-- The direct query of an oracle on `E`. -/
noncomputable def query (E : Type u) [HSpace E] : Prog E (PortFamily.one E) :=
  prim (Junction.query E)

/-- The Cayley module. -/
noncomputable def cayley (E : Type u) [HSpace E] : Prog E (PortFamily.one (Reg 2 E)) :=
  prim (Junction.cayley E)

/-- A chain of `d` queries with known unitaries `cd.V` in between (a finite query circuit). -/
noncomputable def chain {H : Type u} [HSpace H] {d : ℕ} (cd : Junction.ChainData H d) :
    Prog H (PortFamily.chain H d) :=
  prim cd.junction

/-- Oracle tuples for the ports of a program. -/
abbrev Oracles (pf : PortFamily.{u}) : Type u := OracleTuple pf.K

/-- LANG-1. The steady value (transfer value at `z = 1`) of a program. -/
noncomputable def steady (p : Prog P pf) (O : Oracles pf) : P →L[ℂ] P := (denote p).M.steady O

/-- Regularity of a program's loop on `O`. -/
def IsRegular (p : Prog P pf) (O : Oracles pf) : Prop := (denote p).M.IsRegular O

/-- The catalyst weight of port `j` of a program. -/
noncomputable def weight (p : Prog P pf) (O : Oracles pf) (j : pf.ι) (ψ : P) : ℝ :=
  (denote p).M.weight O j ψ

/-- The impulse response of a program. -/
noncomputable def G (p : Prog P pf) (O : Oracles pf) (n : ℕ) : P →L[ℂ] P := (denote p).M.G O n

/-- The port delays of a program. -/
noncomputable def delay (p : Prog P pf) (j : pf.ι) : ℕ := (denote p).M.delay j

/-- The number of queries to port `j` made by the compiled circuit of horizon `N`. -/
noncomputable def queries (p : Prog P pf) (N : ℕ) (j : pf.ι) : ℕ := (denote p).M.queries N j

/-- The compiled circuit (unitary Toeplitz lift) of horizon `N`. -/
noncomputable def lift (p : Prog P pf) (O : Oracles pf) (N : ℕ) :=
  (denote p).M.lift O N

/-- The number of ports (computable). -/
def numPorts (_ : Prog P pf) : ℕ := Fintype.card pf.ι

/-- A printable description of the network structure (computable). -/
def describe : {P : Type u} → [HSpace P] → {pf : PortFamily} → Prog P pf → String
  | _, _, pf, prim _ => s!"prim[{Fintype.card pf.ι} ports]"
  | _, _, _, series p q => s!"({describe p} ;; {describe q})"
  | _, _, _, wireBefore _ _ p => s!"(V ◁ {describe p})"
  | _, _, _, wireAfter _ _ p => s!"({describe p} ▷ V)"
  | _, _, _, dsum p q => s!"({describe p} ⊕ {describe q})"
  | _, _, _, spectator n p => s!"(spectator {n} {describe p})"
  | _, _, _, inverse p => s!"({describe p})⁻¹"
  | _, _, _, subst p _ q => s!"({describe p} ⇐[_] {describe q})"
  | _, _, _, withDelay _ _ p => s!"(delay {describe p})"

/-! ### Notation -/

@[inherit_doc] infixl:60 " ;; " => Prog.series
@[inherit_doc] infixl:65 " ⊕ₚ " => Prog.dsum
/-- `V ◁ p` with a unitarity proof: `Prog.wireBefore V hV p`. -/
notation:70 V " ◁[" hV "] " p:70 => Prog.wireBefore V hV p
/-- `p ▷ V` with a unitarity proof: `Prog.wireAfter V hV p`. -/
notation:70 p:70 " ▷[" hV "] " V => Prog.wireAfter V hV p
/-- Substitution `p ⇐[j] q`: feed port `j` of `p` with the program `q`. -/
notation:70 p:70 " ⇐[" j "] " q:71 => Prog.subst p j q

/-! ### Compositional semantics (LANG-1) -/

@[simp] theorem denote_prim {L : Type u} [HSpace L] (M : Junction P L pf.K) :
    (denote (prim M)).M = M := rfl

theorem steady_prim {L : Type u} [HSpace L] (M : Junction P L pf.K) (O : Oracles pf) :
    steady (prim M) O = M.steady O := rfl

theorem queries_eq (p : Prog P pf) (N : ℕ) (j : pf.ι) : queries p N j = (N - 1) / delay p j :=
  (denote p).M.queries_eq N j

/-- The steady value of a program is unitary (for unitary oracles and a regular loop). -/
theorem isUnitary_steady (p : Prog P pf) {O : Oracles pf} (hO : O.IsUnitary)
    (h : IsRegular p O) : IsUnitary (steady p O) :=
  (denote p).M.isUnitary_steady hO h

theorem steady_query {E : Type u} [HSpace E] (U : E →L[ℂ] E) :
    steady (query E) (oneOracle U) = U :=
  Junction.query_steady U

theorem steady_cayley {E : Type u} [HSpace E] {O : Reg 2 E →L[ℂ] Reg 2 E}
    (hO : Junction.IsSelfInverse O) :
    steady (cayley E) (oneOracle O) =
      (1 - Complex.I • Junction.encoded O) ∘L Ring.inverse (1 + Complex.I • Junction.encoded O) :=
  Junction.cayley_steady hO

theorem steady_chain {H : Type u} [HSpace H] {d : ℕ} (cd : Junction.ChainData H d)
    (O : Fin d → (H →L[ℂ] H)) :
    steady (chain cd) (Junction.ChainData.oracles O) = cd.circuit O :=
  cd.steady_eq_circuit O

theorem steady_series {pf₁ pf₂ : PortFamily.{u}} (p : Prog P pf₁) (q : Prog P pf₂)
    {O : Oracles (pf₁.sum pf₂)} (hp : IsRegular p O.left) (hq : IsRegular q O.right) :
    steady (p ;; q) O = steady q O.right ∘L steady p O.left :=
  Junction.series_steady _ _ hp hq

theorem steady_wireBefore (V : P →L[ℂ] P) (hV : IsUnitary V) (p : Prog P pf) (O : Oracles pf) :
    steady (wireBefore V hV p) O = steady p O ∘L V :=
  Junction.wireBefore_steady _ V hV O

theorem steady_wireAfter (V : P →L[ℂ] P) (hV : IsUnitary V) (p : Prog P pf) (O : Oracles pf) :
    steady (wireAfter V hV p) O = V ∘L steady p O :=
  Junction.wireAfter_steady _ V hV O

theorem steady_dsum {P₁ P₂ : Type u} [HSpace P₁] [HSpace P₂] {pf₁ pf₂ : PortFamily.{u}}
    (p : Prog P₁ pf₁) (q : Prog P₂ pf₂) {O : Oracles (pf₁.sum pf₂)} (hp : IsRegular p O.left)
    (hq : IsRegular q O.right) :
    steady (p ⊕ₚ q) O = DSum.block (steady p O.left) 0 0 (steady q O.right) :=
  Junction.directSum_steady _ _ hp hq

theorem steady_spectator (n : ℕ) (p : Prog P pf) {O : Oracles pf} (h : IsRegular p O) :
    steady (spectator n p) (Junction.OracleTuple.reg n O) = Reg.map (steady p O) :=
  Junction.spectator_steady _ n h

theorem steady_inverse (p : Prog P pf) {O : Oracles pf} (hO : O.IsUnitary) (h : IsRegular p O) :
    steady (inverse p) (Junction.OracleTuple.inv' O) = (steady p O)† := by
  unfold steady IsRegular at *
  simp only [denote]
  exact Junction.inverse_steady _ hO h

theorem steady_subst {pf' : PortFamily.{u}} (p : Prog P pf) (j : pf.ι) (q : Prog (pf.K j) pf')
    {O : Oracles (pf.sum pf')} (hid : O.left j = 1) (hq : IsRegular q O.right)
    (hp : IsRegular p (Function.update O.left j (steady q O.right))) :
    steady (p ⇐[j] q) O = steady p (Function.update O.left j (steady q O.right)) :=
  Junction.subst_steady _ j _ hid hq hp

theorem steady_withDelay (r : pf.ι → ℕ) (hr : ∀ j, 1 ≤ r j) (p : Prog P pf) (O : Oracles pf) :
    steady (withDelay r hr p) O = steady p O := rfl

theorem queries_withDelay (r : pf.ι → ℕ) (hr : ∀ j, 1 ≤ r j) (p : Prog P pf) (N : ℕ) (j : pf.ι) :
    queries (withDelay r hr p) N j = (N - 1) / r j :=
  Junction.withDelay_queries _ r hr N j

/-- Series composition is thrifty: the weight of a port of `q` is evaluated on the state
transmitted by `p` (mQSP Eq. (5.15)). -/
theorem weight_series_inr {pf₁ pf₂ : PortFamily.{u}} (p : Prog P pf₁) (q : Prog P pf₂)
    {O : Oracles (pf₁.sum pf₂)} (hp : IsRegular p O.left) (hq : IsRegular q O.right) (j : pf₂.ι)
    (ψ : P) : weight (p ;; q) O (Sum.inr j) ψ = weight q O.right j (steady p O.left ψ) :=
  Junction.series_weight_inr _ _ hp hq j ψ

theorem weight_series_inl {pf₁ pf₂ : PortFamily.{u}} (p : Prog P pf₁) (q : Prog P pf₂)
    {O : Oracles (pf₁.sum pf₂)} (hp : IsRegular p O.left) (hq : IsRegular q O.right) (j : pf₁.ι)
    (ψ : P) : weight (p ;; q) O (Sum.inl j) ψ = weight p O.left j ψ :=
  Junction.series_weight_inl _ _ hp hq j ψ

/-- Every program compiles: the lift of horizon `N` is unitary and its public block is the
Toeplitz matrix of the impulse response. -/
theorem isUnitary_lift (p : Prog P pf) {O : Oracles pf} (hO : O.IsUnitary) (N : ℕ) :
    IsUnitary (lift p O N) :=
  (denote p).M.isUnitary_lift O N hO

theorem toeplitz_block (p : Prog P pf) {O : Oracles pf} (hO : O.IsUnitary) (N : ℕ)
    (i o : Fin N) :
    Reg.proj o ∘L DSum.fst ∘L lift p O N ∘L DSum.inl ∘L Reg.single i =
      if (i : ℕ) ≤ o then G p O (o - i) else 0 :=
  (denote p).M.toeplitz_block O N hO i o

/-- LANG-1 (end-to-end compilation, mQSP Thm 3.2). Every regular unit-delay program compiles
with the uniform clock of horizon `N` to a circuit that encodes an operator within
`‖Γ‖/√N` of its steady value, at normalization `1`. -/
theorem isEncodingOf_uniform (p : Prog P pf) {O : Oracles pf} (hd : ∀ j, delay p j = 1)
    (hO : O.IsUnitary) (h : IsRegular p O) (N : ℕ) (hN : 0 < N) :
    IsEncodingOf (Reg.map (lift p O N)) (Clock.clockIn (Clock.box N N))
        (Clock.clockIn (Clock.box N N)) ((denote p).M.weighted O (Junction.uniformWeights N) N) ∧
      ‖steady p O - (denote p).M.weighted O (Junction.uniformWeights N) N‖ ≤
        ‖(denote p).M.catalyst O‖ / Real.sqrt N :=
  (denote p).M.isEncodingOf_uniform O hd hO h N hN

end Prog

end MQSP
