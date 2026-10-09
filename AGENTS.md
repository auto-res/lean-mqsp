# Guidance for AI coding agents (lean-mqsp)

Conventions for agents working in this repository. The plan is `dev/plan.md`, the design of the
language is `doc/design.md`, the formal specification with theorem IDs is `dev/formal-spec.md`,
the theorem inventories of the three papers are `dev/inventory/*.md`, the dated log is `PROGRESS.md`.

## Repository and git

- Development branch: `ss`. Never commit to `main`.
- Subagents never run `git add/commit/push`; the parent session commits. Report the list of
  files you created or changed instead.
- One agent per disjoint file set. Never edit a file another agent owns in the same wave.
- `dev/` holds development notes (plan, spec, surveys, inventories; Japanese). `00note/` is a
  private directory excluded from git; never add it.

## Build

- Toolchain `leanprover/lean4:v4.34.1`, Mathlib tag `v4.34.1` (pinned in `lake-manifest.json`).
- After changing dependencies: `lake update` then `lake exe cache get`. Never build Mathlib
  from source; if the cache fails, stop and report.
- Iterate with `lake env lean <file>`; finish with `lake build` (whole library, must be
  warning-free under the Mathlib standard linter set) and `lake test`.
- doc-gen4 and other slow optional targets are not used by default.
- Tests live in `test/MQSPTest.lean` and `test/MQSPTest/*.lean`: `#guard`, `#guard_msgs`, and
  `#guard_msgs in #print axioms <main theorem>` audits (expected axioms: `propext`,
  `Classical.choice`, `Quot.sound` only).

## Lean conventions

- `relaxedAutoImplicit = false`: declare every variable.
- No `axiom`. No `sorry` in committed modules unless the parent explicitly allows a listed
  work-in-progress lemma; list every remaining `sorry` in your report.
- Namespaces follow directories: `MQSP.Core`, `MQSP.Module`, `MQSP.Compose`, `MQSP.Compile`,
  `MQSP.Clock`, `MQSP.Modules`, `MQSP.Algorithms`, `MQSP.QSVT`, `MQSP.CPE`, `MQSP.Poly`, `MQSP.Lang`.
- Separate definition modules (`Defs`) from theorem modules so that statements can import
  definitions only.
- Each declaration that realizes a spec item gets a docstring starting with its ID, e.g.
  `/-- MOD-3 (mQSP Prop 5.1). ... -/`. Keep the paper's theorem numbers in docstrings.
- Header: the Mathlib header linter expects a copyright block; copy the one in
  `MQSP/Core/HSpace.lean`.
- Prefer Mathlib names over local re-definitions; put general lemmas that belong upstream
  in `MQSP/ToMathlib/`.

## Mathlib v4.34.1 notes (pitfalls met so far)

- `WithLp p V` is a structure (`WithLp.toLp`, `WithLp.ofLp`), not a type synonym.
- `CompleteSpace` is not inferred from `FiniteDimensional`; use the bundled class
  `MQSP.HSpace` (finite-dimensional complex Hilbert space) which includes it.
- `Mathlib.Analysis.Matrix` is now `Mathlib.Analysis.Matrix.Normed` / `.Spectrum`;
  `Mathlib.Analysis.InnerProductSpace.Projection` is a directory (`.Projection.Basic`);
  orthogonal projections are `Submodule.orthogonalProjectionOnto` / `Submodule.starProjection`.
- Cauchy estimates: `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`
  (`Mathlib.Analysis.Complex.Liouville`). Abel limits: `Mathlib.Analysis.Complex.AbelLimit`.
- Singular values: `LinearMap.singularValues` (`Mathlib.Analysis.InnerProductSpace.SingularValues`).
- Neumann series: `Units.oneSub`, `NormedRing.inverse_one_sub` (needs `HasSummableGeomSeries`).
- Renamed/deprecated: `ContinuousLinearMap.add_apply/sub_apply/zero_apply/sum_apply/smul_apply` →
  root `add_apply`, `sub_apply`, `zero_apply`, `_root_.sum_apply`, `smul_apply`; `one_apply` →
  `one_apply_eq_self`; `coe_sum'` → `FunLike.coe_sum`; `comp_finset_sum`/`finset_sum_comp` →
  `comp_finsetSum`/`finsetSum_comp`; `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`;
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `Module.End.mul_eq_comp`.
- `IsUnit` of an endomorphism: `ContinuousLinearMap.isUnit_iff_bijective` +
  `LinearMap.injective_iff_surjective`; `Function.Injective ⇑(1 - T)` needs the explicit coercion.
- `Π` is a reserved token; name projections `Pr`, `P₀`, ….
- `simp`/`rw` do not see through `instHSpaceSumElim` (ports indexed by `ι₁ ⊕ ι₂`): state helper
  lemmas at the plain type `K₁ i` and close with `exact`/`change`.
- `lake env lean` ignores lakefile linter options; some warnings only appear under `lake build`.
- Theorems about `Prog` denotations: do not state a program-level theorem by `exact`-ing a
  junction-level theorem (the instance `Den.inst (denote p)` and `Sum.elim … (inr i)` vs `K i`
  unify only by deep unfolding → `maximum recursion depth`); prove through the language's own
  compositional lemmas (`steady_series`, `steady_subst`, …) or `dsimp only [steady, denote]`.
- Never define a notation of the form `p "[" … "]"`: it clashes with array indexing `xs[i]!`.
- `evalExpr` is unsafe; meta code that inspects programs (`#mqsp_info`) walks the `Expr` and
  counts `Sum`/`Fin`/`Unit` index types structurally instead of evaluating.
- `DSum.mk` is a reducible abbreviation, so `rw [DSum.fst_mk]`/`snd_mk` can match any `fst v`;
  use typed `have h : DSum.snd (…) = l := congrArg DSum.snd hv` instead of blind `rw`.
- Rall's rounding promise must use the rounding convention for bits
  (`⌊x·2^(k+1) + 1/2⌋ % 2`); the floor convention is inconsistent with the promise.

## Reporting

- Final report under 40 lines: what was proved, what is left (`sorry` list), files, build
  and test status with timings, API names discovered. Do not paste file contents.
- Append a dated entry to `PROGRESS.md` (Japanese) only when the parent asks for it.
