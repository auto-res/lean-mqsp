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

## Reporting

- Final report under 40 lines: what was proved, what is left (`sorry` list), files, build
  and test status with timings, API names discovered. Do not paste file contents.
- Append a dated entry to `PROGRESS.md` (Japanese) only when the parent asks for it.
