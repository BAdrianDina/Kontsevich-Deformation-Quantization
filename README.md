# Kontsevich Deformation Quantization in Lean

Track 4 working directory.

## Contents

- `Kontsevich-Deformation-Quantization-Problem-And-Lean-Path.tex`
  Working note. States the deformation quantization problem, fixes
  notation for every structure involved (Poisson manifolds, polyvector
  fields, polydifferential operators, $L_\infty$-algebras, Kontsevich
  graphs, weight integrals), states Kontsevich's formality theorem,
  and lays out a layered formalization path in Lean 4 / Mathlib with
  concrete first milestones, challenges, and alternative approaches.
- `Kontsevich-Deformation-Quantization-Problem-And-Lean-Path.pdf`
  Compiled output. 15 pages.
- `lakefile.toml`, `lean-toolchain`
  Minimal Lean 4 / Mathlib project scaffold.
- `Kontsevich.lean`
  Root Lean module. Imports the global implementation path.
- `Kontsevich/Workstreams/`
  Six independent workstream modules. Each one imports only
  `Kontsevich.Workstreams.Common`, so it can be built without importing
  the global project module.
- `Kontsevich/Global/Basic.lean`
  Connects the six workstreams into one ordered implementation path.

## Build

LaTeX note:

```
pdflatex Kontsevich-Deformation-Quantization-Problem-And-Lean-Path.tex
pdflatex Kontsevich-Deformation-Quantization-Problem-And-Lean-Path.tex
pdflatex Kontsevich-Deformation-Quantization-Problem-And-Lean-Path.tex
```

Compiles with 0 errors, 0 warnings, 0 undefined references, and 0
overfull / underfull boxes.

Lean scaffold:

```
lake update
lake exe cache get
lake build
```

Single-workstream smoke test:

```
lake env lean Kontsevich/Workstreams/A_CombinatorialAndPolynomial/Basic.lean
```

## Scope

The note is the baseline for the Lean formalization track. It is not
a survey and does not aim to prove anything new; it fixes definitions,
conventions, and a milestone sequence so subsequent Lean modules and
LaTeX notes share a single set of statements and references.

The Lean scaffold is intentionally minimal. It contains no mathematical
proofs beyond structural smoke tests. Its purpose is to give the team a
stable directory shape before the workstreams are filled in.

## Workstream layout

- `A_CombinatorialAndPolynomial`
  Admissible graphs, polynomial objects on `R^d`, `B_Gamma`, and graph
  weights.
- `B_GradedAndLie`
  Schouten-Nijenhuis, Gerstenhaber, Hochschild differential, and dg Lie
  instances.
- `C_HKR`
  Hochschild-Kostant-Rosenberg map, chain-map statement, and
  quasi-isomorphism statement.
- `D_LInfinityMC`
  `L_infinity` structures, morphisms, Maurer-Cartan elements, gauge
  equivalence, and MC transport.
- `E_KontsevichFormula`
  The maps `U_n`, the Moyal test case, the `L_infinity` identities modulo
  boundary identities, and the star-product corollary.
- `F_AnalyticInput`
  Configuration spaces, compactifications, angle forms, Stokes with
  corners, and weight integrals.

## Next artefacts

The note ends with a sequence of milestones (Section 6 of the PDF).
Each milestone will live in its own subdirectory of this folder, with
its own `Title-Case-With-Hyphens.tex` and, where applicable, a Lean
module.
