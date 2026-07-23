# Public-import refactor progress

## Current state

- The original mass change demoted public imports of modules selected for containing no literal
  `def`, `abbrev`, `irreducible_def`, or `instance`. `Mathlib/Tactic/` and
  `Mathlib/Util/` remain restored as requested.
- All edits are in the working tree; do **not** use `git restore` or reset. The Git index is
  read-only in this environment, so no commit checkpoint was made.
- `git diff --check` passes.

## Last completed validation

1. The first 54 full-build failures were reduced using compiler-suggested public imports and
   direct imports.
2. The final nine in that batch all compiled successfully after:
   - private imports for tangent-cone, derivative-composition, ideal-big-operator, Euclidean,
     and similar APIs;
   - four necessary public boundaries where exported declarations required them.
3. A subsequent full build was recorded in:

   `/tmp/mathlib-full-after-private-repair.log`

   It completed with **41** failures. The repaired nine did not fail.

## Current in-progress batch: 41 failures

### Completed first reduction: compiler-suggested public imports

- Applied the 21 explicit `consider adding public import` suggestions from the 41-failure log.
- Rebuilt all 41 targets, recorded in:

  `/tmp/mathlib-41-public-round1.log`

- This reduced the target set to **36** failures.
- Applied the one additional public suggestion:

  `Mathlib/RingTheory/Etale/Field.lean` → `Mathlib.RingTheory.Spectrum.Prime.RingHom`.

### In-progress second reduction: direct private imports

Immediately before stopping, 30 ordinary imports were added from locally located definitions.
They have **not yet been validated**. The pending target/import pairs are:

- `InverseFunctionTheorem/Deriv` → `FDeriv.Equiv`
- `CartanCriterion` → `LinearAlgebra.JordanChevalley`
- `Finite/GaloisField`, `IntegralClosure/IntegralRestrict` → `NumberTheory.NumberField.Norm`
- `Normed/Module/DoubleDual` → `Normed.Module.HahnBanach`
- `PurelyInseparable/Exponent` → `FieldTheory.Minpoly.MinpolyDiv`
- `FDeriv/Measurable` → `TangentCone.Real`
- `Calculus/Implicit` → `FDeriv.Comp`
- `Sphere/OrthRadius`, `InnerProductSpace/PiL2` → `LinearAlgebra.BilinearForm.Orthogonal`
- `Sphere/SecondInter`, `Euclidean/MongePoint` → `Geometry.Euclidean.Basic`
- `Lie/Weights/Killing` → `LinearAlgebra.Trace`
- `Lie/LieTheorem` → `LinearAlgebra.Eigenspace.Basic`
- `BernoulliPolynomials` → `Algebra.BigOperators.Field`
- `SeparablyGenerated` → `RingTheory.Algebraic.Integral`
- `Kernel/Composition/KernelLemmas` → `Kernel.Composition.CompProd`
- `Kernel/Deterministic` → `Kernel.Composition.CompMap`
- `Kernel/IonescuTulcea/PartialTraj` → `Kernel.Composition.Comp`
- `Padics/Complex` → `Analysis.Normed.Algebra.Ultra`
- `NumberField/Basic` → `Algebra.Ring.Int.Field`
- `Ideal/Height`, `KrullDimension/Zero` → `Ideal.MinimalPrime.Localization`
- `CStarAlgebra/ContinuousFunctionalCalculus/Instances` → `InnerProductSpace.StarOrder`
- `Spectrum/Prime/Chevalley` → `RingTheory.Adjoin.FGBaseChange`
- `WittVector/Verschiebung` → `Algebra.MvPolynomial.Funext`
- `Smooth/StandardSmoothCotangent` → `Ideal.BigOperators`
- `Spectrum/Prime/FreeLocus` → `Algebra.Module.LocalizedModule.AtPrime`
- `Teichmuller` → `Algebra.CharP.Quotient`
- `Unramified/LocalRing` → `RingTheory.Nakayama`
- `Etale/StandardEtale` → `Ideal.Quotient.Nilpotent`

## Resume procedure

1. Validate the 36 targets from the first reduction log after the pending edits:

   ```bash
   rg '^✖ \\[' /tmp/mathlib-41-public-round1.log |
     sed -E 's/^✖ \\[[0-9]+\\/[0-9]+\\] Building ([^ ]+).*/\\1/' |
     sort -u | xargs lake build > /tmp/mathlib-41-private-round1.log 2>&1
   ```

2. For compiler suggestions, add the exact `public import` reported by Lean, rebuilding the
   affected targets after each batch.
3. For remaining unknown constants/identifiers, locate the declaration with `rg -n` (Loogle
   fallback) and add the defining module as an ordinary `import`; rebuild the target.
4. Once this target batch is clean, run a full build to find the next layer:

   ```bash
   lake build > /tmp/mathlib-full-next.log 2>&1
   ```

5. Always finish a batch with `git diff --check`.

## Checkpoint: 41-failure batch repaired

The full iterative reduction has now completed for this batch.  The final target pass is logged
in `/tmp/mathlib-41-private-round5.log`; its three remaining targets were repaired and validated
individually:

- `AlgebraicIndependent/RankAndCardinality`: direct `MvPolynomial.Cardinal` import.
- `ClassNumber/Finite`: restored the required public imports for absolute values, admissibility,
  and norms.
- `Lebesgue/EqHaar`: direct `MeasureTheory.Group.Pointwise` import.

The last direct validation log is `/tmp/mathlib-rank-round10.log`, and `git diff --check` passes.
The next step is a new complete build:

```bash
lake build > /tmp/mathlib-full-next.log 2>&1
```
