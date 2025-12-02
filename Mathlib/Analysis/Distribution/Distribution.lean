/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.LocallyConvex.StrongTopology

/-!
# Distributions

Let `E` be a real **finite-dimensional normed space**, `Ω` an open subset of `E`,
and `F` a real **locally convex topological vector space**.

A **`F`-valued distributions on `Ω`** is a continuous `ℝ`-linear map `T : 𝓓(Ω, ℝ) →L_c[ℝ] F`,
defined on the space `𝓓(Ω, ℝ)` of real-valued test functions, and taking values in `F`.
In particular, if `𝕜` is `RCLike`, this is the usual notion of real or complex distribution.

We denote the space of `F`-valued distributions on `Ω` by `𝓓'(Ω, F)`. Topologically,
it is defined as `𝓓(Ω, ℝ) →L_c[ℝ] F`, meaning that we endow it with topology of uniform
convergence on compact subsets of `𝓓(Ω, ℝ)`. If this choice of topology is surprising,
see the implementation notes below.

Right now, this file contains very few mathematical statements.
The theory will be expanded very soon.

## Main Declarations

* `𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on `Ω` with
  order at most `n`. See the implementation notes below for more information about the parameter
  `n : ℕ∞`; in most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`.
* `Distribution.mapCLM`: any continuous linear map `A : F →L[ℝ] G` induces a continuous linear
  map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to applying `A`
  pointwise.

## Notation

In the `Distributions` scope, we introduce the following notations:
* `𝓓'^{n}(Ω, F)`: the space of `F`-valued distributions on the open set `Ω` with order at most
  `n : ℕ∞`.
* `𝓓'(Ω, F)`: the space of `F`-valued distributions on the open set `Ω`, i.e `𝓓'^{⊤}(Ω, F)`.

## Implementation Notes

### `abbrev` or `def`

At this point in time, it is not clear wether we should enforce an API barrier between
`𝓓'(Ω, F)` and `𝓓(Ω, ℝ) →L_c[ℝ] F`. For now, we have made the "default" choice to implement
`Distribution` as an `abbrev`, which means that we get a lot of instances for free, but also
that there is no API barrier.

If this happens to be a bad decision, which will become clear while developping the theory,
do not hesitate to refactor to a `def` instead.

### Vector-valued distributions

The theory of vector-valued distributions is not as well-known as its scalar-valued analog. The
definition we choose is studied in
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957].

Let us give two examples of how we plan to use this level of generality:
* In the short term, this will allow us to define the *Fréchet derivative* of a distribution,
  as a continuous linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E →L[ℝ] F)`. Note that, even if `F = ℝ`,
  the derivative is naturally vector valued.
* On a longer timescale, we should aim to prove the
  [Schwartz Kernel Theorem](https://en.wikipedia.org/wiki/Schwartz_kernel_theorem), which is
  formulated nicely in terms of vector-valued distributions. Indeed, it says precisely that one
  can (algebraically, at least) identify the spaces `𝓓'(Ω₁ ×ˢ Ω₂, ℝ)` and `𝓓'(Ω₁, 𝓓'(Ω₂, ℝ))`.

### Choice of scalar field

You might be surprised that complex-valued distributions `𝓓'(Ω, ℂ)` are defined
as `𝓓(Ω, ℝ) →L[ℝ] ℂ` instead of `𝓓(Ω, ℂ) →L[ℂ] ℂ` (in other words, we only ever test
against *real-valued* test functions).

This makes no difference mathematically, since `𝓓(Ω, ℂ)` is the complexification of `𝓓(Ω, ℝ)`,
hence there is a topological isomorphism between `𝓓(Ω, ℝ) →L[ℝ] F` and `𝓓(Ω, ℂ) →L[ℂ] F`
whenever `F` is a complex vector space.

We choose this definition because it avoids adding a base field as an extra parameter.
Instead, we use the generality of vector-valued distributions to our advantage: a complex-valued
distribution is nothing more than a distribution taking values in the real vector-space `ℂ`.

### Order of distributions

If you have followed a typical course on distribution theory, you might expect that the
order of a distribution would be formalized by a predicate `Distribution.HasOrderAtMost` on
the space of all distributions, rather than by using a separate space `𝓓'^{n}(Ω, F)`.

We do in fact plan on defining such a predicate as the primary interface for the order of a
distribution. However, we believe that being able to talk about the space `𝓓'^{n}(Ω, F)` is also
quite important, for the following reasons:
* if `T` is a distribution of order at most `n`, it is natural to test it against a `C^n` test
  function (especially if `n = 0`). This means that we naturally want to consider its extension
  `T'` as an element of `𝓓'^{n}(Ω, F)`.
* it is often quite easy to keep track of the regularities while *defining* an operation on
  distributions (e.g differentiation). On the other hand, once you have defined an operation on
  `𝓓'^(Ω, F)`, it can be quite painful to study its relation to order *a posteriori*.

Note that the topology on `𝓓'^{n}(Ω, F)` has no reason to be the subspace topology coming from
`𝓓'(Ω, F)`.

### Choice of topology

Our choice of topology on `𝓓'^{n}(Ω, F)` follows from
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957]. Note that,
since, `𝓓(Ω, ℝ)` is a Montel space, the topology on `𝓓'(Ω, F)` is also that of uniform convergence
on `IsVonNBounded` subsets (the corresponding fact does not hold for `𝓓'^{n}(Ω, F)` though).
Hence, our definition also agrees with [L. Schwartz, *Théorie des distributions*][schwartz1950].

If you have followed a typical course on distribution theory, you might have expected the topology
on `𝓓'(Ω, F)` to be that of pointwise convergence. This misconception comes from the fact that,
for **sequences**, convergence in `𝓓'(Ω, F)` corresponds to pointwise convergence, but this is no
longer true for general filters.
See [L. Schwartz, *Théorie des distributions*, Chapitre III, §3, Theorème XIII][schwartz1950].

## References

* [L. Schwartz, *Théorie des distributions*][schwartz1950]
* [L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957]

-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions CompactConvergenceCLM

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜] [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [Module 𝕜 F] [Module 𝕂 F] [TopologicalSpace F]
  {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [Module 𝕜 F'] [Module 𝕂 F'] [TopologicalSpace F']
  {n k : ℕ∞}

-- TODO: def or abbrev?
variable (Ω F n) in
abbrev Distribution := 𝓓^{n}(Ω, ℝ) →SL_c[RingHom.id ℝ] F

/-- We denote `𝓓'^{n}(Ω, F)` the space of `F`-valued distributions on `Ω` with order at most
`n : ℕ∞`. Note that using `𝓓'` is a bit abusive since this is no longer a dual space unless
`F = 𝕜`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- We denote `𝓓'^{n}(Ω, F)` the space of `F`-valued distributions on `Ω`. Note that using `𝓓'`
is a bit abusive since this is no longer a dual space unless `F = 𝕜`. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [ContinuousSMul 𝕜 F]
variable [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [ContinuousSMul 𝕜 F']

namespace Distribution

section mapCLM
-- TODO: generalize this section to `𝕜` linear maps (or even semilinear maps)
-- by generalizing `ContinuousLinearMap.postcomp`

def mapCLM (A : F →L[ℝ] F') : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F') :=
  ContinuousLinearMap.postcomp_uniformConvergenceCLM (_ : Set <| Set <| 𝓓^{n}(Ω, ℝ)) A

@[simp]
lemma mapCLM_apply {A : F →L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLM A T f = A (T f) := rfl

end mapCLM

end Distribution
