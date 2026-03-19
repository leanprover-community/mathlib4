/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.Algebra.Module.FiniteDimensionStrongTopology

/-!
# Distributions

Let `E` be a real **finite-dimensional normed space**, `Ω` an open subset of `E`,
and `F` a real **locally convex topological vector space**.

An **`F`-valued distribution on `Ω`** is a continuous `ℝ`-linear map `T : 𝓓(Ω, ℝ) →L[ℝ] F`,
defined on the space `𝓓(Ω, ℝ)` of real-valued test functions, and taking values in `F`.
In particular, if `𝕜` is an `RCLike` field, `𝓓'(Ω, 𝕜)` is the usual notion of real or complex
distribution on `Ω`.

We denote the space of `F`-valued distributions on `Ω` by `𝓓'(Ω, F)`. Topologically,
it is defined as `𝓓(Ω, ℝ) →L_c[ℝ] F`, meaning that we endow it with the topology of uniform
convergence on compact subsets of `𝓓(Ω, ℝ)`. In this particular case, this happens to coincide
with the topology of `𝓓(Ω, ℝ) →L[ℝ] F`, namely that of uniform convergence on bounded subsets.
See the implementation notes below for more details.

Right now, this file contains very few mathematical statements.
The theory will be expanded in future PRs.

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

Note that the parameter `n` here lives in `ℕ∞`, unlike the parameter for `ContDiff` which lives
in `WithTop ℕ∞` (to incorporate analytic functions). This means that we can't use the notation
`∞` introduced for `ContDiff` for our regularity, because it denotes an element of `WithTop ℕ∞`.
We could introduce another notation `∞` for `⊤ : ℕ∞`, but we believe it would be confusing.

## Implementation Notes

### `abbrev` or `def`

At this point in time, it is not clear whether we should enforce a separation between the API
for `𝓓'(Ω, F)` and the more generic API about `𝓓(Ω, ℝ) →L_c[ℝ] F`.
For now, we have made the "default" choice to implement `Distribution` as an `abbrev`, which means
that we get a lot of instances for free, but also that there is no such separation of APIs.

If this happens to be a bad decision, which will become clear while developing the theory,
do not hesitate to refactor to a `def` instead.

### Vector-valued distributions

The theory of vector-valued distributions is not as well-known as its scalar-valued analog. The
definition we choose is studied in
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957].

Let us give two examples of how we plan to use this level of generality:
* In the short term, this will allow us to define the *Fréchet derivative* of a distribution,
  as a continuous linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E →L[ℝ] F)`. Note that, even if `F = ℝ`,
  the derivative is naturally vector-valued.
* On a longer timescale, we should aim to prove the
  [Schwartz Kernel Theorem](https://en.wikipedia.org/wiki/Schwartz_kernel_theorem), which is
  formulated nicely in terms of vector-valued distributions. Indeed, it says precisely that one
  can (algebraically, at least) identify the spaces `𝓓'(Ω₁ ×ˢ Ω₂, ℝ)` and `𝓓'(Ω₁, 𝓓'(Ω₂, ℝ))`.

### Choice of scalar field

In the literature, it is common to define complex-valued distributions as continuous `ℂ`-linear
forms `T : 𝓓(Ω, ℂ) →L[ℂ] ℂ`. We use `𝓓(Ω, ℝ) →L[ℝ] ℂ` instead, that is, we only ever test
against *real-valued* test functions.

This makes no difference mathematically, since `𝓓(Ω, ℂ)` is the complexification of `𝓓(Ω, ℝ)`,
hence there is a topological isomorphism between `𝓓(Ω, ℝ) →L[ℝ] F` and `𝓓(Ω, ℂ) →L[ℂ] F`
whenever `F` is a complex vector space.

We choose this definition because it avoids adding a base field as an extra parameter.
Instead, we use the generality of vector-valued distributions to our advantage: a complex-valued
distribution is nothing more than a distribution taking values in the real vector-space `ℂ`.

### Order of distributions

Based on established practice in the literature, a natural way to express the order of a
distribution would be to introduce a predicate `Distribution.HasOrderAtMost` on the space of all
distributions. Here though, we define a separate space `𝓓'^{n}(Ω, F)` whose elements are precisely
distributions of order at most `n`.

This is not incompatible with the predicate approach: in fact, we think that such a predicate
should eventually become the primary interface for the order of a distribution. However, we believe
that being able to talk about the space `𝓓'^{n}(Ω, F)` is also quite important, for the following
reasons:
* if `T : 𝓓'(Ω,F)` is a distribution whose order is at most `n`, it is natural to test it against
  a `C^n` test function (especially if `n = 0`). This means that we naturally want to consider its
  extension `T'` as an element of `𝓓'^{n}(Ω, F)`.
* it is often quite easy to keep track of the regularities while *defining* an operation on
  distributions (e. g. differentiation). On the other hand, once you have defined an operation on
  `𝓓'^(Ω, F)`, it can be quite painful to study its relation to order *a posteriori*.

Note that the topology on `𝓓'^{n}(Ω, F)` has no reason to be the subspace topology coming from
`𝓓'(Ω, F)`.

### Choice of topology

Our choice of the compact convergence topology on `𝓓'^{n}(Ω, F)` follows
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*, §2, p. 49][schwartz1957].

Note that, since `𝓓(Ω, ℝ)` is a Montel space, the topology on `𝓓'(Ω, F)` is also that of
bounded convergence. Hence, our definition also agrees with
[L. Schwartz, *Théorie des distributions*, Chapitre III, §3][schwartz1950].

When `n` is finite, however, `𝓓^{n}(Ω, ℝ)` is no longer a Montel space
(see [L. Schwartz, *Théorie des distributions*, Chapitre III, §2, p. 71][schwartz1950]), hence
these two topologies have no reason to be the same. Schwartz uses compact convergence as a default
(see [L. Schwartz, *Théorie des distributions à valeurs vectorielles*, §2, p. 50][schwartz1957]),
which we follow here.

Finally, note that a **sequence** of distributions converges in `𝓓'(Ω, F)` if and only if it
converges pointwise
(see [L. Schwartz, *Théorie des distributions*, Chapitre III, §3, Theorème XIII][schwartz1950]).
Due to this fact, some texts endow `𝓓'(Ω, F)` with the pointwise convergence topology. While this
gives the same converging sequences as the topology of bounded/compact convergence, this is no
longer true for general filters.

## References

* [L. Schwartz, *Théorie des distributions*][schwartz1950]
* [L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957]

-/

@[expose] public section

open Set TopologicalSpace Topology
open scoped Distributions CompactConvergenceCLM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {Fᵤ : Type*} [AddCommGroup Fᵤ] [Module ℝ Fᵤ] [UniformSpace Fᵤ]
  {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  {Fᵤ' : Type*} [AddCommGroup Fᵤ'] [Module ℝ Fᵤ'] [UniformSpace Fᵤ']
  {n k : ℕ∞}

-- TODO: def or abbrev?
variable (Ω F n) in
/-- `𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on `Ω` with
order at most `n`.

In most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`. -/
abbrev Distribution := 𝓓^{n}(Ω, ℝ) →L_c[ℝ] F

/-- We denote `𝓓'^{n}(Ω, F)` the space of `F`-valued distributions on `Ω` with order at most
`n : ℕ∞`. Note that using `𝓓'` is a bit abusive since this is no longer a dual space unless
`F = 𝕜`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- We denote `𝓓'(Ω, F)` the space of `F`-valued distributions on `Ω`. Note that using `𝓓'`
is a bit abusive since this is no longer a dual space unless `F = 𝕜`. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
variable [IsUniformAddGroup Fᵤ] [ContinuousSMul ℝ Fᵤ]
variable [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']
variable [IsUniformAddGroup Fᵤ'] [ContinuousSMul ℝ Fᵤ']

namespace Distribution

section mapCLM
-- TODO: generalize this section to `𝕜` linear maps (or even semilinear maps)
-- by generalizing `ContinuousLinearMap.postcompCompactConvergenceCLM`

/-- Any continuous linear map `A : F →L[ℝ] G` induces a continuous linear map
`𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to applying `A`
pointwise. -/
noncomputable def mapCLM (A : F →L[ℝ] F') : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F') :=
  A.postcompCompactConvergenceCLM _

@[simp]
lemma mapCLM_apply {A : F →L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLM A T f = A (T f) := rfl

lemma isUniformEmbedding_mapCLM {A : Fᵤ →L[ℝ] Fᵤ'} (hA : IsUniformEmbedding A) :
    IsUniformEmbedding (mapCLM A : 𝓓'^{n}(Ω, Fᵤ) →L[ℝ] 𝓓'^{n}(Ω, Fᵤ')) :=
  UniformConvergenceCLM.isUniformEmbedding_postcomp _ A hA _

-- TODO: add `UniformConvergenceCLM.isEmbedding_postcomp`
lemma isEmbedding_mapCLM {A : F →L[ℝ] F'} (hA : IsEmbedding A) :
    IsEmbedding (mapCLM A : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F')) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI := IsTopologicalAddGroup.rightUniformSpace F'
  haveI : IsUniformAddGroup F' := isUniformAddGroup_of_addCommGroup
  isUniformEmbedding_mapCLM (AddMonoidHom.isUniformEmbedding_of_isEmbedding hA) |>.isEmbedding

end mapCLM

section LineDerivCLM
-- TODO: generalize this section to `𝕜` linearity
-- by generalizing `ContinuousLinearMap.precompCompactConvergenceCLM`

/-- `lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending a distribution
`T : 𝓓'^{k}_{K}(E, F)` to its derivative along the vector `v`, which is a
distribution in `𝓓^{n}_{K}(E, F)`. Because derivativing increases the order, this only makes sense
if `k + 1 ≤ n`, otherwise we define it as the zero map.

The parameters `n` and `k` are implicit as they can often be inferred from context, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of the `LineDeriv`
notation typeclass. -/
noncomputable def lineDerivCLM (v : E) :
    𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  - (TestFunction.lineDerivCLM ℝ v).precompCompactConvergenceCLM _

lemma lineDerivCLM_apply {v : E} {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    lineDerivCLM v T f = - T (TestFunction.lineDerivCLM ℝ v f) :=
  rfl

lemma lineDerivCLM_add {v₁ v₂ : E} :
    (lineDerivCLM (v₁ + v₂) : 𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      lineDerivCLM v₁ + lineDerivCLM v₂ := by
  ext T f
  -- Why `(v := _)` ???
  simp [lineDerivCLM_apply (v := _), TestFunction.lineDerivCLM_add, neg_add, -neg_add_rev]

lemma lineDerivCLM_smul {c : ℝ} {v : E} :
    (lineDerivCLM (c • v) : 𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      c • lineDerivCLM v := by
  ext T f
  -- Why `(v := _)` ???
  simp [lineDerivCLM_apply (v := _), TestFunction.lineDerivCLM_smul]

open LineDeriv

/-- Note: we cannot express the full generality of `lineDerivCLM` purely in terms of this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the input type
`𝓓^{n}_{K}(E, F)`. -/
noncomputable instance : LineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp v := lineDerivCLM v

variable (𝕜) in
lemma lineDerivOp_eq_lineDerivCLM {v : E} {T : 𝓓'(Ω, F)} :
    ∂_{v} T = lineDerivCLM v T :=
  rfl

noncomputable instance : LineDerivAdd E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM v)
  lineDerivOp_left_add _ _ T := congr($lineDerivCLM_add T)

noncomputable instance : LineDerivSMul ℝ E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM v)

noncomputable instance : ContinuousLineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM v).continuous

lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM ℝ 𝓓'(Ω, F) v = lineDerivCLM v :=
  rfl

end LineDerivCLM

variable [FiniteDimensional ℝ E]

section FDerivCLM
-- TODO: generalize this section to `𝕜` linearity
-- by generalizing `ContinuousLinearMap.precompCompactConvergenceCLM`

open ContinuousLinearMap Topology

noncomputable def fderivCLM_v2 :
    𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, E →L[ℝ] F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let step1 (T : 𝓓'^{k}(Ω, F)) (f : 𝓓^{n}(Ω, ℝ)) : E →L[ℝ] F := LinearMap.toContinuousLinearMap
    { toFun v := lineDerivCLM v T f
      map_add' _ _ := by simp [lineDerivCLM_add]
      map_smul' _ _ := by simp [lineDerivCLM_smul] }
  have step1_def (T : 𝓓'^{k}(Ω, F)) (f : 𝓓^{n}(Ω, ℝ)) (v : E) :
    step1 T f v = lineDerivCLM v T f := rfl
  have emb1 : IsEmbedding ((↑) : (E →L[ℝ] F) → (E → F)) :=
    ContinuousLinearMap.isEmbedding_coeFn_of_finiteDimensional
  have step1_cont (T : 𝓓'^{k}(Ω, F)) : Continuous (step1 T) := by
    rw [emb1.continuous_iff, continuous_pi_iff]
    exact fun v ↦ (lineDerivCLM v T).continuous
  let step2 (T : 𝓓'^{k}(Ω, F)) : 𝓓'^{n}(Ω, E →L[ℝ] F) :=
    { toFun := step1 T
      map_add' _ _ := by ext; simp [step1_def]
      map_smul' _ _ := by ext; simp [step1_def] }
  have step2_def (T : 𝓓'^{k}(Ω, F)) (f : 𝓓^{n}(Ω, ℝ)) (v : E) :
    step2 T f v = lineDerivCLM v T f := rfl
  let Φ (T : 𝓓'^{n}(Ω, E →L[ℝ] F)) : E →L[ℝ] 𝓓'^{n}(Ω, F) := LinearMap.toContinuousLinearMap
    sorry
  have step2_cont : Continuous step2 :=
    sorry
  { toFun := step2
    map_add' _ _ := by ext; simp [step2_def]
    map_smul' _ _ := by ext; simp [step2_def] }


noncomputable def fderivCLM :
    𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, E →L[ℝ] F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  let step1 (T : 𝓓'^{k}(Ω, F)) (f : 𝓓^{n}(Ω, ℝ)) : E →L[ℝ] F := LinearMap.toContinuousLinearMap
    { toFun v := lineDerivCLM v T f
      map_add' _ _ := by simp [lineDerivCLM_add]
      map_smul' _ _ := by simp [lineDerivCLM_smul] }
  have step1_def (T : 𝓓'^{k}(Ω, F)) (f : 𝓓^{n}(Ω, ℝ)) (v : E) :
    step1 T f v = lineDerivCLM v T f := rfl
  have emb1 : IsEmbedding ((↑) : (E →L[ℝ] F) → (E → F)) :=
    ContinuousLinearMap.isEmbedding_coeFn_of_finiteDimensional
  have step1_cont (T : 𝓓'^{k}(Ω, F)) : Continuous (step1 T) := by
    rw [emb1.continuous_iff, continuous_pi_iff]
    exact fun v ↦ (lineDerivCLM v T).continuous
  let step2 (T : 𝓓'^{k}(Ω, F)) : 𝓓'^{n}(Ω, E →L[ℝ] F) :=
    { toFun := step1 T
      map_add' _ _ := by ext; simp [step1_def]
      map_smul' _ _ := by ext; simp [step1_def] }
  have step2_def (T : 𝓓'^{k}(Ω, F)) (f : 𝓓^{n}(Ω, ℝ)) (v : E) :
    step2 T f v = lineDerivCLM v T f := rfl
  let Φ (T : 𝓓'^{n}(Ω, E →L[ℝ] F)) : E →L[ℝ] 𝓓'^{n}(Ω, F) := LinearMap.toContinuousLinearMap
    sorry
  have step2_cont : Continuous step2 :=
    sorry
  { toFun := step2
    map_add' _ _ := by ext; simp [step2_def]
    map_smul' _ _ := by ext; simp [step2_def] }

lemma fderivCLM_eq_lineDerivCLM {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} {v : E} :
    fderivCLM T f v = lineDerivCLM v T f :=
  rfl

@[simp]
lemma fderivCLM_apply {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} {v : E} :
    fderivCLM T f v = - T (TestFunction.lineDerivCLM ℝ v f) :=
  rfl

end FDerivCLM

end Distribution
