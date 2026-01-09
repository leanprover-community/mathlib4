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

At this point in time, it is not clear wether we should enforce a separation between the API
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

open Set TopologicalSpace
open scoped Distributions CompactConvergenceCLM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  {n k : ℕ∞}


-- TODO: def or abbrev?
variable (Ω F n) in
abbrev Distribution := 𝓓^{n}(Ω, ℝ) →L_c[ℝ] F

-- TODO: I'm not sure these notations are good
/-- Notation for the space of distributions of order less than `n`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- We denote `𝓓'(Ω, F)` the space of `F`-valued distributions on `Ω`. Note that using `𝓓'`
is a bit abusive since this is no longer a dual space unless `F = 𝕜`. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤


namespace Distribution

section mapCLM

def mapCLM [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [IsTopologicalAddGroup F']
    [ContinuousSMul ℝ F'] (A : F →L[ℝ] F') : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F') :=
  A.postcomp_uniformConvergenceCLM _

@[simp]
lemma mapCLM_apply [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [IsTopologicalAddGroup F']
    [ContinuousSMul ℝ F'] {A : F →L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLM A T f = A (T f) := rfl

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
-- variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']
-- variable [NormedAddCommGroup F'] [NormedAddCommGroup F']
-- TODO: naming...
-- noncomputable def mapCLE (A : F ≃L[ℝ] F') : 𝓓'^{n}(Ω, F) ≃L[ℝ] 𝓓'^{n}(Ω, F') := by
--   -- let φ := @mapCLM E _ _ Ω F _ _ _ F' _ _ _ n _ _ _ _ A
--   -- refine ContinuousLinearEquiv.equivOfInverse φ ?_ ?_ ?_
--
--   let := @ContinuousLinearEquiv.arrowCongr
--   -- let := (ContinuousLinearEquiv.refl ℝ 𝓓'^{n}(Ω, ℝ)).arrowCongr A
--
-- @[simp]
-- lemma mapCLE_apply {A : F ≃L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
--     mapCLE A T f = A (T f) := rfl
--
-- @[simp]
-- lemma mapCLE_symm {A : F ≃L[ℝ] F'} :
--     (mapCLE A : 𝓓'^{n}(Ω, F) ≃L[ℝ] 𝓓'^{n}(Ω, F')).symm = mapCLE A.symm := rfl

end mapCLM

section ofFun


variable [MeasurableSpace E] [OpensMeasurableSpace E]

open Function Seminorm SeminormFamily Set TopologicalSpace MeasureTheory
open scoped BoundedContinuousFunction NNReal Topology ContDiff Distributions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (Ω n) in
/-- The distribution of given order induced by a function:
0 if that function is not locally integrable. -/
noncomputable def ofFunWithOrder (f : E → F) (μ : Measure E := by volume_tac) :
    𝓓'^{n}(Ω, F) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ f

variable (Ω) in
/-- The smooth distribution induced by a function: 0 if that function is not locally integrable. -/
noncomputable def ofFun (f : E → F) (μ : Measure E := by volume_tac) : 𝓓'(Ω, F) :=
  ofFunWithOrder Ω ⊤ f μ

-- TODO: be more consistent about the naming: which is φ and which is f ?

@[simp]
lemma ofFunWithOrder_apply {f : E → F} {μ : Measure E} (hf : LocallyIntegrableOn f Ω μ)
    {φ : 𝓓^{n}(Ω, ℝ)} :
    ofFunWithOrder Ω n f μ φ = ∫ x, φ x • f x ∂μ := by
  simp [ofFunWithOrder, TestFunction.integralAgainstBilinCLM_apply hf]

@[simp]
lemma ofFun_apply {f : E → F} {μ : Measure E} (hf : LocallyIntegrableOn f Ω μ)
    {φ : 𝓓(Ω, ℝ)} :
    ofFun Ω f μ φ = ∫ x, φ x • f x ∂μ :=
  ofFunWithOrder_apply hf

lemma ofFunWithOrder_of_not_locallyIntegrable {f : E → F} {μ : Measure E}
    (hf : ¬LocallyIntegrableOn f Ω μ) : ofFunWithOrder Ω n f μ = 0 := by
  ext φ
  simp_rw [ofFunWithOrder, TestFunction.integralAgainstBilinCLM,
    TestFunction.integralAgainstBilinLM, hf]
  dsimp
  congr -- TODO: this line used to be not necessary!

lemma ofFun_of_not_locallyIntegrable {f : E → F} {μ : Measure E} (hf : ¬LocallyIntegrableOn f Ω μ) :
    ofFun Ω f μ = 0 := by
  ext φ
  simp [ofFun, ofFunWithOrder_of_not_locallyIntegrable hf]

lemma ofFunWithOrder_ae_congr {f f' : E → F} {μ : Measure E} (h : f =ᵐ[μ.restrict Ω] f') :
  ofFunWithOrder Ω n f μ = ofFunWithOrder Ω n f' μ := sorry

lemma ofFun_ae_congr {f f' : E → F} {μ : Measure E} (h : f =ᵐ[μ.restrict Ω] f') :
    ofFun Ω f μ = ofFun Ω f' μ := ofFunWithOrder_ae_congr h

@[simp]
lemma ofFunWithOrder_zero {μ : Measure E} : ofFunWithOrder Ω n (0 : E → F) μ = 0 := by
  ext φ
  simp [ofFunWithOrder, TestFunction.integralAgainstBilinCLM, TestFunction.integralAgainstBilinLM]
  congr -- TODO: this line used to be not necessary!

@[simp]
lemma ofFun_zero {μ : Measure E} : ofFun Ω (0 : E → F) μ = 0 := by
  ext φ
  simp [ofFun]

-- TODO: find a better name!
lemma integrable_smul {f : E → F} {μ : Measure E} (φ : 𝓓(Ω, ℝ)) (hf : LocallyIntegrableOn f Ω μ) :
    Integrable (fun x ↦ φ x • f x) μ := by
  sorry -- φ has support inside Ω, and f is integrable on Ω

@[simp]
lemma ofFun_add {f g : E → F} {μ : Measure E}
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ) :
    ofFun Ω (f + g) μ = ofFun Ω f μ + ofFun Ω g μ := by
  ext φ
  rw [ContinuousLinearMap.add_apply, ofFun_apply hf, ofFun_apply hg, ofFun_apply (hf.add hg),
    ← integral_add (integrable_smul φ hf) (integrable_smul φ hg)]
  simp

lemma ofFun_neg {f : E → F} {μ : Measure E} : ofFun Ω (-f) μ = -ofFun Ω f μ := by
  ext φ
  by_cases hf: LocallyIntegrableOn f Ω μ
  · simp [ofFun_apply hf, ofFun_apply hf.neg, integral_neg]
  · have : ¬ LocallyIntegrableOn (-f) Ω μ := by rwa [locallyIntegrableOn_neg_iff]
    simp [*, ofFun_of_not_locallyIntegrable]

@[simp]
lemma ofFun_smul {f : E → F} {μ : Measure E} (c : ℝ) : ofFun Ω (c • f) μ = c • ofFun Ω f μ := by
  by_cases! hc : c = 0
  · simp [hc]
  by_cases hf: LocallyIntegrableOn f Ω μ; swap
  · have : ¬ LocallyIntegrableOn (c • f) Ω μ := by simp [hc, hf]
    simp [ofFun_of_not_locallyIntegrable this, ofFun_of_not_locallyIntegrable hf]
  ext φ
  rw [ofFun_apply (hf.smul c)]
  simp only [Pi.smul_apply]
  rw [ContinuousLinearMap.coe_smul']
  dsimp -- TODO: this used to be not necessary!
  rw [ofFun_apply hf, ← integral_smul c]
  congr with x
  module

end ofFun

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
variable [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']

section lineDeriv



-- TODO: where to put the minus ? Doesn't matter mathematically of course
variable (n k) in
noncomputable def lineDerivWithOrderCLM (v : E) :
    𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{k}(Ω, F) := sorry
  -- (- TestFunction.lineDerivWithOrderCLM k n v).(precomp F )

@[simp]
lemma lineDerivWithOrderCLM_apply {v : E} {T : 𝓓'^{n}(Ω, F)} {φ : 𝓓^{k}(Ω, ℝ)} :
    lineDerivWithOrderCLM n k v T φ = T (- TestFunction.lineDerivWithOrderCLM k n v φ) := sorry
  -- rfl

-- TODO: where to put the minus ? Doesn't matter mathematically of course
noncomputable def lineDerivCLM (v : E) :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, F) := sorry
  -- .precomp F (- TestFunction.lineDerivCLM v)

@[simp]
lemma lineDerivCLM_apply {v : E} {T : 𝓓'(Ω, F)} {φ : 𝓓(Ω, ℝ)} :
    lineDerivCLM v T φ = T (- TestFunction.lineDerivCLM v φ) := sorry
  -- rfl

end lineDeriv

-- Everything below is quite experimental, although mathematically correct

section fderiv

variable [FiniteDimensional ℝ E]

-- NOTE: these definitions will change (but not their type).
-- Essentially, using the fact that `E` is finite dimensional, you can put the `v : E`
-- argument wherever you want and keep continuity

-- TODO: where to put the minus ? Doesn't matter mathematically of course
noncomputable def fderivCLM :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E →L[ℝ] F) where
  toFun T :=
  { toFun f :=
    { toFun v := lineDerivCLM v T f
      map_add' := sorry
      map_smul' := sorry
      cont := have : FiniteDimensional ℝ E := inferInstance; sorry }
    map_add' := sorry
    map_smul' := sorry
    cont := sorry }
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

end fderiv

section iteratedFDeriv

--
open Distribution ContinuousMultilinearMap
--
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
-- variable [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
--
noncomputable def iteratedFDerivCLM (i : ℕ) :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E [×i]→L[ℝ] F) :=
  sorry -- fails to find a `Module ℝ (ContinuousMultilinearMap ℝ (fun i ↦ E) F)` instance; was
  -- Nat.recOn i
  --   (mapCLM (continuousMultilinearCurryFin0 ℝ E F).symm)
  --   fun j rec ↦
  --     letI C : (E →L[ℝ] E [×j]→L[ℝ] F) →L[ℝ] (E [×(j+1)]→L[ℝ] F) :=
  --       (continuousMultilinearCurryLeftEquiv ℝ (fun (_ : Fin j.succ) ↦ E) F).symm
  --     (mapCLM C) ∘L fderivCLM ∘L rec
--
-- TODO: write lemmas for this...
--

end iteratedFDeriv

end Distribution
