/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Luigi Massacci
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.Sets.Compacts

/-!
# Continuously differentiable functions supported in a given compact set

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with support contained in a given compact set.

Given `n : ℕ∞` and a compact subset `K` of a normed space `E`, we consider the type of bundled
functions `f : E → F` (where `F` is a normed vector space) such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` vanishes outside of a compact set: `EqOn f 0 Kᶜ`.

The main reason this exists as a bundled type is to be endowed with its natural locally convex
topology (namely, uniform convergence of `f` and its derivatives up to order `n`).
Taking the locally convex inductive limit of these as `K` varies yields the natural topology on test
functions, used to define distributions. While most of distribution theory cares only about `C^∞`
functions, we also want to endow the space of `C^n` test functions with its natural topology.
Indeed, distributions of order less than `n` are precisely those which extend continuously to this
larger space of test functions.

## Main definitions

- `ContDiffMapSupportedIn E F n K`: the type of bundled `n`-times continuously differentiable
  functions `E → F` which vanish outside of `K`.
- `ContDiffMapSupportedIn.iteratedFDerivWithOrderLM`: wrapper, as a `𝕜`-linear map, for
  `iteratedFDeriv` from `ContDiffMapSupportedIn E F n K` to
  `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) k K`.
- `ContDiffMapSupportedIn.iteratedFDerivLM`: specialization of the above, giving a `𝕜`-linear map
  from `ContDiffMapSupportedIn E F ⊤ K` to `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) ⊤ K`.
- `ContDiffMapSupportedIn.topologicalSpace`, `ContDiffMapSupportedIn.uniformSpace`: the topology
  and uniform structures on `𝓓^{n}_{K}(E, F)`, given by uniform convergence of the functions and
  all their derivatives up to order `n`.

## Main statements

- `ContDiffMapSupportedIn.isTopologicalAddGroup`, `ContDiffMapSupportedIn.continuousSMul` and
  `ContDiffMapSupportedIn.instLocallyConvexSpace`: `𝓓^{n}_{K}(E, F)` is a locally convex
  topological vector space.

## Notation

In the `Distributions` scope, we introduce the following notations:
- `𝓓^{n}_{K}(E, F)`: the space of `n`-times continuously differentiable functions `E → F`
  which vanish outside of `K`.
- `𝓓_{K}(E, F)`: the space of smooth (infinitely differentiable) functions `E → F`
  which vanish outside of `K`, i.e. `𝓓^{⊤}_{K}(E, F)`.
- `N[𝕜; F]_{K, n, i}` (or simply `N[𝕜]_{K, n, i}`): the `𝕜`-seminorm on `𝓓^{n}_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.
- `N[𝕜; F]_{K, i}` (or simply `N[𝕜]_{K, i}`): the `𝕜`-seminorm on `𝓓_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.

## Implementation details

* The technical choice of spelling `EqOn f 0 Kᶜ` in the definition, as opposed to `tsupport f ⊆ K`
  is to make rewriting `f x` to `0` easier when `x ∉ K`.
* Since the most common case is by far the smooth case, we often reserve the "expected" name
  of a result/definition to this case, and add `WithOrder` to the declaration applying to
  any regularity.
* In `iteratedFDerivWithOrderLM`, we define the `i`-th iterated differentiation operator as
  a map from `𝓓^{n}_{K}` to `𝓓^{k}_{K}` without imposing relations on `n`, `k` and `i`. Of course
  this is defined as `0` if `k + i > n`. This creates some verbosity as all of these variables are
  explicit, but it allows the most flexibility while avoiding DTT hell.

## Tags

distributions
-/

@[expose] public section

open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal ContDiff

variable (𝕜 E F F' : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
  {n k : ℕ∞} {K : Compacts E}

/-- The type of bundled `n`-times continuously differentiable maps which vanish outside of a fixed
compact set `K`. -/
structure ContDiffMapSupportedIn (n : ℕ∞) (K : Compacts E) : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected zero_on_compl' : EqOn toFun 0 Kᶜ

/-- Notation for the space of bundled `n`-times continuously differentiable
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓^{" n "}_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F n K

/-- Notation for the space of bundled smooth (infinitely differentiable)
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F ⊤ K

open Distributions

/-- `ContDiffMapSupportedInClass B E F n K` states that `B` is a type of bundled `n`-times
continuously differentiable functions with support in the compact set `K`. -/
class ContDiffMapSupportedInClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

namespace ContDiffMapSupportedInClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    have := HasCompactSupport.intro K.isCompact (map_zero_on_compl f)
    rcases (map_continuous f).bounded_above_of_compact_support this with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end ContDiffMapSupportedInClass

namespace ContDiffMapSupportedIn

instance toContDiffMapSupportedInClass :
    ContDiffMapSupportedInClass 𝓓^{n}_{K}(E, F) E F n K where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

variable {E F F'}

protected theorem contDiff (f : 𝓓^{n}_{K}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem zero_on_compl (f : 𝓓^{n}_{K}(E, F)) : EqOn f 0 Kᶜ := map_zero_on_compl f
protected theorem compact_supp (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  .intro K.isCompact (map_zero_on_compl f)

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}_{K}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.coe (f : 𝓓^{n}_{K}(E, F)) : E → F := f

initialize_simps_projections ContDiffMapSupportedIn (toFun → coe, as_prefix coe)

@[ext]
theorem ext {f g : 𝓓^{n}_{K}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `ContDiffMapSupportedIn` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}_{K}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
theorem coe_copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
   (f : BoundedContinuousFunction E F) = (f : E → F) := rfl

section AddCommGroup

@[simps -fullyApplied]
instance : Zero 𝓓^{n}_{K}(E, F) where
  zero := .mk 0 contDiff_zero_fun fun _ _ ↦ rfl

@[simps -fullyApplied]
instance : Add 𝓓^{n}_{K}(E, F) where
  add f g := .mk (f + g) (f.contDiff.add g.contDiff) <| by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

@[simps -fullyApplied]
instance : Neg 𝓓^{n}_{K}(E, F) where
  neg f := .mk (-f) (f.contDiff.neg) <| by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

@[simps -fullyApplied]
instance instSub : Sub 𝓓^{n}_{K}(E, F) where
  sub f g := .mk (f - g) (f.contDiff.sub g.contDiff) <| by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

@[simps -fullyApplied]
instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}_{K}(E, F) where
  smul c f := .mk (c • (f : E → F)) (f.contDiff.const_smul c) <| by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left

instance : AddCommGroup 𝓓^{n}_{K}(E, F) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

variable (E F K n)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓓^{n}_{K}(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F n K : 𝓓^{n}_{K}(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F n K) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module

instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}_{K}(E, F) := fast_instance%
  (coeHom_injective n K).module R (coeHom E F n K) fun _ _ ↦ rfl

end Module

protected theorem support_subset (f : 𝓓^{n}_{K}(E, F)) : support f ⊆ K :=
  support_subset_iff'.mpr f.zero_on_compl

protected theorem tsupport_subset (f : 𝓓^{n}_{K}(E, F)) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.isCompact.isClosed

protected theorem hasCompactSupport (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  HasCompactSupport.intro K.isCompact f.zero_on_compl

/-- Inclusion of unbundled `n`-times continuously differentiable function with support included
in a compact `K` into the space `𝓓^{n}_{K}`. -/
@[simps]
protected def of_support_subset {f : E → F} (hf : ContDiff ℝ n f) (hsupp : support f ⊆ K) :
    𝓓^{n}_{K}(E, F) where
  toFun := f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp

protected theorem bounded_iteratedFDeriv (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} (hi : i ≤ n) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)

protected theorem iteratedFDeriv_zero_on_compl (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} :
    EqOn (iteratedFDeriv ℝ i f) 0 Kᶜ := by
  intro x (hx : x ∉ K)
  contrapose! hx
  exact f.tsupport_subset (support_iteratedFDeriv_subset i hx)

/-- Inclusion of `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous maps
as a `𝕜`-linear map.

This is subsumed by `toBoundedContinuousFunctionCLM`, which also bundles the continuity. -/
noncomputable def toBoundedContinuousFunctionLM : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma toBoundedContinuousFunctionLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionLM 𝕜 f = f :=
  rfl

lemma toBoundedContinuousFunctionLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionLM 𝕜' :=
  rfl

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompLM T` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)`
to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`.

This is subsumed by `postcompCLM T`, which also bundles the continuity. -/
noncomputable def postcompLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}_{K}(E, F') where
  toFun f := ⟨T ∘ f, T.restrictScalars ℝ |>.contDiff.comp f.contDiff,
    fun x hx ↦ by simp [f.zero_on_compl hx]⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]
lemma postcompLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompLM T f = T ∘ f :=
  rfl

variable (n k) in
/-- `iteratedFDerivWithOrderLM 𝕜 n k i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its `i`-th iterated derivative as an element of `𝓓^{k}_{K}(E, E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `k + i ≤ n`, otherwise we define it as the zero map.

See `iteratedFDerivLM` for the very common case where everything is infinitely differentiable.

This is subsumed by `iteratedFDerivWithOrderCLM` (not yet in Mathlib), which also bundles the
continuity. -/
noncomputable def iteratedFDerivWithOrderLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{k}_{K}(E, E [×i]→L[ℝ] F) where
  /-
  Note: it is tempting to define this as some linear map if `k + i ≤ n`,
  and the zero map otherwise. However, we would lose the definitional equality between
  `iteratedFDerivWithOrderLM 𝕜 n k i f` and `iteratedFDerivWithOrderLM ℝ n k i f`.

  This is caused by the fact that the equality `f (if p then x else y) = if p then f x else f y`
  is not definitional.
  -/
  toFun f :=
    if hi : k + i ≤ n then
      .of_support_subset
        (f.contDiff.iteratedFDeriv_right <| mod_cast hi)
        ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hi
    · have hi' : (i : ℕ∞ω) ≤ n := mod_cast (le_of_add_le_right hi)
      ext
      simp [iteratedFDeriv_add (f.contDiff.of_le hi') (g.contDiff.of_le hi')]
    · simp
  map_smul' c f := by
    split_ifs with hi
    · have hi' : (i : ℕ∞ω) ≤ n := mod_cast (le_of_add_le_right hi)
      ext
      simp [iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi').contDiffAt]
    · simp

@[simp]
lemma iteratedFDerivWithOrderLM_apply {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivWithOrderLM 𝕜 n k i f = if k + i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDerivWithOrderLM]
  split_ifs <;> rfl

lemma iteratedFDerivWithOrderLM_apply_of_le {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) (hin : k + i ≤ n) :
    iteratedFDerivWithOrderLM 𝕜 n k i f = iteratedFDeriv ℝ i f := by
  simp [hin]

lemma iteratedFDerivWithOrderLM_apply_of_gt {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) (hin : ¬ (k + i ≤ n)) :
    iteratedFDerivWithOrderLM 𝕜 n k i f = 0 := by
  ext : 1
  simp [hin]

lemma iteratedFDerivWithOrderLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (iteratedFDerivWithOrderLM 𝕜 n k i : 𝓓^{n}_{K}(E, F) → _)
      = iteratedFDerivWithOrderLM 𝕜' n k i :=
  rfl

/-- `iteratedFDerivLM 𝕜 i` is the `𝕜`-linear-map sending `f : 𝓓_{K}(E, F)` to
its `i`-th iterated derivative as an element of `𝓓_{K}(E, E [×i]→L[ℝ] F)`.

See also `iteratedFDerivWithOrderLM` if you need more control on the regularities.

This is subsumed by `iteratedFDerivCLM` (not yet in Mathlib), which also bundles the
continuity. -/
noncomputable def iteratedFDerivLM (i : ℕ) :
    𝓓_{K}(E, F) →ₗ[𝕜] 𝓓_{K}(E, E [×i]→L[ℝ] F) where
  toFun f := .of_support_subset
    (f.contDiff.iteratedFDeriv_right le_rfl)
    ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
  map_add' f g := by
    have hi : (i : ℕ∞ω) ≤ ∞ := mod_cast le_top
    ext
    simp [iteratedFDeriv_add (f.contDiff.of_le hi) (g.contDiff.of_le hi)]
  map_smul' c f := by
    have hi : (i : ℕ∞ω) ≤ ∞ := mod_cast le_top
    ext
    simp [iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi).contDiffAt]

@[simp]
lemma iteratedFDerivLM_apply {i : ℕ} (f : 𝓓_{K}(E, F)) :
    iteratedFDerivLM 𝕜 i f = iteratedFDeriv ℝ i f :=
  rfl

/-- Note: this turns out to be a definitional equality thanks to decidablity of the order
on `ℕ∞`. This means we could have *defined* `iteratedFDerivLM` this way, but we avoid it
to make sure that `if`s won't appear in the smooth case. -/
lemma iteratedFDerivLM_eq_withOrder (i : ℕ) :
    (iteratedFDerivLM 𝕜 i : 𝓓_{K}(E, F) →ₗ[𝕜] _) = iteratedFDerivWithOrderLM 𝕜 ⊤ ⊤ i :=
  rfl

lemma iteratedFDerivLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (iteratedFDerivLM 𝕜 i : 𝓓_{K}(E, F) → _) = iteratedFDerivLM 𝕜' i :=
  rfl

variable (n) in
/-- `structureMapLM 𝕜 n i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`. In other words, it
is the composition of `toBoundedContinuousFunctionLM 𝕜` and `iteratedFDerivWithOrderLM 𝕜 n 0 i`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zero map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`.

This is subsumed by `structureMapCLM`, which also bundles the
continuity. -/
noncomputable def structureMapLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  toBoundedContinuousFunctionLM 𝕜 ∘ₗ iteratedFDerivWithOrderLM 𝕜 n 0 i

lemma structureMapLM_eq {i : ℕ} :
    (structureMapLM 𝕜 ⊤ i : 𝓓_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F)) =
      (toBoundedContinuousFunctionLM 𝕜 : 𝓓_{K}(E, E [×i]→L[ℝ] F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F)) ∘ₗ
      (iteratedFDerivLM 𝕜 i : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓓_{K}(E, E [×i]→L[ℝ] F)) :=
  rfl

lemma structureMapLM_apply_withOrder {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    structureMapLM 𝕜 n i f = if i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  simp [structureMapLM]

lemma structureMapLM_apply {i : ℕ} (f : 𝓓_{K}(E, F)) :
    structureMapLM 𝕜 ⊤ i f = iteratedFDeriv ℝ i f := by
  simp [structureMapLM_eq]

lemma structureMapLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (structureMapLM 𝕜 n i : 𝓓^{n}_{K}(E, F) → _) = structureMapLM 𝕜' n i :=
  rfl

lemma structureMapLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapLM 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 ℝ E (f x) := by
  ext
  simp [structureMapLM_apply_withOrder, iteratedFDeriv_zero_eq_comp]

lemma structureMapLM_zero_injective :
    Injective (structureMapLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) → E →ᵇ E [×0]→L[ℝ] F) := by
  intro f g hfg
  simpa [BoundedContinuousFunction.ext_iff, ContinuousMultilinearMap.ext_iff,
    structureMapLM_zero_apply, ContDiffMapSupportedIn.ext_iff] using hfg

section Topology

noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : ℕ), induced (structureMapLM ℝ n i) inferInstance

noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (structureMapLM ℝ n i) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : ℕ), UniformSpace.comap (structureMapLM ℝ n i) inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance isTopologicalAddGroup : IsTopologicalAddGroup 𝓓^{n}_{K}(E, F) :=
  topologicalAddGroup_iInf fun _ ↦ topologicalAddGroup_induced _

instance isUniformAddGroup : IsUniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ ↦ IsUniformAddGroup.comap _

instance continuousSMul : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) :=
  continuousSMul_iInf fun i ↦ continuousSMul_induced (structureMapLM 𝕜 n i)

instance locallyConvexSpace : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _

variable (n) in
/-- `structureMapCLM 𝕜 n i` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zero map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`. -/
noncomputable def structureMapCLM (i : ℕ) :
    𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ (E [×i]→L[ℝ] F) where
  toLinearMap := structureMapLM 𝕜 n i
  cont := continuous_iInf_dom continuous_induced_dom

@[simp]
lemma structureMapCLM_apply_withOrder {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    structureMapCLM 𝕜 n i f = if i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  simp [structureMapCLM, structureMapLM_apply_withOrder]

lemma structureMapCLM_apply {i : ℕ} (f : 𝓓_{K}(E, F)) :
    structureMapCLM 𝕜 ⊤ i f = iteratedFDeriv ℝ i f := by
  simp [structureMapCLM, structureMapLM_apply]

lemma structureMapCLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (structureMapCLM 𝕜 n i : 𝓓^{n}_{K}(E, F) → _) = structureMapCLM 𝕜' n i :=
  rfl

lemma structureMapCLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapCLM 𝕜 n 0 f x = ContinuousMultilinearMap.uncurry0 ℝ E (f x) :=
  structureMapLM_zero_apply 𝕜

lemma structureMapCLM_zero_injective :
    Injective (structureMapCLM 𝕜 n 0 : 𝓓^{n}_{K}(E, F) → E →ᵇ E [×0]→L[ℝ] F) :=
  structureMapLM_zero_injective 𝕜

lemma isUniformEmbedding_pi_structureMapCLM :
    IsUniformEmbedding (ContinuousLinearMap.pi (structureMapCLM 𝕜 n) :
      𝓓^{n}_{K}(E, F) →L[𝕜] Π i, E →ᵇ (E [×i]→L[ℝ] F)) where
  injective f g hfg := structureMapCLM_zero_injective 𝕜 (congr($hfg 0))
  toIsUniformInducing := by
    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
    rfl

/-- The **universal property** of the topology on `𝓓^{n}_{K}(E, F)`: a map to `𝓓^{n}_{K}(E, F)`
is continuous if and only if its composition with each structure map
`structureMapCLM ℝ n i : 𝓓^{n}_{K}(E, F) → (E →ᵇ (E [×i]→L[ℝ] F))` is continuous.

Since `structureMapCLM ℝ n i` is zero whenever `i > n`, it suffices to check it for `i ≤ n`,
as proven by `continuous_iff_comp_withOrder`. -/
-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
theorem continuous_iff_comp {X} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ i, Continuous (structureMapCLM ℝ n i ∘ φ) := by
  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM]

/-- The **universal property** of the topology on `𝓓^{n}_{K}(E, F)`: a map to `𝓓^{n}_{K}(E, F)`
is continuous if and only if its composition with the structure map
`structureMapCLM ℝ n i : 𝓓^{n}_{K}(E, F) → (E →ᵇ (E [×i]→L[ℝ] F))` is continuous for each
`i ≤ n`. -/
-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
theorem continuous_iff_comp_withOrder {X : Type*} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ (i : ℕ), i ≤ n → Continuous (structureMapCLM ℝ n i ∘ φ) := by
  rw [continuous_iff_comp]
  congrm (∀ i, ?_)
  by_cases hin : i ≤ n <;> simp only [hin, true_imp_iff, false_imp_iff, iff_true]
  refine continuous_zero.congr fun x ↦ ?_
  ext t : 1
  simp [hin, structureMapCLM_apply_withOrder]

variable (E F n K)

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by the sup norm of the iterated derivatives.
In the scope `Distributions.Seminorm`, we denote them by `N[𝕜; F]_{K, n, i}`
(or `N[𝕜]_{K, n, i}`), or simply by `N[𝕜; F]_{K, i}` (or `N[𝕜; F]_{K, i}`) when `n = ∞`. -/
protected noncomputable def seminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i)

-- Note: If these end up conflicting with other seminorms (e.g `SchwartzMap.seminorm`),
-- we may want to put them in a more specific scope.
@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "]_{" K ", " n ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ _ n K i

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "]_{" K ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K i

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "; " F "]_{" K ", " n ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ F n K i

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "; " F "]_{" K ", " i "}" =>
  ContDiffMapSupportedIn.seminorm 𝕜 _ F ⊤ K i

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup of the
`ContDiffMapSupportedIn.seminorm k`for `k ≤ i`. -/
protected noncomputable def supSeminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)

protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K) := by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

protected theorem withSeminorms' :
    WithSeminorms (ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K) :=
  (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups

variable {E F n K}

protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f = ‖structureMapCLM 𝕜 n i f‖ :=
  rfl

protected theorem seminorm_eq_bot_of_gt {i : ℕ} (hin : n < i) :
    N[𝕜; F]_{K, n, i} = ⊥ := by
  have : ¬(i ≤ n) := by simpa using hin
  ext f
  simp [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.ext_iff,
    structureMapCLM_apply_withOrder, this]

protected theorem seminorm_le_iff_withOrder {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f ≤ C ↔ (i ≤ n → ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C) := by
  have : (∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C) ↔ (∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C) := by
    congrm ∀ x, ?_
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, f.iteratedFDeriv_zero_on_compl hx, hC]
  by_cases hi : i ≤ n
  · simp [hi, forall_const, ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply_withOrder,
      BoundedContinuousFunction.norm_le hC, this]
  · push_neg at hi
    simp [hi, ContDiffMapSupportedIn.seminorm_eq_bot_of_gt _ hi, hC]

protected theorem seminorm_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} f ≤ C ↔ ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  simp_rw [ContDiffMapSupportedIn.seminorm_le_iff_withOrder 𝕜 hC, le_top, forall_const]

theorem norm_iteratedFDeriv_apply_le_seminorm_withOrder {i : ℕ} (hin : i ≤ n)
    {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv ℝ i f x‖ ≤ N[𝕜]_{K, n, i} f :=
  calc
      ‖iteratedFDeriv ℝ i f x‖
  _ = ‖structureMapLM ℝ n i f x‖ := by simp [structureMapLM_apply_withOrder, hin]
  _ ≤ ‖structureMapLM ℝ n i f‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
  _ = N[𝕜]_{K, n, i} f := rfl

theorem norm_iteratedFDeriv_apply_le_seminorm {i : ℕ}
    {f : 𝓓_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv ℝ i f x‖ ≤ N[𝕜]_{K, i} f :=
  norm_iteratedFDeriv_apply_le_seminorm_withOrder 𝕜 (mod_cast le_top)

theorem norm_apply_le_seminorm {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖f x‖ ≤ N[𝕜]_{K, n, 0} f := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := x)]
  exact norm_iteratedFDeriv_apply_le_seminorm_withOrder 𝕜 (zero_le _)

theorem norm_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    ‖(f : E →ᵇ F)‖ = N[𝕜]_{K, n, 0} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContDiffMapSupportedIn.seminorm_apply, structureMapCLM_apply_withOrder]

/-- The inclusion of the space `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F where
  toLinearMap := toBoundedContinuousFunctionLM 𝕜
  cont := show Continuous (toBoundedContinuousFunctionLM 𝕜) by
    refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{0}, 1, fun f ↦ ?_⟩)
    simp [norm_toBoundedContinuousFunction 𝕜 f]

@[simp]
lemma toBoundedContinuousFunctionCLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionCLM 𝕜 f = f :=
  rfl

lemma toBoundedContinuousFunctionCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl

instance : T3Space 𝓓^{n}_{K}(E, F) :=
  have : Injective (toBoundedContinuousFunctionCLM ℝ : 𝓓^{n}_{K}(E, F) →L[ℝ] E →ᵇ F) :=
    fun _ _ hfg ↦ ext fun x ↦ congr(($hfg : E → F) x)
  have : T2Space 𝓓^{n}_{K}(E, F) := .of_injective_continuous this
    (toBoundedContinuousFunctionCLM ℝ).continuous
  inferInstance

theorem seminorm_postcompLM_le [LinearMap.CompatibleSMul F F' ℝ 𝕜] {i : ℕ} (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} (postcompLM T f) ≤ ‖T‖ * N[𝕜]_{K, n, i} f := by
  set T' := T.restrictScalars ℝ
  change N[ℝ]_{K, n, i} (postcompLM T' f) ≤ ‖T'‖ * N[ℝ]_{K, n, i} f
  rw [ContDiffMapSupportedIn.seminorm_le_iff_withOrder ℝ (by positivity)]
  intro hi x hx
  rw [postcompLM_apply]
  calc
      ‖iteratedFDeriv ℝ i (T' ∘ f) x‖
  _ = ‖T'.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖ := by
        rw [T'.iteratedFDeriv_comp_left f.contDiff.contDiffAt (mod_cast hi)]
  _ ≤ ‖T'‖ * ‖iteratedFDeriv ℝ i f x‖ := T'.norm_compContinuousMultilinearMap_le _
  _ ≤ ‖T'‖ * N[ℝ]_{K, n, i} f := by grw [norm_iteratedFDeriv_apply_le_seminorm_withOrder ℝ hi]

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}_{K}(E, F)` to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`. -/
noncomputable def postcompCLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}_{K}(E, F') where
  toLinearMap := postcompLM T
  cont := show Continuous (postcompLM T) by
    refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _ (fun i ↦ ⟨{i}, ‖T‖₊, fun f ↦ ?_⟩)
    simpa [NNReal.smul_def] using seminorm_postcompLM_le 𝕜 T f

@[simp]
lemma postcompCLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

end Topology

end ContDiffMapSupportedIn
