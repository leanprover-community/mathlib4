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

- `𝓓^{n}_{K}(E, F)`:  the space of `n`-times continuously differentiable functions `E → F`
  which vanish outside of `K`.
- `𝓓_{K}(E, F)`:  the space of smooth (infinitely differentiable) functions `E → F`
  which vanish outside of `K`, i.e. `𝓓^{⊤}_{K}(E, F)`.

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

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
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
scoped[Distributions] notation "𝓓^{" n "}_{"K"}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F n K

/-- Notation for the space of bundled smooth (infinitely differentiable)
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓_{"K"}(" E ", " F ")" =>
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

variable {E F}

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

/-- Inclusion of `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous maps
as a `𝕜`-linear map.

This is subsumed by `toBoundedContinuousFunctionCLM` (not yet in Mathlib), which also bundles the
continuity. -/
@[simps -fullyApplied]
noncomputable def toBoundedContinuousFunctionLM : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- Workaround for simps' automatic name generation: manually specifying names is not supported yet.
alias toBoundedContinuousFunctionLM_apply := toBoundedContinuousFunctionLM_apply_apply

lemma toBoundedContinuousFunctionLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionLM 𝕜' :=
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
        (f.contDiff.iteratedFDeriv_right <| by exact_mod_cast hi)
        ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
    else 0
  map_add' f g := by
    split_ifs with hi
    · have hi' : (i : WithTop ℕ∞) ≤ n := by exact_mod_cast le_of_add_le_right hi
      ext
      simp [iteratedFDeriv_add (f.contDiff.of_le hi') (g.contDiff.of_le hi')]
    · simp
  map_smul' c f := by
    split_ifs with hi
    · have hi' : (i : WithTop ℕ∞) ≤ n := by exact_mod_cast le_of_add_le_right hi
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
    have hi : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    ext
    simp [iteratedFDeriv_add (f.contDiff.of_le hi) (g.contDiff.of_le hi)]
  map_smul' c f := by
    have hi : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
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

end Topology

end ContDiffMapSupportedIn
