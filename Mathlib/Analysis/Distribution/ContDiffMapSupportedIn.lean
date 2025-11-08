/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Luigi Massacci
-/

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Sets.Compacts

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
- `ContDiffMapSupportedIn.iteratedFDerivWithOrderₗ`: wrapper, as a `𝕜`-linear map, for
  `iteratedFDeriv` from `ContDiffMapSupportedIn E F n K` to
  `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) k K`.
- `ContDiffMapSupportedIn.iteratedFDerivₗ`: specialization of the above, giving a `𝕜`-linear map
  from `ContDiffMapSupportedIn E F ⊤ K` to `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) ⊤ K`.

## Main statements

TODO:
- `ContDiffMapSupportedIn.instIsUniformAddGroup` and
  `ContDiffMapSupportedIn.instLocallyConvexSpace`: `ContDiffMapSupportedIn` is a locally convex
  topological vector space.

## Notation

- `𝓓^{n}_{K}(E, F)`:  the space of `n`-times continuously differentiable functions `E → F`
  which vanish outside of `K`.
- `𝓓_{K}(E, F)`:  the space of smooth (infinitely differentiable) functions `E → F`
  which vanish outside of `K`, i.e. `𝓓^{⊤}_{K}(E, F)`.

## Implementation details

The technical choice of spelling `EqOn f 0 Kᶜ` in the definition, as opposed to `tsupport f ⊆ K`
is to make rewriting `f x` to `0` easier when `x ∉ K`.

## Tags

distributions
-/

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
theorem toBoundedContinuousFunction_apply (f : 𝓓^{n}_{K}(E, F)) (x : E) :
   (f : BoundedContinuousFunction E F) x = (f x) := rfl

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
as a `𝕜`-linear map. -/
@[simps]
noncomputable def toBoundedContinuousFunctionₗ : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (n k) in
/-- `iteratedFDerivWithOrderₗ 𝕜 n k i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its `i`-th iterated derivative as an element of `𝓓^{k}_{K}(E, E [×i]→L[ℝ] F)`.
This only makes mathematical sense if `k + i ≤ n`, otherwise we define it as the zero map.

See `iteratedFDerivₗ` for the very common case where everything is infinitely differentiable. -/
noncomputable def iteratedFDerivWithOrderₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{k}_{K}(E, E [×i]→L[ℝ] F) where
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
lemma coe_iteratedFDerivWithOrderₗ {i : ℕ} (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivWithOrderₗ 𝕜 n k i f = if k + i ≤ n then iteratedFDeriv ℝ i f else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDerivWithOrderₗ]
  split_ifs <;> rfl

lemma coe_iteratedFDerivWithOrderₗ_of_le {i : ℕ} (hin : k + i ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivWithOrderₗ 𝕜 n k i f = iteratedFDeriv ℝ i f := by
  simp [hin]

lemma coe_iteratedFDerivWithOrderₗ_of_gt {i : ℕ} (hin : ¬ (k + i ≤ n)) (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivWithOrderₗ 𝕜 n k i f = 0 := by
  ext : 1
  simp [hin]

/-- `iteratedFDerivₗ 𝕜 i` is the `𝕜`-linear-map sending `f : 𝓓_{K}(E, F)` to
its `i`-th iterated derivative as an element of `𝓓_{K}(E, E [×i]→L[ℝ] F)`.

See also `iteratedFDerivWithOrderₗ` if you need more control on the regularities. -/
noncomputable def iteratedFDerivₗ (i : ℕ) :
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
lemma coe_iteratedFDerivₗ {i : ℕ} (f : 𝓓_{K}(E, F)) :
    iteratedFDerivₗ 𝕜 i f = iteratedFDeriv ℝ i f :=
  rfl

lemma iteratedFDerivₗ_eq_withOrder (i : ℕ) :
    (iteratedFDerivₗ 𝕜 i : 𝓓_{K}(E, F) → _) = iteratedFDerivWithOrderₗ 𝕜 ⊤ ⊤ i :=
  rfl

variable (n) in
/-- `structureMapₗ 𝕜 n i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`. In other words, it
is the composition of `toBoundedContinuousFunctionₗ 𝕜` and `iteratedFDerivWithOrderₗ 𝕜 n 0 i`.
This only makes mathematical sense if `i ≤ n`, otherwise we define it as the zero map.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`. -/
noncomputable def structureMapₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  toBoundedContinuousFunctionₗ 𝕜 ∘ₗ iteratedFDerivWithOrderₗ 𝕜 n 0 i

end ContDiffMapSupportedIn
