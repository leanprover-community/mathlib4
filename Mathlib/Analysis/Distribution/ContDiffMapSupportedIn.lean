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
topology (namely, uniform convergence of `f` and its derivative up to order `n`).
Taking the locally convex inductive limit of these as `K` varies yields the natural topology on test
functions, used to define distributions. While most of distribution theory cares only about `C^∞`
functions, we also want to endow the space of `C^n` test functions with its natural topology.
Indeed, distributions of order less than `n` are precisely those which extend continuously to this
larger space of test functions.

## Main definitions

- `ContDiffMapSupportedIn E F n K`: the type of bundled `n`-times continuously differentiable
  functions `E → F` which vanish outside of `K`.
- `ContDiffMapSupportedIn.iteratedFDerivWithOrderₗ`: wrapper as a `𝕜`-linear maps for
  `iteratedFDeriv` on `ContDiffMapSupportedIn E F n K`, as a map into
  `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) (n-i) K`.

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
open scoped BoundedContinuousFunction Topology NNReal

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {n : ℕ∞} {K : Compacts E}

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

/-- Notation for the space of bundled smooth (inifinitely differentiable)
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓_{"K"}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F ⊤ K

open Distributions

/-- `ContDiffMapSupportedInClass B E F n K` states that `B` is a type of bundled `n`-times
continously differentiable functions with support in the compact set `K`. -/
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
def Simps.apply (f : 𝓓^{n}_{K}(E, F)) : E → F := f

initialize_simps_projections ContDiffMapSupportedIn (toFun → apply)

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
   (f : BoundedContinuousFunction E F) x  = (f x) := rfl

section AddCommGroup

instance : Zero 𝓓^{n}_{K}(E, F) where
  zero := ContDiffMapSupportedIn.mk 0 contDiff_zero_fun fun _ _ ↦ rfl

@[simp]
lemma coe_zero : (0 : 𝓓^{n}_{K}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}_{K}(E, F)) x = 0 :=
  rfl

instance : Add 𝓓^{n}_{K}(E, F) where
  add f g := ContDiffMapSupportedIn.mk (f + g) (f.contDiff.add g.contDiff) <| by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

@[simp]
lemma coe_add (f g : 𝓓^{n}_{K}(E, F)) : (f + g : 𝓓^{n}_{K}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}_{K}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

instance : Neg 𝓓^{n}_{K}(E, F) where
  neg f := ContDiffMapSupportedIn.mk (-f) (f.contDiff.neg) <| by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

instance instSub : Sub 𝓓^{n}_{K}(E, F) where
  sub f g := ContDiffMapSupportedIn.mk (f - g) (f.contDiff.sub g.contDiff) <| by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}_{K}(E, F) where
  smul c f := ContDiffMapSupportedIn.mk (c • (f : E → F)) (f.contDiff.const_smul c) <| by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{K}(E, F)) : (c • f : 𝓓^{n}_{K}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{K}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl

instance : AddCommGroup 𝓓^{n}_{K}(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

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
    Module R 𝓓^{n}_{K}(E, F) :=
  (coeHom_injective n K).module R (coeHom E F n K) fun _ _ => rfl

end Module

protected theorem support_subset (f : 𝓓^{n}_{K}(E, F)) : support f ⊆ K :=
  support_subset_iff'.mpr f.zero_on_compl

protected theorem tsupport_subset (f : 𝓓^{n}_{K}(E, F)) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.isCompact.isClosed

protected theorem hasCompactSupport (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  HasCompactSupport.intro K.isCompact f.zero_on_compl

/-- Inclusion of unbundled `n`-times continuously differentiable function with support included
in a compact `K` into the space `𝓓^{n}_{K}`. -/
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
noncomputable def toBoundedContinuousFunctionₗ : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Wrapper for `iteratedFDeriv i` on `𝓓^{n}_{K}(E, F)`,
as a map into `𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F)`. -/
noncomputable def iteratedFDerivWithOrder (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) :=
  if hi : i ≤ n then
    .of_support_subset
    (f.contDiff.iteratedFDeriv_right <| (WithTop.coe_le_coe.mpr ((tsub_add_cancel_of_le hi).le)))
    ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
  else 0

@[simp]
lemma iteratedFDerivWithOrder_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.iteratedFDerivWithOrder i x = if i ≤ n then iteratedFDeriv ℝ i f x else 0 := by
  rw [ContDiffMapSupportedIn.iteratedFDerivWithOrder]
  split_ifs <;> rfl

@[simp]
lemma coe_iteratedFDerivWithOrder_of_le {i : ℕ} (hin : i ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    f.iteratedFDerivWithOrder i = iteratedFDeriv ℝ i f := by
  ext : 1
  rw [iteratedFDerivWithOrder_apply]
  exact dif_pos hin

@[simp]
lemma coe_iteratedFDerivWithOrder_of_gt {i : ℕ} (hin : i > n) (f : 𝓓^{n}_{K}(E, F)) :
    f.iteratedFDerivWithOrder i = 0 := by
  ext : 1
  rw [iteratedFDerivWithOrder_apply]
  exact dif_neg (not_le_of_gt hin)

@[simp]
lemma coe_iteratedFDerivWithOrder_of_gt' {i : ℕ} (hin : i > n) :
    (iteratedFDerivWithOrder i : 𝓓^{n}_{K}(E, F) → _) = 0 := by
  ext : 2
  rw [iteratedFDerivWithOrder_apply]
  exact dif_neg (not_le_of_gt hin)

lemma iteratedFDerivWithOrder_add (i : ℕ) {f g : 𝓓^{n}_{K}(E, F)} :
    (f + g).iteratedFDerivWithOrder i = f.iteratedFDerivWithOrder i + g.iteratedFDerivWithOrder i
  := by
  ext : 1
  simp only [iteratedFDerivWithOrder_apply, add_apply]
  split_ifs with hin
  · refine iteratedFDeriv_add_apply (ContDiff.contDiffAt ?_) (ContDiff.contDiffAt ?_)
    · exact f.contDiff.of_le (by exact_mod_cast hin)
    · exact g.contDiff.of_le (by exact_mod_cast hin)
  · rw [add_zero]

lemma iteratedFDerivWithOrder_smul (i : ℕ) {c : 𝕜} {f : 𝓓^{n}_{K}(E, F)} :
    (c • f).iteratedFDerivWithOrder i = c • f.iteratedFDerivWithOrder i := by
  ext : 1
  simp only [iteratedFDerivWithOrder_apply, smul_apply]
  split_ifs with hin
  · apply iteratedFDeriv_const_smul_apply
    refine ContDiff.contDiffAt <| f.contDiff.of_le (by exact_mod_cast hin)
  · rw [smul_zero]

/-- Wrapper for iteratedFDerivWithOrder as a `𝕜`-linear map. -/
@[simps]
noncomputable def iteratedFDerivWithOrderₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n-i}_{K}(E, E [×i]→L[ℝ] F) where
  toFun f := f.iteratedFDerivWithOrder i
  map_add' _ _ := iteratedFDerivWithOrder_add i
  map_smul' _ _ := iteratedFDerivWithOrder_smul 𝕜 i

lemma iteratedFDerivWithOrderₗ_eq_iteratedFDerivWithOrder (i : ℕ) :
  (iteratedFDerivWithOrderₗ 𝕜 i : 𝓓^{n}_{K}(E, F) → _) = (iteratedFDerivWithOrder i : _) := by
  congr

lemma iteratedFDerivWithOrder_zero (i : ℕ) :
    (0 : 𝓓^{n}_{K}(E, F)).iteratedFDerivWithOrder i = 0 :=
  map_zero (iteratedFDerivWithOrderₗ ℝ i)

/-- The composition of `ContDiffMapSupportedIn.toBoundedContinuousFunctionₗ` and
`ContDiffMapSupportedIn.iteratedFDerivₗ`. We define this as a separate `abbrev` because this family
of maps is used a lot for defining and using the topology on `ContDiffMapSupportedIn`, and Lean
takes a long time to infer the type of `toBoundedContinuousFunctionₗ 𝕜 ∘ₗ iteratedFDerivₗ 𝕜 i`. -/
noncomputable def iteratedFDeriv_toBoundedContinuousFunctionₗ (i : ℕ) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  toBoundedContinuousFunctionₗ 𝕜 ∘ₗ iteratedFDerivWithOrderₗ 𝕜 i

section Topology

noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : ℕ), induced (iteratedFDeriv_toBoundedContinuousFunctionₗ ℝ i) inferInstance

noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : ℕ), UniformSpace.comap (iteratedFDeriv_toBoundedContinuousFunctionₗ ℝ i) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : ℕ), UniformSpace.comap (iteratedFDeriv_toBoundedContinuousFunctionₗ ℝ i)
      inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance : IsUniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  refine isUniformAddGroup_iInf (fun i ↦ ?_)
  exact IsUniformAddGroup.comap _

instance : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) := by
  refine continuousSMul_iInf
    (fun i ↦ continuousSMul_induced (iteratedFDeriv_toBoundedContinuousFunctionₗ 𝕜 i))

instance : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _

lemma continuous_iff_comp {X} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ i, Continuous (iteratedFDeriv_toBoundedContinuousFunctionₗ ℝ i ∘ φ) := by
  simp_rw [continuous_iInf_rng, continuous_induced_rng]


variable (E F n K)

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup norm on the `i`-th derivative. -/
protected noncomputable def seminorm (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (iteratedFDeriv_toBoundedContinuousFunctionₗ 𝕜 i)

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup of the
`ContDiffMapSupportedIn.seminorm k`for `k ≤ i`. -/
protected noncomputable def seminorm' (i : ℕ) : Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).sup (ContDiffMapSupportedIn.seminorm 𝕜 E F n K)

protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminorm 𝕜 E F n K) := by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : ℕ) × Fin 1) :=
    SeminormFamily.sigma fun i ↦ fun _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (iteratedFDeriv_toBoundedContinuousFunctionₗ 𝕜 i)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

protected theorem withSeminorms' :
    WithSeminorms (ContDiffMapSupportedIn.seminorm' 𝕜 E F n K) :=
  (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).partial_sups

variable {E F n K}

@[simp]
protected theorem seminorm_apply (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K i f =
      ‖(f.iteratedFDerivWithOrder i : E →ᵇ (E [×i]→L[ℝ] F))‖ :=
  rfl

protected theorem seminorm_eq_bot {i : ℕ} (hin : n < i) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n K i = ⊥ := by
  ext f
  rw [ContDiffMapSupportedIn.seminorm_apply,
      coe_iteratedFDerivWithOrder_of_gt hin]
  exact norm_zero

theorem norm_toBoundedContinuousFunctionₗ (f : 𝓓^{n}_{K}(E, F)) :
    ‖toBoundedContinuousFunctionₗ 𝕜 f‖ = ContDiffMapSupportedIn.seminorm 𝕜 E F n K 0 f := by
  simp only [BoundedContinuousFunction.norm_eq_iSup_norm, toBoundedContinuousFunctionₗ_apply_apply,
    ContDiffMapSupportedIn.seminorm_apply]
  simp only [toBoundedContinuousFunction_apply, iteratedFDerivWithOrder_apply, CharP.cast_eq_zero,
  zero_le, ↓reduceIte, norm_iteratedFDeriv_zero]

/-- The inclusion of the space `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
@[simps!]
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F :=
  { toLinearMap := toBoundedContinuousFunctionₗ 𝕜
    cont := show Continuous (toBoundedContinuousFunctionₗ 𝕜) by
      refine continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
        (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{0}, 1, fun f ↦ ?_⟩)
      simp [Seminorm.comp_apply, coe_normSeminorm, norm_toBoundedContinuousFunctionₗ,
        one_smul, Finset.sup_singleton] }

protected theorem continuous_iff {X : Type*} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ (i : ℕ) (_ : ↑i ≤ n), Continuous
      (toBoundedContinuousFunctionₗ 𝕜 ∘ ContDiffMapSupportedIn.iteratedFDerivWithOrder i ∘ φ) := by
  simp_rw [continuous_iInf_rng, continuous_induced_rng]
  constructor <;> intro H i
  · exact fun _ ↦ H i
  · by_cases hin : i ≤ n
    · exact H i hin
    · simp [iteratedFDeriv_toBoundedContinuousFunctionₗ,
        iteratedFDerivWithOrderₗ_eq_iteratedFDerivWithOrder,
        coe_iteratedFDerivWithOrder_of_gt' (lt_of_not_ge hin), continuous_zero]

end Topology

section fderiv

open Distributions

/-- Wrapper for `fderiv` on `𝓓^{n}_{K}(E, F)`, as a map into `𝓓^{n-1}_{K}(E, E →L[ℝ] F)` -/
protected noncomputable def fderivWithOrder (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n-1}_{K}(E, E →L[ℝ] F) :=
  if hn : n = 0 then 0 else
    .of_support_subset
    (f.contDiff.fderiv_right <|
    (by exact_mod_cast (tsub_add_cancel_of_le <| ENat.one_le_iff_ne_zero.mpr hn).le))
    ((support_fderiv_subset ℝ).trans f.tsupport_subset)

@[simp]
lemma fderivWithOrder_apply (f : 𝓓^{n}_{K}(E, F)) (x : E) :
    f.fderivWithOrder x = if n = 0 then 0 else fderiv ℝ f x := by
  rw [ContDiffMapSupportedIn.fderivWithOrder]
  split_ifs <;> rfl

@[simp]
lemma coe_fderivWithOrder_of_ne (hn : n ≠ 0) (f : 𝓓^{n}_{K}(E, F)) :
    f.fderivWithOrder = fderiv ℝ f := by
  ext : 1
  rw [fderivWithOrder_apply]
  exact if_neg hn

@[simp]
lemma coe_fderivWithOrder_zero (f : 𝓓^{0}_{K}(E, F)) :
    f.fderivWithOrder = 0 := by
  ext : 1
  rw [fderivWithOrder_apply]
  exact if_pos rfl

/-- Bundling of `fderiv` as a `𝕜`-linear map. -/
@[simps]
noncomputable def fderivWithOrderₗ {n : ℕ∞} : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n-1}_{K}(E, E →L[ℝ] F) where
  toFun f := f.fderivWithOrder
  map_add' f₁ f₂ := by
    ext : 1
    simp only [fderivWithOrder_apply, add_apply]
    split_ifs with hn
    · rw [add_zero]
    · rw [← ne_eq, ← ENat.one_le_iff_ne_zero] at hn
      exact fderiv_add
        (f₁.contDiff.differentiable (by exact_mod_cast hn)).differentiableAt
        (f₂.contDiff.differentiable (by exact_mod_cast hn)).differentiableAt
  map_smul' c f := by
    ext : 1
    simp only [fderivWithOrder_apply, smul_apply]
    split_ifs with hn
    · rw [smul_zero]
    · rw [← ne_eq, ← ENat.one_le_iff_ne_zero] at hn
      exact fderiv_const_smul (f.contDiff.differentiable (by exact_mod_cast hn)).differentiableAt c

theorem seminorm_fderivWithOrder (i : ℕ) (f : 𝓓^{n}_{K}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E (E →L[ℝ] F) (n - 1) K i f.fderivWithOrder =
      ContDiffMapSupportedIn.seminorm 𝕜 E F n K (i+1) f := by
  simp_rw [ContDiffMapSupportedIn.seminorm_apply, BoundedContinuousFunction.norm_eq_iSup_norm]
  refine iSup_congr fun x ↦ ?_
  simp only [toBoundedContinuousFunction_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [iteratedFDerivWithOrder_zero]
  · rcases lt_or_ge (i : ℕ∞) n with (hin|hin)
    · have hin' : i + 1 ≤ n := by
        exact Order.add_one_le_of_lt hin
      have hin'' : i ≤ n - 1 := by
        refine ENat.le_sub_of_add_le_left (ENat.one_ne_top) (add_comm _ (1 : ℕ∞) ▸ hin')
      simp [hin', hin'', hn, ← norm_iteratedFDeriv_fderiv]
    · have hin' : n - 1 < i:= by
        refine (ENat.add_one_le_iff ?_).mp ?_
        · refine ENat.sub_ne_top_iff.mpr (Or.inl (ne_top_of_le_ne_top (ENat.coe_ne_top i) hin))
        · rw [tsub_add_cancel_of_le (ENat.one_le_iff_ne_zero.mpr hn )]
          exact hin
      have hin'' : n < i + 1 := by
        exact lt_of_tsub_lt_tsub_right hin'
      simp [hin', hin'']

/-- Bundling of `fderivWithOrder` as continuous `𝕜`-linear map. -/
@[simps! apply]
noncomputable def fderivWithOrderCLM : 𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n-1}_{K}(E, E →L[ℝ] F) where
  toLinearMap := fderivWithOrderₗ 𝕜
  cont := by
    refine Seminorm.continuous_from_bounded  (τ₁₂ := RingHom.id 𝕜)
      (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
      (ContDiffMapSupportedIn.withSeminorms 𝕜 E (E →L[ℝ] F) (n-1) K) _
      fun i ↦ ⟨{i+1}, 1, fun f ↦ ?_⟩
    simp only [Seminorm.comp_apply, fderivWithOrderₗ_apply,
      Finset.sup_singleton, one_smul]
    rw [seminorm_fderivWithOrder]

section infinite

/-- Specialization of `iteratedFDerivWithOrder` for the space `𝓓_{K}(E, F)` of smooth compactly
supported functions, as a map `𝓓_{K}(E, F) → 𝓓_{K}(E, E [×i]→L[ℝ] F)` with no loss of smoothness. -/
protected noncomputable def iteratedFDeriv (i : ℕ) (f : 𝓓_{K}(E, F)) : 𝓓_{K}(E, E [×i]→L[ℝ] F) :=
  (f.iteratedFDerivWithOrder i).copy (iteratedFDeriv ℝ i f)
    (coe_iteratedFDerivWithOrder_of_le le_top f)

lemma iteratedFDeriv_eq_iteratedFDerivWithOrder (i : ℕ) (f : 𝓓_{K}(E, F)) :
    f.iteratedFDeriv i = f.iteratedFDerivWithOrder i :=
  (f.iteratedFDerivWithOrder i).copy_eq _ _

@[simp]
lemma iteratedFDeriv_apply (i : ℕ) (f : 𝓓_{K}(E, F)) (x : E) :
    f.iteratedFDeriv i x = iteratedFDeriv ℝ i f x := by
  rfl

/-- Bundling of `ContDiffMapSupportedIn.iteratedFDeriv` as `𝕜`-linear map. -/
@[simps! apply]
noncomputable def iteratedFDerivₗ (i : ℕ) : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓓_{K}(E, E [×i]→L[ℝ] F) :=
  (iteratedFDerivWithOrderₗ 𝕜 i).copy (ContDiffMapSupportedIn.iteratedFDeriv i) <| funext <|
    iteratedFDeriv_eq_iteratedFDerivWithOrder i

/-- Specialisation of `fderivWithOrder` to the space `𝓓_{K}(E, F)` of smooth compactly supported
functions as a map `𝓓_{K}(E, F) → 𝓓_{K}(E, E →L[ℝ] F)`, with no loss of smoothness. -/
protected noncomputable def fderiv (f : 𝓓_{K}(E, F)) : 𝓓_{K}(E, E →L[ℝ] F) :=
  f.fderivWithOrder.copy (fderiv ℝ f) (coe_fderivWithOrder_of_ne (by decide) f)

lemma fderiv_eq_fderivWithOrder (f : 𝓓_{K}(E, F)) : f.fderiv = f.fderivWithOrder :=
  f.fderivWithOrder.copy_eq _ _

@[simp]
lemma fderiv_apply (f : 𝓓_{K}(E, F)) (x : E) :
    f.fderiv x = fderiv ℝ f x := by
  rfl

/-- Bundling of `ContDiffMapSupportedIn.fderiv` as a `𝕜`-linear map. -/
@[simps! apply]
noncomputable def fderivₗ : 𝓓_{K}(E, F) →ₗ[𝕜] 𝓓_{K}(E, E →L[ℝ] F) :=
  (fderivWithOrderₗ 𝕜).copy ContDiffMapSupportedIn.fderiv <| funext fderiv_eq_fderivWithOrder

/-- Bundling of `ContDiffMapSupportedIn.fderiv` as a continuous `𝕜`-linear map. -/
@[simps! apply]
noncomputable def fderivCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓓_{K}(E, E →L[ℝ] F) :=
  (fderivWithOrderCLM 𝕜).copy ContDiffMapSupportedIn.fderiv <| funext fderiv_eq_fderivWithOrder

end infinite

end fderiv

section finite

variable {n : ℕ}

protected theorem withSeminorms_of_finite : WithSeminorms
    (fun _ : Fin 1 ↦ (ContDiffMapSupportedIn.seminorm' 𝕜 E F n K n)) := by
  refine (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).congr ?_ ?_
  · intro _
    use Finset.Iic n, 1
    rw [one_smul]
    rfl
  · intro i
    use {0}, 1
    rw [one_smul, Finset.sup_singleton, Seminorm.comp_id]
    rcases le_or_gt i n with (hin|hin)
    · rw [← Finset.mem_Iic] at hin
      exact Finset.le_sup (α := Seminorm 𝕜 𝓓^{n}_{K}(E, F)) hin
    · rw [ContDiffMapSupportedIn.seminorm_eq_bot 𝕜 (by norm_cast)]
      exact bot_le

end finite

end ContDiffMapSupportedIn
