/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Lattice.Image
import Mathlib.GroupTheory.GroupAction.Pointwise
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Compact operators

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `IsCompactOperator` : predicate for compact operators

## Main statements

* `isCompactOperator_iff_isCompact_closure_image_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `IsCompactOperator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `IsCompactOperator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `IsCompactOperator.continuous` : compact operators are automatically continuous
* `isClosed_setOf_isCompactOperator` : the set of compact operators is closed for the operator
  norm

## Implementation details

We define `IsCompactOperator` as a predicate, because the space of compact operators inherits all
of its structure from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre 3][bourbaki2023]

## Tags

Compact operator
-/

@[expose] public section


open Function Set Filter Bornology Metric Pointwise Topology

/-- A compact operator between two topological vector spaces. This definition is usually
given as "there exists a neighborhood of zero whose image is contained in a compact set",
but we choose a definition which involves fewer existential quantifiers and replaces images
with preimages.

We prove the equivalence in `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`. -/
def IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
    (f : M₁ → M₂) : Prop :=
  ∃ K, IsCompact K ∧ f ⁻¹' K ∈ (𝓝 0 : Filter M₁)

theorem isCompactOperator_zero {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁]
    [TopologicalSpace M₂] [Zero M₂] : IsCompactOperator (0 : M₁ → M₂) :=
  ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun _ _ => rfl⟩

theorem isCompactOperator_id_iff_locallyCompactSpace {E : Type*}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] :
    IsCompactOperator (id : E → E) ↔ LocallyCompactSpace E :=
  ⟨fun ⟨_, hK, hK0⟩ ↦ hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ ↦ exists_compact_mem_nhds 0⟩

alias ⟨LocallyCompactSpace.of_isCompactOperator_id, _⟩ :=
  isCompactOperator_id_iff_locallyCompactSpace

@[deprecated (since := "2026-03-04")] alias IsCompactOperator.locallyCompactSpace :=
  LocallyCompactSpace.of_isCompactOperator_id

lemma isCompactOperator_id {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] : IsCompactOperator (id : E → E) :=
  isCompactOperator_id_iff_locallyCompactSpace.2 ‹_›

section Characterizations

section

variable {R₁ : Type*} [Semiring R₁] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂]

theorem isCompactOperator_iff_exists_mem_nhds_image_subset_compact (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), ∃ K : Set M₂, IsCompact K ∧ f '' V ⊆ K :=
  ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨_, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩

theorem isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂] (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), IsCompact (closure <| f '' V) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, hK.closure_of_subset hKV⟩,
      fun ⟨V, hV, hVc⟩ => ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩

end

section Bounded

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [ContinuousConstSMul 𝕜₂ M₂]

theorem IsCompactOperator.image_subset_compact_of_isVonNBounded {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := (hS hKf).exists_pos
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let this := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
  ⟨σ₁₂ c • K, hK.image <| continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff, this.isUnit.preimage_smul_setₛₗ σ₁₂]; exact hrS c hc.le⟩

theorem IsCompactOperator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    IsCompact (closure <| f '' S) :=
  let ⟨_, hK, hKf⟩ := hf.image_subset_compact_of_isVonNBounded hS
  hK.closure_of_subset hKf

end Bounded

section NormedSpace

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂]

theorem IsCompactOperator.image_subset_compact_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : Bornology.IsBounded S) :
    ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded <| by rwa [NormedSpace.isVonNBounded_iff]

theorem IsCompactOperator.isCompact_closure_image_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁}
    (hS : Bornology.IsBounded S) : IsCompact (closure <| f '' S) :=
  hf.isCompact_closure_image_of_isVonNBounded <| by rwa [NormedSpace.isVonNBounded_iff]

theorem IsCompactOperator.image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : ℝ) : ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

theorem IsCompactOperator.image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    ∃ K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

theorem IsCompactOperator.isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    IsCompact (closure <| f '' Metric.ball 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)

theorem IsCompactOperator.isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)

theorem isCompactOperator_iff_image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r ⊆ K :=
  ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩

theorem isCompactOperator_iff_image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r ⊆ K :=
  ⟨fun hf => hf.image_closedBall_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, K, hK, hKr⟩⟩

theorem isCompactOperator_iff_isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.ball 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_ball r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩

theorem isCompactOperator_iff_isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_closedBall r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, hf⟩⟩

end NormedSpace

end Characterizations

section Operations

variable {R₁ R₄ : Type*} [Semiring R₁] [CommSemiring R₄]
  {σ₁₄ : R₁ →+* R₄} {M₁ M₂ M₄ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [TopologicalSpace M₄] [AddCommGroup M₄]

theorem IsCompactOperator.smul {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} (hf : IsCompactOperator f) (c : S) :
    IsCompactOperator (c • f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨c • K, hK.image <| continuous_id.const_smul c,
    mem_of_superset hKf fun _ hx => smul_mem_smul_set hx⟩

theorem IsCompactOperator.smul_unit_iff {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} {c : Sˣ} :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  ⟨fun h ↦ by simpa using h.smul c⁻¹, fun h ↦ h.smul c⟩

theorem IsCompactOperator.smul_isUnit_iff {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} {c : S} (hc : IsUnit c) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f := by
  obtain ⟨c, rfl⟩ := hc
  exact smul_unit_iff

theorem IsCompactOperator.smul_iff {S : Type*} [Group S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} (c : S) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  smul_isUnit_iff (Group.isUnit c)

theorem IsCompactOperator.smul_iff₀ {S : Type*} [GroupWithZero S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} {c : S} (hc : c ≠ 0) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  smul_isUnit_iff hc.isUnit

theorem IsCompactOperator.add [ContinuousAdd M₂] {f g : M₁ → M₂} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f + g) :=
  let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB,
    mem_of_superset (inter_mem hAf hBg) fun _ ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩

theorem IsCompactOperator.neg [ContinuousNeg M₄] {f : M₁ → M₄} (hf : IsCompactOperator f) :
    IsCompactOperator (-f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, mem_of_superset hKf fun x (hx : f x ∈ K) => Set.neg_mem_neg.mpr hx⟩

theorem IsCompactOperator.sub [IsTopologicalAddGroup M₄] {f g : M₁ → M₄} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

variable (σ₁₄ M₁ M₄)

/-- The submodule of compact continuous linear maps. -/
def compactOperator [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
    [IsTopologicalAddGroup M₄] : Submodule R₄ (M₁ →SL[σ₁₄] M₄) where
  carrier := { f | IsCompactOperator f }
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

end Operations

section Comp

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₁] [Module R₁ M₁]

theorem IsCompactOperator.comp_clm [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ → M₃}
    (hf : IsCompactOperator f) (g : M₁ →SL[σ₁₂] M₂) : IsCompactOperator (f ∘ g) := by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩

theorem IsCompactOperator.continuous_comp {f : M₁ → M₂} (hf : IsCompactOperator f) {g : M₂ → M₃}
    (hg : Continuous g) : IsCompactOperator (g ∘ f) := by
  rcases hf with ⟨K, hK, hKf⟩
  refine ⟨g '' K, hK.image hg, mem_of_superset hKf ?_⟩
  rw [preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)

theorem IsCompactOperator.clm_comp [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M₃]
    [Module R₃ M₃] {f : M₁ → M₂} (hf : IsCompactOperator f) (g : M₂ →SL[σ₂₃] M₃) :
    IsCompactOperator (g ∘ f) :=
  hf.continuous_comp g.continuous

/-- Any continuous linear map to a locally compact space is a compact operator. -/
theorem isCompactOperator_of_locallyCompactSpace_dom [AddCommGroup M₂] [Module R₂ M₂]
    [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] (T : M₁ →SL[σ₁₂] M₂) :
    IsCompactOperator T := (isCompactOperator_id.comp_clm T :)

/-- Any continuous linear map from a locally compact space is a compact operator. -/
theorem isCompactOperator_of_locallyCompactSpace_rng [AddCommGroup M₂] [Module R₂ M₂]
    [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] [AddCommMonoid M₃] [Module R₃ M₃]
    (T : M₂ →SL[σ₂₃] M₃) : IsCompactOperator T := isCompactOperator_id.clm_comp T

end Comp

section CodRestrict

variable {R₂ : Type*} [Semiring R₂] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R₂ M₂]

theorem IsCompactOperator.codRestrict {f : M₁ → M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
    (hV : ∀ x, f x ∈ V) (h_closed : IsClosed (V : Set M₂)) :
    IsCompactOperator (Set.codRestrict f V hV) :=
  let ⟨_, hK, hKf⟩ := hf
  ⟨_, h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, hKf⟩

end CodRestrict

section Restrict

variable {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [UniformSpace M₂]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R₁ M₁]
  [Module R₂ M₂]

/-- If a compact operator preserves a closed submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`IsCompactOperator.codRestrict` to `f ∘ U.subtypeL`, which is compact by
`IsCompactOperator.comp_clm`. -/
theorem IsCompactOperator.restrict {f : M₁ →ₗ[R₁] M₁} (hf : IsCompactOperator f)
    {V : Submodule R₁ M₁} (hV : ∀ v ∈ V, f v ∈ V) (h_closed : IsClosed (V : Set M₁)) :
    IsCompactOperator (f.restrict hV) :=
  (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed

/-- If a compact operator preserves a complete submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`IsCompactOperator.codRestrict` to `f ∘ U.subtypeL`, which is compact by
`IsCompactOperator.comp_clm`. -/
theorem IsCompactOperator.restrict' [T0Space M₂] {f : M₂ →ₗ[R₂] M₂}
    (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : ∀ v ∈ V, f v ∈ V)
    [hcomplete : CompleteSpace V] : IsCompactOperator (f.restrict hV) :=
  hf.restrict hV (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

end Restrict

section Continuous

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type*} [TopologicalSpace M₁] [AddCommGroup M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [IsTopologicalAddGroup M₁]
  [ContinuousConstSMul 𝕜₁ M₁] [IsTopologicalAddGroup M₂] [ContinuousSMul 𝕜₂ M₂]

@[continuity]
theorem IsCompactOperator.continuous {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    Continuous f := by
  letI : UniformSpace M₂ := IsTopologicalAddGroup.rightUniformSpace _
  haveI : IsUniformAddGroup M₂ := isUniformAddGroup_of_addCommGroup
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine continuous_of_continuousAt_zero f fun U hU => ?_
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : Set M₂` such that `f ⁻¹' K` is a
  -- neighborhood of `0` in `M₁`.
  rcases hf with ⟨K, hK, hKf⟩
  -- But any compact set is totally bounded, hence Von-Neumann bounded. Thus, `K` absorbs `U`.
  -- This gives `r > 0` such that `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  rcases (hK.totallyBounded.isVonNBounded 𝕜₂ hU).exists_pos with ⟨r, hr, hrU⟩
  -- Choose `c : 𝕜₂` with `r < ‖c‖`.
  rcases NormedField.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩
  have hcnz : c ≠ 0 := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
  -- We have `f ⁻¹' ((σ₁₂ c⁻¹) • K) = c⁻¹ • f ⁻¹' K ∈ 𝓝 0`. Thus, showing that
  -- `(σ₁₂ c⁻¹) • K ⊆ U` is enough to deduce that `f ⁻¹' U ∈ 𝓝 0`.
  suffices (σ₁₂ <| c⁻¹) • K ⊆ U by
    grw [← this]
    have : IsUnit c⁻¹ := hcnz.isUnit.inv
    rwa [mem_map, this.preimage_smul_setₛₗ σ₁₂, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)]
  -- Since `σ₁₂ c⁻¹` = `(σ₁₂ c)⁻¹`, we have to prove that `K ⊆ σ₁₂ c • U`.
  rw [map_inv₀, ← subset_smul_set_iff₀ ((map_ne_zero σ₁₂).mpr hcnz)]
  -- But `σ₁₂` is isometric, so `‖σ₁₂ c‖ = ‖c‖ > r`, which concludes the argument since
  -- `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  refine hrU (σ₁₂ c) ?_
  rw [RingHomIsometric.norm_map]
  exact hc.le

/-- Upgrade a compact `LinearMap` to a `ContinuousLinearMap`. -/
def ContinuousLinearMap.mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    M₁ →SL[σ₁₂] M₂ :=
  ⟨f, hf.continuous⟩

@[simp]
theorem ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
theorem ContinuousLinearMap.coe_mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) : (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ → M₂) = f :=
  rfl

theorem ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    ContinuousLinearMap.mkOfIsCompactOperator hf ∈ compactOperator σ₁₂ M₁ M₂ :=
  hf

end Continuous

/-- The set of compact operators from a normed space to a complete topological vector space is
closed. -/
theorem isClosed_setOf_isCompactOperator {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    IsClosed { f : M₁ →SL[σ₁₂] M₂ | IsCompactOperator f } := by
  refine isClosed_of_closure_subset ?_
  rintro u hu
  rw [mem_closure_iff_nhds_zero] at hu
  suffices TotallyBounded (u '' Metric.closedBall 0 1) by
    change IsCompactOperator (u : M₁ →ₛₗ[σ₁₂] M₂)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall (u : M₁ →ₛₗ[σ₁₂] M₂) zero_lt_one]
    exact this.closure.isCompact_of_isClosed isClosed_closure
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  rcases exists_nhds_zero_half hU with ⟨V, hV, hVU⟩
  let SV : Set M₁ × Set M₂ := ⟨closedBall 0 1, -V⟩
  rcases hu { f | ∀ x ∈ SV.1, f x ∈ SV.2 }
      (ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
        ⟨NormedSpace.isVonNBounded_closedBall _ _ _, neg_mem_nhds_zero M₂ hV⟩) with
    ⟨v, hv, huv⟩
  rcases totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
      (hv.isCompact_closure_image_closedBall 1).totallyBounded V hV with
    ⟨T, hT, hTv⟩
  have hTv : v '' closedBall 0 1 ⊆ _ := subset_closure.trans hTv
  refine ⟨T, hT, ?_⟩
  rw [image_subset_iff, preimage_iUnion₂] at hTv ⊢
  intro x hx
  specialize hTv hx
  rw [mem_iUnion₂] at hTv ⊢
  rcases hTv with ⟨t, ht, htx⟩
  refine ⟨t, ht, ?_⟩
  rw [mem_preimage, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at htx ⊢
  convert hVU _ htx _ (huv x hx) using 1
  rw [ContinuousLinearMap.sub_apply]
  abel

theorem compactOperator_topologicalClosure {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    (compactOperator σ₁₂ M₁ M₂).topologicalClosure = compactOperator σ₁₂ M₁ M₂ :=
  SetLike.ext' isClosed_setOf_isCompactOperator.closure_eq

theorem isCompactOperator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] {l : Filter ι} [l.NeBot]
    {F : ι → M₁ →SL[σ₁₂] M₂} {f : M₁ →SL[σ₁₂] M₂} (hf : Tendsto F l (𝓝 f))
    (hF : ∀ᶠ i in l, IsCompactOperator (F i)) : IsCompactOperator f :=
  isClosed_setOf_isCompactOperator.mem_of_tendsto hf hF
