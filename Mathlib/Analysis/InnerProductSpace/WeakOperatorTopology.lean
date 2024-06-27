/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The weak operator topology

This file defines a type copy of `E →L[𝕜] F` (where `F` is an inner product space) which is
endowed with the weak operator topology (WOT) rather than the topology induced by the operator norm.
The WOT is defined as the coarsest topology such that the functional `fun A => ⟪y, A x⟫` is
continuous for any `x : E` and `y : F`. Basic non-topological properties of `E →L[𝕜] F` (such as
the module structure) are copied over to the type copy.

We also prove that the WOT is induced by the family of seminorms `‖⟪y, A x⟫‖` for `x : E` and
`y : F`.

## Main declarations

* `ContinuousLinearMapWOT 𝕜 E F`: The type copy of `E →L[𝕜] F` endowed with the weak operator
  topology.
* `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`: a function `f` tends to
  `A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a), x⟫` tends to `⟪y, A x⟫` along the same filter.
* `ContinuousLinearMap.toWOT`: the inclusion map from `E →L[𝕜] F` to the type copy
* `ContinuousLinearMap.continuous_toWOT`: the inclusion map is continuous, i.e. the WOT is coarser
  than the norm topology.
* `ContinuousLinearMapWOT.withSeminorms`: the WOT is induced by the family of seminorms
  `‖⟪y, A x⟫‖` for `x : E` and `y : F`.

## Notation

* The type copy of `E →L[𝕜] F` endowed with the weak operator topology is denoted by
  `E →WOT[𝕜] F`.

## Implementation notes

In the literature, the WOT is only defined on operators on a Hilbert space, i.e. `E →L[𝕜] E`. Here
we generalize this a bit to `E →L[𝕜] F` where `F` is an inner product space, and `E` actually only
needs to be a vector space with some topology for most results in this file.
-/

open scoped Topology

/-- The type copy of `E →L[𝕜] F` endowed with the weak operator topology, denoted as
`E →WOT[𝕜] F`. -/
def ContinuousLinearMapWOT (𝕜 : Type*) (E : Type*) (F : Type*) [RCLike 𝕜] [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] := E →L[𝕜] F

notation E " →WOT[" 𝕜 "]" F => ContinuousLinearMapWOT 𝕜 E F

namespace ContinuousLinearMapWOT

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner (𝕜 := 𝕜) x y

/-!
### Basic properties common with `E →L[𝕜] F`

The section copies basic non-topological properties of `E →L[𝕜] F` over to `E →WOT[𝕜] F`, such as
the module structure, `FunLike`, etc.
-/
section Basic

instance instAddCommGroup : AddCommGroup (E →WOT[𝕜] F) :=
  inferInstanceAs <| AddCommGroup (E →L[𝕜] F)

instance instModule : Module 𝕜 (E →WOT[𝕜] F) := inferInstanceAs <| Module 𝕜 (E →L[𝕜] F)

variable (𝕜) (E) (F)
/-- The equivalence that sends a continuous linear map to the type copy endowed with the
weak operator topology.  -/
def _root_.ContinuousLinearMap.toWOT : (E →L[𝕜] F) ≃ₗ[𝕜] (E →WOT[𝕜] F) := LinearEquiv.refl 𝕜 _

variable {𝕜} {E} {F}

instance instFunLike : FunLike (E →WOT[𝕜] F) E F where
  coe f :=  ((ContinuousLinearMap.toWOT 𝕜 E F).symm f : E → F)
  coe_injective' := by intro; simp

instance instContinuousLinearMapClass : ContinuousLinearMapClass (E →WOT[𝕜] F) 𝕜 E F where
  map_add f x y := by simp only [DFunLike.coe]; simp
  map_smulₛₗ f r x := by simp only [DFunLike.coe]; simp
  map_continuous f := ContinuousLinearMap.continuous ((ContinuousLinearMap.toWOT 𝕜 E F).symm f)

lemma _root_.ContinuousLinearMap.toWOT_apply {A : E →L[𝕜] F} {x : E} :
    ((ContinuousLinearMap.toWOT 𝕜 E F) A) x = A x := rfl

lemma ext_iff {A B : E →WOT[𝕜] F} : A = B ↔ ∀ x, A x = B x := ContinuousLinearMap.ext_iff

lemma ext_inner_iff {A B : E →WOT[𝕜] F} : A = B ↔ ∀ x y, ⟪y, A x⟫ = ⟪y, B x⟫ := by
  refine ⟨fun h _ _ => by simp [h], fun h => ?_⟩
  rw [ext_iff]
  exact fun x => ext_inner_left 𝕜 fun y => h x y

@[simp] lemma zero_apply (x : E) : (0 : E →WOT[𝕜] F) x = 0 := by simp only [DFunLike.coe]; rfl

@[simp] lemma add_apply {f g : E →WOT[𝕜] F} (x : E) : (f + g) x = f x + g x := by
  simp only [DFunLike.coe]; rfl

@[simp] lemma neg_apply {f : E →WOT[𝕜] F} (x : E) : (-f) x = -(f x) := by
  simp only [DFunLike.coe]; rfl

@[simp] lemma smul_apply {f : E →WOT[𝕜] F} (c : 𝕜) (x : E) : (c • f) x = c • (f x) := by
  simp only [DFunLike.coe]; rfl

end Basic

/-!
### The topology of `E →WOT[𝕜] F`

The section endows `E →WOT[𝕜] F` with the weak operator topology and shows the basic properties
of this topology. In particular, we show that it is a topological vector space.
-/
section Topology

/-- The weak operator topology is the coarsest topology such that `fun A => ⟪x, A y⟫` is
continuous for all `x, y`. -/
instance instTopologicalSpace : TopologicalSpace (E →WOT[𝕜] F) :=
  TopologicalSpace.induced (fun A (⟨x, y⟩ : E × F) => ⟪y, A x⟫) Pi.topologicalSpace

lemma coeFn_continuous : Continuous fun (A : E →WOT[𝕜] F) (⟨x, y⟩ : E × F) => ⟪y, A x⟫ :=
  continuous_induced_dom

lemma inner_apply_continuous (x : E) (y : F) : Continuous fun (A : E →WOT[𝕜] F) => ⟪y, A x⟫ := by
  refine (continuous_pi_iff.mp coeFn_continuous) ⟨x, y⟩

lemma continuous_of_inner_apply_continuous {α : Type*} [TopologicalSpace α] {g : α → E →WOT[𝕜] F}
    (h : ∀ x y, Continuous fun a => ⟪y, (g a) x⟫) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr fun p => h p.1 p.2)

lemma embedding : Embedding fun (A : E →WOT[𝕜] F) (p : E × F) => ⟪p.2, A p.1⟫ := by
  refine Function.Injective.embedding_induced fun A B hAB => ?_
  rw [ext_inner_iff]
  simpa [Function.funext_iff] using hAB

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a), x⟫` tends to `⟪y, A x⟫` along the same filter. -/
lemma tendsto_iff_forall_inner_apply_tendsto {α : Type*} {l : Filter α} {f : α → E →WOT[𝕜] F}
    {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫) l (𝓝 ⟪y, A x⟫) := by
  have hmain : (∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫) l (𝓝 ⟪y, A x⟫))
      ↔ ∀ (p : E × F), Tendsto (fun a => ⟪p.2, (f a) p.1⟫) l (𝓝 ⟪p.2, A p.1⟫) :=
    ⟨fun h p => h p.1 p.2, fun h x y => h ⟨x, y⟩⟩
  rw [hmain, ← tendsto_pi_nhds, Embedding.tendsto_nhds_iff embedding]
  rfl

lemma le_nhds_iff_forall_inner_apply_le_nhds {l : Filter (E →WOT[𝕜] F)} {A : E →WOT[𝕜] F} :
    l ≤ 𝓝 A ↔ ∀ x y, l.map (fun T => ⟪y, T x⟫) ≤ 𝓝 (⟪y, A x⟫) :=
  tendsto_iff_forall_inner_apply_tendsto (f := id)

instance instT2Space : T2Space (E →WOT[𝕜] F) := Embedding.t2Space embedding

instance instContinuousAdd : ContinuousAdd (E →WOT[𝕜] F) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  change Continuous (fun ⟨A, B⟩ p => ⟪p.2, (A + B) p.1⟫)
  simp only [add_apply, inner_add_right]
  refine Continuous.add ?_ ?_
  · exact Continuous.comp coeFn_continuous continuous_fst
  · exact Continuous.comp coeFn_continuous continuous_snd

instance instContinuousSMul : ContinuousSMul 𝕜 (E →WOT[𝕜] F) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  change Continuous (fun ⟨r, A⟩ p => ⟪p.2, (r • A) p.1⟫)
  simp only [smul_apply, inner_smul_right]
  refine Continuous.mul ?_ ?_
  · change Continuous ((fun x _ => x) ∘ Prod.fst)
    exact Continuous.comp (by fun_prop) continuous_fst
  · exact Continuous.comp coeFn_continuous continuous_snd

instance instTopologicalAddGroup : TopologicalAddGroup (E →WOT[𝕜] F) where
  continuous_neg := by
    refine continuous_induced_rng.2 ?_
    change Continuous (fun (A : E →WOT[𝕜] F) (p : E × F) => ⟪p.2, (-A) p.1⟫)
    simp only [neg_apply, inner_neg_right]
    exact Continuous.comp continuous_neg coeFn_continuous

instance instUniformSpace : UniformSpace (E →WOT[𝕜] F) := TopologicalAddGroup.toUniformSpace _

instance instUniformAddGroup : UniformAddGroup (E →WOT[𝕜] F) :=
  comm_topologicalAddGroup_is_uniform

end Topology

/-! ### The WOT is induced by a family of seminorms -/
section Seminorms

/-- The family of seminorms that induce the weak operator topology, namely `‖⟪y, A x⟫‖` for
all `x` and `y`.  -/
def seminorm (x : E) (y : F) : Seminorm 𝕜 (E →WOT[𝕜] F) where
  toFun A := ‖⟪y, A x⟫‖
  map_zero' := by simp
  add_le' A B := by simp [inner_add_right]; exact norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [inner_smul_right]

variable (𝕜) (E) (F) in
/-- The family of seminorms that induce the weak operator topology, namely `‖⟪y, A x⟫‖` for
all `x` and `y`.  -/
def seminormFamily : SeminormFamily 𝕜 (E →WOT[𝕜] F) (E × F) :=
  fun ⟨x, y⟩ => seminorm x y

lemma hasBasis_seminorms : (𝓝 (0 : E →WOT[𝕜] F)).HasBasis (seminormFamily 𝕜 E F).basisSets id := by
  let p := seminormFamily 𝕜 E F
  rw [nhds_induced, nhds_pi]
  simp only [map_zero, zero_apply, inner_zero_right]
  have h := @Metric.nhds_basis_ball 𝕜 _ 0
  have h' := Filter.hasBasis_pi fun _ : (E × F) => h
  have h'' := Filter.HasBasis.comap (fun (A : E →WOT[𝕜] F) (p : E × F) => ⟪p.2, A p.1⟫) h'
  refine h''.to_hasBasis ?_ ?_
  · intro U hU
    obtain ⟨hU₁, hU₂⟩ := hU
    simp only [id]
    let U' := hU₁.toFinset
    by_cases hU₃ : U.fst.Nonempty
    · have hU₃' : U'.Nonempty := hU₁.toFinset_nonempty.mpr hU₃
      refine ⟨(U'.sup p).ball 0 <| U'.inf' hU₃' U.snd, p.basisSets_mem _ <|
        (Finset.lt_inf'_iff _).2 fun y hy => hU₂ y <| hU₁.mem_toFinset.mp hy, fun x hx y hy => ?_⟩
      simp only [Set.mem_preimage, Set.mem_pi, mem_ball_zero_iff]
      rw [Seminorm.mem_ball_zero] at hx
      have hyU' : y ∈ U' := (Set.Finite.mem_toFinset hU₁).mpr hy
      have hp : p y ≤ U'.sup p := Finset.le_sup hyU'
      refine lt_of_le_of_lt (hp x) (lt_of_lt_of_le hx ?_)
      exact Finset.inf'_le _ hyU'
    · rw [Set.not_nonempty_iff_eq_empty.mp hU₃]
      simp only [Set.empty_pi, Set.preimage_univ, Set.subset_univ, and_true_iff]
      exact ⟨(p 0).ball 0 1, p.basisSets_singleton_mem 0 one_pos⟩
  · intro U (hU : U ∈ p.basisSets)
    rw [SeminormFamily.basisSets_iff] at hU
    obtain ⟨s, r, hr, hU⟩ := hU
    rw [hU]
    refine ⟨(s, fun _ => r), ⟨by simp only [s.finite_toSet], fun y _ => hr⟩, fun x hx => ?_⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, mem_ball_zero_iff] at hx
    simp only [_root_.id, Seminorm.mem_ball, sub_zero]
    exact Seminorm.finset_sup_apply_lt hr fun y hy => hx y hy

lemma withSeminorms : WithSeminorms (seminormFamily 𝕜 E F) :=
  SeminormFamily.withSeminorms_of_hasBasis _ hasBasis_seminorms

instance instLocallyConvexSpace [Module ℝ (E →WOT[𝕜] F)] [IsScalarTower ℝ 𝕜 (E →WOT[𝕜] F)] :
    LocallyConvexSpace ℝ (E →WOT[𝕜] F) :=
  withSeminorms.toLocallyConvexSpace

end Seminorms

end ContinuousLinearMapWOT

section NormedSpace

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The weak operator topology is coarser than the norm topology, i.e. the inclusion map is
continuous. -/
@[continuity, fun_prop]
lemma ContinuousLinearMap.continuous_toWOT :
    Continuous (ContinuousLinearMap.toWOT 𝕜 E F) := by
  refine ContinuousLinearMapWOT.continuous_of_inner_apply_continuous fun x y => ?_
  simp_rw [ContinuousLinearMap.toWOT_apply]
  refine Continuous.inner continuous_const ?_
  change Continuous fun a => (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).flip x a
  fun_prop

/-- The inclusion map from `E →[𝕜] F` to `E →WOT[𝕜] F`, bundled as a continuous linear map. -/
def ContinuousLinearMap.toWOTCLM : (E →L[𝕜] F) →L[𝕜] (E →WOT[𝕜] F) :=
  ⟨LinearEquiv.toLinearMap (ContinuousLinearMap.toWOT 𝕜 E F), ContinuousLinearMap.continuous_toWOT⟩

end NormedSpace
