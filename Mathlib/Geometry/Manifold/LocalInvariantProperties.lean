/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn

! This file was ported from Lean 3 source module geometry.manifold.local_invariant_properties
! leanprover-community/mathlib commit be2c24f56783935652cefffb4bfca7e4b25d167e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `local_invariant_prop G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `charted_space.lift_prop_within_at` (resp. `lift_prop_at`, `lift_prop_on` and `lift_prop`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : local_invariant_prop G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.lift_prop_within_at_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.lift_prop_within_at_congr` saying that if `lift_prop_within_at P g s x` holds, and `g` and `g'`
coincide on `s`, then `lift_prop_within_at P g' s x` holds. We can't call it
`lift_prop_within_at.congr` as it is in the namespace associated to `local_invariant_prop`, not
in the one for `lift_prop_within_at`.
-/


noncomputable section

open Classical Manifold Topology

open Set Filter

variable {H M H' M' X : Type _}

variable [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

variable [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']

variable [TopologicalSpace X]

namespace StructureGroupoid

variable (G : StructureGroupoid H) (G' : StructureGroupoid H')

/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
structure LocalInvariantProp (P : (H → H') → Set H → H → Prop) : Prop where
  is_local : ∀ {s x u} {f : H → H'}, IsOpen u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance' :
    ∀ {s x f} {e : LocalHomeomorph H H},
      e ∈ G → x ∈ e.source → P f s x → P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → f x = g x → P f s x → P g s x
  left_invariance' :
    ∀ {s x f} {e' : LocalHomeomorph H' H'},
      e' ∈ G' → s ⊆ f ⁻¹' e'.source → f x ∈ e'.source → P f s x → P (e' ∘ f) s x
#align structure_groupoid.local_invariant_prop StructureGroupoid.LocalInvariantProp

variable {G G'} {P : (H → H') → Set H → H → Prop} {s t u : Set H} {x : H}

variable (hG : G.LocalInvariantProp G' P)

include hG

namespace LocalInvariantProp

theorem congr_set {s t : Set H} {x : H} {f : H → H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x :=
  by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_set_of, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo, host, ← hG.is_local ho hxo]
#align structure_groupoid.local_invariant_prop.congr_set StructureGroupoid.LocalInvariantProp.congr_set

theorem is_local_nhds {s u : Set H} {x : H} {f : H → H'} (hu : u ∈ 𝓝[s] x) :
    P f s x ↔ P f (s ∩ u) x :=
  hG.congr_set <| mem_nhdsWithin_iff_eventuallyEq.mp hu
#align structure_groupoid.local_invariant_prop.is_local_nhds StructureGroupoid.LocalInvariantProp.is_local_nhds

theorem congr_iff_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g)
    (h2 : f x = g x) : P f s x ↔ P g s x :=
  by
  simp_rw [hG.is_local_nhds h1]
  exact
    ⟨hG.congr_of_forall (fun y hy => hy.2) h2, hG.congr_of_forall (fun y hy => hy.2.symm) h2.symm⟩
#align structure_groupoid.local_invariant_prop.congr_iff_nhds_within StructureGroupoid.LocalInvariantProp.congr_iff_nhdsWithin

theorem congr_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P f s x) : P g s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mp hP
#align structure_groupoid.local_invariant_prop.congr_nhds_within StructureGroupoid.LocalInvariantProp.congr_nhdsWithin

theorem congr_nhds_within' {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P g s x) : P f s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mpr hP
#align structure_groupoid.local_invariant_prop.congr_nhds_within' StructureGroupoid.LocalInvariantProp.congr_nhds_within'

theorem congr_iff {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
  hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h : _)
#align structure_groupoid.local_invariant_prop.congr_iff StructureGroupoid.LocalInvariantProp.congr_iff

theorem congr {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
  (hG.congr_iff h).mp hP
#align structure_groupoid.local_invariant_prop.congr StructureGroupoid.LocalInvariantProp.congr

theorem congr' {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
  hG.congr h.symm hP
#align structure_groupoid.local_invariant_prop.congr' StructureGroupoid.LocalInvariantProp.congr'

theorem left_invariance {s : Set H} {x : H} {f : H → H'} {e' : LocalHomeomorph H' H'}
    (he' : e' ∈ G') (hfs : ContinuousWithinAt f s x) (hxe' : f x ∈ e'.source) :
    P (e' ∘ f) s x ↔ P f s x :=
  by
  have h2f := hfs.preimage_mem_nhds_within (e'.open_source.mem_nhds hxe')
  have h3f :=
    ((e'.continuous_at hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin <|
      e'.symm.open_source.mem_nhds <| e'.maps_to hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invariance' (G'.symm he') (inter_subset_right _ _) (e'.maps_to hxe') h
    rw [← hG.is_local_nhds h3f] at h2
    refine' hG.congr_nhds_within _ (e'.left_inv hxe') h2
    exact eventually_of_mem h2f fun x' => e'.left_inv
  · simp_rw [hG.is_local_nhds h2f]
    exact hG.left_invariance' he' (inter_subset_right _ _) hxe'
#align structure_groupoid.local_invariant_prop.left_invariance StructureGroupoid.LocalInvariantProp.left_invariance

theorem right_invariance {s : Set H} {x : H} {f : H → H'} {e : LocalHomeomorph H H} (he : e ∈ G)
    (hxe : x ∈ e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P f s x :=
  by
  refine' ⟨fun h => _, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.maps_to hxe) h
  rw [e.symm_symm, e.left_inv hxe] at this
  refine' hG.congr _ ((hG.congr_set _).mp this)
  · refine' eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' => _
    simp_rw [Function.comp_apply, e.left_inv hx']
  · rw [eventually_eq_set]
    refine' eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' => _
    simp_rw [mem_preimage, e.left_inv hx']
#align structure_groupoid.local_invariant_prop.right_invariance StructureGroupoid.LocalInvariantProp.right_invariance

end LocalInvariantProp

end StructureGroupoid

namespace ChartedSpace

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`lift_prop_within_at_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
def LiftPropWithinAt (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) (x : M) : Prop :=
  ContinuousWithinAt f s x ∧
    P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)
#align charted_space.lift_prop_within_at ChartedSpace.LiftPropWithinAt

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def LiftPropOn (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, LiftPropWithinAt P f s x
#align charted_space.lift_prop_on ChartedSpace.LiftPropOn

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def LiftPropAt (P : (H → H') → Set H → H → Prop) (f : M → M') (x : M) :=
  LiftPropWithinAt P f univ x
#align charted_space.lift_prop_at ChartedSpace.LiftPropAt

theorem liftPropAt_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} {x : M} :
    LiftPropAt P f x ↔
      ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) :=
  by rw [lift_prop_at, lift_prop_within_at, continuousWithinAt_univ, preimage_univ]
#align charted_space.lift_prop_at_iff ChartedSpace.liftPropAt_iff

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
def LiftProp (P : (H → H') → Set H → H → Prop) (f : M → M') :=
  ∀ x, LiftPropAt P f x
#align charted_space.lift_prop ChartedSpace.LiftProp

theorem liftProp_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} :
    LiftProp P f ↔
      Continuous f ∧ ∀ x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) :=
  by simp_rw [lift_prop, lift_prop_at_iff, forall_and, continuous_iff_continuousAt]
#align charted_space.lift_prop_iff ChartedSpace.liftProp_iff

end ChartedSpace

open ChartedSpace

namespace StructureGroupoid

variable {G : StructureGroupoid H} {G' : StructureGroupoid H'} {e e' : LocalHomeomorph M H}
  {f f' : LocalHomeomorph M' H'} {P : (H → H') → Set H → H → Prop} {g g' : M → M'} {s t : Set M}
  {x : M} {Q : (H → H) → Set H → H → Prop}

theorem liftPropWithinAt_univ : LiftPropWithinAt P g univ x ↔ LiftPropAt P g x :=
  Iff.rfl
#align structure_groupoid.lift_prop_within_at_univ StructureGroupoid.liftPropWithinAt_univ

theorem liftPropOn_univ : LiftPropOn P g univ ↔ LiftProp P g := by
  simp [lift_prop_on, lift_prop, lift_prop_at]
#align structure_groupoid.lift_prop_on_univ StructureGroupoid.liftPropOn_univ

theorem liftPropWithinAt_self {f : H → H'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P f s x :=
  Iff.rfl
#align structure_groupoid.lift_prop_within_at_self StructureGroupoid.liftPropWithinAt_self

theorem liftPropWithinAt_self_source {f : H → M'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P (chartAt H' (f x) ∘ f) s x :=
  Iff.rfl
#align structure_groupoid.lift_prop_within_at_self_source StructureGroupoid.liftPropWithinAt_self_source

theorem liftPropWithinAt_self_target {f : M → H'} :
    LiftPropWithinAt P f s x ↔
      ContinuousWithinAt f s x ∧
        P (f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x) :=
  Iff.rfl
#align structure_groupoid.lift_prop_within_at_self_target StructureGroupoid.liftPropWithinAt_self_target

namespace LocalInvariantProp

variable (hG : G.LocalInvariantProp G' P)

include hG

/-- `lift_prop_within_at P f s x` is equivalent to a definition where we restrict the set we are
  considering to the domain of the charts at `x` and `f x`. -/
theorem liftPropWithinAt_iff {f : M → M'} :
    LiftPropWithinAt P f s x ↔
      ContinuousWithinAt f s x ∧
        P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm)
          ((chartAt H x).target ∩ (chartAt H x).symm ⁻¹' (s ∩ f ⁻¹' (chartAt H' (f x)).source))
          (chartAt H x x) :=
  by
  refine' and_congr_right fun hf => hG.congr_set _
  exact
    LocalHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter hf (mem_chart_source H x)
      (chart_source_mem_nhds H' (f x))
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_iff StructureGroupoid.LocalInvariantProp.liftPropWithinAt_iff

theorem lift_prop_within_at_indep_chart_source_aux (g : M → H') (he : e ∈ G.maximalAtlas M)
    (xe : x ∈ e.source) (he' : e' ∈ G.maximalAtlas M) (xe' : x ∈ e'.source) :
    P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) :=
  by
  rw [← hG.right_invariance (compatible_of_mem_maximal_atlas he he')]
  swap; · simp only [xe, xe', mfld_simps]
  simp_rw [LocalHomeomorph.trans_apply, e.left_inv xe]
  rw [hG.congr_iff]
  · refine' hG.congr_set _
    refine' (eventually_of_mem _ fun y (hy : y ∈ e'.symm ⁻¹' e.source) => _).set_eq
    · refine' (e'.symm.continuous_at <| e'.maps_to xe').preimage_mem_nhds (e.open_source.mem_nhds _)
      simp_rw [e'.left_inv xe', xe]
    simp_rw [mem_preimage, LocalHomeomorph.coe_trans_symm, LocalHomeomorph.symm_symm,
      Function.comp_apply, e.left_inv hy]
  · refine' ((e'.eventually_nhds' _ xe').mpr <| e.eventually_left_inverse xe).mono fun y hy => _
    simp only [mfld_simps]
    rw [hy]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_source_aux StructureGroupoid.LocalInvariantProp.lift_prop_within_at_indep_chart_source_aux

theorem lift_prop_within_at_indep_chart_target_aux2 (g : H → M') {x : H} {s : Set H}
    (hf : f ∈ G'.maximalAtlas M') (xf : g x ∈ f.source) (hf' : f' ∈ G'.maximalAtlas M')
    (xf' : g x ∈ f'.source) (hgs : ContinuousWithinAt g s x) : P (f ∘ g) s x ↔ P (f' ∘ g) s x :=
  by
  have hcont : ContinuousWithinAt (f ∘ g) s x := (f.continuous_at xf).comp_continuousWithinAt hgs
  rw [←
    hG.left_invariance (compatible_of_mem_maximal_atlas hf hf') hcont
      (by simp only [xf, xf', mfld_simps])]
  refine' hG.congr_iff_nhds_within _ (by simp only [xf, mfld_simps])
  exact (hgs.eventually <| f.eventually_left_inverse xf).mono fun y => congr_arg f'
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_target_aux2 StructureGroupoid.LocalInvariantProp.lift_prop_within_at_indep_chart_target_aux2

theorem lift_prop_within_at_indep_chart_target_aux {g : X → M'} {e : LocalHomeomorph X H} {x : X}
    {s : Set X} (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M') (xf : g x ∈ f.source)
    (hf' : f' ∈ G'.maximalAtlas M') (xf' : g x ∈ f'.source) (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
  by
  rw [← e.left_inv xe] at xf xf' hgs
  refine' hG.lift_prop_within_at_indep_chart_target_aux2 (g ∘ e.symm) hf xf hf' xf' _
  exact hgs.comp (e.symm.continuous_at <| e.maps_to xe).ContinuousWithinAt subset.rfl
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_target_aux StructureGroupoid.LocalInvariantProp.lift_prop_within_at_indep_chart_target_aux

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
theorem lift_prop_within_at_indep_chart_aux (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source)
    (he' : e' ∈ G.maximalAtlas M) (xe' : x ∈ e'.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) (hf' : f' ∈ G'.maximalAtlas M') (xf' : g x ∈ f'.source)
    (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  rw [hG.lift_prop_within_at_indep_chart_source_aux (f ∘ g) he xe he' xe',
    hG.lift_prop_within_at_indep_chart_target_aux xe' hf xf hf' xf' hgs]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_aux StructureGroupoid.LocalInvariantProp.lift_prop_within_at_indep_chart_aux

theorem liftPropWithinAt_indep_chart [HasGroupoid M G] [HasGroupoid M' G']
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
  and_congr_right <|
    hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximalAtlas _ _) (mem_chart_source _ _) he xe
      (chart_mem_maximalAtlas _ _) (mem_chart_source _ _) hf xf
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart

/-- A version of `lift_prop_within_at_indep_chart`, only for the source. -/
theorem liftPropWithinAt_indep_chart_source [HasGroupoid M G] (he : e ∈ G.maximalAtlas M)
    (xe : x ∈ e.source) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
  by
  have := e.symm.continuous_within_at_iff_continuous_within_at_comp_right xe
  rw [e.symm_symm] at this
  rw [lift_prop_within_at_self_source, lift_prop_within_at, ← this]
  simp_rw [Function.comp_apply, e.left_inv xe]
  refine' and_congr Iff.rfl _
  rw [hG.lift_prop_within_at_indep_chart_source_aux (chart_at H' (g x) ∘ g)
      (chart_mem_maximal_atlas G x) (mem_chart_source H x) he xe]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_source StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source

/-- A version of `lift_prop_within_at_indep_chart`, only for the target. -/
theorem liftPropWithinAt_indep_chart_target [HasGroupoid M' G'] (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g) s x :=
  by
  rw [lift_prop_within_at_self_target, lift_prop_within_at, and_congr_right_iff]
  intro hg
  simp_rw [(f.continuous_at xf).comp_continuousWithinAt hg, true_and_iff]
  exact
    hG.lift_prop_within_at_indep_chart_target_aux (mem_chart_source _ _)
      (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf hg
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart_target StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target

/-- A version of `lift_prop_within_at_indep_chart`, that uses `lift_prop_within_at` on both sides.
-/
theorem liftPropWithinAt_indep_chart' [HasGroupoid M G] [HasGroupoid M' G']
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔
      ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
  by
  rw [hG.lift_prop_within_at_indep_chart he xe hf xf, lift_prop_within_at_self, and_left_comm,
    Iff.comm, and_iff_right_iff_imp]
  intro h
  have h1 := (e.symm.continuous_within_at_iff_continuous_within_at_comp_right xe).mp h.1
  have : ContinuousAt f ((g ∘ e.symm) (e x)) := by
    simp_rw [Function.comp, e.left_inv xe, f.continuous_at xf]
  exact this.comp_continuous_within_at h1
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_indep_chart' StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart'

theorem liftPropOn_indep_chart [HasGroupoid M G] [HasGroupoid M' G'] (he : e ∈ G.maximalAtlas M)
    (hf : f ∈ G'.maximalAtlas M') (h : LiftPropOn P g s) {y : H}
    (hy : y ∈ e.target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.source)) : P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y :=
  by
  convert((hG.lift_prop_within_at_indep_chart he (e.symm_maps_to hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]
#align structure_groupoid.local_invariant_prop.lift_prop_on_indep_chart StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart

theorem liftPropWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x :=
  by
  rw [lift_prop_within_at, lift_prop_within_at, continuousWithinAt_inter' ht, hG.congr_set]
  simp_rw [eventually_eq_set, mem_preimage,
    (chart_at H x).eventually_nhds' (fun x => x ∈ s ∩ t ↔ x ∈ s) (mem_chart_source H x)]
  exact (mem_nhds_within_iff_eventually_eq.mp ht).symm.mem_iff
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_inter' StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter'

theorem liftPropWithinAt_inter (ht : t ∈ 𝓝 x) :
    LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_inter' (mem_nhdsWithin_of_mem_nhds ht)
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_inter StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter

theorem liftPropAt_of_liftPropWithinAt (h : LiftPropWithinAt P g s x) (hs : s ∈ 𝓝 x) :
    LiftPropAt P g x := by rwa [← univ_inter s, hG.lift_prop_within_at_inter hs] at h
#align structure_groupoid.local_invariant_prop.lift_prop_at_of_lift_prop_within_at StructureGroupoid.LocalInvariantProp.liftPropAt_of_liftPropWithinAt

theorem liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs : s ∈ 𝓝 x) :
    LiftPropWithinAt P g s x := by rwa [← univ_inter s, hG.lift_prop_within_at_inter hs]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_of_lift_prop_at_of_mem_nhds StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt_of_mem_nhds

theorem liftPropOn_of_locally_liftPropOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g (s ∩ u)) : LiftPropOn P g s :=
  by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.lift_prop_within_at_inter] at this
  exact IsOpen.mem_nhds u_open xu
#align structure_groupoid.local_invariant_prop.lift_prop_on_of_locally_lift_prop_on StructureGroupoid.LocalInvariantProp.liftPropOn_of_locally_liftPropOn

theorem liftProp_of_locally_liftPropOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g u) :
    LiftProp P g := by
  rw [← lift_prop_on_univ]
  apply hG.lift_prop_on_of_locally_lift_prop_on fun x hx => _
  simp [h x]
#align structure_groupoid.local_invariant_prop.lift_prop_of_locally_lift_prop_on StructureGroupoid.LocalInvariantProp.liftProp_of_locally_liftPropOn

theorem liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x :=
  by
  refine' ⟨h.1.congr_of_eventuallyEq h₁ hx, _⟩
  refine'
    hG.congr_nhds_within' _
      (by simp_rw [Function.comp_apply, (chart_at H x).left_inv (mem_chart_source H x), hx]) h.2
  simp_rw [eventually_eq, Function.comp_apply,
    (chart_at H x).eventually_nhdsWithin'
      (fun y => chart_at H' (g' x) (g' y) = chart_at H' (g x) (g y)) (mem_chart_source H x)]
  exact h₁.mono fun y hy => by rw [hx, hy]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_of_eventually_eq StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_eventuallyEq

theorem liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  ⟨fun h => hG.liftPropWithinAt_congr_of_eventuallyEq h h₁.symm hx.symm, fun h =>
    hG.liftPropWithinAt_congr_of_eventuallyEq h h₁ hx⟩
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff_of_eventually_eq StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq

theorem liftPropWithinAt_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) hx
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_congr_iff StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff

theorem liftPropWithinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : ∀ y ∈ s, g' y = g y)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ hx).mpr h
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_congr StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr

theorem liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x ↔ LiftPropAt P g x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (by simp_rw [nhdsWithin_univ, h₁]) h₁.eq_of_nhds
#align structure_groupoid.local_invariant_prop.lift_prop_at_congr_iff_of_eventually_eq StructureGroupoid.LocalInvariantProp.liftPropAt_congr_iff_of_eventuallyEq

theorem liftPropAt_congr_of_eventuallyEq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x :=
  (hG.liftPropAt_congr_iff_of_eventuallyEq h₁).mpr h
#align structure_groupoid.local_invariant_prop.lift_prop_at_congr_of_eventually_eq StructureGroupoid.LocalInvariantProp.liftPropAt_congr_of_eventuallyEq

theorem liftPropOn_congr (h : LiftPropOn P g s) (h₁ : ∀ y ∈ s, g' y = g y) : LiftPropOn P g' s :=
  fun x hx => hG.liftPropWithinAt_congr (h x hx) h₁ (h₁ x hx)
#align structure_groupoid.local_invariant_prop.lift_prop_on_congr StructureGroupoid.LocalInvariantProp.liftPropOn_congr

theorem liftPropOn_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s :=
  ⟨fun h => hG.liftPropOn_congr h fun y hy => (h₁ y hy).symm, fun h => hG.liftPropOn_congr h h₁⟩
#align structure_groupoid.local_invariant_prop.lift_prop_on_congr_iff StructureGroupoid.LocalInvariantProp.liftPropOn_congr_iff

omit hG

theorem liftPropWithinAt_mono_of_mem
    (mono_of_mem : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, s ∈ 𝓝[t] x → P f s x → P f t x)
    (h : LiftPropWithinAt P g s x) (hst : s ∈ 𝓝[t] x) : LiftPropWithinAt P g t x :=
  by
  refine' ⟨h.1.mono_of_mem hst, mono_of_mem _ h.2⟩
  simp_rw [← mem_map, (chart_at H x).symm.map_nhdsWithin_preimage_eq (mem_chart_target H x),
    (chart_at H x).left_inv (mem_chart_source H x), hst]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_mono_of_mem StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem

theorem liftPropWithinAt_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropWithinAt P g s x) (hts : t ⊆ s) : LiftPropWithinAt P g t x :=
  by
  refine' ⟨h.1.mono hts, _⟩
  apply mono (fun y hy => _) h.2
  simp only [mfld_simps] at hy
  simp only [hy, hts _, mfld_simps]
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_mono StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono

theorem liftPropWithinAt_of_liftPropAt (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropAt P g x) : LiftPropWithinAt P g s x :=
  by
  rw [← lift_prop_within_at_univ] at h
  exact lift_prop_within_at_mono mono h (subset_univ _)
#align structure_groupoid.local_invariant_prop.lift_prop_within_at_of_lift_prop_at StructureGroupoid.LocalInvariantProp.liftPropWithinAt_of_liftPropAt

theorem liftPropOn_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropOn P g t) (hst : s ⊆ t) : LiftPropOn P g s := fun x hx =>
  liftPropWithinAt_mono mono (h x (hst hx)) hst
#align structure_groupoid.local_invariant_prop.lift_prop_on_mono StructureGroupoid.LocalInvariantProp.liftPropOn_mono

theorem liftPropOn_of_liftProp (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftProp P g) : LiftPropOn P g s :=
  by
  rw [← lift_prop_on_univ] at h
  exact lift_prop_on_mono mono h (subset_univ _)
#align structure_groupoid.local_invariant_prop.lift_prop_on_of_lift_prop StructureGroupoid.LocalInvariantProp.liftPropOn_of_liftProp

theorem liftPropAt_of_mem_maximalAtlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) (hx : x ∈ e.source) : LiftPropAt Q e x :=
  by
  simp_rw [lift_prop_at,
    hG.lift_prop_within_at_indep_chart he hx G.id_mem_maximal_atlas (mem_univ _),
    (e.continuous_at hx).ContinuousWithinAt, true_and_iff]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)
#align structure_groupoid.local_invariant_prop.lift_prop_at_of_mem_maximal_atlas StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_maximalAtlas

theorem liftPropOn_of_mem_maximalAtlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) : LiftPropOn Q e e.source :=
  by
  intro x hx
  apply
    hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
      (hG.lift_prop_at_of_mem_maximal_atlas hQ he hx)
  exact IsOpen.mem_nhds e.open_source hx
#align structure_groupoid.local_invariant_prop.lift_prop_on_of_mem_maximal_atlas StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_maximalAtlas

theorem liftPropAt_symm_of_mem_maximalAtlas [HasGroupoid M G] {x : H}
    (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G)
    (hx : x ∈ e.target) : LiftPropAt Q e.symm x :=
  by
  suffices h : Q (e ∘ e.symm) univ x
  · have A : e.symm ⁻¹' e.source ∩ e.target = e.target := by mfld_set_tac
    have : e.symm x ∈ e.source := by simp only [hx, mfld_simps]
    rw [lift_prop_at,
      hG.lift_prop_within_at_indep_chart G.id_mem_maximal_atlas (mem_univ _) he this]
    refine' ⟨(e.symm.continuous_at hx).ContinuousWithinAt, _⟩
    simp only [h, mfld_simps]
  exact hG.congr' (e.eventually_right_inverse hx) (hQ x)
#align structure_groupoid.local_invariant_prop.lift_prop_at_symm_of_mem_maximal_atlas StructureGroupoid.LocalInvariantProp.liftPropAt_symm_of_mem_maximalAtlas

theorem liftPropOn_symm_of_mem_maximalAtlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) : LiftPropOn Q e.symm e.target :=
  by
  intro x hx
  apply
    hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds
      (hG.lift_prop_at_symm_of_mem_maximal_atlas hQ he hx)
  exact IsOpen.mem_nhds e.open_target hx
#align structure_groupoid.local_invariant_prop.lift_prop_on_symm_of_mem_maximal_atlas StructureGroupoid.LocalInvariantProp.liftPropOn_symm_of_mem_maximalAtlas

theorem liftPropAt_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftPropAt Q (chartAt H x) x :=
  hG.liftPropAt_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (mem_chart_source H x)
#align structure_groupoid.local_invariant_prop.lift_prop_at_chart StructureGroupoid.LocalInvariantProp.liftPropAt_chart

theorem liftPropOn_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftPropOn Q (chartAt H x) (chartAt H x).source :=
  hG.liftPropOn_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)
#align structure_groupoid.local_invariant_prop.lift_prop_on_chart StructureGroupoid.LocalInvariantProp.liftPropOn_chart

theorem liftPropAt_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) : LiftPropAt Q (chartAt H x).symm ((chartAt H x) x) :=
  hG.liftPropAt_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (by simp)
#align structure_groupoid.local_invariant_prop.lift_prop_at_chart_symm StructureGroupoid.LocalInvariantProp.liftPropAt_chart_symm

theorem liftPropOn_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) : LiftPropOn Q (chartAt H x).symm (chartAt H x).target :=
  hG.liftPropOn_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)
#align structure_groupoid.local_invariant_prop.lift_prop_on_chart_symm StructureGroupoid.LocalInvariantProp.liftPropOn_chart_symm

theorem liftPropAt_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y)
    {f : LocalHomeomorph H H} (hf : f ∈ G) {x : H} (hx : x ∈ f.source) : LiftPropAt Q f x :=
  liftPropAt_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf) hx
#align structure_groupoid.local_invariant_prop.lift_prop_at_of_mem_groupoid StructureGroupoid.LocalInvariantProp.liftPropAt_of_mem_groupoid

theorem liftPropOn_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y)
    {f : LocalHomeomorph H H} (hf : f ∈ G) : LiftPropOn Q f f.source :=
  liftPropOn_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf)
#align structure_groupoid.local_invariant_prop.lift_prop_on_of_mem_groupoid StructureGroupoid.LocalInvariantProp.liftPropOn_of_mem_groupoid

theorem liftProp_id (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftProp Q (id : M → M) :=
  by
  simp_rw [lift_prop_iff, continuous_id, true_and_iff]
  exact fun x => hG.congr' ((chart_at H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)
#align structure_groupoid.local_invariant_prop.lift_prop_id StructureGroupoid.LocalInvariantProp.liftProp_id

end LocalInvariantProp

section LocalStructomorph

variable (G)

open LocalHomeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def IsLocalStructomorphWithinAt (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : LocalHomeomorph H H, e ∈ G ∧ EqOn f e.toFun (s ∩ e.source) ∧ x ∈ e.source
#align structure_groupoid.is_local_structomorph_within_at StructureGroupoid.IsLocalStructomorphWithinAt

/-- For a groupoid `G` which is `closed_under_restriction`, being a local structomorphism is a local
invariant property. -/
theorem isLocalStructomorphWithinAt_localInvariantProp [ClosedUnderRestriction G] :
    LocalInvariantProp G G (IsLocalStructomorphWithinAt G) :=
  { is_local := by
      intro s x u f hu hux
      constructor
      · rintro h hx
        rcases h hx.1 with ⟨e, heG, hef, hex⟩
        have : s ∩ u ∩ e.source ⊆ s ∩ e.source := by mfld_set_tac
        exact ⟨e, heG, hef.mono this, hex⟩
      · rintro h hx
        rcases h ⟨hx, hux⟩ with ⟨e, heG, hef, hex⟩
        refine' ⟨e.restr (interior u), _, _, _⟩
        · exact closed_under_restriction' heG isOpen_interior
        · have : s ∩ u ∩ e.source = s ∩ (e.source ∩ u) := by mfld_set_tac
          simpa only [this, interior_interior, hu.interior_eq, mfld_simps] using hef
        · simp only [*, interior_interior, hu.interior_eq, mfld_simps]
    right_invariance' := by
      intro s x f e' he'G he'x h hx
      have hxs : x ∈ s := by simpa only [e'.left_inv he'x, mfld_simps] using hx
      rcases h hxs with ⟨e, heG, hef, hex⟩
      refine' ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, _, _⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.2⟩, mfld_simps]
      · simp only [hex, he'x, mfld_simps]
    congr_of_forall := by
      intro s x f g hfgs hfg' h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine' ⟨e, heG, _, hex⟩
      intro y hy
      rw [← hef hy, hfgs y hy.1]
    left_invariance' := by
      intro s x f e' he'G he' hfx h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine' ⟨e.trans e', G.trans heG he'G, _, _⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.1⟩, mfld_simps]
      · simpa only [hex, hef ⟨hx, hex⟩, mfld_simps] using hfx }
#align structure_groupoid.is_local_structomorph_within_at_local_invariant_prop StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp

/-- A slight reformulation of `is_local_structomorph_within_at` when `f` is a local homeomorph.
  This gives us an `e` that is defined on a subset of `f.source`. -/
theorem LocalHomeomorph.isLocalStructomorphWithinAt_iff {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : LocalHomeomorph H H) {s : Set H} {x : H}
    (hx : x ∈ f.source ∪ sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x ∈ s →
        ∃ e : LocalHomeomorph H H,
          e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) (s ∩ e.source) ∧ x ∈ e.source :=
  by
  constructor
  · intro hf h2x
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x
    refine' ⟨e.restr f.source, closed_under_restriction' he f.open_source, _, _, hxe, _⟩
    · simp_rw [LocalHomeomorph.restr_source]
      refine' (inter_subset_right _ _).trans interior_subset
    · intro x' hx'
      exact hfe ⟨hx'.1, hx'.2.1⟩
    · rw [f.open_source.interior_eq]
      exact Or.resolve_right hx (not_not.mpr h2x)
  · intro hf hx
    obtain ⟨e, he, h2e, hfe, hxe⟩ := hf hx
    exact ⟨e, he, hfe, hxe⟩
#align local_homeomorph.is_local_structomorph_within_at_iff LocalHomeomorph.isLocalStructomorphWithinAt_iff

/-- A slight reformulation of `is_local_structomorph_within_at` when `f` is a local homeomorph and
  the set we're considering is a superset of `f.source`. -/
theorem LocalHomeomorph.isLocalStructomorphWithinAt_iff' {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : LocalHomeomorph H H) {s : Set H} {x : H} (hs : f.source ⊆ s)
    (hx : x ∈ f.source ∪ sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x ∈ s →
        ∃ e : LocalHomeomorph H H,
          e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) e.source ∧ x ∈ e.source :=
  by
  simp_rw [f.is_local_structomorph_within_at_iff hx]
  refine' imp_congr_right fun hx => exists_congr fun e => and_congr_right fun he => _
  refine' and_congr_right fun h2e => _
  rw [inter_eq_right_iff_subset.mpr (h2e.trans hs)]
#align local_homeomorph.is_local_structomorph_within_at_iff' LocalHomeomorph.isLocalStructomorphWithinAt_iff'

/-- A slight reformulation of `is_local_structomorph_within_at` when `f` is a local homeomorph and
  the set we're considering is `f.source`. -/
theorem LocalHomeomorph.isLocalStructomorphWithinAt_source_iff {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : LocalHomeomorph H H) {x : H} :
    G.IsLocalStructomorphWithinAt (⇑f) f.source x ↔
      x ∈ f.source →
        ∃ e : LocalHomeomorph H H,
          e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) e.source ∧ x ∈ e.source :=
  haveI : x ∈ f.source ∪ f.sourceᶜ := by simp_rw [union_compl_self]
  f.is_local_structomorph_within_at_iff' subset.rfl this
#align local_homeomorph.is_local_structomorph_within_at_source_iff LocalHomeomorph.isLocalStructomorphWithinAt_source_iff

variable {H₁ : Type _} [TopologicalSpace H₁] {H₂ : Type _} [TopologicalSpace H₂] {H₃ : Type _}
  [TopologicalSpace H₃] [ChartedSpace H₁ H₂] [ChartedSpace H₂ H₃] {G₁ : StructureGroupoid H₁}
  [HasGroupoid H₂ G₁] [ClosedUnderRestriction G₁] (G₂ : StructureGroupoid H₂) [HasGroupoid H₃ G₂]

variable (G₂)

theorem HasGroupoid.comp
    (H : ∀ e ∈ G₂, LiftPropOn (IsLocalStructomorphWithinAt G₁) (e : H₂ → H₂) e.source) :
    @HasGroupoid H₁ _ H₃ _ (ChartedSpace.comp H₁ H₂ H₃) G₁ :=
  {
    compatible := by
      rintro _ _ ⟨e, f, he, hf, rfl⟩ ⟨e', f', he', hf', rfl⟩
      apply G₁.locality
      intro x hx
      simp only [mfld_simps] at hx
      have hxs : x ∈ f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
      have hxs' : x ∈ f.target ∩ f.symm ⁻¹' ((e.symm ≫ₕ e').source ∩ e.symm ≫ₕ e' ⁻¹' f'.source) :=
        by simp only [hx, mfld_simps]
      obtain ⟨φ, hφG₁, hφ, hφ_dom⟩ :=
        local_invariant_prop.lift_prop_on_indep_chart
          (is_local_structomorph_within_at_local_invariant_prop G₁) (G₁.subset_maximal_atlas hf)
          (G₁.subset_maximal_atlas hf') (H _ (G₂.compatible he he')) hxs' hxs
      simp_rw [← LocalHomeomorph.coe_trans, LocalHomeomorph.trans_assoc] at hφ
      simp_rw [LocalHomeomorph.trans_symm_eq_symm_trans_symm, LocalHomeomorph.trans_assoc]
      have hs : IsOpen (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').source :=
        (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').open_source
      refine' ⟨_, hs.inter φ.open_source, _, _⟩
      · simp only [hx, hφ_dom, mfld_simps]
      · refine' G₁.eq_on_source (closed_under_restriction' hφG₁ hs) _
        rw [LocalHomeomorph.restr_source_inter]
        refine' (hφ.mono _).restr_eqOn_source
        mfld_set_tac }
#align structure_groupoid.has_groupoid.comp StructureGroupoid.HasGroupoid.comp

end LocalStructomorph

end StructureGroupoid

