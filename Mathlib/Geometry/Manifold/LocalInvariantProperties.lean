/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ChartedSpace

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

* `LocalInvariantProp G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `ChartedSpace.LiftPropWithinAt` (resp. `LiftPropAt`, `LiftPropOn` and `LiftProp`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : LocalInvariantProp G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.liftPropWithinAt_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.liftPropWithinAt_congr` saying that if `LiftPropWithinAt P g s x` holds, and `g` and `g'`
coincide on `s`, then `LiftPropWithinAt P g' s x` holds. We can't call it
`LiftPropWithinAt.congr` as it is in the namespace associated to `LocalInvariantProp`, not
in the one for `LiftPropWithinAt`.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold Topology

variable {H M H' M' X : Type*}
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
  right_invariance' : ∀ {s x f} {e : OpenPartialHomeomorph H H},
    e ∈ G → x ∈ e.source → P f s x → P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : ∀ {s x} {f g : H → H'}, (∀ y ∈ s, f y = g y) → f x = g x → P f s x → P g s x
  left_invariance' : ∀ {s x f} {e' : OpenPartialHomeomorph H' H'},
    e' ∈ G' → s ⊆ f ⁻¹' e'.source → f x ∈ e'.source → P f s x → P (e' ∘ f) s x

variable {G G'} {P : (H → H') → Set H → H → Prop}
variable (hG : G.LocalInvariantProp G' P)
include hG

namespace LocalInvariantProp

theorem congr_set {s t : Set H} {x : H} {f : H → H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x := by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_setOf, ← and_congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo, host, ← hG.is_local ho hxo]

theorem is_local_nhds {s u : Set H} {x : H} {f : H → H'} (hu : u ∈ 𝓝[s] x) :
    P f s x ↔ P f (s ∩ u) x :=
  hG.congr_set <| mem_nhdsWithin_iff_eventuallyEq.mp hu

theorem congr_iff_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g)
    (h2 : f x = g x) : P f s x ↔ P g s x := by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy ↦ hy.2) h2, hG.congr_of_forall (fun y hy ↦ hy.2.symm) h2.symm⟩

theorem congr_nhdsWithin {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P f s x) : P g s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mp hP

theorem congr_nhdsWithin' {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x)
    (hP : P g s x) : P f s x :=
  (hG.congr_iff_nhdsWithin h1 h2).mpr hP

theorem congr_iff {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
  hG.congr_iff_nhdsWithin (mem_nhdsWithin_of_mem_nhds h) (mem_of_mem_nhds h :)

theorem congr {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
  (hG.congr_iff h).mp hP

theorem congr' {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
  hG.congr h.symm hP

theorem left_invariance {s : Set H} {x : H} {f : H → H'} {e' : OpenPartialHomeomorph H' H'}
    (he' : e' ∈ G') (hfs : ContinuousWithinAt f s x) (hxe' : f x ∈ e'.source) :
    P (e' ∘ f) s x ↔ P f s x := by
  have h2f := hfs.preimage_mem_nhdsWithin (e'.open_source.mem_nhds hxe')
  have h3f :=
    ((e'.continuousAt hxe').comp_continuousWithinAt hfs).preimage_mem_nhdsWithin <|
      e'.symm.open_source.mem_nhds <| e'.mapsTo hxe'
  constructor
  · intro h
    rw [hG.is_local_nhds h3f] at h
    have h2 := hG.left_invariance' (G'.symm he') inter_subset_right (e'.mapsTo hxe') h
    rw [← hG.is_local_nhds h3f] at h2
    refine hG.congr_nhdsWithin ?_ (e'.left_inv hxe') h2
    exact eventually_of_mem h2f fun x' ↦ e'.left_inv
  · simp_rw [hG.is_local_nhds h2f]
    exact hG.left_invariance' he' inter_subset_right hxe'

theorem right_invariance {s : Set H} {x : H} {f : H → H'} {e : OpenPartialHomeomorph H H}
    (he : e ∈ G) (hxe : x ∈ e.source) : P (f ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P f s x := by
  refine ⟨fun h ↦ ?_, hG.right_invariance' he hxe⟩
  have := hG.right_invariance' (G.symm he) (e.mapsTo hxe) h
  rw [e.symm_symm, e.left_inv hxe] at this
  refine hG.congr ?_ ((hG.congr_set ?_).mp this)
  · refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' ↦ ?_
    simp_rw [Function.comp_apply, e.left_inv hx']
  · rw [eventuallyEq_set]
    refine eventually_of_mem (e.open_source.mem_nhds hxe) fun x' hx' ↦ ?_
    simp_rw [mem_preimage, e.left_inv hx']

end LocalInvariantProp

end StructureGroupoid

namespace ChartedSpace

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`liftPropWithinAt_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
@[mk_iff liftPropWithinAt_iff']
structure LiftPropWithinAt (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) (x : M) :
    Prop where
  continuousWithinAt : ContinuousWithinAt f s x
  prop : P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def LiftPropOn (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, LiftPropWithinAt P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def LiftPropAt (P : (H → H') → Set H → H → Prop) (f : M → M') (x : M) :=
  LiftPropWithinAt P f univ x

theorem liftPropAt_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} {x : M} :
    LiftPropAt P f x ↔
      ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) := by
  rw [LiftPropAt, liftPropWithinAt_iff', continuousWithinAt_univ, preimage_univ]

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
def LiftProp (P : (H → H') → Set H → H → Prop) (f : M → M') :=
  ∀ x, LiftPropAt P f x

theorem liftProp_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} :
    LiftProp P f ↔
      Continuous f ∧ ∀ x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) univ (chartAt H x x) := by
  simp_rw [LiftProp, liftPropAt_iff, forall_and, continuous_iff_continuousAt]

end ChartedSpace

open ChartedSpace

namespace StructureGroupoid

variable {G : StructureGroupoid H} {G' : StructureGroupoid H'} {e e' : OpenPartialHomeomorph M H}
  {f f' : OpenPartialHomeomorph M' H'} {P : (H → H') → Set H → H → Prop} {g g' : M → M'}
  {s t : Set M} {x : M} {Q : (H → H) → Set H → H → Prop}

theorem liftPropWithinAt_univ : LiftPropWithinAt P g univ x ↔ LiftPropAt P g x := Iff.rfl

theorem liftPropOn_univ : LiftPropOn P g univ ↔ LiftProp P g := by
  simp [LiftPropOn, LiftProp, LiftPropAt]

theorem liftPropWithinAt_self {f : H → H'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P f s x :=
  liftPropWithinAt_iff' ..

theorem liftPropWithinAt_self_source {f : H → M'} {s : Set H} {x : H} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P (chartAt H' (f x) ∘ f) s x :=
  liftPropWithinAt_iff' ..

theorem liftPropWithinAt_self_target {f : M → H'} :
    LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧
      P (f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x) :=
  liftPropWithinAt_iff' ..

namespace LocalInvariantProp

section
variable (hG : G.LocalInvariantProp G' P)
include hG

/-- `LiftPropWithinAt P f s x` is equivalent to a definition where we restrict the set we are
  considering to the domain of the charts at `x` and `f x`. -/
theorem liftPropWithinAt_iff {f : M → M'} :
    LiftPropWithinAt P f s x ↔
      ContinuousWithinAt f s x ∧
        P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm)
          ((chartAt H x).target ∩ (chartAt H x).symm ⁻¹' (s ∩ f ⁻¹' (chartAt H' (f x)).source))
          (chartAt H x x) := by
  rw [liftPropWithinAt_iff']
  refine and_congr_right fun hf ↦ hG.congr_set ?_
  exact OpenPartialHomeomorph.preimage_eventuallyEq_target_inter_preimage_inter hf
    (mem_chart_source H x) (chart_source_mem_nhds H' (f x))

theorem liftPropWithinAt_indep_chart_source_aux (g : M → H') (he : e ∈ G.maximalAtlas M)
    (xe : x ∈ e.source) (he' : e' ∈ G.maximalAtlas M) (xe' : x ∈ e'.source) :
    P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  rw [← hG.right_invariance (compatible_of_mem_maximalAtlas he he')]
  swap; · simp only [xe, xe', mfld_simps]
  simp_rw [OpenPartialHomeomorph.trans_apply, e.left_inv xe]
  rw [hG.congr_iff]
  · refine hG.congr_set ?_
    refine (eventually_of_mem ?_ fun y (hy : y ∈ e'.symm ⁻¹' e.source) ↦ ?_).set_eq
    · refine (e'.symm.continuousAt <| e'.mapsTo xe').preimage_mem_nhds (e.open_source.mem_nhds ?_)
      simp_rw [e'.left_inv xe', xe]
    simp_rw [mem_preimage, OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
      Function.comp_apply, e.left_inv hy]
  · refine ((e'.eventually_nhds' _ xe').mpr <| e.eventually_left_inverse xe).mono fun y hy ↦ ?_
    simp only [mfld_simps]
    rw [hy]

theorem liftPropWithinAt_indep_chart_target_aux2 (g : H → M') {x : H} {s : Set H}
    (hf : f ∈ G'.maximalAtlas M') (xf : g x ∈ f.source) (hf' : f' ∈ G'.maximalAtlas M')
    (xf' : g x ∈ f'.source) (hgs : ContinuousWithinAt g s x) : P (f ∘ g) s x ↔ P (f' ∘ g) s x := by
  have hcont : ContinuousWithinAt (f ∘ g) s x := (f.continuousAt xf).comp_continuousWithinAt hgs
  rw [← hG.left_invariance (compatible_of_mem_maximalAtlas hf hf') hcont
      (by simp only [xf, xf', mfld_simps])]
  refine hG.congr_iff_nhdsWithin ?_ (by simp only [xf, mfld_simps])
  exact (hgs.eventually <| f.eventually_left_inverse xf).mono fun y ↦ congr_arg f'

theorem liftPropWithinAt_indep_chart_target_aux {g : X → M'} {e : OpenPartialHomeomorph X H} {x : X}
    {s : Set X} (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M') (xf : g x ∈ f.source)
    (hf' : f' ∈ G'.maximalAtlas M') (xf' : g x ∈ f'.source) (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [← e.left_inv xe] at xf xf' hgs
  refine hG.liftPropWithinAt_indep_chart_target_aux2 (g ∘ e.symm) hf xf hf' xf' ?_
  exact hgs.comp (e.symm.continuousAt <| e.mapsTo xe).continuousWithinAt Subset.rfl

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` cannot be captured with a chart in the target). -/
theorem liftPropWithinAt_indep_chart_aux (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source)
    (he' : e' ∈ G.maximalAtlas M) (xe' : x ∈ e'.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) (hf' : f' ∈ G'.maximalAtlas M') (xf' : g x ∈ f'.source)
    (hgs : ContinuousWithinAt g s x) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) ↔ P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  rw [← Function.comp_assoc, hG.liftPropWithinAt_indep_chart_source_aux (f ∘ g) he xe he' xe',
    Function.comp_assoc, hG.liftPropWithinAt_indep_chart_target_aux xe' hf xf hf' xf' hgs]

theorem liftPropWithinAt_indep_chart [HasGroupoid M G] [HasGroupoid M' G']
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔
    ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  simp only [liftPropWithinAt_iff']
  exact and_congr_right <|
    hG.liftPropWithinAt_indep_chart_aux (chart_mem_maximalAtlas _ _) (mem_chart_source _ _) he xe
      (chart_mem_maximalAtlas _ _) (mem_chart_source _ _) hf xf

/-- A version of `liftPropWithinAt_indep_chart`, only for the source. -/
theorem liftPropWithinAt_indep_chart_source [HasGroupoid M G] (he : e ∈ G.maximalAtlas M)
    (xe : x ∈ e.source) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [liftPropWithinAt_self_source, liftPropWithinAt_iff',
    e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe, e.symm_symm]
  refine and_congr Iff.rfl ?_
  rw [Function.comp_apply, e.left_inv xe, ← Function.comp_assoc,
    hG.liftPropWithinAt_indep_chart_source_aux (chartAt _ (g x) ∘ g) (chart_mem_maximalAtlas G x)
      (mem_chart_source _ x) he xe, Function.comp_assoc]

/-- A version of `liftPropWithinAt_indep_chart`, only for the target. -/
theorem liftPropWithinAt_indep_chart_target [HasGroupoid M' G'] (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g) s x := by
  rw [liftPropWithinAt_self_target, liftPropWithinAt_iff', and_congr_right_iff]
  intro hg
  simp_rw [(f.continuousAt xf).comp_continuousWithinAt hg, true_and]
  exact hG.liftPropWithinAt_indep_chart_target_aux (mem_chart_source _ _)
    (chart_mem_maximalAtlas _ _) (mem_chart_source _ _) hf xf hg

/-- A version of `liftPropWithinAt_indep_chart`, that uses `LiftPropWithinAt` on both sides. -/
theorem liftPropWithinAt_indep_chart' [HasGroupoid M G] [HasGroupoid M' G']
    (he : e ∈ G.maximalAtlas M) (xe : x ∈ e.source) (hf : f ∈ G'.maximalAtlas M')
    (xf : g x ∈ f.source) :
    LiftPropWithinAt P g s x ↔
      ContinuousWithinAt g s x ∧ LiftPropWithinAt P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
  rw [hG.liftPropWithinAt_indep_chart he xe hf xf, liftPropWithinAt_self, and_left_comm,
    Iff.comm, and_iff_right_iff_imp]
  intro h
  have h1 := (e.symm.continuousWithinAt_iff_continuousWithinAt_comp_right xe).mp h.1
  have : ContinuousAt f ((g ∘ e.symm) (e x)) := by
    simp_rw [Function.comp, e.left_inv xe, f.continuousAt xf]
  exact this.comp_continuousWithinAt h1

theorem liftPropOn_indep_chart [HasGroupoid M G] [HasGroupoid M' G'] (he : e ∈ G.maximalAtlas M)
    (hf : f ∈ G'.maximalAtlas M') (h : LiftPropOn P g s) {y : H}
    (hy : y ∈ e.target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.source)) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y := by
  convert ((hG.liftPropWithinAt_indep_chart he (e.symm_mapsTo hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]

theorem liftPropWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x := by
  rw [liftPropWithinAt_iff', liftPropWithinAt_iff', continuousWithinAt_inter' ht, hG.congr_set]
  simp_rw [eventuallyEq_set, mem_preimage,
    (chartAt _ x).eventually_nhds' (fun x ↦ x ∈ s ∩ t ↔ x ∈ s) (mem_chart_source _ x)]
  exact (mem_nhdsWithin_iff_eventuallyEq.mp ht).symm.mem_iff

theorem liftPropWithinAt_inter (ht : t ∈ 𝓝 x) :
    LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_inter' (mem_nhdsWithin_of_mem_nhds ht)

theorem liftPropWithinAt_congr_set (hu : s =ᶠ[𝓝 x] t) :
    LiftPropWithinAt P g s x ↔ LiftPropWithinAt P g t x := by
  rw [← hG.liftPropWithinAt_inter (s := s) hu, ← hG.liftPropWithinAt_inter (s := t) hu,
    ← eq_iff_iff]
  congr 1
  aesop

theorem liftPropAt_of_liftPropWithinAt (h : LiftPropWithinAt P g s x) (hs : s ∈ 𝓝 x) :
    LiftPropAt P g x := by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs] at h

theorem liftPropWithinAt_of_liftPropAt_of_mem_nhds (h : LiftPropAt P g x) (hs : s ∈ 𝓝 x) :
    LiftPropWithinAt P g s x := by
  rwa [← univ_inter s, hG.liftPropWithinAt_inter hs]

theorem liftPropOn_of_locally_liftPropOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g (s ∩ u)) : LiftPropOn P g s := by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.liftPropWithinAt_inter] at this
  exact u_open.mem_nhds xu

theorem liftProp_of_locally_liftPropOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g u) :
    LiftProp P g := by
  rw [← liftPropOn_univ]
  refine hG.liftPropOn_of_locally_liftPropOn fun x _ ↦ ?_
  simp [h x]

theorem liftPropWithinAt_congr_of_eventuallyEq (h : LiftPropWithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x := by
  refine ⟨h.1.congr_of_eventuallyEq h₁ hx, ?_⟩
  refine hG.congr_nhdsWithin' ?_
    (by simp_rw [Function.comp_apply, (chartAt H x).left_inv (mem_chart_source H x), hx]) h.2
  simp_rw [EventuallyEq, Function.comp_apply]
  rw [(chartAt H x).eventually_nhdsWithin'
    (fun y ↦ chartAt H' (g' x) (g' y) = chartAt H' (g x) (g y)) (mem_chart_source H x)]
  exact h₁.mono fun y hy ↦ by rw [hx, hy]

theorem liftPropWithinAt_congr_of_eventuallyEq_of_mem (h : LiftPropWithinAt P g s x)
    (h₁ : g' =ᶠ[𝓝[s] x] g) (h₂ : x ∈ s) : LiftPropWithinAt P g' s x :=
  liftPropWithinAt_congr_of_eventuallyEq hG h h₁ (mem_of_mem_nhdsWithin h₂ h₁ :)

theorem liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  ⟨fun h ↦ hG.liftPropWithinAt_congr_of_eventuallyEq h h₁.symm hx.symm,
    fun h ↦ hG.liftPropWithinAt_congr_of_eventuallyEq h h₁ hx⟩

theorem liftPropWithinAt_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) hx

theorem liftPropWithinAt_congr_iff_of_mem (h₁ : ∀ y ∈ s, g' y = g y) (hx : x ∈ s) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (eventually_nhdsWithin_of_forall h₁) (h₁ _ hx)

theorem liftPropWithinAt_congr (h : LiftPropWithinAt P g s x) (h₁ : ∀ y ∈ s, g' y = g y)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ hx).mpr h

theorem liftPropWithinAt_congr_of_mem (h : LiftPropWithinAt P g s x) (h₁ : ∀ y ∈ s, g' y = g y)
    (hx : x ∈ s) : LiftPropWithinAt P g' s x :=
  (hG.liftPropWithinAt_congr_iff h₁ (h₁ _ hx)).mpr h

theorem liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x ↔ LiftPropAt P g x :=
  hG.liftPropWithinAt_congr_iff_of_eventuallyEq (by simp_rw [nhdsWithin_univ, h₁]) h₁.eq_of_nhds

theorem liftPropAt_congr_of_eventuallyEq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g) :
    LiftPropAt P g' x :=
  (hG.liftPropAt_congr_iff_of_eventuallyEq h₁).mpr h

theorem liftPropOn_congr (h : LiftPropOn P g s) (h₁ : ∀ y ∈ s, g' y = g y) : LiftPropOn P g' s :=
  fun x hx ↦ hG.liftPropWithinAt_congr (h x hx) h₁ (h₁ x hx)

theorem liftPropOn_congr_iff (h₁ : ∀ y ∈ s, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s :=
  ⟨fun h ↦ hG.liftPropOn_congr h fun y hy ↦ (h₁ y hy).symm, fun h ↦ hG.liftPropOn_congr h h₁⟩

end

theorem liftPropWithinAt_mono_of_mem_nhdsWithin
    (mono_of_mem_nhdsWithin : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, s ∈ 𝓝[t] x → P f s x → P f t x)
    (h : LiftPropWithinAt P g s x) (hst : s ∈ 𝓝[t] x) : LiftPropWithinAt P g t x := by
  simp only [liftPropWithinAt_iff'] at h ⊢
  refine ⟨h.1.mono_of_mem_nhdsWithin hst, mono_of_mem_nhdsWithin ?_ h.2⟩
  simp_rw [← mem_map, (chartAt H x).symm.map_nhdsWithin_preimage_eq (mem_chart_target H x),
    (chartAt H x).left_inv (mem_chart_source H x), hst]

theorem liftPropWithinAt_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropWithinAt P g s x) (hts : t ⊆ s) : LiftPropWithinAt P g t x := by
  refine ⟨h.1.mono hts, mono (fun y hy ↦ ?_) h.2⟩
  simp only [mfld_simps] at hy
  simp only [hy, hts _, mfld_simps]

theorem liftPropWithinAt_of_liftPropAt (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropAt P g x) : LiftPropWithinAt P g s x := by
  rw [← liftPropWithinAt_univ] at h
  exact liftPropWithinAt_mono mono h (subset_univ _)

theorem liftPropOn_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropOn P g t) (hst : s ⊆ t) : LiftPropOn P g s :=
  fun x hx ↦ liftPropWithinAt_mono mono (h x (hst hx)) hst

theorem liftPropOn_of_liftProp (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftProp P g) : LiftPropOn P g s := by
  rw [← liftPropOn_univ] at h
  exact liftPropOn_mono mono h (subset_univ _)

theorem liftPropAt_of_mem_maximalAtlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) (hx : x ∈ e.source) : LiftPropAt Q e x := by
  simp_rw [LiftPropAt, hG.liftPropWithinAt_indep_chart he hx G.id_mem_maximalAtlas (mem_univ _),
    (e.continuousAt hx).continuousWithinAt, true_and]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)

theorem liftPropOn_of_mem_maximalAtlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) : LiftPropOn Q e e.source := by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds (hG.liftPropAt_of_mem_maximalAtlas hQ he hx)
  exact e.open_source.mem_nhds hx

theorem liftPropAt_symm_of_mem_maximalAtlas [HasGroupoid M G] {x : H}
    (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G)
    (hx : x ∈ e.target) : LiftPropAt Q e.symm x := by
  suffices h : Q (e ∘ e.symm) univ x by
    have : e.symm x ∈ e.source := by simp only [hx, mfld_simps]
    rw [LiftPropAt, hG.liftPropWithinAt_indep_chart G.id_mem_maximalAtlas (mem_univ _) he this]
    refine ⟨(e.symm.continuousAt hx).continuousWithinAt, ?_⟩
    simp only [h, mfld_simps]
  exact hG.congr' (e.eventually_right_inverse hx) (hQ x)

theorem liftPropOn_symm_of_mem_maximalAtlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) (he : e ∈ maximalAtlas M G) : LiftPropOn Q e.symm e.target := by
  intro x hx
  apply hG.liftPropWithinAt_of_liftPropAt_of_mem_nhds
    (hG.liftPropAt_symm_of_mem_maximalAtlas hQ he hx)
  exact e.open_target.mem_nhds hx

theorem liftPropAt_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftPropAt Q (chartAt (H := H) x) x :=
  hG.liftPropAt_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (mem_chart_source H x)

theorem liftPropOn_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftPropOn Q (chartAt (H := H) x) (chartAt (H := H) x).source :=
  hG.liftPropOn_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

theorem liftPropAt_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) : LiftPropAt Q (chartAt (H := H) x).symm ((chartAt H x) x) :=
  hG.liftPropAt_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x) (by simp)

theorem liftPropOn_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id univ y) : LiftPropOn Q (chartAt (H := H) x).symm (chartAt H x).target :=
  hG.liftPropOn_symm_of_mem_maximalAtlas hQ (chart_mem_maximalAtlas G x)

theorem liftPropAt_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y)
    {f : OpenPartialHomeomorph H H} (hf : f ∈ G) {x : H} (hx : x ∈ f.source) : LiftPropAt Q f x :=
  liftPropAt_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf) hx

theorem liftPropOn_of_mem_groupoid (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y)
    {f : OpenPartialHomeomorph H H} (hf : f ∈ G) : LiftPropOn Q f f.source :=
  liftPropOn_of_mem_maximalAtlas hG hQ (G.mem_maximalAtlas_of_mem_groupoid hf)

theorem liftProp_id (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id univ y) :
    LiftProp Q (id : M → M) := by
  simp_rw [liftProp_iff, continuous_id, true_and]
  exact fun x ↦ hG.congr' ((chartAt H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)

theorem liftPropAt_iff_comp_subtype_val (hG : LocalInvariantProp G G' P) {U : Opens M}
    (f : M → M') (x : U) :
    LiftPropAt P f x ↔ LiftPropAt P (f ∘ Subtype.val) x := by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ, U.isOpenEmbedding'.continuousAt_iff]
  · apply hG.congr_iff
    exact (U.chartAt_subtype_val_symm_eventuallyEq).fun_comp (chartAt H' (f x) ∘ f)

theorem liftPropAt_iff_comp_inclusion (hG : LocalInvariantProp G G' P) {U V : Opens M} (hUV : U ≤ V)
    (f : V → M') (x : U) :
    LiftPropAt P f (Set.inclusion hUV x) ↔ LiftPropAt P (f ∘ Set.inclusion hUV : U → M') x := by
  simp only [LiftPropAt, liftPropWithinAt_iff']
  congrm ?_ ∧ ?_
  · simp_rw [continuousWithinAt_univ,
      (TopologicalSpace.Opens.isOpenEmbedding_of_le hUV).continuousAt_iff]
  · apply hG.congr_iff
    exact (TopologicalSpace.Opens.chartAt_inclusion_symm_eventuallyEq hUV).fun_comp
      (chartAt H' (f (Set.inclusion hUV x)) ∘ f)

theorem liftProp_subtype_val {Q : (H → H) → Set H → H → Prop} (hG : LocalInvariantProp G G Q)
    (hQ : ∀ y, Q id univ y) (U : Opens M) :
    LiftProp Q (Subtype.val : U → M) := by
  intro x
  change LiftPropAt Q (id ∘ Subtype.val) x
  rw [← hG.liftPropAt_iff_comp_subtype_val]
  apply hG.liftProp_id hQ

theorem liftProp_inclusion {Q : (H → H) → Set H → H → Prop} (hG : LocalInvariantProp G G Q)
    (hQ : ∀ y, Q id univ y) {U V : Opens M} (hUV : U ≤ V) :
    LiftProp Q (Opens.inclusion hUV : U → V) := by
  intro x
  change LiftPropAt Q (id ∘ Opens.inclusion hUV) x
  rw [← hG.liftPropAt_iff_comp_inclusion hUV]
  apply hG.liftProp_id hQ

end LocalInvariantProp

section LocalStructomorph

variable (G)

open OpenPartialHomeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def IsLocalStructomorphWithinAt (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : OpenPartialHomeomorph H H, e ∈ G ∧ EqOn f e.toFun (s ∩ e.source) ∧ x ∈ e.source

/-- For a groupoid `G` which is `ClosedUnderRestriction`, being a local structomorphism is a local
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
        refine ⟨e.restr (interior u), ?_, ?_, ?_⟩
        · exact closedUnderRestriction' heG isOpen_interior
        · have : s ∩ u ∩ e.source = s ∩ (e.source ∩ u) := by mfld_set_tac
          simpa only [this, interior_interior, hu.interior_eq, mfld_simps] using hef
        · simp only [*, hu.interior_eq, mfld_simps]
    right_invariance' := by
      intro s x f e' he'G he'x h hx
      have hxs : x ∈ s := by simpa only [e'.left_inv he'x, mfld_simps] using hx
      rcases h hxs with ⟨e, heG, hef, hex⟩
      refine ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, ?_, ?_⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.2⟩, mfld_simps]
      · simp only [hex, he'x, mfld_simps]
    congr_of_forall := by
      intro s x f g hfgs _ h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine ⟨e, heG, ?_, hex⟩
      intro y hy
      rw [← hef hy, hfgs y hy.1]
    left_invariance' := by
      intro s x f e' he'G _ hfx h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine ⟨e.trans e', G.trans heG he'G, ?_, ?_⟩
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [hef ⟨hy.1, hy.2.1⟩, mfld_simps]
      · simpa only [hex, hef ⟨hx, hex⟩, mfld_simps] using hfx }

/-- A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open partial homeomorph.
  This gives us an `e` that is defined on a subset of `f.source`. -/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {s : Set H} {x : H}
    (hx : x ∈ f.source ∪ sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x ∈ s → ∃ e : OpenPartialHomeomorph H H,
      e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) (s ∩ e.source) ∧ x ∈ e.source := by
  constructor
  · intro hf h2x
    obtain ⟨e, he, hfe, hxe⟩ := hf h2x
    refine ⟨e.restr f.source, closedUnderRestriction' he f.open_source, ?_, ?_, hxe, ?_⟩
    · simp_rw [OpenPartialHomeomorph.restr_source]
      exact inter_subset_right.trans interior_subset
    · intro x' hx'
      exact hfe ⟨hx'.1, hx'.2.1⟩
    · rw [f.open_source.interior_eq]
      exact Or.resolve_right hx (not_not.mpr h2x)
  · intro hf hx
    obtain ⟨e, he, _, hfe, hxe⟩ := hf hx
    exact ⟨e, he, hfe, hxe⟩

/-- A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open partial homeomorph
and the set we're considering is a superset of `f.source`. -/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_iff' {G : StructureGroupoid H}
    [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {s : Set H} {x : H}
    (hs : f.source ⊆ s) (hx : x ∈ f.source ∪ sᶜ) :
    G.IsLocalStructomorphWithinAt (⇑f) s x ↔
      x ∈ s → ∃ e : OpenPartialHomeomorph H H,
      e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) e.source ∧ x ∈ e.source := by
  rw [f.isLocalStructomorphWithinAt_iff hx]
  refine imp_congr_right fun _ ↦ exists_congr fun e ↦ and_congr_right fun _ ↦ ?_
  refine and_congr_right fun h2e ↦ ?_
  rw [inter_eq_right.mpr (h2e.trans hs)]

/-- A slight reformulation of `IsLocalStructomorphWithinAt` when `f` is an open partial homeomorph
and the set we're considering is `f.source`. -/
theorem _root_.OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    {G : StructureGroupoid H} [ClosedUnderRestriction G] (f : OpenPartialHomeomorph H H) {x : H} :
    G.IsLocalStructomorphWithinAt (⇑f) f.source x ↔
      x ∈ f.source → ∃ e : OpenPartialHomeomorph H H,
      e ∈ G ∧ e.source ⊆ f.source ∧ EqOn f (⇑e) e.source ∧ x ∈ e.source :=
  haveI : x ∈ f.source ∪ f.sourceᶜ := by simp_rw [union_compl_self, mem_univ]
  f.isLocalStructomorphWithinAt_iff' Subset.rfl this

variable {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂] {H₃ : Type*}
  [TopologicalSpace H₃] [ChartedSpace H₁ H₂] [ChartedSpace H₂ H₃] {G₁ : StructureGroupoid H₁}
  [HasGroupoid H₂ G₁] [ClosedUnderRestriction G₁] (G₂ : StructureGroupoid H₂) [HasGroupoid H₃ G₂]

theorem HasGroupoid.comp
    (H : ∀ e ∈ G₂, LiftPropOn (IsLocalStructomorphWithinAt G₁) (e : H₂ → H₂) e.source) :
    @HasGroupoid H₁ _ H₃ _ (ChartedSpace.comp H₁ H₂ H₃) G₁ :=
  let _ := ChartedSpace.comp H₁ H₂ H₃
  { compatible := by
      rintro _ _ ⟨e, he, f, hf, rfl⟩ ⟨e', he', f', hf', rfl⟩
      apply G₁.locality
      intro x hx
      simp only [mfld_simps] at hx
      have hxs : x ∈ f.symm ⁻¹' (e.symm ≫ₕ e').source := by simp only [hx, mfld_simps]
      have hxs' : x ∈ f.target ∩ f.symm ⁻¹' ((e.symm ≫ₕ e').source ∩ e.symm ≫ₕ e' ⁻¹' f'.source) :=
        by simp only [hx, mfld_simps]
      obtain ⟨φ, hφG₁, hφ, hφ_dom⟩ := LocalInvariantProp.liftPropOn_indep_chart
        (isLocalStructomorphWithinAt_localInvariantProp G₁) (G₁.subset_maximalAtlas hf)
        (G₁.subset_maximalAtlas hf') (H _ (G₂.compatible he he')) hxs' hxs
      simp_rw [← OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_assoc] at hφ
      simp_rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      have hs : IsOpen (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').source :=
        (f.symm ≫ₕ e.symm ≫ₕ e' ≫ₕ f').open_source
      refine ⟨_, hs.inter φ.open_source, ?_, ?_⟩
      · simp only [hx, hφ_dom, mfld_simps]
      · refine G₁.mem_of_eqOnSource (closedUnderRestriction' hφG₁ hs) ?_
        rw [OpenPartialHomeomorph.restr_source_inter]
        refine OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source (hφ.mono ?_)
        mfld_set_tac }

end LocalStructomorph

end StructureGroupoid
