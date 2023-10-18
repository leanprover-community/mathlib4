/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Topology.IsLocallyHomeomorph
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.UnitInterval

#align_import topology.covering from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `Trivialization` of `f` at `x` with fiber `I`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/


open Bundle

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet
#align is_evenly_covered IsEvenlyCovered

namespace IsEvenlyCovered

variable {f}

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm
#align is_evenly_covered.to_trivialization IsEvenlyCovered.toTrivialization

theorem mem_toTrivialization_baseSet {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : x ∈ h.toTrivialization.baseSet :=
  Classical.choose_spec h.2
#align is_evenly_covered.mem_to_trivialization_base_set IsEvenlyCovered.mem_toTrivialization_baseSet

theorem toTrivialization_apply {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toLocalEquiv.eq_symm_apply (e.mem_source.mpr h)
            (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm
#align is_evenly_covered.to_trivialization_apply IsEvenlyCovered.toTrivialization_apply

protected theorem continuousAt {x : E} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
#align is_evenly_covered.continuous_at IsEvenlyCovered.continuousAt

theorem to_isEvenlyCovered_preimage {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨_, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph
          (Classical.choose_spec h2)).embedding.discreteTopology,
    _, h.mem_toTrivialization_baseSet⟩
#align is_evenly_covered.to_is_evenly_covered_preimage IsEvenlyCovered.to_isEvenlyCovered_preimage

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map_on IsCoveringMapOn

namespace IsCoveringMapOn

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩
#align is_covering_map_on.mk IsCoveringMapOn.mk

variable {f} {s}

protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x :=
  (hf (f x) hx).continuousAt
#align is_covering_map_on.continuous_at IsCoveringMapOn.continuousAt

protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  ContinuousAt.continuousOn fun _ => hf.continuousAt
#align is_covering_map_on.continuous_on IsCoveringMapOn.continuousOn

protected theorem isLocallyHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocallyHomeomorphOn f (f ⁻¹' s) := by
  refine' IsLocallyHomeomorphOn.mk f (f ⁻¹' s) fun x hx => _
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine'
    ⟨e.toLocalHomeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.baseSet ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.baseSet
          open_source :=
            e.open_baseSet.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_baseSet
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p _ => rfl
          continuous_toFun := continuous_fst.continuousOn
          continuous_invFun := (continuous_id'.prod_mk continuous_const).continuousOn },
      ⟨he, by rwa [e.toLocalHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩
#align is_covering_map_on.is_locally_homeomorph_on IsCoveringMapOn.isLocallyHomeomorphOn

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map IsCoveringMap

variable {f}

theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]
#align is_covering_map_iff_is_covering_map_on_univ isCoveringMap_iff_isCoveringMapOn_univ

protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf
#align is_covering_map.is_covering_map_on IsCoveringMap.isCoveringMapOn

variable (f)

namespace IsCoveringMap

theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (IsCoveringMapOn.mk f Set.univ F (fun x _ => e x) fun x _ => h x)
#align is_covering_map.mk IsCoveringMap.mk

variable {f}

protected theorem continuous (hf : IsCoveringMap f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.isCoveringMapOn.continuousOn
#align is_covering_map.continuous IsCoveringMap.continuous

protected theorem isLocallyHomeomorph (hf : IsCoveringMap f) : IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocallyHomeomorphOn
#align is_covering_map.is_locally_homeomorph IsCoveringMap.isLocallyHomeomorph

protected theorem isOpenMap (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.isLocallyHomeomorph.isOpenMap
#align is_covering_map.is_open_map IsCoveringMap.isOpenMap

protected theorem quotientMap (hf : IsCoveringMap f) (hf' : Function.Surjective f) :
    QuotientMap f :=
  hf.isOpenMap.to_quotientMap hf.continuous hf'
#align is_covering_map.quotient_map IsCoveringMap.quotientMap

end IsCoveringMap

variable {f}

protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
#align is_fiber_bundle.IsCoveringMap IsFiberBundle.isCoveringMap

protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩
#align fiber_bundle.IsCoveringMap FiberBundle.isCoveringMap

namespace isCoveringMap



lemma clopen_set_intersect_ConnectedComponents_whole_set (Y: Type*) [TopologicalSpace Y]
  (S : Set Y) (hS : IsClopen S) (w : ∀ x : Y, ∃ y ∈ connectedComponent x, y ∈ S) :
  S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hy, h⟩ := w x
  exact hS.connectedComponent_subset h (connectedComponent_eq hy ▸ mem_connectedComponent)


open TopologicalSpace

lemma is_open_inter_of_coe_preim {X : Type*} [TopologicalSpace X] (s t : Set X) (hs : IsOpen s)
  (h : IsOpen (((↑)  : s → X) ⁻¹' t)) : IsOpen (t ∩ s) := by
  let ⟨a, b, c⟩ := inducing_subtype_val.isOpen_iff.mp h
  exact Subtype.preimage_coe_eq_preimage_coe_iff.mp c ▸ b.inter hs

lemma is_open_of_is_open_coe (Y:Type*) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ nhds x), IsOpen (((↑) : U → Y) ⁻¹' A)) : IsOpen A := by
  refine' isOpen_iff_forall_mem_open.mpr (fun x hx => _)
  let ⟨U, hU1, hU2⟩ := hA x
  let ⟨V, hV1, hV2, hV3⟩ := mem_nhds_iff.mp hU1
  exact ⟨A ∩ V, Set.inter_subset_left A V,
    is_open_inter_of_coe_preim V A hV2 ((continuous_inclusion hV1).isOpen_preimage _ hU2), hx, hV3⟩

lemma is_closed_of_is_closed_coe (Y:Type*) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ nhds x), IsClosed (((↑ ) : U → Y) ⁻¹' A)) : IsClosed A :=
 ⟨ is_open_of_is_open_coe Y Aᶜ (fun x  => by
 let ⟨U, hU,hN⟩ := hA x
 exact ⟨ U,  hU , hN.1 ⟩) ⟩

lemma is_clopen_of_is_clopen_coe (Y:Type*) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ nhds x), IsClopen (((↑ ) : U → Y) ⁻¹' A)) : IsClopen A :=
⟨is_open_of_is_open_coe  Y A (fun x => by
let  ⟨ z,hz,hhz⟩:= hA x
exact ⟨ z,hz,hhz.1⟩  ) ,
 is_closed_of_is_closed_coe  Y A (fun x => by
 let ⟨z,hz,hhz⟩:= hA x
 exact ⟨ z,hz,hhz.2⟩  )⟩

theorem clopen_equalizer_of_discrete {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [DiscreteTopology Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
  IsClopen {x : X | f x = g x} := (isClopen_discrete (Set.diagonal Y)).preimage (hf.prod_mk hg)


lemma tautology : true := by rw [Bool.eq_iff_iff]

theorem uniqueness_of_homotopy_lifting (Y : Type*) [TopologicalSpace Y] (hf : IsCoveringMap f)
  (H₁ H₂ : ContinuousMap Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) :
  H₁ = H₂ := by
  refine' FunLike.ext H₁ H₂ (Set.eq_univ_iff_forall.mp
    (clopen_set_intersect_ConnectedComponents_whole_set _ _
    (is_clopen_of_is_clopen_coe _ _ (fun x => _)) hC))


  let t := (hf (f (H₁ x))).toTrivialization
  let U := (f ∘ H₁) ⁻¹' t.baseSet
  refine' ⟨U, (t.open_baseSet.preimage (hf.continuous.comp H₁.continuous)).mem_nhds
    ((hf (f (H₁ x)))).mem_toTrivialization_baseSet, _⟩
  change IsClopen {y : U | H₁ y = H₂ y}
  have h0 : ∀ y : U, f (H₁ y) = f (H₂ y) := fun y => congr_fun h y
  have h1 : ∀ y : U, f (H₁ y) ∈ t.baseSet := Subtype.prop
  have h2 : ∀ y : U, f (H₂ y) ∈ t.baseSet := fun y => h0 y ▸ h1 y
  have key : ∀ y : U, H₁ y = H₂ y ↔ (t (H₁ y)).2 = (t (H₂ y)).2
  { refine' fun y => ⟨congr_arg (Prod.snd ∘ t), fun m => _⟩
    have h0 : f (H₁ y) = f (H₂ y) := congr_fun h y
    rw [←t.coe_fst' (h1 y), ←t.coe_fst' (h2 y)] at h0
    refine' t.injOn (t.mem_source.mpr (h1 y)) (t.mem_source.mpr (h2 y)) (Prod.ext h0 m) }
  simp_rw [key]
  haveI := (hf (f (H₁ x))).1
  simp only [←t.mem_source] at h1 h2
  refine' clopen_equalizer_of_discrete
    (continuous_snd.comp (t.continuous_toFun.comp_continuous (H₁.2.comp continuous_subtype_val) h1))
     (continuous_snd.comp (t.continuous_toFun.comp_continuous (H₂.2.comp continuous_subtype_val) h2))

lemma connected_uniqueness_of_homotopy_lifting (Y : Type*)[TopologicalSpace Y]  [ConnectedSpace Y]
    (hf : IsCoveringMap f)(y:Y)
    (H₁ H₂ : ContinuousMap Y E) (h : f ∘ H₁ = f ∘ H₂)
    (hC : H₁ y = H₂ y) : H₁ = H₂ := by
  refine' uniqueness_of_homotopy_lifting Y hf H₁ H₂ h (fun x:Y => ⟨y,_⟩ )
  rw [PreconnectedSpace.connectedComponent_eq_univ x]
  exact { left := trivial, right := hC }

open unitInterval


/-


      if hS : S.Nonempty then ⟨sSup ((↑) '' S), by
      refine' ⟨_, csSup_le (hS.image (↑)) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.2)⟩
      obtain ⟨c, hc⟩ := hS
      exact c.2.1.trans (le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩)⟩
    else ⟨a, le_rfl, h⟩
    -/

open Classical

noncomputable def tada1 {α : Type*} [ConditionallyCompleteLattice α] {a b : α} (h : a ≤ b) :
    CompleteLattice (Set.Icc a b) :=
{ Set.Icc.boundedOrder h with
  sSup := fun S ↦ if hS : S = ∅ then ⟨a, le_rfl, h⟩ else ⟨sSup ((↑) '' S), by
    rw [←Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine' ⟨_, csSup_le (hS.image (↑)) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.2)⟩
    obtain ⟨c, hc⟩ := hS
    exact c.2.1.trans (le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩)⟩
  le_sSup := by
    intro S c hc
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · simp [hS] at hc
    · exact le_csSup ⟨b, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.2⟩ ⟨c, hc, rfl⟩
  sSup_le := by
    intro S c hc
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · exact c.2.1
    · exact csSup_le ((Set.nonempty_iff_ne_empty.mpr hS).image (↑))
        (fun _ ⟨d, h, hd⟩ ↦ hd ▸ hc d h)
  sInf := fun S ↦ if hS : S = ∅ then ⟨b, h, le_rfl⟩ else ⟨sInf ((↑) '' S), by
    rw [←Set.not_nonempty_iff_eq_empty, not_not] at hS
    refine' ⟨le_csInf (hS.image (↑)) (fun _ ⟨c, _, hc⟩ ↦ hc ▸ c.2.1), _⟩
    obtain ⟨c, hc⟩ := hS
    exact le_trans (csInf_le ⟨a, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩) c.2.2⟩
  sInf_le := by
    intro S c hc
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · simp [hS] at hc
    · exact csInf_le ⟨a, fun _ ⟨d, _, hd⟩ ↦ hd ▸ d.2.1⟩ ⟨c, hc, rfl⟩
  le_sInf := by
    intro S c hc
    by_cases hS : S = ∅ <;> simp only [hS, dite_true, dite_false]
    · exact c.2.2
    · exact le_csInf ((Set.nonempty_iff_ne_empty.mpr hS).image (↑))
        (fun _ ⟨d, h, hd⟩ ↦ hd ▸ hc d h) }

noncomputable instance tada2 {α : Type*} [ConditionallyCompleteLinearOrder α] {a b : α} (h : a ≤ b) :
    CompleteLinearOrder (Set.Icc a b) :=
{ tada1 h, Subtype.linearOrder _ with }

lemma real_key_lemma {α : Type*} [CompleteLinearOrder α] (S : Set α)
    (convex : ∀ x y, x ≤ y → y ∈ S → x ∈ S)
    (interior : ∀ x, (∀ y < x, y ∈ S) → ∃ z > x, z ∈ S) : S = Set.univ := by

  sorry

lemma key_lemma (b : Set I) (convex : ∀ x y, x ≤ y → y ∈ b → x ∈ b)
    (interior : ∀ x, (∀ y < x, y ∈ b) → ∃ z > x, z ∈ b) : b = Set.univ :=
  real_key_lemma b convex interior

lemma existence_of_path_lifting (hf : IsCoveringMap f)
  (p : ContinuousMap I X) (x':E) (hx': f x' = p 0): ∃ P : ContinuousMap I E, f ∘ P = p ∧ P 0 = x'  := by
  let b := {r:I | ∃Q:ContinuousMap (Set.Icc 0 r) E, f∘Q = p ∘ Subtype.val ∧ Q ⟨ 0, Set.left_mem_Icc.2 (r.2.1)⟩ = x'}
  have : 0 ∈ b := by
    use ContinuousMap.const _ x'
    constructor
    ext x
    change f x' = p x
    have : (x:I) = 0
    exact le_antisymm x.2.2 x.2.1
    rwa [this]
    rfl


  have convex: ∀ x y:I, x≤ y∧y ∈ b → x∈ b := by
    intro x y ⟨ζ ,r,hr₁,hr₂⟩
    rw [Set.mem_setOf_eq]
    let ι :(Set.Icc 0 x) → (Set.Icc 0 y) := Set.inclusion (Set.Icc_subset_Icc_right ζ )
    let ρ : Continuous ι := continuous_inclusion (Set.Icc_subset_Icc_right ζ )
    use ⟨ r∘ ι, r.2.comp ρ⟩
    constructor
    rw[Function.funext_iff] at hr₁ ⊢
    exact fun ξ ↦ hr₁ ( ι (ξ))
    exact hr₂

  have interior: ∀ x: I, (∀ y, y<x → y∈b ) → ∃ z: I,x<z∧ z∈ b




  let U := (hf (p 0)).toTrivialization






end isCoveringMap
