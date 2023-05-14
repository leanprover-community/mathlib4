/-
Copyright (c) 2022 Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu

! This file was ported from Lean 3 source module category_theory.cofiltered_system
! leanprover-community/mathlib commit 178a32653e369dce2da68dc6b2694e385d484ef1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Filtered
import Mathbin.Data.Set.Finite
import Mathbin.Topology.Category.Top.Limits.Konig

/-!
# Cofiltered systems

This file deals with properties of cofiltered (and inverse) systems.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventual_range j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.is_mittag_leffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.to_eventual_ranges` is the subfunctor of `F` obtained by restriction
  to `F.eventual_range`.
* `F.to_preimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `is_mittag_leffler.to_preimages`.

## Main statements

* `nonempty_sections_of_finite_cofiltered_system` shows that if `J` is cofiltered and each
  `F.obj j` is nonempty and finite, `F.sections` is nonempty.
* `nonempty_sections_of_finite_inverse_system` is a specialization of the above to `J` being a
   directed set (and `F : Jᵒᵖ ⥤ Type v`).
* `is_mittag_leffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `to_eventual_ranges_surjective` shows that if `F` is Mittag-Leffler, then `F.to_eventual_ranges`
  has all morphisms `F.map f` surjective.

## Todo

* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/


universe u v w

open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes

section FiniteKonig

/-- This bootstraps `nonempty_sections_of_finite_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `Top.nonempty_limit_cone_of_compact_t2_inverse_system`. -/
theorem NonemptySectionsOfFiniteCofilteredSystem.init {J : Type u} [SmallCategory J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : ∀ j, Finite (F.obj j)]
    [hne : ∀ j, Nonempty (F.obj j)] : F.sections.Nonempty :=
  by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  haveI : ∀ j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  haveI : ∀ j, Finite (F'.obj j) := hf
  haveI : ∀ j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system F'
  exact ⟨u, fun _ _ => hu⟩
#align nonempty_sections_of_finite_cofiltered_system.init NonemptySectionsOfFiniteCofilteredSystem.init

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty :=
  by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := as_small.down
  let F' : J' ⥤ Type max u v w := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  haveI : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  haveI : ∀ i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  cases isEmpty_or_nonempty J
  · fconstructor <;> exact isEmptyElim
  haveI : is_cofiltered J := ⟨⟩
  obtain ⟨u, hu⟩ := NonemptySectionsOfFiniteCofilteredSystem.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [as_small.down, functor.comp_map, ulift_functor_map, functor.op_map] at h
  simp_rw [← h]
  rfl
#align nonempty_sections_of_finite_cofiltered_system nonempty_sections_of_finite_cofiltered_system

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (F : Jᵒᵖ ⥤ Type v) [∀ j : Jᵒᵖ, Finite (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := by
  cases isEmpty_or_nonempty J
  · haveI : IsEmpty Jᵒᵖ := ⟨fun j => isEmptyElim j.unop⟩
    -- TODO: this should be a global instance
    exact ⟨isEmptyElim, isEmptyElim⟩
  · exact nonempty_sections_of_finite_cofiltered_system _
#align nonempty_sections_of_finite_inverse_system nonempty_sections_of_finite_inverse_system

end FiniteKonig

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

/-- The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)
#align category_theory.functor.eventual_range CategoryTheory.Functor.eventualRange

theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_interᵢ₂
#align category_theory.functor.mem_eventual_range_iff CategoryTheory.Functor.mem_eventualRange_iff

/-- The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `is_mittag_leffler_iff_eventual_range`), the eventual range at `j` is attained
by some `f : i ⟶ j`.
-/
def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _)(f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
#align category_theory.functor.is_mittag_leffler CategoryTheory.Functor.IsMittagLeffler

theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _)(f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun j =>
    exists₂_congr fun i f =>
      ⟨fun h => (interᵢ₂_subset _ _).antisymm <| subset_interᵢ₂ h, fun h => h ▸ interᵢ₂_subset⟩
#align category_theory.functor.is_mittag_leffler_iff_eventual_range CategoryTheory.Functor.isMittagLeffler_iff_eventualRange

theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j :=
  by
  obtain ⟨k, g, hg⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventual_range_iff.1 hx (g ≫ f)
  refine' ⟨_, ⟨x, rfl⟩, by simpa only [F.map_comp] ⟩
#align category_theory.functor.is_mittag_leffler.subset_image_eventual_range CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange

theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) :=
  by
  apply subset_antisymm
  · apply Inter₂_subset
  · rw [h, F.map_comp]
    apply range_comp_subset_range
#align category_theory.functor.eventual_range_eq_range_precomp CategoryTheory.Functor.eventualRange_eq_range_precomp

theorem isMittagLeffler_of_surjective (h : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) :
    F.IsMittagLeffler := fun j =>
  ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩
#align category_theory.functor.is_mittag_leffler_of_surjective CategoryTheory.Functor.isMittagLeffler_of_surjective

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps]
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map j k g :=
    MapsTo.restrict (F.map g) _ _ fun x h =>
      by
      rw [mem_Inter] at h⊢; intro f
      rw [← mem_preimage, preimage_preimage]
      convert h (g ≫ f); rw [F.map_comp]; rfl
  map_id' j := by
    simp_rw [F.map_id]
    ext
    rfl
  map_comp' j k l f g := by
    simp_rw [F.map_comp]
    rfl
#align category_theory.functor.to_preimages CategoryTheory.Functor.toPreimages

instance toPreimages_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite ((F.toPreimages s).obj j) :=
  fun j => Subtype.finite
#align category_theory.functor.to_preimages_finite CategoryTheory.Functor.toPreimages_finite

variable [IsCofilteredOrEmpty J]

theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx =>
  by
  rw [mem_eventual_range_iff] at hx⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← map_comp_apply, he, F.map_comp]
  exact ⟨_, rfl⟩
#align category_theory.functor.eventual_range_maps_to CategoryTheory.Functor.eventualRange_mapsTo

theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
  (h.subset_image_eventualRange F f).antisymm <| mapsTo'.1 (F.eventualRange_mapsTo f)
#align category_theory.functor.is_mittag_leffler.eq_image_eventual_range CategoryTheory.Functor.IsMittagLeffler.eq_image_eventualRange

theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) :=
  by
  rw [subset_antisymm_iff, eventual_range, and_iff_right (Inter₂_subset _ _), subset_Inter₂_iff]
  refine' ⟨fun h k g => h _ _, fun h j' f' => _⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine' (h g).trans _
  rw [he, F.map_comp]
  apply range_comp_subset_range
#align category_theory.functor.eventual_range_eq_iff CategoryTheory.Functor.eventualRange_eq_iff

theorem isMittagLeffler_iff_subset_range_comp :
    F.IsMittagLeffler ↔
      ∀ j : J, ∃ (i : _)(f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) :=
  by simp_rw [is_mittag_leffler_iff_eventual_range, eventual_range_eq_iff]
#align category_theory.functor.is_mittag_leffler_iff_subset_range_comp CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp

theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j =>
    by
    obtain ⟨j₁, g₁, f₁, -⟩ := cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.is_mittag_leffler_iff_eventual_range.1 h j₁
    refine' ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => _⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x ∈ F.eventual_range j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventual_range F (f₃ ≫ f₂) this
    refine' ⟨⟨y, mem_Inter.2 fun g₂ => _⟩, Subtype.ext _⟩
    · obtain ⟨j₄, f₄, h₄⟩ := cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      obtain ⟨y, rfl⟩ := F.mem_eventual_range_iff.1 hy f₄
      rw [← map_comp_apply] at h₃
      rw [mem_preimage, ← map_comp_apply, h₄, ← category.assoc, map_comp_apply, h₃, ←
        map_comp_apply]
      apply mem_Inter.1 hx
    · simp_rw [to_preimages_map, maps_to.coe_restrict_apply, Subtype.coe_mk]
      rw [← category.assoc, map_comp_apply, h₃, map_comp_apply]
#align category_theory.functor.is_mittag_leffler.to_preimages CategoryTheory.Functor.IsMittagLeffler.toPreimages

theorem isMittagLeffler_of_exists_finite_range
    (h : ∀ j : J, ∃ (i : _)(f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := fun j =>
  by
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ :=
    finset.is_well_founded_lt.wf.has_min
      { s : Finset (F.obj j) | ∃ (i : _)(f : i ⟶ j), ↑s = range (F.map f) }
      ⟨_, i, hi, hf.coe_to_finset⟩
  refine'
    ⟨i, f, fun k g =>
      (directed_on_range.mp <| F.ranges_directed j).is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ _ _
        ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  refine' (eq_of_le_of_not_lt hl _).ge
  have := hmin _ ⟨k', g', (m.finite_to_set.subset <| hm.substr hl).coe_toFinset⟩
  rwa [Finset.lt_iff_ssubset, ← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this
#align category_theory.functor.is_mittag_leffler_of_exists_finite_range CategoryTheory.Functor.isMittagLeffler_of_exists_finite_range

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index.
-/
@[simps]
def toEventualRanges : J ⥤ Type v
    where
  obj j := F.eventualRange j
  map i j f := (F.eventualRange_mapsTo f).restrict _ _ _
  map_id' i := by
    simp_rw [F.map_id]
    ext
    rfl
  map_comp' _ _ _ _ _ := by
    simp_rw [F.map_comp]
    rfl
#align category_theory.functor.to_eventual_ranges CategoryTheory.Functor.toEventualRanges

instance toEventualRanges_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite (F.toEventualRanges.obj j) :=
  fun j => Subtype.finite
#align category_theory.functor.to_eventual_ranges_finite CategoryTheory.Functor.toEventualRanges_finite

/-- The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.eventual_ranges`.
-/
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections
    where
  toFun s := ⟨_, fun i j f => Subtype.coe_inj.2 <| s.Prop f⟩
  invFun s :=
    ⟨fun j => ⟨_, mem_interᵢ₂.2 fun i f => ⟨_, s.Prop f⟩⟩, fun i j f => Subtype.ext <| s.Prop f⟩
  left_inv _ := by
    ext
    rfl
  right_inv _ := by
    ext
    rfl
#align category_theory.functor.to_eventual_ranges_sections_equiv CategoryTheory.Functor.toEventualRangesSectionsEquiv

/--
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a surjective
functor.
-/
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) :
    (F.toEventualRanges.map f).Surjective := fun ⟨x, hx⟩ =>
  by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventual_range F f hx
  exact ⟨⟨y, hy⟩, rfl⟩
#align category_theory.functor.surjective_to_eventual_ranges CategoryTheory.Functor.surjective_toEventualRanges

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.to_eventual_ranges`. -/
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [∀ j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) :=
  by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [to_eventual_ranges_obj, h]
  infer_instance
#align category_theory.functor.to_eventual_ranges_nonempty CategoryTheory.Functor.toEventualRanges_nonempty

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
theorem thin_diagram_of_surjective (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) {i j}
    (f g : i ⟶ j) : F.map f = F.map g :=
  let ⟨k, φ, hφ⟩ := cone_maps f g
  (Fsur φ).injective_comp_right <| by simp_rw [← types_comp, ← F.map_comp, hφ]
#align category_theory.functor.thin_diagram_of_surjective CategoryTheory.Functor.thin_diagram_of_surjective

theorem toPreimages_nonempty_of_surjective [hFn : ∀ j : J, Nonempty (F.obj j)]
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) (hs : s.Nonempty) (j) :
    Nonempty ((F.toPreimages s).obj j) :=
  by
  simp only [to_preimages_obj, nonempty_coe_sort, nonempty_Inter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji' ji).symm ▸ ys⟩
#align category_theory.functor.to_preimages_nonempty_of_surjective CategoryTheory.Functor.toPreimages_nonempty_of_surjective

theorem eval_section_injective_of_eventually_injective {j}
    (Finj : ∀ (i) (f : i ⟶ j), (F.map f).Injective) (i) (f : i ⟶ j) :
    (fun s : F.sections => s.val j).Injective :=
  by
  refine' fun s₀ s₁ h => Subtype.ext <| funext fun k => _
  obtain ⟨m, mi, mk, _⟩ := cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f), ← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk, ← s₁.prop mk]
  refine' congr_arg _ (Finj m (mi ≫ f) h)
#align category_theory.functor.eval_section_injective_of_eventually_injective CategoryTheory.Functor.eval_section_injective_of_eventually_injective

section FiniteCofilteredSystem

variable [∀ j : J, Nonempty (F.obj j)] [∀ j : J, Finite (F.obj j)]
  (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective)

include Fsur

theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x =>
  by
  let s : Set (F.obj i) := {x}
  haveI := F.to_preimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.to_preimages s)
  refine' ⟨⟨fun j => (sec j).val, fun j k jk => by simpa [Subtype.ext_iff] using h jk⟩, _⟩
  · have := (sec i).Prop
    simp only [mem_Inter, mem_preimage, mem_singleton_iff] at this
    replace this := this (𝟙 i)
    rwa [map_id_apply] at this
#align category_theory.functor.eval_section_surjective_of_surjective CategoryTheory.Functor.eval_section_surjective_of_surjective

theorem eventually_injective [Nonempty J] [Finite F.sections] :
    ∃ j, ∀ (i) (f : i ⟶ j), (F.map f).Injective :=
  by
  haveI : ∀ j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  haveI : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : ∀ j, Fintype.card (F.obj j) ≤ Fintype.card F.sections := fun j =>
    Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surjective Fsur j)
  let fn j := Fintype.card F.sections - Fintype.card (F.obj j)
  refine'
    ⟨fn.argmin nat.well_founded_lt.wf, fun i f =>
      ((Fintype.bijective_iff_surjective_and_card _).2
          ⟨Fsur f, le_antisymm _ (Fintype.card_le_of_surjective _ <| Fsur f)⟩).1⟩
  rw [← Nat.sub_sub_self (card_le i), tsub_le_iff_tsub_le]
  apply fn.argmin_le
#align category_theory.functor.eventually_injective CategoryTheory.Functor.eventually_injective

end FiniteCofilteredSystem

end Functor

end CategoryTheory

