/-
Copyright (c) 2022 Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu
-/
import Mathlib.CategoryTheory.Filtered
import Mathlib.Data.Set.Finite
import Mathlib.Topology.Category.TopCat.Limits.Konig

#align_import category_theory.cofiltered_system from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!
# Cofiltered systems

This file deals with properties of cofiltered (and inverse) systems.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventualRange j` is the intersections of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.IsMittagLeffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.toEventualRanges` is the subfunctor of `F` obtained by restriction
  to `F.eventualRange`.
* `F.toPreimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `IsMittagLeffler.toPreimages`.

## Main statements

* `nonempty_sections_of_finite_cofiltered_system` shows that if `J` is cofiltered and each
  `F.obj j` is nonempty and finite, `F.sections` is nonempty.
* `nonempty_sections_of_finite_inverse_system` is a specialization of the above to `J` being a
   directed set (and `F : Jᵒᵖ ⥤ Type v`).
* `isMittagLeffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `surjective_toEventualRanges` shows that if `F` is Mittag-Leffler, then `F.toEventualRanges`
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
corollary to `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`. -/
theorem nonempty_sections_of_finite_cofiltered_system.init {J : Type u} [SmallCategory J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : ∀ j, Finite (F.obj j)]
    [hne : ∀ j, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  -- ⊢ Set.Nonempty (Functor.sections F)
  haveI : ∀ j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  -- ⊢ Set.Nonempty (Functor.sections F)
  haveI : ∀ j, Finite (F'.obj j) := hf
  -- ⊢ Set.Nonempty (Functor.sections F)
  haveI : ∀ j, Nonempty (F'.obj j) := hne
  -- ⊢ Set.Nonempty (Functor.sections F)
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  -- ⊢ Set.Nonempty (Functor.sections F)
  exact ⟨u, hu⟩
  -- 🎉 no goals
#align nonempty_sections_of_finite_cofiltered_system.init nonempty_sections_of_finite_cofiltered_system.init

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  -- ⊢ Set.Nonempty (Functor.sections F)
  let down : J' ⥤ J := AsSmall.down
  -- ⊢ Set.Nonempty (Functor.sections F)
  let F' : J' ⥤ Type max u v w := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  -- ⊢ Set.Nonempty (Functor.sections F)
  haveI : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  -- ⊢ Set.Nonempty (Functor.sections F)
  haveI : ∀ i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) Equiv.ulift.symm
  -- ⊢ Set.Nonempty (Functor.sections F)
  -- Step 2: apply the bootstrap theorem
  cases isEmpty_or_nonempty J
  -- ⊢ Set.Nonempty (Functor.sections F)
  · fconstructor <;> apply isEmptyElim
    -- ⊢ (j : J) → F.obj j
                     -- 🎉 no goals
                     -- 🎉 no goals
  haveI : IsCofiltered J := ⟨⟩
  -- ⊢ Set.Nonempty (Functor.sections F)
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system.init F'
  -- ⊢ Set.Nonempty (Functor.sections F)
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  -- ⊢ (fun j => (u { down := j }).down) ∈ Functor.sections F
  intro j j' f
  -- ⊢ F.map f ((fun j => (u { down := j }).down) j) = (fun j => (u { down := j }). …
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  -- ⊢ F.map f ((fun j => (u { down := j }).down) j) = (fun j => (u { down := j }). …
  simp only [AsSmall.down, Functor.comp_map, uliftFunctor_map, Functor.op_map] at h
  -- ⊢ F.map f ((fun j => (u { down := j }).down) j) = (fun j => (u { down := j }). …
  simp_rw [← h]
  -- 🎉 no goals
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
  -- ⊢ Set.Nonempty (Functor.sections F)
  · haveI : IsEmpty Jᵒᵖ := ⟨fun j => isEmptyElim j.unop⟩ -- TODO: this should be a global instance
    -- ⊢ Set.Nonempty (Functor.sections F)
    exact ⟨isEmptyElim, by apply isEmptyElim⟩
    -- 🎉 no goals
  · exact nonempty_sections_of_finite_cofiltered_system _
    -- 🎉 no goals
#align nonempty_sections_of_finite_inverse_system nonempty_sections_of_finite_inverse_system

end FiniteKonig

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

/-- The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`. -/
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)
#align category_theory.functor.eventual_range CategoryTheory.Functor.eventualRange

theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_iInter₂
#align category_theory.functor.mem_eventual_range_iff CategoryTheory.Functor.mem_eventualRange_iff

/-- The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `isMittagLeffler_iff_eventualRange`), the eventual range at `j` is attained
by some `f : i ⟶ j`. -/
def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _) (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
#align category_theory.functor.is_mittag_leffler CategoryTheory.Functor.IsMittagLeffler

theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
      ⟨fun h => (iInter₂_subset _ _).antisymm <| subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩
#align category_theory.functor.is_mittag_leffler_iff_eventual_range CategoryTheory.Functor.isMittagLeffler_iff_eventualRange

theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j := by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  -- ⊢ eventualRange F i ⊆ F.map f '' eventualRange F j
  rw [hg]; intro x hx
  -- ⊢ eventualRange F i ⊆ F.map f '' range (F.map g)
           -- ⊢ x ∈ F.map f '' range (F.map g)
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  -- ⊢ F.map (g ≫ f) x ∈ F.map f '' range (F.map g)
  refine' ⟨_, ⟨x, rfl⟩, by rw [map_comp_apply] ⟩
  -- 🎉 no goals
#align category_theory.functor.is_mittag_leffler.subset_image_eventual_range CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange

theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) := by
  apply subset_antisymm
  -- ⊢ eventualRange F k ⊆ range (F.map (f ≫ g))
  · apply iInter₂_subset
    -- 🎉 no goals
  · rw [h, F.map_comp]
    -- ⊢ range (F.map f ≫ F.map g) ⊆ range (F.map g)
    apply range_comp_subset_range
    -- 🎉 no goals
#align category_theory.functor.eventual_range_eq_range_precomp CategoryTheory.Functor.eventualRange_eq_range_precomp

theorem isMittagLeffler_of_surjective (h : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) :
    F.IsMittagLeffler :=
  fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩
                                  -- 🎉 no goals
#align category_theory.functor.is_mittag_leffler_of_surjective CategoryTheory.Functor.isMittagLeffler_of_surjective

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps]
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    -- ⊢ ∀ (i_1 : Y✝ ⟶ i), F.map g x ∈ F.map i_1 ⁻¹' s
    intro f
    -- ⊢ F.map g x ∈ F.map f ⁻¹' s
    rw [← mem_preimage, preimage_preimage, mem_preimage]
    -- ⊢ F.map f (F.map g x) ∈ s
    convert h (g ≫ f); rw [F.map_comp]; rfl
    -- ⊢ F.map f (F.map g x) ∈ s ↔ x ∈ F.map (g ≫ f) ⁻¹' s
                       -- ⊢ F.map f (F.map g x) ∈ s ↔ x ∈ (F.map g ≫ F.map f) ⁻¹' s
                                        -- 🎉 no goals
  map_id j := by
    simp_rw [MapsTo.restrict, Subtype.map, F.map_id]
    -- ⊢ (fun x => { val := 𝟙 (F.obj j) ↑x, property := (_ : (fun x => x ∈ ⋂ (f : j ⟶ …
    ext
    -- ⊢ ↑{ val := 𝟙 (F.obj j) ↑a✝, property := (_ : (fun x => x ∈ ⋂ (f : j ⟶ i), F.m …
    rfl
    -- 🎉 no goals
  map_comp f g := by
    simp_rw [MapsTo.restrict, Subtype.map, F.map_comp]
    -- ⊢ (fun x => { val := (F.map f ≫ F.map g) ↑x, property := (_ : (fun x => x ∈ ⋂  …
    rfl
    -- 🎉 no goals
#align category_theory.functor.to_preimages CategoryTheory.Functor.toPreimages

instance toPreimages_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite ((F.toPreimages s).obj j) :=
  fun _ => Subtype.finite
#align category_theory.functor.to_preimages_finite CategoryTheory.Functor.toPreimages_finite

variable [IsCofilteredOrEmpty J]

theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  -- ⊢ ∀ ⦃i_1 : J⦄ (f_1 : i_1 ⟶ i), F.map f x ∈ range (F.map f_1)
  intro k f'
  -- ⊢ F.map f x ∈ range (F.map f')
  obtain ⟨l, g, g', he⟩ := cospan f f'
  -- ⊢ F.map f x ∈ range (F.map f')
  obtain ⟨x, rfl⟩ := hx g
  -- ⊢ F.map f (F.map g x) ∈ range (F.map f')
  rw [← map_comp_apply, he, F.map_comp]
  -- ⊢ (F.map g' ≫ F.map f') x ∈ range (F.map f')
  exact ⟨_, rfl⟩
  -- 🎉 no goals
#align category_theory.functor.eventual_range_maps_to CategoryTheory.Functor.eventualRange_mapsTo

theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
  (h.subset_image_eventualRange F f).antisymm <| mapsTo'.1 (F.eventualRange_mapsTo f)
#align category_theory.functor.is_mittag_leffler.eq_image_eventual_range CategoryTheory.Functor.IsMittagLeffler.eq_image_eventualRange

theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  rw [subset_antisymm_iff, eventualRange, and_iff_right (iInter₂_subset _ _), subset_iInter₂_iff]
  -- ⊢ (∀ (i_1 : J) (j_1 : i_1 ⟶ j), range (F.map f) ⊆ range (F.map j_1)) ↔ ∀ ⦃k :  …
  refine' ⟨fun h k g => h _ _, fun h j' f' => _⟩
  -- ⊢ range (F.map f) ⊆ range (F.map f')
  obtain ⟨k, g, g', he⟩ := cospan f f'
  -- ⊢ range (F.map f) ⊆ range (F.map f')
  refine' (h g).trans _
  -- ⊢ range (F.map (g ≫ f)) ⊆ range (F.map f')
  rw [he, F.map_comp]
  -- ⊢ range (F.map g' ≫ F.map f') ⊆ range (F.map f')
  apply range_comp_subset_range
  -- 🎉 no goals
#align category_theory.functor.eventual_range_eq_iff CategoryTheory.Functor.eventualRange_eq_iff

theorem isMittagLeffler_iff_subset_range_comp : F.IsMittagLeffler ↔
    ∀ j : J, ∃ (i : _) (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) :=
  by simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]
     -- 🎉 no goals
#align category_theory.functor.is_mittag_leffler_iff_subset_range_comp CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp

theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    -- ⊢ ∃ i_1 f, ∀ ⦃k : J⦄ (g : k ⟶ i_1), range ((Functor.toPreimages F s).map f) ⊆  …
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    -- ⊢ ∃ i_1 f, ∀ ⦃k : J⦄ (g : k ⟶ i_1), range ((Functor.toPreimages F s).map f) ⊆  …
    refine' ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => _⟩
    -- ⊢ range ((Functor.toPreimages F s).map (f₂ ≫ f₁)) ⊆ range ((Functor.toPreimage …
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    -- ⊢ (Functor.toPreimages F s).map (f₂ ≫ f₁) { val := x, property := hx } ∈ range …
    have : F.map f₂ x ∈ F.eventualRange j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventualRange F (f₃ ≫ f₂) this
    -- ⊢ (Functor.toPreimages F s).map (f₂ ≫ f₁) { val := x, property := hx } ∈ range …
    refine' ⟨⟨y, mem_iInter.2 fun g₂ => _⟩, Subtype.ext _⟩
    -- ⊢ y ∈ F.map g₂ ⁻¹' s
    · obtain ⟨j₄, f₄, h₄⟩ := IsCofilteredOrEmpty.cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      -- ⊢ y ∈ F.map g₂ ⁻¹' s
      obtain ⟨y, rfl⟩ := F.mem_eventualRange_iff.1 hy f₄
      -- ⊢ F.map f₄ y ∈ F.map g₂ ⁻¹' s
      rw [← map_comp_apply] at h₃
      -- ⊢ F.map f₄ y ∈ F.map g₂ ⁻¹' s
      rw [mem_preimage, ← map_comp_apply, h₄, ← Category.assoc, map_comp_apply, h₃,
        ← map_comp_apply]
      apply mem_iInter.1 hx
      -- 🎉 no goals
    · simp_rw [toPreimages_map, MapsTo.val_restrict_apply]
      -- ⊢ F.map (f₃ ≫ f₂ ≫ f₁) y = F.map (f₂ ≫ f₁) x
      rw [← Category.assoc, map_comp_apply, h₃, map_comp_apply]
      -- 🎉 no goals
#align category_theory.functor.is_mittag_leffler.to_preimages CategoryTheory.Functor.IsMittagLeffler.toPreimages

theorem isMittagLeffler_of_exists_finite_range
    (h : ∀ j : J, ∃ (i : _) (f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := by
  intro j
  -- ⊢ ∃ i f, ∀ ⦃k : J⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
  obtain ⟨i, hi, hf⟩ := h j
  -- ⊢ ∃ i f, ∀ ⦃k : J⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | ∃ (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine' ⟨i, f, fun k g =>
    (directedOn_range.mp <| F.ranges_directed j).is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ _ _ ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  -- ⊢ (fun f => range (F.map f.snd)) { fst := i, snd := f } ≤ (fun f => range (F.m …
  refine' (eq_of_le_of_not_lt hl _).ge
  -- ⊢ ¬(fun f => range (F.map f.snd)) { fst := k', snd := g' } < (fun f => range ( …
  have := hmin _ ⟨k', g', (m.finite_toSet.subset <| hm.substr hl).coe_toFinset⟩
  -- ⊢ ¬(fun f => range (F.map f.snd)) { fst := k', snd := g' } < (fun f => range ( …
  rwa [Finset.lt_iff_ssubset, ← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this
  -- 🎉 no goals
#align category_theory.functor.is_mittag_leffler_of_exists_finite_range CategoryTheory.Functor.isMittagLeffler_of_exists_finite_range

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index. -/
@[simps]
def toEventualRanges : J ⥤ Type v where
  obj j := F.eventualRange j
  map f := (F.eventualRange_mapsTo f).restrict _ _ _
  map_id i := by
    simp_rw [MapsTo.restrict, Subtype.map, F.map_id]
    -- ⊢ (fun x => { val := 𝟙 (F.obj i) ↑x, property := (_ : (fun x => x ∈ eventualRa …
    ext
    -- ⊢ ↑{ val := 𝟙 (F.obj i) ↑a✝, property := (_ : (fun x => x ∈ eventualRange F i) …
    rfl
    -- 🎉 no goals
  map_comp _ _ := by
    simp_rw [MapsTo.restrict, Subtype.map, F.map_comp]
    -- ⊢ (fun x => { val := (F.map x✝¹ ≫ F.map x✝) ↑x, property := (_ : (fun x => x ∈ …
    rfl
    -- 🎉 no goals
#align category_theory.functor.to_eventual_ranges CategoryTheory.Functor.toEventualRanges

instance toEventualRanges_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite (F.toEventualRanges.obj j) :=
  fun _ => Subtype.finite
#align category_theory.functor.to_eventual_ranges_finite CategoryTheory.Functor.toEventualRanges_finite

/-- The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.toEventualRanges`. -/
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections where
  toFun s := ⟨_, fun f => Subtype.coe_inj.2 <| s.prop f⟩
  invFun s :=
    ⟨fun j => ⟨_, mem_iInter₂.2 fun i f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext <| s.prop f⟩
  left_inv _ := by
    ext
    -- ⊢ ↑((fun s => { val := fun j => { val := ↑s j, property := (_ : ↑s j ∈ ⋂ (i :  …
    rfl
    -- 🎉 no goals
  right_inv _ := by
    ext
    -- ⊢ ↑((fun s => { val := fun {j} => ↑(↑s j), property := (_ : ∀ {j j' : J} (f :  …
    rfl
    -- 🎉 no goals
#align category_theory.functor.to_eventual_ranges_sections_equiv CategoryTheory.Functor.toEventualRangesSectionsEquiv

/-- If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a
surjective functor. -/
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) :
    (F.toEventualRanges.map f).Surjective := fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  -- ⊢ ∃ a, (toEventualRanges F).map f a = { val := F.map f y, property := hx }
  exact ⟨⟨y, hy⟩, rfl⟩
  -- 🎉 no goals
#align category_theory.functor.surjective_to_eventual_ranges CategoryTheory.Functor.surjective_toEventualRanges

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.toEventualRanges`. -/
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [∀ j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) := by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  -- ⊢ _root_.Nonempty ((toEventualRanges F).obj j)
  rw [toEventualRanges_obj, h]
  -- ⊢ _root_.Nonempty ↑(range (F.map f))
  infer_instance
  -- 🎉 no goals
#align category_theory.functor.to_eventual_ranges_nonempty CategoryTheory.Functor.toEventualRanges_nonempty

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
theorem thin_diagram_of_surjective (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) {i j}
    (f g : i ⟶ j) : F.map f = F.map g :=
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  (Fsur φ).injective_comp_right <| by simp_rw [← types_comp, ← F.map_comp, hφ]
                                      -- 🎉 no goals
#align category_theory.functor.thin_diagram_of_surjective CategoryTheory.Functor.thin_diagram_of_surjective

theorem toPreimages_nonempty_of_surjective [hFn : ∀ j : J, Nonempty (F.obj j)]
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective) (hs : s.Nonempty) (j) :
    Nonempty ((F.toPreimages s).obj j) := by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  -- ⊢ ∃ x, ∀ (i_1 : j ⟶ i), F.map i_1 x ∈ s
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  -- ⊢ ∃ x, ∀ (i_1 : j ⟶ i), F.map i_1 x ∈ s
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
    -- 🎉 no goals
  · obtain ⟨y, ys⟩ := hs
    -- ⊢ ∃ x, ∀ (i_1 : j ⟶ i), F.map i_1 x ∈ s
    obtain ⟨x, rfl⟩ := Fsur ji y
    -- ⊢ ∃ x, ∀ (i_1 : j ⟶ i), F.map i_1 x ∈ s
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji' ji).symm ▸ ys⟩
    -- 🎉 no goals
#align category_theory.functor.to_preimages_nonempty_of_surjective CategoryTheory.Functor.toPreimages_nonempty_of_surjective

theorem eval_section_injective_of_eventually_injective {j}
    (Finj : ∀ (i) (f : i ⟶ j), (F.map f).Injective) (i) (f : i ⟶ j) :
    (fun s : F.sections => s.val j).Injective := by
  refine' fun s₀ s₁ h => Subtype.ext <| funext fun k => _
  -- ⊢ ↑s₀ k = ↑s₁ k
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  -- ⊢ ↑s₀ k = ↑s₁ k
  dsimp at h
  -- ⊢ ↑s₀ k = ↑s₁ k
  rw [← s₀.prop (mi ≫ f), ← s₁.prop (mi ≫ f)] at h
  -- ⊢ ↑s₀ k = ↑s₁ k
  rw [← s₀.prop mk, ← s₁.prop mk]
  -- ⊢ F.map mk (↑s₀ m) = F.map mk (↑s₁ m)
  refine' congr_arg _ (Finj m (mi ≫ f) h)
  -- 🎉 no goals
#align category_theory.functor.eval_section_injective_of_eventually_injective CategoryTheory.Functor.eval_section_injective_of_eventually_injective

section FiniteCofilteredSystem

variable [∀ j : J, Nonempty (F.obj j)] [∀ j : J, Finite (F.obj j)]
  (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f).Surjective)

theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x => by
  let s : Set (F.obj i) := {x}
  -- ⊢ ∃ a, (fun s => ↑s i) a = x
  haveI := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  -- ⊢ ∃ a, (fun s => ↑s i) a = x
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  -- ⊢ ∃ a, (fun s => ↑s i) a = x
  refine' ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using h jk⟩, _⟩
  -- ⊢ (fun s => ↑s i) { val := fun j => ↑(sec j), property := (_ : ∀ {j j' : J} (j …
  · have := (sec i).prop
    -- ⊢ (fun s => ↑s i) { val := fun j => ↑(sec j), property := (_ : ∀ {j j' : J} (j …
    simp only [mem_iInter, mem_preimage, mem_singleton_iff] at this
    -- ⊢ (fun s => ↑s i) { val := fun j => ↑(sec j), property := (_ : ∀ {j j' : J} (j …
    have := this (𝟙 i)
    -- ⊢ (fun s => ↑s i) { val := fun j => ↑(sec j), property := (_ : ∀ {j j' : J} (j …
    rwa [map_id_apply] at this
    -- 🎉 no goals
#align category_theory.functor.eval_section_surjective_of_surjective CategoryTheory.Functor.eval_section_surjective_of_surjective

theorem eventually_injective [Nonempty J] [Finite F.sections] :
    ∃ j, ∀ (i) (f : i ⟶ j), (F.map f).Injective := by
  haveI : ∀ j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  -- ⊢ ∃ j, ∀ (i : J) (f : i ⟶ j), Function.Injective (F.map f)
  haveI : Fintype F.sections := Fintype.ofFinite F.sections
  -- ⊢ ∃ j, ∀ (i : J) (f : i ⟶ j), Function.Injective (F.map f)
  have card_le : ∀ j, Fintype.card (F.obj j) ≤ Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surjective Fsur j)
  let fn j := Fintype.card F.sections - Fintype.card (F.obj j)
  -- ⊢ ∃ j, ∀ (i : J) (f : i ⟶ j), Function.Injective (F.map f)
  refine' ⟨fn.argmin Nat.lt_wfRel.wf,
    fun i f => ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨Fsur f, le_antisymm _ (Fintype.card_le_of_surjective _ <| Fsur f)⟩).1⟩
  rw [← Nat.sub_sub_self (card_le i), tsub_le_iff_tsub_le]
  -- ⊢ Fintype.card ↑(sections F) - Fintype.card (F.obj (Function.argmin fn (_ : We …
  apply fn.argmin_le
  -- 🎉 no goals
#align category_theory.functor.eventually_injective CategoryTheory.Functor.eventually_injective

end FiniteCofilteredSystem

end Functor

end CategoryTheory
