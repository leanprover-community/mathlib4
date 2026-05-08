/-
Copyright (c) 2022 Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Konig

/-!
# Cofiltered systems

This file deals with properties of cofiltered (and inverse) systems.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventualRange j` is the intersection of all ranges of morphisms `F.map f`
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

## TODO

* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/

@[expose] public section


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
  haveI : ∀ j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  haveI : ∀ j, Finite (F'.obj j) := hf
  haveI : ∀ j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u, hu⟩

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_inverse_system` for a specialization to inverse limits. -/
theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  haveI : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  haveI : ∀ i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) Equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  cases isEmpty_or_nonempty J
  · fconstructor <;> apply isEmptyElim
  haveI : IsCofiltered J := ⟨⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [F', down, AsSmall.down, Functor.comp_map, uliftFunctor_map] at h
  simp_rw [← h]
  rfl

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
theorem nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J]
    (F : Jᵒᵖ ⥤ Type v) [∀ j : Jᵒᵖ, Finite (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := nonempty_sections_of_finite_cofiltered_system F

end FiniteKonig

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category* J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

/-- The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`. -/
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)

theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_iInter₂

/-- The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `isMittagLeffler_iff_eventualRange`), the eventual range at `j` is attained
by some `f : i ⟶ j`. -/
def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _) (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)

theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
      ⟨fun h => (iInter₂_subset _ _).antisymm <| subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩

theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j := by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp, comp_apply]⟩

theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) := by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp, types_comp]
    apply range_comp_subset_range

theorem isMittagLeffler_of_surjective (h : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    F.IsMittagLeffler :=
  fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps]
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := ↾(MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    intro f
    rw [← mem_preimage, preimage_preimage, mem_preimage]
    convert h (g ≫ f); rw [F.map_comp]; rfl)

instance toPreimages_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite ((F.toPreimages s).obj j) :=
  fun _ => Subtype.finite

variable [IsCofilteredOrEmpty J]

theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← comp_apply, ← map_comp, he, F.map_comp]
  exact ⟨_, rfl⟩

theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
  (h.subset_image_eventualRange F f).antisymm <| mapsTo_iff_image_subset.1
    (F.eventualRange_mapsTo f)

theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  rw [subset_antisymm_iff, eventualRange, and_iff_right (iInter₂_subset _ _), subset_iInter₂_iff]
  refine ⟨fun h k g => h _ _, fun h j' f' => ?_⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine (h g).trans ?_
  rw [he, F.map_comp, types_comp]
  apply range_comp_subset_range

theorem isMittagLeffler_iff_subset_range_comp : F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j),
    ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    refine ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x ∈ F.eventualRange j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventualRange F (f₃ ≫ f₂) this
    refine ⟨⟨y, mem_iInter.2 fun g₂ => ?_⟩, Subtype.ext ?_⟩
    · obtain ⟨j₄, f₄, h₄⟩ := IsCofilteredOrEmpty.cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      obtain ⟨y, rfl⟩ := F.mem_eventualRange_iff.1 hy f₄
      rw [← comp_apply, ← map_comp] at h₃
      rw [mem_preimage, ← comp_apply, ← map_comp, h₄, ← Category.assoc, map_comp, comp_apply, h₃,
        ← comp_apply, ← map_comp]
      apply mem_iInter.1 hx
    · simp only [toPreimages_obj, toPreimages_map, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, MapsTo.val_restrict_apply]
      rw [← Category.assoc, map_comp, comp_apply, h₃, map_comp, comp_apply]

theorem isMittagLeffler_of_exists_finite_range
    (h : ∀ j : J, ∃ (i : _) (f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := by
  intro j
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | ∃ (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine ⟨i, f, fun k g =>
    (directedOn_range.mp <| F.ranges_directed j).is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ ?_ _ ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  refine (eq_of_le_of_not_lt hl ?_).ge
  have := hmin _ ⟨k', g', (m.finite_toSet.subset <| hm.substr hl).coe_toFinset⟩
  rwa [Finset.lt_iff_ssubset, ← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index. -/
@[simps obj map]
def toEventualRanges : J ⥤ Type v where
  obj j := F.eventualRange j
  map f := ↾((F.eventualRange_mapsTo f).restrict _ _ _)

instance toEventualRanges_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite (F.toEventualRanges.obj j) :=
  fun _ => Subtype.finite

/-- The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.toEventualRanges`. -/
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections where
  toFun s := ⟨_, fun f => Subtype.coe_inj.2 <| s.prop f⟩
  invFun s :=
    ⟨fun _ => ⟨_, mem_iInter₂.2 fun _ f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext <| s.prop f⟩

/-- If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a
surjective functor. -/
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) :
    Function.Surjective (F.toEventualRanges.map f) := fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  exact ⟨⟨y, hy⟩, rfl⟩

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.toEventualRanges`. -/
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [∀ j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) := by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [toEventualRanges_obj, h]
  infer_instance

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
theorem thin_diagram_of_surjective
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) {i j}
    (f g : i ⟶ j) : F.map f = F.map g := by
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  apply ConcreteCategory.ext
  have := congrArg F.map hφ
  simp only [map_comp, ConcreteCategory.ext_iff, DFunLike.ext_iff, comp_apply, ← funext_iff] at this
  simpa using (Fsur φ).injective_comp_right <| this

theorem toPreimages_nonempty_of_surjective [hFn : ∀ j : J, Nonempty (F.obj j)]
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) (hs : s.Nonempty) (j) :
    Nonempty ((F.toPreimages s).obj j) := by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji' ji).symm ▸ ys⟩

theorem eval_section_injective_of_eventually_injective {j}
    (Finj : ∀ (i) (f : i ⟶ j), Function.Injective (F.map f)) (i) (f : i ⟶ j) :
    (fun s : F.sections => s.val j).Injective := by
  refine fun s₀ s₁ h => Subtype.ext <| funext fun k => ?_
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f), ← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk, ← s₁.prop mk]
  exact congr_arg _ (Finj m (mi ≫ f) h)

section FiniteCofilteredSystem

variable [∀ j : J, Nonempty (F.obj j)] [∀ j : J, Finite (F.obj j)]
  (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))
include Fsur

set_option backward.defeqAttrib.useBackward true in
theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x => by
  let s : Set (F.obj i) := {x}
  haveI := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using h jk⟩, ?_⟩
  · have := (sec i).prop
    simp only [mem_iInter, mem_preimage] at this
    have := this (𝟙 i)
    rwa [map_id, id_apply] at this

theorem eventually_injective [Nonempty J] [Finite F.sections] :
    ∃ j, ∀ (i) (f : i ⟶ j), Function.Injective (F.map f) := by
  haveI : ∀ j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  haveI : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : ∀ j, Fintype.card (F.obj j) ≤ Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surjective Fsur j)
  let fn j := Fintype.card F.sections - Fintype.card (F.obj j)
  refine ⟨fn.argmin,
    fun i f => ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨Fsur f, le_antisymm ?_ (Fintype.card_le_of_surjective _ <| Fsur f)⟩).1⟩
  rw [← Nat.sub_le_sub_iff_left (card_le i)]
  apply fn.argmin_le

end FiniteCofilteredSystem

end Functor

end CategoryTheory
