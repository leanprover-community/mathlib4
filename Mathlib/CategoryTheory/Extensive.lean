/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory

#align_import category_theory.extensive from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.
- `CategoryTheory.Extensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_extensive`: The initial object
  in extensive categories is strict.
- `CategoryTheory.Extensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.extensive`: The category of types is extensive.

## TODO

Show that the following are finitary extensive:
- the categories of sheaves over a site
- `Scheme`
- `AffineScheme` (`CommRingᵒᵖ`)

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/


open CategoryTheory.Limits

namespace CategoryTheory

universe v' u' v u w

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C]

/-- A natural transformation is equifibered if every commutative square of the following form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def NatTrans.Equifibered {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
  ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)
#align category_theory.nat_trans.equifibered CategoryTheory.NatTrans.Equifibered

theorem NatTrans.equifibered_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Equifibered α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩
#align category_theory.nat_trans.equifibered_of_is_iso CategoryTheory.NatTrans.equifibered_of_isIso

theorem NatTrans.Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
    (hβ : Equifibered β) : Equifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)
#align category_theory.nat_trans.equifibered.comp CategoryTheory.NatTrans.Equifibered.comp

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is universal if it is stable under pullbacks. -/
def IsUniversalColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    (∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) → Nonempty (IsColimit c')
#align category_theory.is_universal_colimit CategoryTheory.IsUniversalColimit

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is van Kampen if for every cocone `c'` over the
pullback of the diagram `F' : J ⥤ C'`, `c'` is colimiting iff `c'` is the pullback of `c`.

TODO: Show that this is iff the functor `C ⥤ Catᵒᵖ` sending `x` to `C/x` preserves it.
TODO: Show that this is iff the inclusion functor `C ⥤ Span(C)` preserves it.
-/
def IsVanKampenColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (_ : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (_ : NatTrans.Equifibered α),
    Nonempty (IsColimit c') ↔ ∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)
#align category_theory.is_van_kampen_colimit CategoryTheory.IsVanKampenColimit

lemma isVanKampenColimit_coproduct {I : Type w} {X : I → C} (c : Cocone (Discrete.functor X)) :
    IsVanKampenColimit c ↔ ∀ ⦃Z : I → C⦄

theorem IsVanKampenColimit.isUniversal {F : J ⥤ C} {c : Cocone F} (H : IsVanKampenColimit c) :
    IsUniversalColimit c :=
  fun _ c' α f h hα => (H c' α f h hα).mpr
#align category_theory.is_van_kampen_colimit.is_universal CategoryTheory.IsVanKampenColimit.isUniversal

/-- A van Kampen colimit is a colimit. -/
noncomputable def IsVanKampenColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsVanKampenColimit c) : IsColimit c := by
  refine' ((h c (𝟙 F) (𝟙 c.pt : _) (by rw [Functor.map_id, Category.comp_id, Category.id_comp])
    (NatTrans.equifibered_of_isIso _)).mpr fun j => _).some
  haveI : IsIso (𝟙 c.pt) := inferInstance
  exact IsPullback.of_vert_isIso ⟨by erw [NatTrans.id_app, Category.comp_id, Category.id_comp]⟩
#align category_theory.is_van_kampen_colimit.is_colimit CategoryTheory.IsVanKampenColimit.isColimit

theorem IsInitial.isVanKampenColimit [HasStrictInitialObjects C] {X : C} (h : IsInitial X) :
    IsVanKampenColimit (asEmptyCocone X) := by
  intro F' c' α f hf hα
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  haveI := h.isIso_to f
  refine' ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocones.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩
#align category_theory.is_initial.is_van_kampen_colimit CategoryTheory.IsInitial.isVanKampenColimit


section Extensive

variable {X Y : C}

variable (C) in
/--
Describes the property of having pullbacks of morphsims into a finite coproduct, where one
of the morphisms is an inclusion map into the coproduct (up to isomorphism).
-/
class HasPullbacksOfInclusions : Prop where
    /-- For any morphism `f : X ⟶ Z`, where `Z` is the coproduct of `i : (a : α) → Y a ⟶ Z` with
    `α` finite, the pullback of `f` and `i a` exists for every `a : α`. -/
    has_pullback : ∀ {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbacksOfInclusions C] {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbacksOfInclusions.has_pullback f i a

/--
If `C` has pullbacks then it has the pullbacks relevant to `HasPullbacksOfInclusions`.
-/
instance (priority := 10) [HasPullbacks C] :
  HasPullbacksOfInclusions C := ⟨fun _ _ _ => inferInstance⟩

variable (C) in
/--
A category is *extensive* if it has all finite coproducts and those coproducts are preserved
by pullbacks (we only require the relevant pullbacks to exist, via `HasPullbacksOfInclusions`).
-/
class Extensive extends HasFiniteCoproducts C, HasPullbacksOfInclusions C : Prop where
  /-- Pulling back an isomorphism from a coproduct yields an isomorphism. -/
  sigma_desc_iso : ∀ {α : Type w} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
    {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))


attribute [instance] Extensive.toHasFiniteCoproducts

variable [Extensive C]

theorem Extensive.vanKampen_general (I : Type w) [Fintype I] {F : Discrete I ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  intro F' c' α f hc hα
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · let i : F' ≅ Discrete.functor (fun i : I ↦ F'.obj ⟨i⟩) := Discrete.natIsoFunctor
    have hI : IsIso (Sigma.desc (fun j ↦ NatTrans.app c.ι ⟨j⟩))
    · sorry
    have := Extensive.sigma_desc_iso (fun j ↦ NatTrans.app c.ι ⟨j⟩) f hI
    constructor
    · sorry
    · constructor
      simp only [← NatTrans.comp_app, hc]
      rfl
  · sorry

theorem Extensive.vanKampen [Extensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c :=
  vanKampen_general WalkingPair c hc

theorem mapPair_equifibered {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') :
    NatTrans.Equifibered α := by
  rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩
  all_goals
    dsimp; simp only [Discrete.functor_map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
#align category_theory.map_pair_equifibered CategoryTheory.mapPair_equifibered

theorem BinaryCofan.isVanKampen_iff (c : BinaryCofan X Y) :
    IsVanKampenColimit c ↔
      ∀ {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : c'.pt ⟶ c.pt)
        (_ : αX ≫ c.inl = c'.inl ≫ f) (_ : αY ≫ c.inr = c'.inr ≫ f),
        Nonempty (IsColimit c') ↔ IsPullback c'.inl αX f c.inl ∧ IsPullback c'.inr αY f c.inr := by
  constructor
  · introv H hαX hαY
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (mapPair_equifibered _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨WalkingPair.left⟩
    let Y' := F'.obj ⟨WalkingPair.right⟩
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    clear_value X' Y'
    subst this
    change BinaryCofan X' Y' at c'
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts [H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩
#align category_theory.binary_cofan.is_van_kampen_iff CategoryTheory.BinaryCofan.isVanKampen_iff

theorem BinaryCofan.isVanKampen_mk {X Y : C} (c : BinaryCofan X Y)
    (cofans : ∀ X Y : C, BinaryCofan X Y) (colimits : ∀ X Y, IsColimit (cofans X Y))
    (cones : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PullbackCone f g)
    (limits : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), IsLimit (cones f g))
    (h₁ : ∀ {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : (cofans X' Y').pt ⟶ c.pt)
      (_ : αX ≫ c.inl = (cofans X' Y').inl ≫ f) (_ : αY ≫ c.inr = (cofans X' Y').inr ≫ f),
      IsPullback (cofans X' Y').inl αX f c.inl ∧ IsPullback (cofans X' Y').inr αY f c.inr)
    (h₂ : ∀ {Z : C} (f : Z ⟶ c.pt),
      IsColimit (BinaryCofan.mk (cones f c.inl).fst (cones f c.inr).fst)) :
    IsVanKampenColimit c := by
  rw [BinaryCofan.isVanKampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [hX]) (by simp [hY])
    constructor
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      haveI : IsIso (𝟙 X') := inferInstance
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      haveI : IsIso (𝟙 Y') := inferInstance
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
    refine' ⟨IsColimit.ofIsoColimit _ <| (isoBinaryCofanMk _).symm⟩
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp
    rw [he₁, he₂]
    apply BinaryCofan.isColimitCompRightIso (BinaryCofan.mk _ _)
    apply BinaryCofan.isColimitCompLeftIso (BinaryCofan.mk _ _)
    exact h₂ f
#align category_theory.binary_cofan.is_van_kampen_mk CategoryTheory.BinaryCofan.isVanKampen_mk

theorem BinaryCofan.mono_inr_of_isVanKampen [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : Mono c.inr := by
  refine' PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit _)
  refine' (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some
#align category_theory.binary_cofan.mono_inr_of_is_van_kampen CategoryTheory.BinaryCofan.mono_inr_of_isVanKampen

theorem Extensive.mono_inr_of_isColimit [Extensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr := sorry

theorem Extensive.mono_inl_of_isColimit [Extensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl := sorry

instance [Extensive C] (X Y : C) : Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  (Extensive.mono_inl_of_isColimit (coprodIsCoprod X Y) : _)

instance [Extensive C] (X Y : C) : Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  (Extensive.mono_inr_of_isColimit (coprodIsCoprod X Y) : _)

theorem BinaryCofan.isPullback_initial_to_of_isVanKampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr := by
  refine' ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some#align category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen

theorem Extensive.isPullback_initial_to_binaryCofan [Extensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (Extensive.vanKampen c hc)

theorem hasStrictInitial_of_isUniversal [HasInitial C]
    (H : IsUniversalColimit (BinaryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) : HasStrictInitialObjects C :=
  hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases(Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine' (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> simp)
        (mapPair_equifibered _) _).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
#align category_theory.has_strict_initial_of_is_universal CategoryTheory.hasStrictInitial_of_isUniversal

instance (priority := 100) hasStrictInitialObjects_of_finitaryExtensive [Extensive C] :
    HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (Extensive.vanKampen _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some).isUniversal
#align category_theory.has_strict_initial_objects_of_finitary_extensive CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive


instance types.extensive : Extensive (Type u) := by sorry

section TopCat

instance : Extensive TopCat.{u} := by sorry

-- TODO: add Stonean, Profinite, CompHaus

end TopCat

section Functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

theorem NatTrans.Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [PreservesLimitsOfShape WalkingCospan H] : Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H
#align category_theory.nat_trans.equifibered.whisker_right CategoryTheory.NatTrans.Equifibered.whiskerRight

theorem IsVanKampenColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
    (e : c ≅ c') : IsVanKampenColimit c' := by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.Hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  haveI : IsIso e.inv.Hom := Functor.map_isIso (Cocones.forget _) e.inv
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm
#align category_theory.is_van_kampen_colimit.of_iso CategoryTheory.IsVanKampenColimit.of_iso

theorem IsVanKampenColimit.of_map {D : Type*} [Category D] (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G] [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  refine' (Iff.trans _ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => _)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)
#align category_theory.is_van_kampen_colimit.of_map CategoryTheory.IsVanKampenColimit.of_map

theorem isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
    (c : Cocone F) (hc : ∀ x : C, IsVanKampenColimit (((evaluation C D).obj x).mapCocone c)) :
    IsVanKampenColimit c := by
  intro F' c' α f e hα
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  · rintro ⟨hc'⟩ j
    refine' ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ _⟩⟩
    refine' fun x => (isLimitMapConePullbackConeEquiv _ _).symm _
    exact ((this x).mp ⟨PreservesColimit.preserves hc'⟩ _).isLimit
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩
#align category_theory.is_van_kampen_colimit_of_evaluation CategoryTheory.isVanKampenColimit_of_evaluation

instance [HasPullbacks C] [Extensive C] : Extensive (D ⥤ C) := sorry

theorem extensive_of_preserves_and_reflects (F : C ⥤ D) [Extensive D]
    [HasFiniteCoproducts C] [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : Extensive C := sorry

theorem extensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [Extensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [ReflectsIsomorphisms F] :
    Extensive C := sorry

end Functor

end Extensive

end CategoryTheory
