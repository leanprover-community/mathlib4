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
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

#align_import category_theory.extensive from "leanprover-community/mathlib"@"178a32653e369dce2da68dc6b2694e385d484ef1"

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.
- `CategoryTheory.FinitaryExtensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive`: The initial object
  in extensive categories is strict.
- `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.finitaryExtensive`: The category of types is extensive.
- `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`: Finite coproducts in a
  finitary extensive category are van Kampen.

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

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]

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

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen. -/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]
  /-- In a finitary extensive category, all coproducts are van Kampen-/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c
#align category_theory.finitary_extensive CategoryTheory.FinitaryExtensive

attribute [instance] FinitaryExtensive.hasFiniteCoproducts FinitaryExtensive.hasPullbackInl

theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc
#align category_theory.finitary_extensive.van_kampen CategoryTheory.FinitaryExtensive.vanKampen

instance FinitaryExtensive.hasPullbackInl' [FinitaryExtensive C] {X Y Z : C} (f : Z ⟶ X ⨿ Y) :
    HasPullback f coprod.inl :=
  hasPullback_symmetry _ _

instance FinitaryExtensive.hasPullbackInr' [FinitaryExtensive C] {X Y Z : C} (f : Z ⟶ X ⨿ Y) :
    HasPullback f coprod.inr := by
  have : IsPullback (𝟙 _) (f ≫ (coprod.braiding X Y).hom) f (coprod.braiding Y X).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := (IsPullback.of_hasPullback (f ≫ (coprod.braiding X Y).hom) coprod.inl).paste_horiz this
  simp only [coprod.braiding_hom, Category.comp_id, colimit.ι_desc, BinaryCofan.mk_pt,
    BinaryCofan.ι_app_left, BinaryCofan.mk_inl] at this
  exact ⟨⟨⟨_, this.isLimit⟩⟩⟩

instance FinitaryExtensive.hasPullbackInr [FinitaryExtensive C] {X Y Z : C} (f : Z ⟶ X ⨿ Y) :
    HasPullback coprod.inr f :=
  hasPullback_symmetry _ _

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

theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)
#align category_theory.finitary_extensive.mono_inr_of_is_colimit CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit

theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)
#align category_theory.finitary_extensive.mono_inl_of_is_colimit CategoryTheory.FinitaryExtensive.mono_inl_of_isColimit

instance [FinitaryExtensive C] (X Y : C) : Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  (FinitaryExtensive.mono_inl_of_isColimit (coprodIsCoprod X Y) : _)

instance [FinitaryExtensive C] (X Y : C) : Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  (FinitaryExtensive.mono_inr_of_isColimit (coprodIsCoprod X Y) : _)

theorem BinaryCofan.isPullback_initial_to_of_isVanKampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr := by
  refine' ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some
#align category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen

theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)
#align category_theory.finitary_extensive.is_pullback_initial_to_binary_cofan CategoryTheory.FinitaryExtensive.isPullback_initial_to_binaryCofan

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

instance (priority := 100) hasStrictInitialObjects_of_finitaryExtensive [FinitaryExtensive C] :
    HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryExtensive.vanKampen _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some).isUniversal
#align category_theory.has_strict_initial_objects_of_finitary_extensive CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive

theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [hasPullbackInl : ∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine' ⟨fun H => H.van_kampen' c₀ hc₀, fun H => _⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of% hX, hd, Category.assoc])
      (by rw [← reassoc_of% hY, hd', Category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]
#align category_theory.finitary_extensive_iff_of_is_terminal CategoryTheory.finitaryExtensive_iff_of_isTerminal

instance types.finitaryExtensive : FinitaryExtensive (Type u) := by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPunit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intros _ _ _ _ f hαX hαY
    constructor
    · refine' ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases' h : s.fst x with val val
        · simp only [Types.binaryCoproductCocone_pt, Functor.const_obj_obj, Sum.inl.injEq,
            exists_unique_eq']
        · apply_fun f at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαY val : _).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      exact ⟨l, (funext hl).symm, Types.isTerminalPunit.hom_ext _ _,
        fun {l'} h₁ _ => funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
    · refine' ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases' h : s.fst x with val val
        · apply_fun f at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαX val : _).symm
        · simp only [Types.binaryCoproductCocone_pt, Functor.const_obj_obj, Sum.inr.injEq,
            exists_unique_eq']
      delta ExistsUnique at this
      choose l hl hl' using this
      exact ⟨l, (funext hl).symm, Types.isTerminalPunit.hom_ext _ _,
        fun {l'} h₁ _ => funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
  · intro Z f
    dsimp [Limits.Types.binaryCoproductCocone]
    delta Types.PullbackObj
    have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit := by
      intro x
      rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      exacts [Or.inl rfl, Or.inr rfl]
    let eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, by convert p.2⟩, fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl,
        fun _ => by ext; rfl⟩
    let eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩,
        fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
    fapply BinaryCofan.isColimitMk
    · exact fun s x => dite _ (fun h => s.inl <| eX.symm ⟨x, h⟩)
        fun h => s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, _⟩
      dsimp
      split_ifs <;> rfl
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, hx⟩
      dsimp
      split_ifs with h
      · cases h.symm.trans hx
      · rfl
    · intro s m e₁ e₂
      ext x
      split_ifs
      · rw [← e₁]
        rfl
      · rw [← e₂]
        rfl
#align category_theory.types.finitary_extensive CategoryTheory.types.finitaryExtensive

section TopCat

/-- (Implementation) An auxiliary lemma for the proof that `TopCat` is finitary extensive. -/
-- Porting note : needs to add noncomputable modifier
noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (Sum PUnit.{u + 1} PUnit.{u + 1})) :
    IsColimit (BinaryCofan.mk
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) := by
  have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit := by
    intro x
    rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    exacts [Or.inl rfl, Or.inr rfl]
  letI eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
    ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inl <| Subsingleton.elim _ _)⟩,
      fun x => ⟨⟨_, PUnit.unit⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
  letI eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
    ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩,
      fun x => ⟨⟨_, PUnit.unit⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
  fapply BinaryCofan.isColimitMk
  classical -- Porting note: Added
  · refine' fun s => ⟨fun x => dite _
      (fun h => s.inl <| eX.symm ⟨x, h⟩) fun h => s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩, _⟩
    rw [continuous_iff_continuousAt]
    intro x
    by_cases f x = Sum.inl PUnit.unit
    · revert h x
      apply (IsOpen.continuousOn_iff _).mp
      · rw [continuousOn_iff_continuous_restrict]
        convert_to Continuous fun x : { x | f x = Sum.inl PUnit.unit } =>
            s.inl ⟨(x.1, PUnit.unit), x.2⟩
        · ext ⟨x, hx⟩
          exact dif_pos hx
        -- Porting note : this `(BinaryCofan.inl s).2` was unnecessary
        have := (BinaryCofan.inl s).2
        continuity
      · convert f.2.1 _ openEmbedding_inl.open_range
        rename_i x
        exact ⟨fun h => ⟨_, h.symm⟩,
          fun ⟨e, h⟩ => h.symm.trans (congr_arg Sum.inl <| Subsingleton.elim _ _)⟩
    · revert h x
      apply (IsOpen.continuousOn_iff _).mp
      · rw [continuousOn_iff_continuous_restrict]
        convert_to Continuous fun x : { x | f x ≠ Sum.inl PUnit.unit } =>
            s.inr ⟨(x.1, PUnit.unit), (this _).resolve_left x.2⟩
        · ext ⟨x, hx⟩
          exact dif_neg hx
        -- Porting note : this `(BinaryCofan.inr s).2` was unnecessary
        have := (BinaryCofan.inr s).2
        continuity
      · convert f.2.1 _ openEmbedding_inr.open_range
        rename_i x
        change f x ≠ Sum.inl PUnit.unit ↔ f x ∈ Set.range Sum.inr
        trans f x = Sum.inr PUnit.unit
        · rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;>
            simp only [iff_self_iff, eq_self_iff_true, not_true, Ne.def, not_false_iff]
        · exact ⟨fun h => ⟨_, h.symm⟩,
            fun ⟨e, h⟩ => h.symm.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩
  · intro s
    ext ⟨⟨x, ⟨⟩⟩, (hx : f x = Sum.inl PUnit.unit)⟩
    change dite _ _ _ = _
    split_ifs with h
    · rfl
    · cases (h hx) -- Porting note : in Lean3 it is `rfl`
  · intro s
    ext ⟨⟨x, ⟨⟩⟩, hx⟩
    change dite _ _ _ = _
    split_ifs with h
    · cases h.symm.trans hx
    · rfl
  · intro s m e₁ e₂
    ext x
    change m x = dite _ _ _
    split_ifs
    · rw [← e₁]
      rfl
    · rw [← e₂]
      rfl
set_option linter.uppercaseLean3 false in
#align category_theory.finitary_extensive_Top_aux CategoryTheory.finitaryExtensiveTopCatAux

instance : FinitaryExtensive TopCat.{u} := by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constructor
    · refine' ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases' h : s.fst x with val val
        · exact ⟨val, rfl, fun y h => Sum.inl_injective h.symm⟩
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val : _).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine' ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => ContinuousMap.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inl (α := X') (β := Y')).toInducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
    · refine' ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases' h : s.fst x with val val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val : _).symm
        · exact ⟨val, rfl, fun y h => Sum.inr_injective h.symm⟩
      delta ExistsUnique at this
      choose l hl hl' using this
      refine' ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          ContinuousMap.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inr (α := X') (β := Y')).toInducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
  · intro Z f
    exact finitaryExtensiveTopCatAux Z f

end TopCat

section Functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

theorem NatTrans.Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [PreservesLimitsOfShape WalkingCospan H] : Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H
#align category_theory.nat_trans.equifibered.whisker_right CategoryTheory.NatTrans.Equifibered.whiskerRight

theorem NatTrans.Equifibered.whiskerLeft {K : Type*} [Category K]  {F G : J ⥤ C} {α : F ⟶ G}
    (hα : Equifibered α) (H : K ⥤ J) : Equifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem IsVanKampenColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
    (e : c ≅ c') : IsVanKampenColimit c' := by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.const J).map e.inv.hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← Category.comp_id (α.app j)]
  haveI : IsIso e.inv.hom := Functor.map_isIso (Cocones.forget _) e.inv
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

theorem IsVanKampenColimit.precompose_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit ((Cocones.precompose α).obj c) := by
  intros F' c' α' f e hα
  refine (hc c' (α' ≫ α) f ((Category.assoc _ _ _).trans e)
    (hα.comp (NatTrans.equifibered_of_isIso _))).trans ?_
  apply forall_congr'
  intro j
  simp only [Functor.const_obj_obj, NatTrans.comp_app,
    Cocones.precompose_obj_pt, Cocones.precompose_obj_ι]
  have : IsPullback (α.app j ≫ c.ι.app j) (α.app j) (𝟙 _) (c.ι.app j) :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  rw [← IsPullback.paste_vert_iff this _, Category.comp_id]
  exact (congr_app e j).symm

theorem IsVanKampenColimit.precompose_isIso_iff {F G : J ⥤ C} (α : F ⟶ G) [IsIso α]
    {c : Cocone G} : IsVanKampenColimit ((Cocones.precompose α).obj c) ↔ IsVanKampenColimit c :=
  ⟨fun hc ↦ IsVanKampenColimit.of_iso (IsVanKampenColimit.precompose_isIso (inv α) hc)
    (Cocones.ext (Iso.refl _) (by simp)),
    IsVanKampenColimit.precompose_isIso α⟩

theorem IsVanKampenColimit.whiskerEquivalence {K : Type*} [Category K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} (hc : IsVanKampenColimit c) :
    IsVanKampenColimit (c.whisker e.functor) := by
  intro F' c' α f e' hα
  convert hc (c'.whisker e.inverse) (whiskerLeft e.inverse α ≫ (e.invFunIdAssoc F).hom) f ?_
    ((hα.whiskerLeft _).comp (NatTrans.equifibered_of_isIso _)) using 1
  · exact (IsColimit.whiskerEquivalenceEquiv e.symm).nonempty_congr
  · simp only [Functor.const_obj_obj, Functor.comp_obj, Cocone.whisker_pt, Cocone.whisker_ι,
      whiskerLeft_app, NatTrans.comp_app, Equivalence.invFunIdAssoc_hom_app, Functor.id_obj]
    constructor
    · intro H k
      rw [← Category.comp_id f]
      refine (H (e.inverse.obj k)).paste_vert ?_
      have : IsIso (𝟙 (Cocone.whisker e.functor c).pt) := inferInstance
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · intro H j
      have : α.app j = F'.map (e.unit.app _) ≫ α.app _ ≫ F.map (e.counit.app (e.functor.obj j))
      · simp [← Functor.map_comp]
      rw [← Category.id_comp f, this]
      refine IsPullback.paste_vert ?_ (H (e.functor.obj j))
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  · ext k
    simpa using congr_app e' (e.inverse.obj k)

theorem IsVanKampenColimit.whiskerEquivalence_iff {K : Type*} [Category K] (e : J ≌ K)
    {F : K ⥤ C} {c : Cocone F} :
    IsVanKampenColimit (c.whisker e.functor) ↔ IsVanKampenColimit c :=
  ⟨fun hc ↦ ((hc.whiskerEquivalence e.symm).precompose_isIso (e.invFunIdAssoc F).inv).of_iso
      (Cocones.ext (Iso.refl _) (by simp)), IsVanKampenColimit.whiskerEquivalence e⟩

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

instance [HasPullbacks C] [FinitaryExtensive C] : FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
    FinitaryExtensive.vanKampen _ <| PreservesColimit.preserves hc⟩

theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [∀ {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]
    [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C :=
  ⟨fun _ hc => (FinitaryExtensive.vanKampen _ (isColimitOfPreserves F hc)).of_map F⟩
#align category_theory.finitary_extensive_of_preserves_and_reflects CategoryTheory.finitaryExtensive_of_preserves_and_reflects

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [ReflectsIsomorphisms F] :
    FinitaryExtensive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShapeOfReflectsIsomorphisms
  haveI : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShapeOfReflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F
#align category_theory.finitary_extensive_of_preserves_and_reflects_isomorphism CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism

end Functor

section FiniteCoproducts

theorem NatTrans.equifibered_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : NatTrans.Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  refine IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

theorem isUniversalColimit_extendCofan {n : ℕ} (f : Fin (n + 1) → C)
    {c₁ : Cofan fun i : Fin n ↦ f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsUniversalColimit c₁) (t₂ : IsUniversalColimit c₂)
    [∀ {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i] :
    IsUniversalColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα H
  let F' : Fin (n + 1) → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor F'
  · apply Functor.hext
    · exact fun i ↦ rfl
    · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
      simp
  have t₁' := @t₁ (Discrete.functor (fun j ↦ F.obj ⟨j.succ⟩))
    (Cofan.mk (pullback c₂.inr i) <| fun j ↦ pullback.lift (α.app _ ≫ c₁.inj _) (c.ι.app _) ?_)
    (Discrete.natTrans <| fun i ↦ α.app _) pullback.fst ?_ (NatTrans.equifibered_of_discrete _) ?_
  rotate_left
  · simpa only [Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj, Category.assoc,
      extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
      Fin.cases_succ, Functor.const_map_app] using congr_app e ⟨j.succ⟩
  · ext j
    dsimp
    simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  · intro j
    simp only [pair_obj_right, Functor.const_obj_obj, Discrete.functor_obj, id_eq,
      extendCofan_pt, eq_mpr_eq_cast, Cofan.mk_pt, Cofan.mk_ι_app, Discrete.natTrans_app]
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
    · simp only [Functor.const_obj_obj, pair_obj_right, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      exact H _
    · simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Cofan.inj]
  obtain ⟨H₁⟩ := t₁'
  have t₂' := @t₂ (pair (F.obj ⟨0⟩) (pullback c₂.inr i)) (BinaryCofan.mk (c.ι.app ⟨0⟩) pullback.snd)
    (mapPair (α.app _) pullback.fst) i ?_ (mapPair_equifibered _) ?_
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa [mapPair] using congr_app e ⟨0⟩
    · simpa using pullback.condition
  · rintro ⟨⟨⟩⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, pair_obj_left, BinaryCofan.mk_pt,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, mapPair_left]
      exact H ⟨0⟩
    · simp only [pair_obj_right, Functor.const_obj_obj, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
        BinaryCofan.mk_inr, mapPair_right]
      exact (IsPullback.of_hasPullback (BinaryCofan.inr c₂) i).flip
  obtain ⟨H₂⟩ := t₂'
  clear_value F'
  subst this
  refine ⟨IsColimit.ofIsoColimit (extendCofanIsColimit
    (fun i ↦ (Discrete.functor F').obj ⟨i⟩) H₁ H₂) <| Cocones.ext (Iso.refl _) ?_⟩
  dsimp
  rintro ⟨j⟩
  simp only [Discrete.functor_obj, limit.lift_π, PullbackCone.mk_pt,
    PullbackCone.mk_π_app, Category.comp_id]
  induction' j using Fin.inductionOn
  · simp only [Fin.cases_zero]
  · simp only [Fin.cases_succ]

theorem isVanKampenColimit_extendCofan {n : ℕ} (f : Fin (n + 1) → C)
    {c₁ : Cofan fun i : Fin n ↦ f i.succ} {c₂ : BinaryCofan (f 0) c₁.pt}
    (t₁ : IsVanKampenColimit c₁) (t₂ : IsVanKampenColimit c₂)
    [∀ {Z} (i : Z ⟶ c₂.pt), HasPullback c₂.inr i]
    [HasFiniteCoproducts C] :
    IsVanKampenColimit (extendCofan c₁ c₂) := by
  intro F c α i e hα
  refine ⟨?_, isUniversalColimit_extendCofan f t₁.isUniversal t₂.isUniversal c α i e hα⟩
  intro ⟨Hc⟩ ⟨j⟩
  have t₂' := (@t₂ (pair (F.obj ⟨0⟩) (∐ fun (j : Fin n) ↦ F.obj ⟨j.succ⟩))
    (BinaryCofan.mk (P := c.pt) (c.ι.app _) (Sigma.desc <| fun b ↦ c.ι.app _))
    (mapPair (α.app _) (Sigma.desc <| fun b ↦ α.app _ ≫ c₁.inj _)) i ?_
    (mapPair_equifibered _)).mp ⟨?_⟩
  rotate_left
  · ext ⟨⟨⟩⟩
    · simpa only [pair_obj_left, Functor.const_obj_obj, pair_obj_right, Discrete.functor_obj,
        NatTrans.comp_app, mapPair_left, BinaryCofan.ι_app_left, BinaryCofan.mk_pt,
        BinaryCofan.mk_inl, Functor.const_map_app, extendCofan_pt,
        extendCofan_ι_app, Fin.cases_zero] using congr_app e ⟨0⟩
    · dsimp
      ext j
      simpa only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
        Category.assoc, extendCofan_pt, Functor.const_obj_obj, NatTrans.comp_app, extendCofan_ι_app,
        Fin.cases_succ, Functor.const_map_app] using congr_app e ⟨j.succ⟩
  · let F' : Fin (n + 1) → C := F.obj ∘ Discrete.mk
    have : F = Discrete.functor F'
    · apply Functor.hext
      · exact fun i ↦ rfl
      · rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
        simp
    clear_value F'
    subst this
    apply BinaryCofan.IsColimit.mk _ (fun {T} f₁ f₂ ↦ Hc.desc (Cofan.mk T (Fin.cases f₁
      (fun i ↦ Sigma.ι (fun (j : Fin n) ↦ (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))))
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_left, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.ι_app_left, BinaryCofan.mk_inl, IsColimit.fac, Cofan.mk_pt, Cofan.mk_ι_app,
        Fin.cases_zero]
    · intro T f₁ f₂
      simp only [Discrete.functor_obj, pair_obj_right, BinaryCofan.mk_pt, Functor.const_obj_obj,
        BinaryCofan.ι_app_right, BinaryCofan.mk_inr]
      ext j
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt,
        Cofan.mk_ι_app, IsColimit.fac, Fin.cases_succ]
    · intro T f₁ f₂ f₃ m₁ m₂
      simp at m₁ m₂ ⊢
      refine Hc.uniq (Cofan.mk T (Fin.cases f₁
        (fun i ↦ Sigma.ι (fun (j : Fin n) ↦ (Discrete.functor F').obj ⟨j.succ⟩) _ ≫ f₂))) _ ?_
      intro ⟨j⟩
      simp only [Discrete.functor_obj, Cofan.mk_pt, Functor.const_obj_obj, Cofan.mk_ι_app]
      induction' j using Fin.inductionOn with j _
      · simp only [Fin.cases_zero, m₁]
      · simp only [← m₂, colimit.ι_desc_assoc, Discrete.functor_obj,
          Cofan.mk_pt, Cofan.mk_ι_app, Fin.cases_succ]
  induction' j using Fin.inductionOn with j _
  · exact t₂' ⟨WalkingPair.left⟩
  · have t₁' := (@t₁ (Discrete.functor (fun j ↦ F.obj ⟨j.succ⟩)) (Cofan.mk _ _) (Discrete.natTrans
      <| fun i ↦ α.app _) (Sigma.desc (fun j ↦ α.app _ ≫ c₁.inj _)) ?_
      (NatTrans.equifibered_of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨j⟩
    rotate_left
    · ext ⟨j⟩
      dsimp
      erw [colimit.ι_desc] -- Why?
      rfl
    simpa [Functor.const_obj_obj, Discrete.functor_obj, extendCofan_pt, extendCofan_ι_app,
      Fin.cases_succ, BinaryCofan.mk_pt, colimit.cocone_x, Cofan.mk_pt, Cofan.mk_ι_app,
      BinaryCofan.ι_app_right, BinaryCofan.mk_inr, colimit.ι_desc,
      Discrete.natTrans_app] using t₁'.paste_horiz (t₂' ⟨WalkingPair.right⟩)

def functorOfIsEmpty (J : Type*) [Category J] (C : Type*) [Category C] [IsEmpty J] : J ⥤ C where
  obj := isEmptyElim
  map := fun {X} ↦ isEmptyElim X
  map_id := fun {X} ↦ isEmptyElim X
  map_comp := fun {X} ↦ isEmptyElim X

instance (α : Type*) [IsEmpty α] : IsEmpty (Discrete α) := Function.isEmpty Discrete.as

def equivalenceOfIsEmpty (J : Type*) [Category J] [IsEmpty J] (K : Type*) [Category K] [IsEmpty K] :
  J ≌ K where
  functor := functorOfIsEmpty J K
  inverse := functorOfIsEmpty K J
  unitIso := NatIso.ofComponents isEmptyElim (fun {X} ↦ isEmptyElim X)
  counitIso := NatIso.ofComponents isEmptyElim (fun {X} ↦ isEmptyElim X)
  functor_unitIso_comp := fun {X} ↦ isEmptyElim X

theorem isVanKampenColimit_of_isEmpty [HasStrictInitialObjects C] [IsEmpty J] {F : J ⥤ C}
  (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  have : IsInitial c.pt
  · have := (IsColimit.precomposeInvEquiv (Functor.uniqueFromEmpty _) _).symm
      (hc.whiskerEquivalence (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J))
    exact IsColimit.ofIsoColimit this (Cocones.ext (Iso.refl c.pt) (fun {X} ↦ isEmptyElim X))
  replace this := IsInitial.isVanKampenColimit this
  apply (IsVanKampenColimit.whiskerEquivalence_iff
    (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)).mp
  exact (this.precompose_isIso (Functor.uniqueFromEmpty
    ((equivalenceOfIsEmpty (Discrete PEmpty.{1}) J).functor ⋙ F)).hom).of_iso
    (Cocones.ext (Iso.refl _) (by simp))

theorem FinitaryExtensive.isVanKampen_finiteCoproducts_Fin [FinitaryExtensive C] {n : ℕ}
  {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  let f : Fin n → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f
  · refine Functor.hext (fun i ↦ rfl) ?_
    rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
    simp
  clear_value f
  subst this
  induction' n with n IH
  · exact isVanKampenColimit_of_isEmpty _ hc
  · apply IsVanKampenColimit.of_iso _
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    apply @isVanKampenColimit_extendCofan _ _ _ _ _ _ _ _ ?_
    · apply IH
      exact coproductIsCoproduct _
    · apply FinitaryExtensive.van_kampen'
      exact coprodIsCoprod _ _
    · dsimp
      infer_instance

theorem FinitaryExtensive.isVanKampen_finiteCoproducts [FinitaryExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

lemma FinitaryExtensive.hasPullbacks_of_is_coproduct [FinitaryExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) {X : C}
    (g : X ⟶ _) : HasPullback g (c.ι.app i) := by
  classical
  let f : ι → C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f
  · refine Functor.hext (fun i ↦ rfl) ?_
    rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
    simp
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
  { hom := Sigma.desc (fun j ↦ if h : j = i then eqToHom (congr_arg f h) ≫ coprod.inl else
      Sigma.ι (fun j : ({i}ᶜ : Set ι) ↦ f j) ⟨j, h⟩ ≫ coprod.inr)
    inv := coprod.desc (Sigma.ι f i) (Sigma.desc <| fun j ↦ Sigma.ι f j)
    hom_inv_id := by aesop_cat
    inv_hom_id := by
      ext j
      · simp
      · simp only [coprod.desc_comp, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
          eqToHom_refl, Category.id_comp, dite_true, BinaryCofan.mk_pt, BinaryCofan.ι_app_right,
          BinaryCofan.mk_inr, colimit.ι_desc_assoc, Discrete.functor_obj, Category.comp_id]
        exact dif_neg j.prop }
  let e' : c.pt ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) ↦ f j) :=
    hc.coconePointUniqueUpToIso (getColimitCocone _).2 ≪≫ e
  have : coprod.inl ≫ e'.inv = c.ι.app ⟨i⟩
  · simp only [Iso.trans_inv, coprod.desc_comp, colimit.ι_desc, BinaryCofan.mk_pt,
      BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    exact colimit.comp_coconePointUniqueUpToIso_inv _ _
  clear_value e'
  rw [← this]
  have : IsPullback (𝟙 _) (g ≫ e'.hom) g e'.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨⟨⟨_, ((IsPullback.of_hasPullback (g ≫ e'.hom) coprod.inl).paste_horiz this).isLimit⟩⟩⟩

instance FinitaryExtensive.hasPullbacks_of_inclusions [FinitaryExtensive C] {X Z : C} {α : Type*}
    (f : X ⟶ Z) {Y : (a : α) → C} (i : (a : α) → Y a ⟶ Z) [Finite α]
    [hi : IsIso (Sigma.desc i)] (a : α) : HasPullback f (i a) := by
  apply FinitaryExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) hi

lemma FinitaryExtensive.sigma_desc_iso [FinitaryExtensive C] {α : Type} [Finite α] {X : C}
    {Z : α → C} (π : (a : α) → Z a ⟶ X) {Y : C} (f : Y ⟶ X) (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _)) := by
  suffices IsColimit (Cofan.mk _ ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _)) by
    change IsIso (this.coconePointUniqueUpToIso (getColimitCocone _).2).inv
    infer_instance
  let : IsColimit (Cofan.mk X π)
  · refine @IsColimit.ofPointIso (t := Cofan.mk X π) (P := coproductIsCoproduct Z) ?_
    convert hπ
    simp [coproductIsCoproduct]
  refine ((FinitaryExtensive.isVanKampen_finiteCoproducts this
    (Cofan.mk _ ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))
    (Discrete.natTrans <| fun i ↦ pullback.snd) f ?_
    (NatTrans.equifibered_of_discrete _)).mpr ?_).some
  · ext
    simp [pullback.condition]
  · exact fun j ↦ IsPullback.of_hasPullback f (π j.as)

end FiniteCoproducts

end Extensive

end CategoryTheory
