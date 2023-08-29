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
  -- ⊢ IsPullback (NatTrans.app c.ι j) (NatTrans.app (𝟙 F) j) (𝟙 c.pt) (NatTrans.ap …
  exact IsPullback.of_vert_isIso ⟨by erw [NatTrans.id_app, Category.comp_id, Category.id_comp]⟩
  -- 🎉 no goals
#align category_theory.is_van_kampen_colimit.is_colimit CategoryTheory.IsVanKampenColimit.isColimit

theorem IsInitial.isVanKampenColimit [HasStrictInitialObjects C] {X : C} (h : IsInitial X) :
    IsVanKampenColimit (asEmptyCocone X) := by
  intro F' c' α f hf hα
  -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete PEmpty), IsPullback (NatTrans.app  …
  have : F' = Functor.empty C := by apply Functor.hext <;> rintro ⟨⟨⟩⟩
  -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete PEmpty), IsPullback (NatTrans.app  …
  subst this
  -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete PEmpty), IsPullback (NatTrans.app  …
  haveI := h.isIso_to f
  -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete PEmpty), IsPullback (NatTrans.app  …
  refine' ⟨by rintro _ ⟨⟨⟩⟩,
    fun _ => ⟨IsColimit.ofIsoColimit h (Cocones.ext (asIso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩
#align category_theory.is_initial.is_van_kampen_colimit CategoryTheory.IsInitial.isVanKampenColimit

section Extensive

variable {X Y : C}

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen.

TODO: Show that this is iff all finite coproducts are van Kampen. -/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  /-- In a finitary extensive category, all coproducts are van Kampen-/
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c
#align category_theory.finitary_extensive CategoryTheory.FinitaryExtensive

attribute [instance] FinitaryExtensive.hasFiniteCoproducts

theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  -- ⊢ IsVanKampenColimit c
  let Y := F.obj ⟨WalkingPair.right⟩
  -- ⊢ IsVanKampenColimit c
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
  clear_value X Y
  -- ⊢ IsVanKampenColimit c
  subst this
  -- ⊢ IsVanKampenColimit c
  exact FinitaryExtensive.van_kampen' c hc
  -- 🎉 no goals
#align category_theory.finitary_extensive.van_kampen CategoryTheory.FinitaryExtensive.vanKampen

theorem mapPair_equifibered {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') :
    NatTrans.Equifibered α := by
  rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩
  -- ⊢ IsPullback (F.map { down := { down := (_ : { as := WalkingPair.left }.as = { …
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
  -- ⊢ IsVanKampenColimit c → ∀ {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X)  …
  · introv H hαX hαY
    -- ⊢ Nonempty (IsColimit c') ↔ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan. …
    rw [H c' (mapPair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (mapPair_equifibered _)]
    -- ⊢ (∀ (j : Discrete WalkingPair), IsPullback (NatTrans.app c'.ι j) (NatTrans.ap …
    constructor
    -- ⊢ (∀ (j : Discrete WalkingPair), IsPullback (NatTrans.app c'.ι j) (NatTrans.ap …
    · intro H
      -- ⊢ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan.inl c) ∧ IsPullback (Binar …
      exact ⟨H _, H _⟩
      -- 🎉 no goals
    · rintro H ⟨⟨⟩⟩
      -- ⊢ IsPullback (NatTrans.app c'.ι { as := WalkingPair.left }) (NatTrans.app (map …
      exacts [H.1, H.2]
      -- 🎉 no goals
  · introv H F' hα h
    -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete WalkingPair), IsPullback (NatTrans …
    let X' := F'.obj ⟨WalkingPair.left⟩
    -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete WalkingPair), IsPullback (NatTrans …
    let Y' := F'.obj ⟨WalkingPair.right⟩
    -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete WalkingPair), IsPullback (NatTrans …
    have : F' = pair X' Y' := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    clear_value X' Y'
    -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete WalkingPair), IsPullback (NatTrans …
    subst this
    -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete WalkingPair), IsPullback (NatTrans …
    change BinaryCofan X' Y' at c'
    -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : Discrete WalkingPair), IsPullback (NatTrans …
    rw [H c' _ _ _ (NatTrans.congr_app hα ⟨WalkingPair.left⟩)
        (NatTrans.congr_app hα ⟨WalkingPair.right⟩)]
    constructor
    -- ⊢ IsPullback (BinaryCofan.inl c') (NatTrans.app α { as := WalkingPair.left })  …
    · rintro H ⟨⟨⟩⟩
      -- ⊢ IsPullback (NatTrans.app c'.ι { as := WalkingPair.left }) (NatTrans.app α {  …
      exacts [H.1, H.2]
      -- 🎉 no goals
    · intro H
      -- ⊢ IsPullback (BinaryCofan.inl c') (NatTrans.app α { as := WalkingPair.left })  …
      exact ⟨H _, H _⟩
      -- 🎉 no goals
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
  -- ⊢ ∀ {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : c'.p …
  introv hX hY
  -- ⊢ Nonempty (IsColimit c') ↔ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan. …
  constructor
  -- ⊢ Nonempty (IsColimit c') → IsPullback (BinaryCofan.inl c') αX f (BinaryCofan. …
  · rintro ⟨h⟩
    -- ⊢ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan.inl c) ∧ IsPullback (Binar …
    let e := h.coconePointUniqueUpToIso (colimits _ _)
    -- ⊢ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan.inl c) ∧ IsPullback (Binar …
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [hX]) (by simp [hY])
    -- ⊢ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan.inl c) ∧ IsPullback (Binar …
    constructor
    -- ⊢ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan.inl c)
    · rw [← Category.id_comp αX, ← Iso.hom_inv_id_assoc e f]
      -- ⊢ IsPullback (BinaryCofan.inl c') (𝟙 X' ≫ αX) (e.hom ≫ e.inv ≫ f) (BinaryCofan …
      haveI : IsIso (𝟙 X') := inferInstance
      -- ⊢ IsPullback (BinaryCofan.inl c') (𝟙 X' ≫ αX) (e.hom ≫ e.inv ≫ f) (BinaryCofan …
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl := by
        dsimp
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hl
      -- 🎉 no goals
    · rw [← Category.id_comp αY, ← Iso.hom_inv_id_assoc e f]
      -- ⊢ IsPullback (BinaryCofan.inr c') (𝟙 Y' ≫ αY) (e.hom ≫ e.inv ≫ f) (BinaryCofan …
      haveI : IsIso (𝟙 Y') := inferInstance
      -- ⊢ IsPullback (BinaryCofan.inr c') (𝟙 Y' ≫ αY) (e.hom ≫ e.inv ≫ f) (BinaryCofan …
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr := by
        dsimp
        simp
      exact (IsPullback.of_vert_isIso ⟨this⟩).paste_vert hr
      -- 🎉 no goals
  · rintro ⟨H₁, H₂⟩
    -- ⊢ Nonempty (IsColimit c')
    refine' ⟨IsColimit.ofIsoColimit _ <| (isoBinaryCofanMk _).symm⟩
    -- ⊢ IsColimit (BinaryCofan.mk (BinaryCofan.inl c') (BinaryCofan.inr c'))
    let e₁ : X' ≅ _ := H₁.isLimit.conePointUniqueUpToIso (limits _ _)
    -- ⊢ IsColimit (BinaryCofan.mk (BinaryCofan.inl c') (BinaryCofan.inr c'))
    let e₂ : Y' ≅ _ := H₂.isLimit.conePointUniqueUpToIso (limits _ _)
    -- ⊢ IsColimit (BinaryCofan.mk (BinaryCofan.inl c') (BinaryCofan.inr c'))
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp
    -- ⊢ IsColimit (BinaryCofan.mk (BinaryCofan.inl c') (BinaryCofan.inr c'))
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp
    -- ⊢ IsColimit (BinaryCofan.mk (BinaryCofan.inl c') (BinaryCofan.inr c'))
    rw [he₁, he₂]
    -- ⊢ IsColimit (BinaryCofan.mk (e₁.hom ≫ PullbackCone.fst (cones f (BinaryCofan.i …
    apply BinaryCofan.isColimitCompRightIso (BinaryCofan.mk _ _)
    -- ⊢ IsColimit (BinaryCofan.mk (e₁.hom ≫ PullbackCone.fst (cones f (BinaryCofan.i …
    apply BinaryCofan.isColimitCompLeftIso (BinaryCofan.mk _ _)
    -- ⊢ IsColimit (BinaryCofan.mk ((cones f (BinaryCofan.inl c)).π.1 WalkingCospan.l …
    exact h₂ f
    -- 🎉 no goals
#align category_theory.binary_cofan.is_van_kampen_mk CategoryTheory.BinaryCofan.isVanKampen_mk

theorem BinaryCofan.mono_inr_of_isVanKampen [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : Mono c.inr := by
  refine' PullbackCone.mono_of_isLimitMkIdId _ (IsPullback.isLimit _)
  -- ⊢ IsPullback (𝟙 ((pair X Y).obj { as := WalkingPair.right })) (𝟙 ((pair X Y).o …
  refine' (h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.right⟩
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
    -- ⊢ NatTrans.app (mapPair (initial.to X) (𝟙 Y) ≫ c.ι) { as := WalkingPair.left } …
                 -- ⊢ initial.to X ≫ BinaryCofan.inl c = initial.to Y ≫ BinaryCofan.inr c
                 -- 🎉 no goals
                        -- 🎉 no goals
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
    -- ⊢ NatTrans.app (mapPair (initial.to X) (𝟙 Y) ≫ c.ι) { as := WalkingPair.left } …
                 -- ⊢ initial.to X ≫ BinaryCofan.inl c = initial.to Y ≫ BinaryCofan.inr c
                 -- 🎉 no goals
                        -- 🎉 no goals
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
      -- ⊢ IsIso f
      suffices IsColimit (BinaryCofan.mk (𝟙 A) (𝟙 A)) by
        obtain ⟨l, h₁, h₂⟩ := Limits.BinaryCofan.IsColimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases(Category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((Category.id_comp _).symm.trans h₁).symm, initialIsInitial.hom_ext _ _⟩⟩
      refine' (H (BinaryCofan.mk (𝟙 _) (𝟙 _)) (mapPair f f) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> simp)
        (mapPair_equifibered _) _).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
      -- ⊢ IsPullback (NatTrans.app (BinaryCofan.mk (𝟙 A) (𝟙 A)).ι { as := WalkingPair. …
                      -- ⊢ IsPullback (𝟙 A) f f (𝟙 (⊥_ C))
                      -- ⊢ IsPullback (𝟙 A) f f (𝟙 (⊥_ C))
        exact IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩)
        -- 🎉 no goals
        -- 🎉 no goals
#align category_theory.has_strict_initial_of_is_universal CategoryTheory.hasStrictInitial_of_isUniversal

instance (priority := 100) hasStrictInitialObjects_of_finitaryExtensive [FinitaryExtensive C] :
    HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryExtensive.vanKampen _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      -- ⊢ IsIso (𝟙 (⊥_ C))
      infer_instance)).some).isUniversal
      -- 🎉 no goals
#align category_theory.has_strict_initial_objects_of_finitary_extensive CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive

theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine' ⟨fun H => H.2 c₀ hc₀, fun H => _⟩
  -- ⊢ FinitaryExtensive C
  constructor
  -- ⊢ ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  -- ⊢ ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → ∀ {X' Y' : C} (c' : BinaryC …
  intro X Y c hc X' Y' c' αX αY f hX hY
  -- ⊢ Nonempty (IsColimit c') ↔ IsPullback (BinaryCofan.inl c') αX f (BinaryCofan. …
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of% hX, hd, Category.assoc])
      (by rw [← reassoc_of% hY, hd', Category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  -- ⊢ IsPullback (BinaryCofan.inl c') (αX ≫ IsTerminal.from HT X) (f ≫ d) (BinaryC …
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]
  -- 🎉 no goals
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
    -- ⊢ IsPullback (BinaryCofan.inl (TopCat.binaryCofan X' Y')) αX f (BinaryCofan.in …
    constructor
    -- ⊢ IsPullback (BinaryCofan.inl (TopCat.binaryCofan X' Y')) αX f (BinaryCofan.in …
    · refine' ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      -- ⊢ (s : PullbackCone f (BinaryCofan.inl (TopCat.binaryCofan (TopCat.of PUnit) ( …
      intro s
      -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (BinaryCofan.inl (TopCat.binary …
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases' h : s.fst x with val val
        · exact ⟨val, rfl, fun y h => Sum.inl_injective h.symm⟩
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val : _).symm
      delta ExistsUnique at this
      -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (BinaryCofan.inl (TopCat.binary …
      choose l hl hl' using this
      -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (BinaryCofan.inl (TopCat.binary …
      refine' ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => ContinuousMap.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inl (α := X') (β := Y')).toInducing.continuous_iff.mpr
      -- ⊢ Continuous (Sum.inl ∘ l)
      convert s.fst.2 using 1
      -- ⊢ Sum.inl ∘ l = (PullbackCone.fst s).toFun
      exact (funext hl).symm
      -- 🎉 no goals
    · refine' ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ _⟩⟩
      -- ⊢ (s : PullbackCone f (BinaryCofan.inr (TopCat.binaryCofan (TopCat.of PUnit) ( …
      intro s
      -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (BinaryCofan.inr (TopCat.binary …
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases' h : s.fst x with val val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val : _).symm
        · exact ⟨val, rfl, fun y h => Sum.inr_injective h.symm⟩
      delta ExistsUnique at this
      -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (BinaryCofan.inr (TopCat.binary …
      choose l hl hl' using this
      -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk (BinaryCofan.inr (TopCat.binary …
      refine' ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          ContinuousMap.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (embedding_inr (α := X') (β := Y')).toInducing.continuous_iff.mpr
      -- ⊢ Continuous (Sum.inr ∘ l)
      convert s.fst.2 using 1
      -- ⊢ Sum.inr ∘ l = (PullbackCone.fst s).toFun
      exact (funext hl).symm
      -- 🎉 no goals
  · intro Z f
    -- ⊢ IsColimit (BinaryCofan.mk (PullbackCone.fst (TopCat.pullbackCone f (BinaryCo …
    exact finitaryExtensiveTopCatAux Z f
    -- 🎉 no goals

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
  -- ⊢ Nonempty (IsColimit c'') ↔ ∀ (j : J), IsPullback (NatTrans.app c''.ι j) (Nat …
  have : c'.ι ≫ (Functor.const J).map e.inv.Hom = c.ι := by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [Functor.map_comp, ← reassoc_of% h, this]) hα]
  -- ⊢ (∀ (j : J), IsPullback (NatTrans.app c''.ι j) (NatTrans.app α j) (f ≫ e.inv. …
  apply forall_congr'
  -- ⊢ ∀ (a : J), IsPullback (NatTrans.app c''.ι a) (NatTrans.app α a) (f ≫ e.inv.H …
  intro j
  -- ⊢ IsPullback (NatTrans.app c''.ι j) (NatTrans.app α j) (f ≫ e.inv.Hom) (NatTra …
  conv_lhs => rw [← Category.comp_id (α.app j)]
  -- ⊢ IsPullback (NatTrans.app c''.ι j) (NatTrans.app α j ≫ 𝟙 (F.obj j)) (f ≫ e.in …
  haveI : IsIso e.inv.Hom := Functor.map_isIso (Cocones.forget _) e.inv
  -- ⊢ IsPullback (NatTrans.app c''.ι j) (NatTrans.app α j ≫ 𝟙 (F.obj j)) (f ≫ e.in …
  exact (IsPullback.of_vert_isIso ⟨by simp⟩).paste_vert_iff (NatTrans.congr_app h j).symm
  -- 🎉 no goals
#align category_theory.is_van_kampen_colimit.of_iso CategoryTheory.IsVanKampenColimit.of_iso

theorem IsVanKampenColimit.of_map {D : Type*} [Category D] (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G] [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : J), IsPullback (NatTrans.app c'.ι j) (NatTr …
  refine' (Iff.trans _ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => _)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
    -- 🎉 no goals
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)
    -- 🎉 no goals
#align category_theory.is_van_kampen_colimit.of_map CategoryTheory.IsVanKampenColimit.of_map

theorem isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
    (c : Cocone F) (hc : ∀ x : C, IsVanKampenColimit (((evaluation C D).obj x).mapCocone c)) :
    IsVanKampenColimit c := by
  intro F' c' α f e hα
  -- ⊢ Nonempty (IsColimit c') ↔ ∀ (j : J), IsPullback (NatTrans.app c'.ι j) (NatTr …
  have := fun x => hc x (((evaluation C D).obj x).mapCocone c') (whiskerRight α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact NatTrans.congr_app (NatTrans.congr_app e y) x)
      (hα.whiskerRight _)
  constructor
  -- ⊢ Nonempty (IsColimit c') → ∀ (j : J), IsPullback (NatTrans.app c'.ι j) (NatTr …
  · rintro ⟨hc'⟩ j
    -- ⊢ IsPullback (NatTrans.app c'.ι j) (NatTrans.app α j) f (NatTrans.app c.ι j)
    refine' ⟨⟨(NatTrans.congr_app e j).symm⟩, ⟨evaluationJointlyReflectsLimits _ _⟩⟩
    -- ⊢ (k : C) → IsLimit (((evaluation C D).obj k).mapCone (PullbackCone.mk (NatTra …
    refine' fun x => (isLimitMapConePullbackConeEquiv _ _).symm _
    -- ⊢ IsLimit (PullbackCone.mk (((evaluation C D).obj x).map (NatTrans.app c'.ι j) …
    exact ((this x).mp ⟨PreservesColimit.preserves hc'⟩ _).isLimit
    -- 🎉 no goals
  · exact fun H => ⟨evaluationJointlyReflectsColimits _ fun x =>
      ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩
#align category_theory.is_van_kampen_colimit_of_evaluation CategoryTheory.isVanKampenColimit_of_evaluation

instance [HasPullbacks C] [FinitaryExtensive C] : FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
    FinitaryExtensive.vanKampen _ <| PreservesColimit.preserves hc⟩

theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C :=
  ⟨fun _ hc => (FinitaryExtensive.vanKampen _ (isColimitOfPreserves F hc)).of_map F⟩
#align category_theory.finitary_extensive_of_preserves_and_reflects CategoryTheory.finitaryExtensive_of_preserves_and_reflects

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [ReflectsIsomorphisms F] :
    FinitaryExtensive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShapeOfReflectsIsomorphisms
  -- ⊢ FinitaryExtensive C
  haveI : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShapeOfReflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F
  -- 🎉 no goals
#align category_theory.finitary_extensive_of_preserves_and_reflects_isomorphism CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism

end Functor

end Extensive

end CategoryTheory
