/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.extensive
! leanprover-community/mathlib commit 178a32653e369dce2da68dc6b2694e385d484ef1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.CommSq
import Mathbin.CategoryTheory.Limits.Shapes.StrictInitial
import Mathbin.CategoryTheory.Limits.Shapes.Types
import Mathbin.Topology.Category.Top.Limits.Pullbacks
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!

# Extensive categories

## Main definitions
- `category_theory.is_van_kampen_colimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.
- `category_theory.finitary_extensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `category_theory.has_strict_initial_objects_of_finitary_extensive`: The initial object
  in extensive categories is strict.
- `category_theory.finitary_extensive.mono_inr_of_is_colimit`: Coproduct injections are monic in
  extensive categories.
- `category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `category_theory.types.finitary_extensive`: The category of types is extensive.

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

theorem NatTrans.equifibered_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : α.Equifibered :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩
#align category_theory.nat_trans.equifibered_of_is_iso CategoryTheory.NatTrans.equifibered_of_isIso

theorem NatTrans.Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : α.Equifibered)
    (hβ : β.Equifibered) : (α ≫ β).Equifibered := fun i j f => (hα f).paste_vert (hβ f)
#align category_theory.nat_trans.equifibered.comp CategoryTheory.NatTrans.Equifibered.comp

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is universal if it is stable under pullbacks. -/
def IsUniversalColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (h : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (hα : α.Equifibered),
    (∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)) → Nonempty (IsColimit c')
#align category_theory.is_universal_colimit CategoryTheory.IsUniversalColimit

/-- A (colimit) cocone over a diagram `F : J ⥤ C` is van Kampen if for every cocone `c'` over the
pullback of the diagram `F' : J ⥤ C'`, `c'` is colimiting iff `c'` is the pullback of `c`.

TODO: Show that this is iff the functor `C ⥤ Catᵒᵖ` sending `x` to `C/x` preserves it.
TODO: Show that this is iff the inclusion functor `C ⥤ Span(C)` preserves it.
-/
def IsVanKampenColimit {F : J ⥤ C} (c : Cocone F) : Prop :=
  ∀ ⦃F' : J ⥤ C⦄ (c' : Cocone F') (α : F' ⟶ F) (f : c'.pt ⟶ c.pt)
    (h : α ≫ c.ι = c'.ι ≫ (Functor.const J).map f) (hα : α.Equifibered),
    Nonempty (IsColimit c') ↔ ∀ j : J, IsPullback (c'.ι.app j) (α.app j) f (c.ι.app j)
#align category_theory.is_van_kampen_colimit CategoryTheory.IsVanKampenColimit

theorem IsVanKampenColimit.is_universal {F : J ⥤ C} {c : Cocone F} (H : IsVanKampenColimit c) :
    IsUniversalColimit c := fun _ c' α f h hα => (H c' α f h hα).mpr
#align category_theory.is_van_kampen_colimit.is_universal CategoryTheory.IsVanKampenColimit.is_universal

/-- A van Kampen colimit is a colimit. -/
noncomputable def IsVanKampenColimit.isColimit {F : J ⥤ C} {c : Cocone F}
    (h : IsVanKampenColimit c) : IsColimit c :=
  by
  refine'
    ((h c (𝟙 F) (𝟙 c.X : _) (by rw [Functor.map_id, category.comp_id, category.id_comp])
            (nat_trans.equifibered_of_is_iso _)).mpr
        fun j => _).some
  haveI : is_iso (𝟙 c.X) := inferInstance
  exact is_pullback.of_vert_is_iso ⟨by erw [nat_trans.id_app, category.comp_id, category.id_comp]⟩
#align category_theory.is_van_kampen_colimit.is_colimit CategoryTheory.IsVanKampenColimit.isColimit

theorem IsInitial.isVanKampenColimit [HasStrictInitialObjects C] {X : C} (h : IsInitial X) :
    IsVanKampenColimit (asEmptyCocone X) :=
  by
  intro F' c' α f hf hα
  have : F' = functor.empty C := by apply functor.hext <;> rintro ⟨⟨⟩⟩
  subst this
  haveI := h.is_iso_to f
  refine'
    ⟨by rintro _ ⟨⟨⟩⟩, fun _ =>
      ⟨is_colimit.of_iso_colimit h (cocones.ext (as_iso f).symm <| by rintro ⟨⟨⟩⟩)⟩⟩
#align category_theory.is_initial.is_van_kampen_colimit CategoryTheory.IsInitial.isVanKampenColimit

section Extensive

variable {X Y : C}

/-- A category is (finitary) extensive if it has finite coproducts,
and binary coproducts are van Kampen.

TODO: Show that this is iff all finite coproducts are van Kampen. -/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [HasFiniteCoproducts : HasFiniteCoproducts C]
  van_kampen' : ∀ {X Y : C} (c : BinaryCofan X Y), IsColimit c → IsVanKampenColimit c
#align category_theory.finitary_extensive CategoryTheory.FinitaryExtensive

attribute [instance] finitary_extensive.has_finite_coproducts

theorem FinitaryExtensive.van_kampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c :=
  by
  let X := F.obj ⟨walking_pair.left⟩
  let Y := F.obj ⟨walking_pair.right⟩
  have : F = pair X Y := by
    apply functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simpa
  clear_value X Y
  subst this
  exact finitary_extensive.van_kampen' c hc
#align category_theory.finitary_extensive.van_kampen CategoryTheory.FinitaryExtensive.van_kampen

theorem map_pair_equifibered {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') : α.Equifibered :=
  by
  rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩
  all_goals
    dsimp; simp only [discrete.functor_map_id]
    exact is_pullback.of_horiz_is_iso ⟨by simp only [category.comp_id, category.id_comp]⟩
#align category_theory.map_pair_equifibered CategoryTheory.map_pair_equifibered

theorem BinaryCofan.is_van_kampen_iff (c : BinaryCofan X Y) :
    IsVanKampenColimit c ↔
      ∀ {X' Y' : C} (c' : BinaryCofan X' Y') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : c'.pt ⟶ c.pt)
        (hαX : αX ≫ c.inl = c'.inl ≫ f) (hαY : αY ≫ c.inr = c'.inr ≫ f),
        Nonempty (IsColimit c') ↔ IsPullback c'.inl αX f c.inl ∧ IsPullback c'.inr αY f c.inr :=
  by
  constructor
  · introv H hαX hαY
    rw [H c' (map_pair αX αY) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> assumption) (map_pair_equifibered _)]
    constructor
    · intro H
      exact ⟨H _, H _⟩
    · rintro H ⟨⟨⟩⟩
      exacts[H.1, H.2]
  · introv H F' hα h
    let X' := F'.obj ⟨walking_pair.left⟩
    let Y' := F'.obj ⟨walking_pair.right⟩
    have : F' = pair X' Y' := by
      apply functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simpa
    clear_value X' Y'
    subst this
    change binary_cofan X' Y' at c'
    rw [H c' _ _ _ (nat_trans.congr_app hα ⟨walking_pair.left⟩)
        (nat_trans.congr_app hα ⟨walking_pair.right⟩)]
    constructor
    · rintro H ⟨⟨⟩⟩
      exacts[H.1, H.2]
    · intro H
      exact ⟨H _, H _⟩
#align category_theory.binary_cofan.is_van_kampen_iff CategoryTheory.BinaryCofan.is_van_kampen_iff

theorem BinaryCofan.is_van_kampen_mk {X Y : C} (c : BinaryCofan X Y)
    (cofans : ∀ X Y : C, BinaryCofan X Y) (colimits : ∀ X Y, IsColimit (cofans X Y))
    (cones : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), PullbackCone f g)
    (limits : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), IsLimit (cones f g))
    (h₁ :
      ∀ {X' Y' : C} (αX : X' ⟶ X) (αY : Y' ⟶ Y) (f : (cofans X' Y').pt ⟶ c.pt)
        (hαX : αX ≫ c.inl = (cofans X' Y').inl ≫ f) (hαY : αY ≫ c.inr = (cofans X' Y').inr ≫ f),
        IsPullback (cofans X' Y').inl αX f c.inl ∧ IsPullback (cofans X' Y').inr αY f c.inr)
    (h₂ :
      ∀ {Z : C} (f : Z ⟶ c.pt),
        IsColimit (BinaryCofan.mk (cones f c.inl).fst (cones f c.inr).fst)) :
    IsVanKampenColimit c := by
  rw [binary_cofan.is_van_kampen_iff]
  introv hX hY
  constructor
  · rintro ⟨h⟩
    let e := h.cocone_point_unique_up_to_iso (colimits _ _)
    obtain ⟨hl, hr⟩ := h₁ αX αY (e.inv ≫ f) (by simp [hX]) (by simp [hY])
    constructor
    · rw [← category.id_comp αX, ← iso.hom_inv_id_assoc e f]
      have : c'.inl ≫ e.hom = 𝟙 X' ≫ (cofans X' Y').inl :=
        by
        dsimp
        simp
      haveI : is_iso (𝟙 X') := inferInstance
      exact (is_pullback.of_vert_is_iso ⟨this⟩).paste_vert hl
    · rw [← category.id_comp αY, ← iso.hom_inv_id_assoc e f]
      have : c'.inr ≫ e.hom = 𝟙 Y' ≫ (cofans X' Y').inr :=
        by
        dsimp
        simp
      haveI : is_iso (𝟙 Y') := inferInstance
      exact (is_pullback.of_vert_is_iso ⟨this⟩).paste_vert hr
  · rintro ⟨H₁, H₂⟩
    refine' ⟨is_colimit.of_iso_colimit _ <| (iso_binary_cofan_mk _).symm⟩
    let e₁ : X' ≅ _ := H₁.is_limit.cone_point_unique_up_to_iso (limits _ _)
    let e₂ : Y' ≅ _ := H₂.is_limit.cone_point_unique_up_to_iso (limits _ _)
    have he₁ : c'.inl = e₁.hom ≫ (cones f c.inl).fst := by simp
    have he₂ : c'.inr = e₂.hom ≫ (cones f c.inr).fst := by simp
    rw [he₁, he₂]
    apply binary_cofan.is_colimit_comp_right_iso (binary_cofan.mk _ _)
    apply binary_cofan.is_colimit_comp_left_iso (binary_cofan.mk _ _)
    exact h₂ f
#align category_theory.binary_cofan.is_van_kampen_mk CategoryTheory.BinaryCofan.is_van_kampen_mk

theorem BinaryCofan.mono_inr_of_is_van_kampen [HasInitial C] {X Y : C} {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : Mono c.inr :=
  by
  refine' pullback_cone.mono_of_is_limit_mk_id_id _ (is_pullback.is_limit _)
  refine'
    (h (binary_cofan.mk (initial.to Y) (𝟙 Y)) (map_pair (initial.to X) (𝟙 Y)) c.inr _
          (map_pair_equifibered _)).mp
      ⟨_⟩ ⟨walking_pair.right⟩
  · ext ⟨⟨⟩⟩ <;> dsimp <;> simp
  ·
    exact
      ((binary_cofan.is_colimit_iff_is_iso_inr initial_is_initial _).mpr
          (by
            dsimp
            infer_instance)).some
#align category_theory.binary_cofan.mono_inr_of_is_van_kampen CategoryTheory.BinaryCofan.mono_inr_of_is_van_kampen

theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_is_van_kampen (FinitaryExtensive.van_kampen c hc)
#align category_theory.finitary_extensive.mono_inr_of_is_colimit CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit

theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)
#align category_theory.finitary_extensive.mono_inl_of_is_colimit CategoryTheory.FinitaryExtensive.mono_inl_of_isColimit

instance [FinitaryExtensive C] (X Y : C) : Mono (coprod.inl : X ⟶ X ⨿ Y) :=
  (FinitaryExtensive.mono_inl_of_isColimit (coprodIsCoprod X Y) : _)

instance [FinitaryExtensive C] (X Y : C) : Mono (coprod.inr : Y ⟶ X ⨿ Y) :=
  (FinitaryExtensive.mono_inr_of_isColimit (coprodIsCoprod X Y) : _)

theorem BinaryCofan.isPullback_initial_to_of_is_van_kampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  by
  refine'
    ((h (binary_cofan.mk (initial.to Y) (𝟙 Y)) (map_pair (initial.to X) (𝟙 Y)) c.inr _
            (map_pair_equifibered _)).mp
        ⟨_⟩ ⟨walking_pair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> dsimp <;> simp
  ·
    exact
      ((binary_cofan.is_colimit_iff_is_iso_inr initial_is_initial _).mpr
          (by
            dsimp
            infer_instance)).some
#align category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen CategoryTheory.BinaryCofan.isPullback_initial_to_of_is_van_kampen

theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_is_van_kampen (FinitaryExtensive.van_kampen c hc)
#align category_theory.finitary_extensive.is_pullback_initial_to_binary_cofan CategoryTheory.FinitaryExtensive.isPullback_initial_to_binaryCofan

theorem has_strict_initial_of_is_universal [HasInitial C]
    (H : IsUniversalColimit (BinaryCofan.mk (𝟙 (⊥_ C)) (𝟙 (⊥_ C)))) : HasStrictInitialObjects C :=
  hasStrictInitialObjects_of_initial_is_strict
    (by
      intro A f
      suffices is_colimit (binary_cofan.mk (𝟙 A) (𝟙 A))
        by
        obtain ⟨l, h₁, h₂⟩ := limits.binary_cofan.is_colimit.desc' this (f ≫ initial.to A) (𝟙 A)
        rcases(category.id_comp _).symm.trans h₂ with rfl
        exact ⟨⟨_, ((category.id_comp _).symm.trans h₁).symm, initial_is_initial.hom_ext _ _⟩⟩
      refine'
        (H (binary_cofan.mk (𝟙 _) (𝟙 _)) (map_pair f f) f (by ext ⟨⟨⟩⟩ <;> dsimp <;> simp)
            (map_pair_equifibered _) _).some
      rintro ⟨⟨⟩⟩ <;> dsimp <;>
        exact is_pullback.of_horiz_is_iso ⟨(category.id_comp _).trans (category.comp_id _).symm⟩)
#align category_theory.has_strict_initial_of_is_universal CategoryTheory.has_strict_initial_of_is_universal

instance (priority := 100) hasStrictInitialObjects_of_finitaryExtensive [FinitaryExtensive C] :
    HasStrictInitialObjects C :=
  has_strict_initial_of_is_universal
    (FinitaryExtensive.van_kampen _
        ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr
            (by
              dsimp
              infer_instance)).some).is_universal
#align category_theory.has_strict_initial_objects_of_finitary_extensive CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive

theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ :=
  by
  refine' ⟨fun H => H.2 c₀ hc₀, fun H => _⟩
  constructor
  simp_rw [binary_cofan.is_van_kampen_iff] at H⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    limits.binary_cofan.is_colimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of hX, hd, category.assoc])
      (by rw [← reassoc_of hY, hd', category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  rw [hl.paste_vert_iff hX.symm, hr.paste_vert_iff hY.symm]
#align category_theory.finitary_extensive_iff_of_is_terminal CategoryTheory.finitaryExtensive_iff_of_isTerminal

instance types.finitaryExtensive : FinitaryExtensive (Type u) :=
  by
  rw [finitary_extensive_iff_of_is_terminal (Type u) PUnit types.is_terminal_punit _
      (types.binary_coproduct_colimit _ _)]
  apply
    binary_cofan.is_van_kampen_mk _ _ (fun X Y => types.binary_coproduct_colimit X Y) _
      fun X Y Z f g => (limits.types.pullback_limit_cone f g).2
  · intros
    constructor
    · refine' ⟨⟨hαX.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases h : s.fst x
        · simp_rw [sum.inl_injective.eq_iff]
          exact exists_unique_eq'
        · apply_fun f  at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαY val : _).symm
      delta ExistsUnique at this
      choose l hl hl'
      exact
        ⟨l, (funext hl).symm, types.is_terminal_punit.hom_ext _ _, fun l' h₁ h₂ =>
          funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
    · refine' ⟨⟨hαY.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩
      intro s
      dsimp
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases h : s.fst x
        · apply_fun f  at h
          cases ((congr_fun s.condition x).symm.trans h).trans (congr_fun hαX val : _).symm
        · simp_rw [sum.inr_injective.eq_iff]
          exact exists_unique_eq'
      delta ExistsUnique at this
      choose l hl hl'
      exact
        ⟨l, (funext hl).symm, types.is_terminal_punit.hom_ext _ _, fun l' h₁ h₂ =>
          funext fun x => hl' x (l' x) (congr_fun h₁ x).symm⟩
  · intro Z f
    dsimp [limits.types.binary_coproduct_cocone]
    delta types.pullback_obj
    have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit :=
      by
      intro x
      rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      exacts[Or.inl rfl, Or.inr rfl]
    let eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, by convert p.2⟩, fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext <;> rfl, fun _ =>
        by ext <;> rfl⟩
    let eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩, fun x =>
        ⟨⟨_, _⟩, x.2⟩, fun _ => by ext <;> rfl, fun _ => by ext <;> rfl⟩
    fapply binary_cofan.is_colimit_mk
    ·
      exact fun s x =>
        dite _ (fun h => s.inl <| eX.symm ⟨x, h⟩) fun h =>
          s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, _⟩
      dsimp
      split_ifs <;> rfl
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, hx⟩
      dsimp
      split_ifs
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

/-- (Implementation) An auxiliary lemma for the proof that `Top` is finitary extensive. -/
def finitaryExtensiveTopAux (Z : TopCat.{u}) (f : Z ⟶ TopCat.of (Sum PUnit.{u + 1} PUnit.{u + 1})) :
    IsColimit
      (BinaryCofan.mk
        (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
        (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) :=
  by
  have : ∀ x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit :=
    by
    intro x
    rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
    exacts[Or.inl rfl, Or.inr rfl]
  let eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
    ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inl <| Subsingleton.elim _ _)⟩, fun x =>
      ⟨⟨_, _⟩, x.2⟩, fun _ => by ext <;> rfl, fun _ => by ext <;> rfl⟩
  let eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
    ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩, fun x =>
      ⟨⟨_, _⟩, x.2⟩, fun _ => by ext <;> rfl, fun _ => by ext <;> rfl⟩
  fapply binary_cofan.is_colimit_mk
  · refine' fun s =>
      ⟨fun x =>
        dite _ (fun h => s.inl <| eX.symm ⟨x, h⟩) fun h =>
          s.inr <| eY.symm ⟨x, (this x).resolve_left h⟩,
        _⟩
    rw [continuous_iff_continuousAt]
    intro x
    by_cases f x = Sum.inl PUnit.unit
    · revert h x
      apply (IsOpen.continuousOn_iff _).mp
      · rw [continuousOn_iff_continuous_restrict]
        convert_to Continuous fun x : { x | f x = Sum.inl PUnit.unit } =>
            s.inl ⟨(x, PUnit.unit), x.2⟩
        · ext ⟨x, hx⟩
          exact dif_pos hx
        continuity
      · convert f.2.1 _ openEmbedding_inl.open_range
        ext x
        exact
          ⟨fun h => ⟨_, h.symm⟩, fun ⟨e, h⟩ =>
            h.symm.trans (congr_arg Sum.inl <| Subsingleton.elim _ _)⟩
    · revert h x
      apply (IsOpen.continuousOn_iff _).mp
      · rw [continuousOn_iff_continuous_restrict]
        convert_to Continuous fun x : { x | f x ≠ Sum.inl PUnit.unit } =>
            s.inr ⟨(x, PUnit.unit), (this _).resolve_left x.2⟩
        · ext ⟨x, hx⟩
          exact dif_neg hx
        continuity
      · convert f.2.1 _ openEmbedding_inr.open_range
        ext x
        change f x ≠ Sum.inl PUnit.unit ↔ f x ∈ Set.range Sum.inr
        trans f x = Sum.inr PUnit.unit
        ·
          rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;>
            simp only [iff_self_iff, eq_self_iff_true, not_true, Ne.def, not_false_iff]
        ·
          exact
            ⟨fun h => ⟨_, h.symm⟩, fun ⟨e, h⟩ =>
              h.symm.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩
  · intro s
    ext ⟨⟨x, ⟨⟩⟩, _⟩
    change dite _ _ _ = _
    split_ifs <;> rfl
  · intro s
    ext ⟨⟨x, ⟨⟩⟩, hx⟩
    change dite _ _ _ = _
    split_ifs
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
#align category_theory.finitary_extensive_Top_aux CategoryTheory.finitaryExtensiveTopAux

instance : FinitaryExtensive TopCat.{u} :=
  by
  rw [finitary_extensive_iff_of_is_terminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply
    binary_cofan.is_van_kampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun X Y Z f g => TopCat.pullbackConeIsLimit f g
  · intros
    constructor
    · refine' ⟨⟨hαX.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩
      intro s
      have : ∀ x, ∃! y, s.fst x = Sum.inl y := by
        intro x
        cases h : s.fst x
        · simp_rw [sum.inl_injective.eq_iff]
          exact exists_unique_eq'
        · apply_fun f  at h
          cases
            ((concrete_category.congr_hom s.condition x).symm.trans h).trans
              (concrete_category.congr_hom hαY val : _).symm
      delta ExistsUnique at this
      choose l hl hl'
      refine'
        ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, Top.is_terminal_punit.hom_ext _ _,
          fun l' h₁ h₂ =>
          ContinuousMap.ext fun x => hl' x (l' x) (concrete_category.congr_hom h₁ x).symm⟩
      apply embedding_inl.to_inducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
    · refine' ⟨⟨hαY.symm⟩, ⟨pullback_cone.is_limit_aux' _ _⟩⟩
      intro s
      dsimp
      have : ∀ x, ∃! y, s.fst x = Sum.inr y := by
        intro x
        cases h : s.fst x
        · apply_fun f  at h
          cases
            ((concrete_category.congr_hom s.condition x).symm.trans h).trans
              (concrete_category.congr_hom hαX val : _).symm
        · simp_rw [sum.inr_injective.eq_iff]
          exact exists_unique_eq'
      delta ExistsUnique at this
      choose l hl hl'
      refine'
        ⟨⟨l, _⟩, ContinuousMap.ext fun a => (hl a).symm, Top.is_terminal_punit.hom_ext _ _,
          fun l' h₁ h₂ =>
          ContinuousMap.ext fun x => hl' x (l' x) (concrete_category.congr_hom h₁ x).symm⟩
      apply embedding_inr.to_inducing.continuous_iff.mpr
      convert s.fst.2 using 1
      exact (funext hl).symm
  · intro Z f
    exact finitary_extensive_Top_aux Z f

end TopCat

section Functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

theorem NatTrans.Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : α.Equifibered) (H : C ⥤ D)
    [PreservesLimitsOfShape WalkingCospan H] : (whiskerRight α H).Equifibered := fun i j f =>
  (hα f).map H
#align category_theory.nat_trans.equifibered.whisker_right CategoryTheory.NatTrans.Equifibered.whiskerRight

theorem IsVanKampenColimit.of_iso {F : J ⥤ C} {c c' : Cocone F} (H : IsVanKampenColimit c)
    (e : c ≅ c') : IsVanKampenColimit c' :=
  by
  intro F' c'' α f h hα
  have : c'.ι ≫ (Functor.Const J).map e.inv.hom = c.ι :=
    by
    ext j
    exact e.inv.2 j
  rw [H c'' α (f ≫ e.inv.1) (by rw [functor.map_comp, ← reassoc_of h, this]) hα]
  apply forall_congr'
  intro j
  conv_lhs => rw [← category.comp_id (α.app j)]
  haveI : is_iso e.inv.hom := functor.map_is_iso (cocones.forget _) e.inv
  exact (is_pullback.of_vert_is_iso ⟨by simp⟩).paste_vert_iff (nat_trans.congr_app h j).symm
#align category_theory.is_van_kampen_colimit.of_iso CategoryTheory.IsVanKampenColimit.of_iso

theorem IsVanKampenColimit.of_map {D : Type _} [Category D] (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G] [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c :=
  by
  intro F' c' α f h hα
  refine'
    (Iff.trans _
          (H (G.map_cocone c') (whisker_right α G) (G.map f)
            (by
              ext j
              simpa using G.congr_map (nat_trans.congr_app h j))
            (hα.whisker_right G))).trans
      (forall_congr' fun j => _)
  · exact ⟨fun h => ⟨is_colimit_of_preserves G h.some⟩, fun h => ⟨is_colimit_of_reflects G h.some⟩⟩
  · exact is_pullback.map_iff G (nat_trans.congr_app h.symm j)
#align category_theory.is_van_kampen_colimit.of_map CategoryTheory.IsVanKampenColimit.of_map

theorem isVanKampenColimit_of_evaluation [HasPullbacks D] [HasColimitsOfShape J D] (F : J ⥤ C ⥤ D)
    (c : Cocone F) (hc : ∀ x : C, IsVanKampenColimit (((evaluation C D).obj x).mapCocone c)) :
    IsVanKampenColimit c := by
  intro F' c' α f e hα
  have := fun x =>
    hc x (((evaluation C D).obj x).mapCocone c') (whisker_right α _)
      (((evaluation C D).obj x).map f)
      (by
        ext y
        dsimp
        exact nat_trans.congr_app (nat_trans.congr_app e y) x)
      (hα.whisker_right _)
  constructor
  · rintro ⟨hc'⟩ j
    refine' ⟨⟨(nat_trans.congr_app e j).symm⟩, ⟨evaluation_jointly_reflects_limits _ _⟩⟩
    refine' fun x => (is_limit_map_cone_pullback_cone_equiv _ _).symm _
    exact ((this x).mp ⟨preserves_colimit.preserves hc'⟩ _).IsLimit
  ·
    exact fun H =>
      ⟨evaluation_jointly_reflects_colimits _ fun x =>
          ((this x).mpr fun j => (H j).map ((evaluation C D).obj x)).some⟩
#align category_theory.is_van_kampen_colimit_of_evaluation CategoryTheory.isVanKampenColimit_of_evaluation

instance [HasPullbacks C] [FinitaryExtensive C] : FinitaryExtensive (D ⥤ C) :=
  haveI : has_finite_coproducts (D ⥤ C) := ⟨fun n => limits.functor_category_has_colimits_of_shape⟩
  ⟨fun X Y c hc =>
    is_van_kampen_colimit_of_evaluation _ c fun x =>
      finitary_extensive.van_kampen _ <| preserves_colimit.preserves hc⟩

theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C :=
  ⟨fun X Y c hc => (FinitaryExtensive.van_kampen _ (isColimitOfPreserves F hc)).of_map F⟩
#align category_theory.finitary_extensive_of_preserves_and_reflects CategoryTheory.finitaryExtensive_of_preserves_and_reflects

theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [ReflectsIsomorphisms F] :
    FinitaryExtensive C :=
  by
  haveI : reflects_limits_of_shape walking_cospan F :=
    reflects_limits_of_shape_of_reflects_isomorphisms
  haveI : reflects_colimits_of_shape (discrete walking_pair) F :=
    reflects_colimits_of_shape_of_reflects_isomorphisms
  exact finitary_extensive_of_preserves_and_reflects F
#align category_theory.finitary_extensive_of_preserves_and_reflects_isomorphism CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism

end Functor

end Extensive

end CategoryTheory

