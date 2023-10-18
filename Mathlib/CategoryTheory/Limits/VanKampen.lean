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

# Universal colimits and van Kampen colimits

## Main definitions
- `CategoryTheory.IsVanKampenColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is universal
  if it is stabler under pullbacks.
- `CategoryTheory.IsUniversalColimit`: A (colimit) cocone over a diagram `F : J ⥤ C` is van
  Kampen if for every cocone `c'` over the pullback of the diagram `F' : J ⥤ C'`,
  `c'` is colimiting iff `c'` is the pullback of `c`.

-/


open CategoryTheory.Limits

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

section NatTrans

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

theorem NatTrans.Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [PreservesLimitsOfShape WalkingCospan H] : Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H
#align category_theory.nat_trans.equifibered.whisker_right CategoryTheory.NatTrans.Equifibered.whiskerRight

theorem NatTrans.Equifibered.whiskerLeft {K : Type*} [Category K]  {F G : J ⥤ C} {α : F ⟶ G}
    (hα : Equifibered α) (H : K ⥤ J) : Equifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem mapPair_equifibered {F F' : Discrete WalkingPair ⥤ C} (α : F ⟶ F') :
    NatTrans.Equifibered α := by
  rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩
  all_goals
    dsimp; simp only [Discrete.functor_map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
#align category_theory.map_pair_equifibered CategoryTheory.mapPair_equifibered

theorem NatTrans.equifibered_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : NatTrans.Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  refine IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

end NatTrans

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

section Functor

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

theorem IsVanKampenColimit.of_mapCocone (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [PreservesLimitsOfShape WalkingCospan G] [ReflectsLimitsOfShape WalkingCospan G]
    [PreservesColimitsOfShape J G] [ReflectsColimitsOfShape J G]
    (H : IsVanKampenColimit (G.mapCocone c)) : IsVanKampenColimit c := by
  intro F' c' α f h hα
  refine' (Iff.trans _ (H (G.mapCocone c') (whiskerRight α G) (G.map f)
      (by ext j; simpa using G.congr_map (NatTrans.congr_app h j))
      (hα.whiskerRight G))).trans (forall_congr' fun j => _)
  · exact ⟨fun h => ⟨isColimitOfPreserves G h.some⟩, fun h => ⟨isColimitOfReflects G h.some⟩⟩
  · exact IsPullback.map_iff G (NatTrans.congr_app h.symm j)
#align category_theory.is_van_kampen_colimit.of_map CategoryTheory.IsVanKampenColimit.of_mapCocone

theorem IsVanKampenColimit.mapCocone_iff (G : C ⥤ D) {F : J ⥤ C} {c : Cocone F}
    [IsEquivalence G] : IsVanKampenColimit (G.mapCocone c) ↔ IsVanKampenColimit c :=
  ⟨IsVanKampenColimit.of_mapCocone G, fun hc ↦ by
    let e : F ⋙ G ⋙ Functor.inv G ≅ F := NatIso.hcomp (Iso.refl F) G.asEquivalence.unitIso.symm
    apply IsVanKampenColimit.of_mapCocone G.inv
    apply (IsVanKampenColimit.precompose_isIso_iff e.inv).mp
    refine hc.of_iso (Cocones.ext (G.asEquivalence.unitIso.app c.pt) ?_)
    simp [Functor.asEquivalence]⟩

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

end Functor

section Initial

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

end Initial

section BinaryCoproduct

variable {X Y : C}

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

theorem BinaryCofan.isPullback_initial_to_of_isVanKampen [HasInitial C] {c : BinaryCofan X Y}
    (h : IsVanKampenColimit c) : IsPullback (initial.to _) (initial.to _) c.inl c.inr := by
  refine' ((h (BinaryCofan.mk (initial.to Y) (𝟙 Y)) (mapPair (initial.to X) (𝟙 Y)) c.inr _
      (mapPair_equifibered _)).mp ⟨_⟩ ⟨WalkingPair.left⟩).flip
  · ext ⟨⟨⟩⟩ <;> dsimp; simp
  · exact ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some
#align category_theory.binary_cofan.is_pullback_initial_to_of_is_van_kampen CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen

end BinaryCoproduct

section FiniteCoproducts

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

end FiniteCoproducts

end CategoryTheory
