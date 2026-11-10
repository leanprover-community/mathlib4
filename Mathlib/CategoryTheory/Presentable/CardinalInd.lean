/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.IsClosedUnderCardinalFilteredColimits
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# `κ`-ind objects

Let `C` be a locally small `w`-small category and `κ : Cardinal.{w}` be a regular cardinal`.
For a presheaf `P : Cᵒᵖ ⥤ Type w`, we introduce a typeclass `P.IsCardinalIndObject κ`
saying that `P` is a `κ`-ind object in `C`. The lemma `Functor.isCardinalIndObject_iff`
characterizes `κ`-ind objects as (small) `κ`-filtered colimits of representable presheaves.
We define the full subcategory `CardinalInd C κ` of `Cᵒᵖ ⥤ Type w` consisting of
`κ`-ind objects in `C`. We show that `CardinalInd C κ` is also locally `w`-small and
we show that the corresponding property of objects `isCardinalIndObject C κ`
of `Cᵒᵖ ⥤ Type w` is closed under `κ`-filtered colimits.
The inclusion `CardinalInd C κ ⥤ Cᵒᵖ ⥤ Type w` preserves with all limits.

When `C` is essentially `w`-small, we show that `CardinalInd C κ` is a `κ`-accessible
category.

## Implementation notes

If `P : Cᵒᵖ ⥤ Type w` is a presheaf, we do not define `P.IsCardinalIndObject κ`
by saying that the exists a presentation of `P` as a small `κ`-filtered colimit
of representable presheaves. Instead, we define this property by requiring
that the opposite category `P.Elementsᵒᵖ` of the category of elements of `P`
is both `κ`-filtered and finally `w`-small (i.e. `P.Elements` is initially `w`-small).
Using this definition, it is relatively easy to show that `κ`-ind objects are
closed under `κ`-filtered colimits. We do this in two steps, by showing first
that the stability under `κ`-filtered colimits of the property
`Presheaf.isCardinalFilteredElementsOp` satisfied by functors `P` such that
`P.Elementsᵒᵖ` is `κ`-filtered, and secondly that when we restrict to presheaves
satisfying this property, the initially `w`-small condition is closed under
`κ`-filtered colimits.

Using the tautological cocone expressing a presheaf `P` as a colimit indexed by
its category of elements, we easily obtain that `κ`-ind objects are `κ`-filtered
colimits of representable presheaves. Using the fact that a representable functor
is a `κ`-ind object and that `κ`-ind objects are closed under `κ`-filtered colimits,
we obtain that `κ`-ind objects are exactly the `κ`-filtered colimits of
representable presheaves.

-/

public section

universe w₁ w₂ w

namespace CategoryTheory

open Opposite Limits

variable {C D : Type*} [Category* C] [Category* D]

namespace Presheaf

variable (C) in
/-- The property of objects in `C ⥤ Type w` that is satisfied by
the functors `P` such that `P.Elementsᵒᵖ` is `κ`-filtered. -/
abbrev isCardinalFilteredElementsOp (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ObjectProperty (C ⥤ Type w) :=
  fun P ↦ IsCardinalFiltered P.Elementsᵒᵖ κ

instance (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (P : (isCardinalFilteredElementsOp C κ).FullSubcategory) :
  IsCardinalFiltered P.obj.Elementsᵒᵖ κ := P.property

@[simp]
lemma isCardinalFilteredElementsOp_iff
    (P : C ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    isCardinalFilteredElementsOp C κ P ↔ IsCardinalFiltered P.Elementsᵒᵖ κ := Iff.rfl

lemma isCardinalFilteredElementsOp_shrinkCoyoneda_obj [LocallySmall.{w} C]
    (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    isCardinalFilteredElementsOp C κ (shrinkCoyoneda.{w}.obj (op X)) := by
  have := (Functor.Elements.isInitialShrinkCoyonedaObj (op X)).hasInitial
  apply isCardinalFiltered_of_hasTerminal

lemma isCardinalFilteredElementsOp_shrinkYoneda_obj [LocallySmall.{w} C]
    (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    isCardinalFilteredElementsOp Cᵒᵖ κ (CategoryTheory.shrinkYoneda.{w}.obj X) := by
  have := (Functor.Elements.isInitialShrinkYonedaObj X).hasInitial
  apply isCardinalFiltered_of_hasTerminal

open CategoryTheory.Functor IsCardinalFiltered in
instance (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalFilteredElementsOp C κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    intro P ⟨p⟩
    have := p.prop_diag_obj
    have := isFiltered_of_isCardinalFiltered J κ
    simp only [isCardinalFiltered_iff]
    refine ⟨fun ι e hι ↦ ?_, fun ι ⟨e₁⟩ ⟨e₂⟩ f hι ↦ ?_⟩
    · choose j₁ s₁ hs₁ using fun i ↦ Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves ((evaluation ..).obj _) p.isColimit) (e i).unop.val
      dsimp at s₁ hs₁
      let t (i : ι) : (p.diag.obj (max j₁ hι)).Elementsᵒᵖ :=
        (op (Functor.elementsMk _ _ ((p.diag.map (toMax j₁ hι i)).app _ (s₁ i))))
      refine ⟨(p.ι.app _).mapElements.op.obj (max t hι),
        fun i ↦ ⟨(Elements.homMk ?_ ?_).op⟩⟩
      · exact (toMax t hι i).unop.hom
      · dsimp
        rw [← NatTrans.naturality_apply, (toMax t hι i).unop.map_val,
          ← hs₁, ← NatTrans.comp_app_apply, p.w]
    · have (e : P.Elements) :
          ∃ j e', (p.ι.app j).mapElements.obj e' = e := by
        obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves ((evaluation ..).obj _) p.isColimit) e.val
        exact ⟨j, elementsMk _ _ x, Elements.ext _ _ rfl (by simpa)⟩
      obtain ⟨j, e₁, e₂, rfl, rfl⟩ :
          ∃ (j : J) (e₁' e₂' : (p.diag.obj j).Elements),
            (p.ι.app j).mapElements.obj e₁' = e₁ ∧
            (p.ι.app j).mapElements.obj e₂' = e₂ := by
        obtain ⟨j₁, e₁, rfl⟩ := this e₁
        obtain ⟨j₂, e₂, rfl⟩ := this e₂
        refine ⟨IsFiltered.max j₁ j₂,
          (p.diag.map (IsFiltered.leftToMax j₁ j₂)).mapElements.obj e₁,
          (p.diag.map (IsFiltered.rightToMax j₁ j₂)).mapElements.obj e₂, ?_, ?_⟩
        all_goals simp [← NatTrans.mapElements_comp_obj]
      have (i : ι) : ∃ (j' : J) (g : j ⟶ j')
          (φ : (p.diag.map g).mapElements.obj e₂ ⟶ (p.diag.map g).mapElements.obj e₁),
            (f i).unop.hom = φ.hom := by
        have := (f i).unop.map_val
        dsimp at this
        rw [← dsimp% (p.ι.app j).naturality_apply (f i).unop.hom] at this
        obtain ⟨j', g, h⟩ := (Types.FilteredColimit.isColimit_eq_iff'
          ((isColimitOfPreserves ((evaluation ..).obj e₁.obj) p.isColimit)) _ _).mp this
        exact ⟨j', g, Elements.homMk _ (by simp [← dsimp% h]), rfl⟩
      obtain ⟨j', g, φ, hφ⟩ :
          ∃ (j' : J) (g : j ⟶ j')
            (φ : ∀ (i : ι), (p.diag.map g).mapElements.obj e₂ ⟶ (p.diag.map g).mapElements.obj e₁),
            ∀ (i : ι), (f i).unop.hom = (φ i).hom := by
        choose j' g φ hφ using this
        obtain ⟨j'', a, g', hg'⟩ := wideSpan g hι
        have hg'' (i : ι) : p.diag.map g' = p.diag.map (g i) ≫ p.diag.map (a i) := by
          rw [← Functor.map_comp, hg']
        exact ⟨j'', g', fun i ↦ (NatTrans.congrMapElements (hg'' i)).hom.app _ ≫
          (p.diag.map (a i)).mapElements.map (φ i) ≫
          (NatTrans.congrMapElements (hg'' i)).inv.app _, fun i ↦ by simp [hφ]⟩
      let φ' (i : ι) := (φ i).op
      refine ⟨op ((p.ι.app j').mapElements.obj (coeq φ' hι).unop),
        ((NatTrans.mapElements (p.ι.app j')).map (coeqHom φ' hι).unop ≫
          (NatTrans.congrMapElements (p.w g)).hom.app e₂).op,
        ((NatTrans.mapElements (p.ι.app j')).map (toCoeq φ' hι).unop ≫
          (NatTrans.congrMapElements (p.w g)).hom.app e₁).op, fun i ↦ ?_⟩
      ext
      simp [hφ, ← coeq_condition φ' hι i, φ']

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalFilteredElementsOp C κ).IsClosedUnderCardinalFilteredColimits κ where

end Presheaf

namespace Functor

/-- A presheaf `P : Cᵒᵖ ⥤ Type w` on a locally `w`-small category `C` is a
`κ`-ind object (for `κ` a regular cardinal) if
1. the category `P.Elementsᵒᵖ` is `κ`-filtered;
2. the category `P.Elements` is initially `w`-small.
(If `C` is essentially `w`-small, 2. always holds and can be proven using the lemma
`initiallySmall_of_essentiallySmall`.)
See the lemma `Functor.isCardinalIndObject_iff` for an alternative characterization
of `κ`-ind objects as (small) `κ`-filtered colimits of representable presheaves. -/
class IsCardinalIndObject
    [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  isCardinalFiltered_elements_op (P κ) : IsCardinalFiltered P.Elementsᵒᵖ κ
  initiallySmall_elements (P κ) : InitiallySmall.{w} P.Elements

attribute [instance] IsCardinalIndObject.isCardinalFiltered_elements_op

variable [LocallySmall.{w} C]

variable (C) in
/-- `κ`-ind objects, as property of objects in `Cᵒᵖ ⥤ Type w`. -/
abbrev isCardinalIndObject (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ObjectProperty (Cᵒᵖ ⥤ Type w) :=
  fun P ↦ P.IsCardinalIndObject κ

attribute [local instance] isCofiltered_of_isFiltered_op in
instance (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalIndObject C κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    intro P ⟨p⟩
    have (j : J) := (p.prop_diag_obj j).isCardinalFiltered_elements_op
    have (j : J) := isFiltered_of_isCardinalFiltered (p.diag.obj j).Elementsᵒᵖ κ
    have h₁ (j : J) := (p.prop_diag_obj j).initiallySmall_elements
    have : IsCardinalFiltered P.Elementsᵒᵖ κ :=
      (Presheaf.isCardinalFilteredElementsOp Cᵒᵖ κ).prop_of_isColimit p.isColimit inferInstance
    have := isFiltered_of_isCardinalFiltered P.Elementsᵒᵖ κ
    refine ⟨inferInstance, ?_⟩
    simp only [initiallySmall_iff_of_isCofiltered] at h₁ ⊢
    choose Q _ hQ using h₁
    simp only [ObjectProperty.initial_ι_iff_of_isCofiltered] at hQ ⊢
    choose e he he' using hQ
    refine ⟨⨆ (j : J), (Q j).strictMap (p.ι.app j).mapElements, inferInstance,
      fun x ↦ ?_⟩
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj x.obj) p.isColimit) x.val
    dsimp at y hy
    refine ⟨(p.ι.app j).mapElements.obj (e j (elementsMk _ _ y)), ?_, ?_⟩
    · simp only [const_obj_obj, ObjectProperty.prop_iSup_iff]
      exact ⟨j, ObjectProperty.strictMap_obj _ _ (he _ _)⟩
    · obtain ⟨f⟩ := he' j (((p.diag.obj j)).elementsMk x.obj y)
      refine ⟨Elements.homMk f.hom ?_⟩
      dsimp
      simp only [← hy, ← dsimp% f.map_val, NatTrans.naturality_apply]

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalIndObject C κ).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let c : Cocone ((Functor.const (Discrete PUnit.{w + 1})).obj X) :=
      { pt := Y, ι.app _ := e.hom }
    have hc : IsColimit c :=
      IsColimit.ofIsoColimit (isColimitConstCocone ..) (Cocone.ext e)
    exact (isCardinalIndObject C κ).prop_of_isColimit hc (fun _ ↦ hX)

lemma IsCardinalIndObject.of_iso
    {P Q : Cᵒᵖ ⥤ Type w} (e : P ≅ Q) {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : P.IsCardinalIndObject κ := by infer_instance) :
    IsCardinalIndObject Q κ :=
  (isCardinalIndObject C κ).prop_of_iso e hP

instance (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    (isCardinalIndObject C κ).IsClosedUnderCardinalFilteredColimits κ where

lemma RepresentableBy.isCardinalIndObject {P : Cᵒᵖ ⥤ Type w} {X : C} (h : P.RepresentableBy X)
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    P.IsCardinalIndObject κ := by
  have := (Elements.isInitialOfRepresentableBy h).hasInitial
  exact ⟨isCardinalFiltered_of_hasTerminal .., inferInstance⟩

instance {P : Cᵒᵖ ⥤ Type w} [P.IsRepresentable]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    P.IsCardinalIndObject κ :=
  P.representableBy.isCardinalIndObject κ

lemma isCardinalIndObject_iff
    (P : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    P.IsCardinalIndObject κ ↔
      ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ) (F : J ⥤ C)
        (ι : F ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj P),
          Nonempty (IsColimit (Cocone.mk _ ι)) := by
  refine ⟨fun _ ↦ ?_,
    fun ⟨J, _, _, F, ι, ⟨h⟩⟩ ↦ (isCardinalIndObject C κ).prop_of_isColimit h
      (fun j ↦ by dsimp; infer_instance)⟩
  have := IsCardinalIndObject.initiallySmall_elements P κ
  obtain ⟨J, _, _, F, _⟩ :=
    (isCardinalFiltered_and_finallySmall_iff P.Elementsᵒᵖ κ).mp
      ⟨inferInstance, inferInstance⟩
  exact ⟨J, inferInstance, inferInstance, F ⋙ (Elements.π P).leftOp,  _,
    ⟨(Functor.Final.isColimitWhiskerEquiv F _).symm (Elements.isColimitShrinkYonedaCocone P)⟩⟩

lemma IsCardinalIndObject.small_hom
    (P Q : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular] [P.IsCardinalIndObject κ] :
  Small.{w} (P ⟶ Q) := by
    obtain ⟨J, _, _, F, ι, ⟨h⟩⟩ := (P.isCardinalIndObject_iff κ).mp inferInstance
    let φ (f : P ⟶ Q) (j : J) : shrinkYoneda.{w}.obj (F.obj j) ⟶ Q := ι.app j ≫ f
    exact small_of_injective (f := φ) (fun a b hab ↦ h.hom_ext (fun j ↦ congr($(hab) j)))

instance [LocallySmall.{w} D] (P : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [P.IsCardinalIndObject κ] (F : Dᵒᵖ ⥤ Cᵒᵖ) [F.IsEquivalence] :
    (F ⋙ P).IsCardinalIndObject κ :=
  have := IsCardinalIndObject.initiallySmall_elements P κ
  have e : P.Elements ≌ (F ⋙ P).Elements := F.asEquivalence.congrElements P
  { isCardinalFiltered_elements_op := IsCardinalFiltered.of_equivalence κ e.op
    initiallySmall_elements := initiallySmall_of_initial_of_initiallySmall e.functor }

@[simp]
lemma isCardinalIndObject_precomp_iff
    [LocallySmall.{w} D] (P : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (F : Dᵒᵖ ⥤ Cᵒᵖ) [F.IsEquivalence] :
    (F ⋙ P).IsCardinalIndObject κ ↔ P.IsCardinalIndObject κ :=
  ⟨fun _ ↦ .of_iso (show F.inv ⋙ F ⋙ P ≅ P from
    (associator _ _ _).symm ≪≫ isoWhiskerRight F.asEquivalence.counitIso _ ≪≫ P.leftUnitor),
  fun _ ↦ inferInstance⟩

end Functor

variable (C) in
/-- If `C` is a locally `w`-small category and `κ` a regular cardinal,
this is the category of `κ`-ind objects in `C`, as a full subcategory of `Cᵒᵖ ⥤ Type w`. -/
abbrev CardinalInd [LocallySmall.{w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular] :=
  (Functor.isCardinalIndObject C κ).FullSubcategory

namespace CardinalInd

section LocallySmall

variable [LocallySmall.{w} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

instance (P : CardinalInd C κ) : P.obj.IsCardinalIndObject κ := P.property

lemma exists_presentation (P : CardinalInd C κ) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ) (F : J ⥤ C)
      (ι : F ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj P.obj),
        Nonempty (IsColimit (Cocone.mk _ ι)) :=
  (P.obj.isCardinalIndObject_iff κ).mp inferInstance

/-- The inclusion of the category of `κ`-ind objects of a category `C`
into the category of presheaves of types on `C`. -/
abbrev inclusion : CardinalInd C κ ⥤ Cᵒᵖ ⥤ Type w := ObjectProperty.ι _

/-- The fully faithful embedding `C ⥤ CardinalInd C κ` of a category `C` in its
category of `κ`-ind objects. -/
noncomputable abbrev ι : C ⥤ CardinalInd C κ :=
  ObjectProperty.lift _ shrinkYoneda.{w} inferInstance

variable (C κ) in
/-- The composition of `ι : C ⥤ CardinalInd C κ` and
`inclusion : CardinalInd C κ ⥤ Cᵒᵖ ⥤ Type w` identifies the the
Yoneda embedding. -/
@[expose, simps! hom_app inv_app]
noncomputable def ιCompInclusion : ι (C := C) (κ := κ) ⋙ inclusion ≅ shrinkYoneda.{w} := Iso.refl _

variable (C κ) in
/-- The functor `ι : C ⥤ CardinalInd C κ` is fully faithful. -/
noncomputable def fullyFaithfulι : (ι : C ⥤ CardinalInd C κ).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (.ofIso (fullyFaithfulShrinkYoneda C) (ιCompInclusion C κ).symm)

instance : (ι : C ⥤ CardinalInd C κ).Faithful :=
  (fullyFaithfulι C κ).faithful

instance : (ι : C ⥤ CardinalInd C κ).Full :=
  (fullyFaithfulι C κ).full

instance : PreservesLimitsOfSize.{w₁, w₂} (CardinalInd.ι : C ⥤ CardinalInd C κ) where
  preservesLimitsOfShape {J _} := by
    have := preservesLimitsOfShape_of_natIso (J := J) (ιCompInclusion C κ).symm
    exact preservesLimitsOfShape_of_reflects_of_preserves _ inclusion

instance : LocallySmall.{w} (CardinalInd C κ) where
  hom_small P Q :=
    have := Functor.IsCardinalIndObject.small_hom P.obj Q.obj κ
    small_of_injective (f := fun f ↦ f.hom) (ObjectProperty.ι _).map_injective

end LocallySmall

section EssentiallySmall

variable [EssentiallySmall.{w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

variable (C) in
lemma isCardinalFilteredGenerator_essImage_ι :
    (ι.essImage : ObjectProperty (CardinalInd C κ)).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rw [← ObjectProperty.map_top, ObjectProperty.map_le_iff]
    intro P _
    exact ObjectProperty.isCardinalPresentable_of_fullSubcategory _ _ (by dsimp; infer_instance)
  exists_colimitsOfShape P := by
    obtain ⟨J, _, _, F, ι, ⟨h⟩⟩ := P.exists_presentation
    refine ⟨J, inferInstance, inferInstance,
    ⟨{diag := F ⋙ CardinalInd.ι
      ι :=
        { app j := ObjectProperty.homMk (ι.app j)
          naturality _ _ f := by ext : 1; simp [dsimp% ι.naturality f] }
      isColimit := isColimitOfReflects (ObjectProperty.ι _) h
      prop_diag_obj _ := Functor.obj_mem_essImage _ _ }⟩⟩

instance : IsCardinalAccessibleCategory (CardinalInd C κ) κ where
  exists_generator :=
    ⟨_, inferInstance, isCardinalFilteredGenerator_essImage_ι C κ⟩

instance :
    IsAccessibleCategory.{w} (CardinalInd C κ) where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

example : (CardinalInd.inclusion : CardinalInd C κ ⥤ Cᵒᵖ ⥤ Type w).IsCardinalAccessible κ :=
  inferInstance

end EssentiallySmall

end CardinalInd

/-- If two `w`-small categories `C₁` and `C₂` are equivalent,
and `κ` is a regular cardinal, then the categories of `κ`-ind
objects of `C₁` and `C₂` are also equivalent. -/
@[expose, implicit_reducible, simps! +dsimpLhs]
def Equivalence.congrCardinalInd
    {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [LocallySmall.{w} C₁] [LocallySmall.{w} C₂]
    (e : C₁ ≌ C₂) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    CardinalInd C₁ κ ≌ CardinalInd C₂ κ :=
  e.op.congrLeft.congrFullSubcategory (by aesop)

end CategoryTheory
