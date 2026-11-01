/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.IsClosedUnderCardinalFilteredColimits
public import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Presheaves that are `κ`-filtered colimits of representable presheaves

Let `C` be a category and `κ` be a regular cardinal. In this file, we introduce
a property `Presheaf.isCardinalFilteredElementsOp` of objects in `C ⥤ Type w`
that is satisfied by functors `P` such that `P.Elementsᵒᵖ` is `κ`-filtered,
and we show that this property is stable under `κ`-filtered colimits.

-/

public section

universe w

namespace CategoryTheory

open Opposite Limits

variable {C : Type*} [Category* C]

namespace Presheaf

variable (C) in
/-- The property of objects in `C ⥤ Type w` that is satisfied by
the functors `P` such that `P.Elementsᵒᵖ` is `κ`-filtered. -/
abbrev isCardinalFilteredElementsOp (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    ObjectProperty (C ⥤ Type w) :=
  fun P ↦ IsCardinalFiltered P.Elementsᵒᵖ κ

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

open ObjectProperty.IsClosedUnderCardinalFilteredColimits in
lemma isCardinalFilteredElementsOp_of_isColimit
    [LocallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type*} [Category* J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] (F : J ⥤ C)
    (ι : F ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj P)
    (h : IsColimit (Cocone.mk _ ι)) :
    isCardinalFilteredElementsOp Cᵒᵖ κ P :=
  have := isCardinalClosedUnderColimitsOfShape (isCardinalFilteredElementsOp Cᵒᵖ κ) κ J
  (isCardinalFilteredElementsOp Cᵒᵖ κ).prop_of_isColimit h
    (fun _ ↦ isCardinalFilteredElementsOp_shrinkYoneda_obj _ _)

open ObjectProperty.IsClosedUnderCardinalFilteredColimits in
lemma isCardinalFilteredElementsOp_of_isColimit'
    [LocallySmall.{w} C] (P : C ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    {J : Type*} [Category* J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] (F : J ⥤ Cᵒᵖ)
    (ι : F ⋙ shrinkCoyoneda.{w} ⟶ (Functor.const _).obj P)
    (h : IsColimit (Cocone.mk _ ι)) :
    isCardinalFilteredElementsOp C κ P :=
  have := isCardinalClosedUnderColimitsOfShape (isCardinalFilteredElementsOp C κ) κ J
  (isCardinalFilteredElementsOp C κ).prop_of_isColimit h
    (fun _ ↦ isCardinalFilteredElementsOp_shrinkCoyoneda_obj _ _)

open CategoryTheory.Functor Elements in
lemma isCardinalFiltered_elements_op_iff [EssentiallySmall.{w} C]
    (P : Cᵒᵖ ⥤ Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular] :
    IsCardinalFiltered P.Elementsᵒᵖ κ ↔
      ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ) (F : J ⥤ C)
        (ι : F ⋙ shrinkYoneda.{w} ⟶ (Functor.const _).obj P),
        Nonempty (IsColimit (Cocone.mk _ ι)) := by
  refine ⟨fun h ↦ ?_,
    fun ⟨J, _, _, F, ι, ⟨h⟩⟩ ↦ isCardinalFilteredElementsOp_of_isColimit P κ F ι h⟩
  let e := equivSmallModel.{w} P.Elementsᵒᵖ
  exact ⟨SmallModel.{w} P.Elementsᵒᵖ, inferInstance, IsCardinalFiltered.of_equivalence κ e,
    e.inverse ⋙ (π P).leftOp,
    (Functor.associator _ _ _).hom ≫ whiskerLeft e.inverse (shrinkYonedaCocone P).ι,
    ⟨IsColimit.equivOfNatIsoOfIso ((Functor.associator _ _ _).symm) _ _ (Cocone.ext (Iso.refl _))
      ((isColimitShrinkYonedaCocone P).whiskerEquivalence e.symm)⟩⟩

end Presheaf

end CategoryTheory
