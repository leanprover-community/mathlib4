/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.StructuredArrow
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.PUnit

#align_import category_theory.elements from "leanprover-community/mathlib"@"8a318021995877a44630c898d0b2bc376fceef3b"

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type`, an object of `F.Elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction, so this is mostly just a
more convenient API. We prove the equivalence in
`CategoryTheory.CategoryOfElements.structuredArrowEquivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/


namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def Functor.Elements (F : C ⥤ Type w) :=
  Σc : C, F.obj c
#align category_theory.functor.elements CategoryTheory.Functor.Elements

-- porting note: added because Sigma.ext would be triggered automatically
lemma Functor.Elements.ext {F : C ⥤ Type w} (x y : F.Elements) (h₁ : x.fst = y.fst)
    (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  -- ⊢ { fst := fst✝, snd := snd✝ } = y
  cases y
  -- ⊢ { fst := fst✝¹, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
  cases h₁
  -- ⊢ { fst := fst✝, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
  -- ⊢ { fst := fst✝, snd := snd✝¹ } = { fst := fst✝, snd := snd✝ }
  simp [h₂]
  -- 🎉 no goals

/-- The category structure on `F.Elements`, for `F : C ⥤ Type`.
    A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.
 -/
instance categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by aesop_cat⟩
                     -- 🎉 no goals
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩
                                         -- 🎉 no goals
#align category_theory.category_of_elements CategoryTheory.categoryOfElements

namespace CategoryOfElements

@[ext]
theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext_val w
#align category_theory.category_of_elements.ext CategoryTheory.CategoryOfElements.ext

@[simp]
theorem comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl
#align category_theory.category_of_elements.comp_val CategoryTheory.CategoryOfElements.comp_val

@[simp]
theorem id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl
#align category_theory.category_of_elements.id_val CategoryTheory.CategoryOfElements.id_val

end CategoryOfElements

noncomputable instance groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) :
    Groupoid F.Elements
    where
  inv {p q} f :=
    ⟨inv f.val,
      calc
        F.map (inv f.val) q.2 = F.map (inv f.val) (F.map f.val p.2) := by rw [f.2]
                                                                          -- 🎉 no goals
        _ = (F.map f.val ≫ F.map (inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          -- ⊢ F.map (↑f ≫ inv ↑f) p.snd = p.snd
          simp
          -- 🎉 no goals
        ⟩
  inv_comp _ := by
    ext
    -- ⊢ ↑((fun {p q} f => { val := inv ↑f, property := (_ : F.map (inv ↑f) q.snd = p …
    simp
    -- 🎉 no goals
  comp_inv _ := by
    ext
    -- ⊢ ↑(x✝ ≫ (fun {p q} f => { val := inv ↑f, property := (_ : F.map (inv ↑f) q.sn …
    simp
    -- 🎉 no goals
#align category_theory.groupoid_of_elements CategoryTheory.groupoidOfElements

namespace CategoryOfElements

variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
def π : F.Elements ⥤ C where
  obj X := X.1
  map f := f.val
#align category_theory.category_of_elements.π CategoryTheory.CategoryOfElements.π

/-- A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements
    where
  obj t := ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [← k.2] using (FunctorToTypes.naturality _ _ α k.1 t₁.2).symm⟩
                            -- 🎉 no goals
#align category_theory.category_of_elements.map CategoryTheory.CategoryOfElements.map

@[simp]
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl
#align category_theory.category_of_elements.map_π CategoryTheory.CategoryOfElements.map_π

/-- The forward direction of the equivalence `F.Elements ≅ (*, F)`. -/
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where
  obj X := StructuredArrow.mk fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by funext; simp [f.2])
                                                 -- ⊢ (((fun X => StructuredArrow.mk fun x => X.snd) X).hom ≫ F.map ↑f) x✝ = Comma …
                                                         -- 🎉 no goals
#align category_theory.category_of_elements.to_structured_arrow CategoryTheory.CategoryOfElements.toStructuredArrow

@[simp]
theorem toStructuredArrow_obj (X) :
    (toStructuredArrow F).obj X =
      { left := ⟨⟨⟩⟩
        right := X.1
        hom := fun _ => X.2 } :=
  rfl
#align category_theory.category_of_elements.to_structured_arrow_obj CategoryTheory.CategoryOfElements.toStructuredArrow_obj

@[simp]
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right = f.val :=
  rfl
#align category_theory.category_of_elements.to_comma_map_right CategoryTheory.CategoryOfElements.to_comma_map_right

/-- The reverse direction of the equivalence `F.Elements ≅ (*, F)`. -/
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where
  obj X := ⟨X.right, X.hom PUnit.unit⟩
  map f := ⟨f.right, congr_fun f.w.symm PUnit.unit⟩
#align category_theory.category_of_elements.from_structured_arrow CategoryTheory.CategoryOfElements.fromStructuredArrow

@[simp]
theorem fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩ :=
  rfl
#align category_theory.category_of_elements.from_structured_arrow_obj CategoryTheory.CategoryOfElements.fromStructuredArrow_obj

@[simp]
theorem fromStructuredArrow_map {X Y} (f : X ⟶ Y) :
    (fromStructuredArrow F).map f = ⟨f.right, congr_fun f.w.symm PUnit.unit⟩ :=
  rfl
#align category_theory.category_of_elements.from_structured_arrow_map CategoryTheory.CategoryOfElements.fromStructuredArrow_map

/-- The equivalence between the category of elements `F.Elements`
    and the comma category `(*, F)`. -/
@[simps! functor_obj functor_map inverse_obj inverse_map unitIso_hom
  unitIso_inv counitIso_hom counitIso_inv]
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F :=
  Equivalence.mk (toStructuredArrow F) (fromStructuredArrow F)
    (NatIso.ofComponents fun X => eqToIso (by aesop_cat))
                                              -- 🎉 no goals
    (NatIso.ofComponents fun X => StructuredArrow.isoMk (Iso.refl _))
#align category_theory.category_of_elements.structured_arrow_equivalence CategoryTheory.CategoryOfElements.structuredArrowEquivalence

open Opposite

/-- The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaSections`.
-/
@[simps]
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F
    where
  obj X := CostructuredArrow.mk ((yonedaSections (unop (unop X).fst) F).inv (ULift.up (unop X).2))
  map f := by
    fapply CostructuredArrow.homMk
    -- ⊢ ((fun X => CostructuredArrow.mk ((yonedaSections X.unop.fst.unop F).inv { do …
    · exact f.unop.val.unop
      -- 🎉 no goals
    · ext Z y
      -- ⊢ NatTrans.app (yoneda.map (↑f.unop).unop ≫ ((fun X => CostructuredArrow.mk (( …
      dsimp
      -- ⊢ F.map (↑f.unop ≫ y.op) Y✝.unop.snd = F.map y.op X✝.unop.snd
      simp only [FunctorToTypes.map_comp_apply, ← f.unop.2]
      -- 🎉 no goals
#align category_theory.category_of_elements.to_costructured_arrow CategoryTheory.CategoryOfElements.toCostructuredArrow

/-- The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements where
  obj X := ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f :=
    ⟨f.unop.1.op, by
      convert (congr_fun ((unop X).hom.naturality f.unop.left.op) (𝟙 _)).symm
      -- ⊢ ((fun X => { fst := op X.unop.left, snd := Equiv.toFun yonedaEquiv X.unop.ho …
      simp only [Equiv.toFun_as_coe, Quiver.Hom.unop_op, yonedaEquiv_apply, types_comp_apply,
        Category.comp_id, yoneda_obj_map]
      have : yoneda.map f.unop.left ≫ (unop X).hom = (unop Y).hom := by
        convert f.unop.3
      erw [← this]
      -- ⊢ NatTrans.app (yoneda.map f.unop.left ≫ X.unop.hom) (op Y.unop.left) (𝟙 Y.uno …
      simp only [yoneda_map_app, FunctorToTypes.comp]
      -- ⊢ NatTrans.app X.unop.hom (op Y.unop.left) (𝟙 Y.unop.left ≫ f.unop.left) = Nat …
      erw [Category.id_comp]⟩
      -- 🎉 no goals
#align category_theory.category_of_elements.from_costructured_arrow CategoryTheory.CategoryOfElements.fromCostructuredArrow

@[simp]
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaEquiv.1 f⟩ :=
  rfl
#align category_theory.category_of_elements.from_costructured_arrow_obj_mk CategoryTheory.CategoryOfElements.fromCostructuredArrow_obj_mk

/-- The unit of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem from_toCostructuredArrow_eq (F : Cᵒᵖ ⥤ Type v) :
    (toCostructuredArrow F).rightOp ⋙ fromCostructuredArrow F = 𝟭 _ := by
  refine' Functor.ext _ _
  -- ⊢ ∀ (X : Functor.Elements F), ((toCostructuredArrow F).rightOp ⋙ fromCostructu …
  · intro X
    -- ⊢ ((toCostructuredArrow F).rightOp ⋙ fromCostructuredArrow F).obj X = (𝟭 (Func …
    exact Functor.Elements.ext _ _ rfl (by simp [yonedaEquiv])
    -- 🎉 no goals
  · intro X Y f
    -- ⊢ ((toCostructuredArrow F).rightOp ⋙ fromCostructuredArrow F).map f = eqToHom  …
    have : ∀ {a b : F.Elements} (H : a = b),
        (eqToHom H).1 = eqToHom (show a.fst = b.fst by cases H; rfl) := by
      rintro _ _ rfl
      simp
    ext
    -- ⊢ ↑(((toCostructuredArrow F).rightOp ⋙ fromCostructuredArrow F).map f) = ↑(eqT …
    simp [this]
    -- 🎉 no goals
#align category_theory.category_of_elements.from_to_costructured_arrow_eq CategoryTheory.CategoryOfElements.from_toCostructuredArrow_eq

/-- The counit of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` is indeed iso. -/
theorem to_fromCostructuredArrow_eq (F : Cᵒᵖ ⥤ Type v) :
    (fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F = 𝟭 _ := by
  refine' Functor.ext _ _
  -- ⊢ ∀ (X : CostructuredArrow yoneda F), ((fromCostructuredArrow F).rightOp ⋙ toC …
  · intro X
    -- ⊢ ((fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F).obj X = (𝟭 (Cost …
    cases' X with X_left X_right X_hom
    -- ⊢ ((fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F).obj { left := X_ …
    cases X_right
    -- ⊢ ((fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F).obj { left := X_ …
    simp only [Functor.id_obj, Functor.rightOp_obj, toCostructuredArrow_obj, Functor.comp_obj,
      CostructuredArrow.mk]
    congr
    -- ⊢ (yonedaSections (op ((fromCostructuredArrow F).obj (op { left := X_left, rig …
    ext x f
    -- ⊢ NatTrans.app ((yonedaSections (op ((fromCostructuredArrow F).obj (op { left  …
    convert congr_fun (X_hom.naturality f.op).symm (𝟙 X_left)
    -- ⊢ NatTrans.app X_hom x f = ((yoneda.obj X_left).map f.op ≫ NatTrans.app X_hom  …
    simp
    -- 🎉 no goals
  · intro X Y f
    -- ⊢ ((fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F).map f = eqToHom  …
    ext
    -- ⊢ (((fromCostructuredArrow F).rightOp ⋙ toCostructuredArrow F).map f).left = ( …
    simp [CostructuredArrow.eqToHom_left]
    -- 🎉 no goals
#align category_theory.category_of_elements.to_from_costructured_arrow_eq CategoryTheory.CategoryOfElements.to_fromCostructuredArrow_eq

/-- The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps! functor_obj functor_map inverse_obj inverse_map unitIso_inv counitIso_hom counitIso_inv]
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F :=
  Equivalence.mk (toCostructuredArrow F) (fromCostructuredArrow F).rightOp
    (NatIso.op (eqToIso (from_toCostructuredArrow_eq F))) (eqToIso <| to_fromCostructuredArrow_eq F)
#align category_theory.category_of_elements.costructured_arrow_yoneda_equivalence CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence

-- Porting note:
-- Running `@[simps! unitIso_hom]` is mysteriously slow.
-- We separate it out to avoid needing to increase the maxHeartbeats.
attribute [simps! unitIso_hom] costructuredArrowYonedaEquivalence

/-- The equivalence `(-.Elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
theorem costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ CostructuredArrow.map α := by
  fapply Functor.ext
  -- ⊢ ∀ (X : (Functor.Elements F₁)ᵒᵖ), ((map α).op ⋙ toCostructuredArrow F₂).obj X …
  · intro X
    -- ⊢ ((map α).op ⋙ toCostructuredArrow F₂).obj X = (toCostructuredArrow F₁ ⋙ Cost …
    simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
      Functor.comp_obj]
    congr
    -- ⊢ (yonedaSections (op ((map α).obj X.unop)).unop.fst.unop F₂).inv { down := (o …
    ext _ f
    -- ⊢ NatTrans.app ((yonedaSections (op ((map α).obj X.unop)).unop.fst.unop F₂).in …
    simpa using congr_fun (α.naturality f.op).symm (unop X).snd
    -- 🎉 no goals
  · intro X Y f
    -- ⊢ ((map α).op ⋙ toCostructuredArrow F₂).map f = eqToHom (_ : ((map α).op ⋙ toC …
    ext
    -- ⊢ (((map α).op ⋙ toCostructuredArrow F₂).map f).left = (eqToHom (_ : ((map α). …
    simp [CostructuredArrow.eqToHom_left]
    -- 🎉 no goals
#align category_theory.category_of_elements.costructured_arrow_yoneda_equivalence_naturality CategoryTheory.CategoryOfElements.costructuredArrow_yoneda_equivalence_naturality

end CategoryOfElements

end CategoryTheory
