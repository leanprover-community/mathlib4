/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.EssentiallySmall

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

@[expose] public section


namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C]

/-- The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def Functor.Elements (F : C ⥤ Type w) :=
  Σ c : C, F.obj c

/-- Constructor for the type `F.Elements` when `F` is a functor to types. -/
abbrev Functor.elementsMk (F : C ⥤ Type w) (X : C) (x : F.obj X) : F.Elements := ⟨X, x⟩

lemma Functor.Elements.ext {F : C ⥤ Type w} (x y : F.Elements) (h₁ : x.fst = y.fst)
    (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  cases y
  cases h₁
  simp_all

/-- The category structure on `F.Elements`, for `F : C ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`. -/
instance categoryOfElements (F : C ⥤ Type w) : Category.{v} F.Elements where
  Hom p q := { f : p.1 ⟶ q.1 // (F.map f) p.2 = q.2 }
  id p := ⟨𝟙 p.1, by simp⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by simp [f.2, g.2]⟩

/-- Natural transformations are mapped to functors between categories of elements. -/
@[simps]
def NatTrans.mapElements {F G : C ⥤ Type w} (φ : F ⟶ G) : F.Elements ⥤ G.Elements where
  obj := fun ⟨X, x⟩ ↦ ⟨_, φ.app X x⟩
  map {p q} := fun ⟨f, h⟩ ↦ ⟨f, by have hb := φ.naturality_apply f p.2; cat_disch⟩

/-- The functor mapping functors `C ⥤ Type w` to their category of elements -/
@[simps]
def Functor.elementsFunctor : (C ⥤ Type w) ⥤ Cat where
  obj F := Cat.of F.Elements
  map n := (NatTrans.mapElements n).toCatHom

namespace CategoryOfElements

/-- Constructor for morphisms in the category of elements of a functor to types. -/
@[simps]
def homMk {F : C ⥤ Type w} (x y : F.Elements) (f : x.1 ⟶ y.1) (hf : F.map f x.snd = y.snd) :
    x ⟶ y :=
  ⟨f, hf⟩

@[ext]
theorem ext (F : C ⥤ Type w) {x y : F.Elements} (f g : x ⟶ y) (w : f.val = g.val) : f = g :=
  Subtype.ext w

@[simp]
theorem comp_val {F : C ⥤ Type w} {p q r : F.Elements} {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

@[simp]
theorem id_val {F : C ⥤ Type w} {p : F.Elements} : (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl

@[simp]
theorem map_snd {F : C ⥤ Type w} {p q : F.Elements} (f : p ⟶ q) : (F.map f.val) p.2 = q.2 :=
  f.property

/-- Constructor for isomorphisms in the category of elements of a functor to types. -/
@[simps]
def isoMk {F : C ⥤ Type w} (x y : F.Elements) (e : x.1 ≅ y.1)
    (he : F.map e.hom x.snd = y.snd) : x ≅ y where
  hom := homMk x y e.hom he
  inv := homMk y x e.inv (by rw [← he, Functor.map_hom_inv'_apply])

instance [LocallySmall.{w} C] (F : C ⥤ Type w) : LocallySmall.{w} F.Elements where
  hom_small := by
    rintro ⟨X, _⟩ ⟨Y, y⟩
    exact small_of_injective (f := fun g ↦ g.val) (by cat_disch)

end CategoryOfElements

instance groupoidOfElements {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) :
    Groupoid F.Elements where
  inv {p q} f :=
    ⟨Groupoid.inv f.val,
      calc
        F.map (Groupoid.inv f.val) q.2 = F.map (Groupoid.inv f.val) (F.map f.val p.2) := by rw [f.2]
        _ = (F.map f.val ≫ F.map (Groupoid.inv f.val)) p.2 := rfl
        _ = p.2 := by
          rw [← F.map_comp]
          simp
        ⟩
  inv_comp _ := by
    ext
    simp
  comp_inv _ := by
    ext
    simp

namespace CategoryOfElements

variable (F : C ⥤ Type w)

/-- The functor out of the category of elements which forgets the element. -/
@[simps]
def π : F.Elements ⥤ C where
  obj X := X.1
  map f := f.val

instance : (π F).Faithful where

set_option backward.defeqAttrib.useBackward true in
instance : (π F).ReflectsIsomorphisms where
  reflects f h := by
    refine ⟨⟨(inv ((π F).map f) :), ?_⟩, ?_, ?_⟩
    · simp only [← map_snd f, ← Functor.map_comp_apply,
        π_obj, π_map, IsIso.hom_inv_id, Functor.map_id_apply]
    · cat_disch
    · cat_disch

/-- A natural transformation between functors induces a functor between the categories of elements.
-/
@[simps]
def map {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : F₁.Elements ⥤ F₂.Elements where
  obj t := ⟨t.1, α.app t.1 t.2⟩
  map {t₁ t₂} k := ⟨k.1, by simpa [map_snd] using (NatTrans.naturality_apply α k.1 t₁.2).symm⟩

@[simp]
theorem map_π {F₁ F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl

/-- The forward direction of the equivalence `F.Elements ≅ (*, F)`. -/
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where
  obj X := StructuredArrow.mk <| ↾fun _ => X.2
  map {X Y} f := StructuredArrow.homMk f.val (by ext; simp [f.2])

@[simp]
theorem toStructuredArrow_obj (X) :
    (toStructuredArrow F).obj X =
      { left := ⟨⟨⟩⟩
        right := X.1
        hom := ↾fun _ => X.2 } :=
  rfl

@[simp]
theorem to_comma_map_right {X Y} (f : X ⟶ Y) : ((toStructuredArrow F).map f).right = f.val :=
  rfl

/-- The reverse direction of the equivalence `F.Elements ≅ (*, F)`. -/
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where
  obj X := Functor.elementsMk _ X.right (X.hom .unit)
  map f := ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm .unit]; rfl⟩

@[simp]
theorem fromStructuredArrow_obj (X) : (fromStructuredArrow F).obj X = ⟨X.right, X.hom PUnit.unit⟩ :=
  rfl

@[simp]
theorem fromStructuredArrow_map {X Y} (f : X ⟶ Y) :
    (fromStructuredArrow F).map f =
      ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm PUnit.unit]; rfl⟩ :=
  rfl

/-- The equivalence between the category of elements `F.Elements`
and the comma category `(*, F)`. -/
@[simps]
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F where
  functor := toStructuredArrow F
  inverse := fromStructuredArrow F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

open Opposite

/-- The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F where
  obj X := CostructuredArrow.mk (yonedaEquiv.symm (unop X).2)
  map f :=
    CostructuredArrow.homMk f.unop.val.unop (by
      ext Z y
      simp [yonedaEquiv])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps]
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements where
  obj X := ⟨op (unop X).1, yonedaEquiv.1 (unop X).3⟩
  map {X Y} f := ⟨f.unop.1.op, by simp [yonedaEquiv_naturality]⟩

@[simp]
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (op (CostructuredArrow.mk f)) = ⟨op X, yonedaEquiv.1 f⟩ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by yoneda lemma. -/
@[simps]
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F where
  functor := toCostructuredArrow F
  inverse := (fromCostructuredArrow F).rightOp
  unitIso :=
    NatIso.ofComponents
      (fun X ↦ Iso.op (CategoryOfElements.isoMk _ _ (Iso.refl _) (by simp; rfl))) (by
        rintro ⟨x⟩ ⟨y⟩ ⟨f : y ⟶ x⟩
        exact Quiver.Hom.unop_inj (by ext; simp))
  counitIso := NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _) (by
    dsimp
    simpa only [Functor.map_id, Category.id_comp] using
      (yonedaEquiv.symm_apply_apply X.hom).symm))

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `(-.Elements)ᵒᵖ ≅ (yoneda, -)` of is actually a natural isomorphism of functors.
-/
theorem costructuredArrow_yoneda_equivalence_naturality {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    (map α).op ⋙ toCostructuredArrow F₂ = toCostructuredArrow F₁ ⋙ CostructuredArrow.map α := by
  fapply Functor.ext
  · intro X
    simp only [CostructuredArrow.map_mk, toCostructuredArrow_obj, Functor.op_obj,
      Functor.comp_obj]
    congr
    ext _ f
    exact (α.naturality_apply f.op (unop X).snd).symm
  · simp

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
def costructuredArrowYonedaEquivalenceFunctorProj (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).functor ⋙ CostructuredArrow.proj _ _ ≅ (π F).leftOp :=
  Iso.refl _

/-- The equivalence `F.elementsᵒᵖ ≌ (yoneda, F)` is compatible with the forgetful functors. -/
@[simps!]
def costructuredArrowYonedaEquivalenceInverseπ (F : Cᵒᵖ ⥤ Type v) :
    (costructuredArrowYonedaEquivalence F).inverse ⋙ (π F).leftOp ≅ CostructuredArrow.proj _ _ :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The opposite of the category of elements of a presheaf of types
is equivalent to a category of costructured arrows for the Yoneda embedding functor. -/
@[simps]
def costructuredArrowULiftYonedaEquivalence (F : Cᵒᵖ ⥤ Type (max w v)) :
    F.Elementsᵒᵖ ≌ CostructuredArrow uliftYoneda.{w} F where
  functor :=
    { obj x := CostructuredArrow.mk (uliftYonedaEquiv.{w}.symm x.unop.2)
      map f := CostructuredArrow.homMk f.1.1.unop (by
        dsimp
        rw [← uliftYonedaEquiv_symm_map, map_snd]) }
  inverse :=
    { obj X := op (F.elementsMk _ (uliftYonedaEquiv.{w} X.hom))
      map f := (homMk _ _ f.left.op (by
        dsimp
        rw [← CostructuredArrow.w f, uliftYonedaEquiv_naturality, Quiver.Hom.unop_op])).op }
  unitIso := NatIso.ofComponents (fun x ↦ Iso.op (isoMk _ _ (Iso.refl _) (by
    dsimp
    simpa only [Functor.map_id_apply] using
      uliftYonedaEquiv.apply_symm_apply (unop x).snd)))
    (fun f ↦ Quiver.Hom.unop_inj (by aesop))
  counitIso := NatIso.ofComponents (fun X ↦ CostructuredArrow.isoMk (Iso.refl _))

/-- The equivalence of categories `costructuredArrowULiftYonedaEquivalence`
commutes with the projections. -/
def costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso (F : Cᵒᵖ ⥤ Type (max w v)) :
    (costructuredArrowULiftYonedaEquivalence.{w} F).functor ⋙ CostructuredArrow.proj _ _ ≅
      (π F).leftOp :=
  Iso.refl _

end CategoryOfElements

namespace Functor

/-- The initial object in `F.Elements` if `F` is representable. -/
@[simps]
def Elements.initialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    F.Elements :=
  ⟨.op X, h.homEquiv (𝟙 X)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is represented by `X`, `X` with its universal element is the initial object of
`F.Elements.` -/
def Elements.isInitialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    Limits.IsInitial (initialOfRepresentableBy h) :=
  .ofUniqueHom (fun Y ↦ ⟨h.homEquiv.symm Y.snd |>.op, by simp [← h.homEquiv_comp]⟩) fun Y m ↦ by
    simp [← m.2, ← h.homEquiv_unop_comp]

/-- The initial object in `F.Elements` if `F` is corepresentable. -/
@[simps]
def Elements.initialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    F.Elements :=
  ⟨X, h.homEquiv (𝟙 X)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is corepresented by `X`, `X` with its universal element is the initial object of
`F.Elements.` -/
def Elements.isInitialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    Limits.IsInitial (initialOfCorepresentableBy h) :=
  .ofUniqueHom (fun Y ↦ ⟨h.homEquiv.symm Y.snd, by simp [← h.homEquiv_comp]⟩) fun Y m ↦ by
    simp [← m.2, ← h.homEquiv_comp]

/--
The initial object in the category of elements for a representable functor. In `isInitial` it is
shown that this is initial.
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩

/-- Show that `Elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def Elements.isInitial (A : C) : Limits.IsInitial (Elements.initial A) :=
  isInitialOfRepresentableBy (.yoneda A)

end Functor

end CategoryTheory
