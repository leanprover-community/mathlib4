/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck
construction.

Given a functor `F : C ⥤ Type*`, an object of `F.Elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C` such that `F.map f` takes `x` to `y`.

## Implementation notes

This construction is equivalent to a special case of a comma construction,
so this is mostly just a more convenient API. We prove the equivalence in
`CategoryTheory.Functor.Elements.structuredArrowEquivalence`.

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
structure Functor.Elements (F : C ⥤ Type w) where
  /-- the underlying object of an element of a functor to types -/
  {obj : C}
  /-- the value of the element -/
  val : F.obj obj

@[deprecated (since := "2026-08-30")] alias Functor.Elements.fst := Functor.Elements.obj
@[deprecated (since := "2026-08-30")] alias Functor.Elements.snd := Functor.Elements.val

variable {F : C ⥤ Type w}

variable (F) in
/-- Constructor for the type `F.Elements` when `F` is a functor to types. -/
abbrev Functor.elementsMk (X : C) (x : F.obj X) : F.Elements := .mk x

namespace Functor.Elements

lemma ext (x y : F.Elements) (h₁ : x.obj = y.obj)
    (h₂ : F.map (eqToHom h₁) x.val = y.val) : x = y := by
  cases x
  cases y
  cases h₁
  simp_all

/-- A morphism `x ⟶ y` in the category `F.Elements` of elements of a functor `F : C ⥤ Type w`
consists of a morphism `hom : x.obj ⟶ y.obj` such that `F.map hom` sends `x.val` to `y.val`. -/
@[ext]
structure Hom (x y : F.Elements) where
  /-- the underlying morphism of objects -/
  hom : x.obj ⟶ y.obj
  map_val : F.map hom x.val = y.val := by cat_disch

attribute [simp] Hom.map_val

/-- The category structure on `F.Elements`, for `F : C ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`. -/
@[simps!]
instance : Category.{v} F.Elements where
  Hom := Hom
  id x := { hom := 𝟙 x.obj }
  comp f g := { hom := f.hom ≫ g.hom }

variable (F) in
/-- The functor out of the category of elements which forgets the element. -/
@[implicit_reducible, simps]
def π : F.Elements ⥤ C where
  obj X := X.1
  map f := f.hom

end Functor.Elements

/-- Natural transformations are mapped to functors between categories of elements. -/
@[implicit_reducible, simps]
def NatTrans.mapElements {G : C ⥤ Type w} (φ : F ⟶ G) : F.Elements ⥤ G.Elements where
  obj e := .mk (φ.app _ e.val)
  map {e₁ e₂} f :=
    { hom := f.hom
      map_val := by simpa using (φ.naturality_apply f.hom e₁.val).symm }

/-- If `φ : F ⟶ G` is a natural transformation between functors to types, this is the
canonical isomorphism `φ.mapElements ⋙ Functor.Elements.π G ≅ Functor.Elements.π F`. -/
@[simps!]
def NatTrans.mapElementsCompπIso {G : C ⥤ Type w} (φ : F ⟶ G) :
    φ.mapElements ⋙ Functor.Elements.π G ≅ Functor.Elements.π F :=
  Iso.refl _

lemma NatTrans.mapElements_comp_π {G : C ⥤ Type w} (φ : F ⟶ G) :
    φ.mapElements ⋙ Functor.Elements.π G = Functor.Elements.π F :=
  rfl

/-- The functor mapping functors `C ⥤ Type w` to their category of elements -/
@[simps]
def Functor.elementsFunctor : (C ⥤ Type w) ⥤ Cat where
  obj F := ↧F.Elements
  map n := (NatTrans.mapElements n).toCatHom

namespace Functor.Elements

/-- Constructor for morphisms in the category of elements of a functor to types. -/
abbrev homMk {x y : F.Elements} (f : x.obj ⟶ y.obj)
    (hf : F.map f x.val = y.val := by cat_disch) : x ⟶ y := .mk f hf

@[ext]
theorem hom_ext {x y : F.Elements} {f g : x ⟶ y} (w : f.hom = g.hom) : f = g :=
  Hom.ext w

/-- Constructor for isomorphisms in the category of elements of a functor to types. -/
@[simps hom inv]
def isoMk {x y : F.Elements} (e : x.obj ≅ y.obj)
    (he : F.map e.hom x.val = y.val := by cat_disch) : x ≅ y where
  hom := homMk e.hom he
  inv := homMk e.inv (by rw [← he, Functor.map_hom_inv'_apply])

instance [LocallySmall.{w} C] : LocallySmall.{w} F.Elements where
  hom_small x y := small_of_injective (f := fun g ↦ g.hom) (by cat_disch)

instance groupoid {G : Type u} [Groupoid.{v} G] (F : G ⥤ Type w) : Groupoid F.Elements where
  inv {p q} f := Functor.Elements.homMk (Groupoid.inv f.hom) (by
    rw [← f.map_val, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    simp)

instance : (π F).Faithful where

instance : (π F).ReflectsIsomorphisms where
  reflects f (_ : IsIso f.hom) :=
    ⟨homMk (CategoryTheory.inv f.hom) (by
      rw [← f.map_val, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      simp), by cat_disch, by cat_disch⟩

variable (F) in
/-- The forward direction of the equivalence `F.Elements ≅ (*, F)`. -/
@[simps, implicit_reducible]
def toStructuredArrow : F.Elements ⥤ StructuredArrow PUnit F where
  obj e := StructuredArrow.mk <| ↾fun _ ↦ e.val
  map f := StructuredArrow.homMk f.hom

variable (F) in
/-- The reverse direction of the equivalence `F.Elements ≅ (*, F)`. -/
@[simps obj map_hom, simps -isSimp map, implicit_reducible]
def fromStructuredArrow : StructuredArrow PUnit F ⥤ F.Elements where
  obj X := Functor.elementsMk _ X.right (X.hom .unit)
  map f := ⟨f.right, by simp [ConcreteCategory.congr_hom f.w.symm .unit]; dsimp⟩

variable (F) in
/-- The equivalence between the category of elements `F.Elements`
and the comma category `(*, F)`. -/
@[implicit_reducible, simps]
def structuredArrowEquivalence : F.Elements ≌ StructuredArrow PUnit F where
  functor := toStructuredArrow F
  inverse := fromStructuredArrow F
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The forward direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps, implicit_reducible]
def toCostructuredArrow (F : Cᵒᵖ ⥤ Type v) : F.Elementsᵒᵖ ⥤ CostructuredArrow yoneda F where
  obj X := CostructuredArrow.mk (yonedaEquiv.symm X.unop.val)
  map f :=
    CostructuredArrow.homMk f.unop.hom.unop (by
      ext
      simp [yonedaEquiv])

/-- The reverse direction of the equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)`,
given by `CategoryTheory.yonedaEquiv`.
-/
@[simps obj map, implicit_reducible]
def fromCostructuredArrow (F : Cᵒᵖ ⥤ Type v) :
    (CostructuredArrow yoneda F)ᵒᵖ ⥤ F.Elements where
  obj X := F.elementsMk (Opposite.op X.unop.left) (yonedaEquiv X.unop.hom)
  map f := homMk f.unop.left.op (by simp [yonedaEquiv_naturality])

@[simp]
theorem fromCostructuredArrow_obj_mk (F : Cᵒᵖ ⥤ Type v) {X : C} (f : yoneda.obj X ⟶ F) :
    (fromCostructuredArrow F).obj (Opposite.op (CostructuredArrow.mk f)) =
      F.elementsMk (Opposite.op X) (yonedaEquiv f) := rfl

/-- The equivalence `F.Elementsᵒᵖ ≅ (yoneda, F)` given by Yoneda's lemma. -/
@[simps, implicit_reducible]
def costructuredArrowYonedaEquivalence (F : Cᵒᵖ ⥤ Type v) :
    F.Elementsᵒᵖ ≌ CostructuredArrow yoneda F where
  functor := toCostructuredArrow F
  inverse := (fromCostructuredArrow F).rightOp
  unitIso :=
    NatIso.ofComponents (fun e ↦ Iso.op (isoMk (Iso.refl _)))
      (fun _ ↦ Quiver.Hom.unop_inj (by cat_disch))
  counitIso :=
    NatIso.ofComponents (fun f ↦ CostructuredArrow.isoMk (Iso.refl _))

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

/-- The opposite of the category of elements of a presheaf of types
is equivalent to a category of costructured arrows for the Yoneda embedding functor. -/
@[implicit_reducible, simps]
def costructuredArrowULiftYonedaEquivalence (F : Cᵒᵖ ⥤ Type (max w v)) :
    F.Elementsᵒᵖ ≌ CostructuredArrow uliftYoneda.{w} F where
  functor.obj x := CostructuredArrow.mk (uliftYonedaEquiv.symm x.unop.val)
  functor.map f := CostructuredArrow.homMk f.unop.hom.unop (by
    simp [← uliftYonedaEquiv_symm_map.{w}])
  inverse.obj x := Opposite.op (Functor.elementsMk _ _ (uliftYonedaEquiv x.hom))
  inverse.map f := (homMk f.left.op (by simp [uliftYonedaEquiv_naturality.{w}])).op
  unitIso :=
    NatIso.ofComponents (fun x ↦ Iso.op (isoMk (Iso.refl _) (by simp)))
      (fun _ ↦ Quiver.Hom.unop_inj (by cat_disch))
  counitIso := NatIso.ofComponents (fun x ↦ CostructuredArrow.isoMk (Iso.refl _))

/-- The functor of the equivalence `costructuredArrowULiftYonedaEquivalence F` followed
by the projection `CostructuredArrow uliftYoneda.{w} F ⥤ C` identifies to `(π F).leftOp`. -/
@[simps!]
def costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso (F : Cᵒᵖ ⥤ Type (max w v)) :
    (costructuredArrowULiftYonedaEquivalence.{w} F).functor ⋙ CostructuredArrow.proj _ _ ≅
      (π F).leftOp :=
  Iso.refl _

/-- Given `F : Cᵒᵖ ⥤ Type w` where `C` is a locally `w`-small category, this is the
equivalence between the opposite of the category of elements of `F` and
`CostructuredArrow shrinkYoneda.{w} F`. -/
@[implicit_reducible, simps]
noncomputable def costructuredArrowShrinkYonedaEquivalence
    [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w) :
    F.Elementsᵒᵖ ≌ CostructuredArrow shrinkYoneda.{w} F where
  functor.obj x := CostructuredArrow.mk (shrinkYonedaEquiv.symm x.unop.val)
  functor.map f := CostructuredArrow.homMk f.unop.hom.unop (by
    simp [← shrinkYonedaEquiv_symm_map.{w}])
  inverse.obj x := Opposite.op (Functor.elementsMk _ _ (shrinkYonedaEquiv x.hom))
  inverse.map f := (homMk f.left.op (by simp [shrinkYonedaEquiv_naturality])).op
  unitIso :=
    NatIso.ofComponents (fun x ↦ Iso.op (isoMk (Iso.refl _) (by simp)))
      (fun _ ↦ Quiver.Hom.unop_inj (by cat_disch))
  counitIso := NatIso.ofComponents (fun x ↦ CostructuredArrow.isoMk (Iso.refl _))

/-- The functor of the equivalence `costructuredArrowShrinkYonedaEquivalence F` followed
by the projection `CostructuredArrow shrinkYoneda.{w} F ⥤ C` identifies to `(π F).leftOp`. -/
noncomputable def costructuredArrowShrinkYonedaEquivalenceFunctorCompProjIso
    [LocallySmall.{w} C] (F : Cᵒᵖ ⥤ Type w) :
    (costructuredArrowShrinkYonedaEquivalence.{w} F).functor ⋙ CostructuredArrow.proj _ _ ≅
      (π F).leftOp :=
  Iso.refl _

/-- The initial object in `F.Elements` if `F` is representable. -/
abbrev initialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    F.Elements :=
  .mk (h.homEquiv (𝟙 X))

/-- If `F` is represented by `X`, `X` with its universal element is the initial object of
`F.Elements.` -/
def isInitialOfRepresentableBy {F : Cᵒᵖ ⥤ Type*} {X : C} (h : F.RepresentableBy X) :
    Limits.IsInitial (initialOfRepresentableBy h) :=
  .ofUniqueHom (fun e ↦ ⟨h.homEquiv.symm e.val |>.op, by simp [← h.homEquiv_comp]⟩)
    (fun _ m ↦ by ext; simp [← m.map_val, ← h.homEquiv_unop_comp])

/-- The initial object in `F.Elements` if `F` is corepresentable. -/
abbrev initialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    F.Elements :=
  .mk (h.homEquiv (𝟙 X))

/-- If `F` is corepresented by `X`, `X` with its universal element is the initial object of
`F.Elements.` -/
def isInitialOfCorepresentableBy {F : C ⥤ Type*} {X : C} (h : F.CorepresentableBy X) :
    Limits.IsInitial (initialOfCorepresentableBy h) :=
  .ofUniqueHom (fun e ↦ ⟨h.homEquiv.symm e.val, by simp [← h.homEquiv_comp]⟩)
    (fun _ m ↦ by ext; simp [← m.map_val, ← h.homEquiv_comp])

/--
The initial object in the category of elements for a representable functor. In `isInitial` it is
shown that this is initial.
-/
abbrev initialYonedaObj (A : C) : (yoneda.obj A).Elements :=
  .mk (𝟙 A)

/-- Show that `Elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def isInitialYonedaObj (A : C) : Limits.IsInitial (Elements.initialYonedaObj A) :=
  isInitialOfRepresentableBy (.yoneda A)

@[deprecated (since := "2026-08-30")] alias yoneda := initialYonedaObj
@[deprecated (since := "2026-08-30")] alias isInitial := isInitialYonedaObj

/-- The functor `(F ⋙ G).Elements ⥤ G.Elements`. -/
@[implicit_reducible, simps]
def precomp {D : Type*} [Category D] (F : C ⥤ D) (G : D ⥤ Type w) :
    (F ⋙ G).Elements ⥤ G.Elements where
  obj x := G.elementsMk (F.obj x.obj) x.val
  map f := homMk (F.map f.hom) f.map_val

instance essentiallySmall {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} F.Elements := by
  rw [essentiallySmall_iff_objectPropertyEssentiallySmall_top]
  obtain ⟨P, _, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le' (⊤ : ObjectProperty C)
  refine ⟨fun x ↦ P x.obj, ?_, fun y _ ↦ ?_⟩
  · exact small_of_surjective.{w} (α := Σ (Z : Subtype P), F.obj Z.val)
      (f := fun x ↦ ⟨F.elementsMk _ x.2, x.1.2⟩)
      (fun ⟨x, hx⟩ ↦ ⟨⟨⟨x.obj, hx⟩, x.val⟩, rfl⟩)
  · obtain ⟨Z, hZ, ⟨e⟩⟩ := hP y.obj (by simp)
    exact ⟨F.elementsMk Z (F.map e.hom y.val), hZ, ⟨isoMk e rfl⟩⟩

end Functor.Elements

open Functor.Elements in
/-- The functor `Functor.Elements.toCostructuredArrow` is compatible with
`NatTrans.mapElements`. -/
@[simps! hom_app inv_app]
def NatTrans.mapElementsOpCompToCostructuredArrowIso {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    α.mapElements.op ⋙ toCostructuredArrow F₂ ≅
      toCostructuredArrow F₁ ⋙ CostructuredArrow.map α :=
  NatIso.ofComponents (fun e ↦
    CostructuredArrow.isoMk (Iso.refl _) (yonedaEquiv.injective (by simp [yonedaEquiv])))

open Functor.Elements in
lemma NatTrans.mapElements_op_comp_toCostructuredArrow {F₁ F₂ : Cᵒᵖ ⥤ Type v} (α : F₁ ⟶ F₂) :
    α.mapElements.op ⋙ toCostructuredArrow F₂ =
      toCostructuredArrow F₁ ⋙ CostructuredArrow.map α :=
  Functor.ext_of_iso (α.mapElementsOpCompToCostructuredArrowIso)
    (fun _ ↦ CostructuredArrow.obj_ext _ _ (by dsimp)
      (yonedaEquiv.injective (by simp [yonedaEquiv])))

namespace CategoryOfElements

@[deprecated (since := "2026-08-30")] alias homMk := Functor.Elements.homMk
@[deprecated (since := "2026-08-30")] alias isoMk := Functor.Elements.isoMk
@[deprecated (since := "2026-08-30")] alias ext := Functor.Elements.hom_ext
@[deprecated (since := "2026-08-30")] alias id_val := Functor.Elements.id_hom
@[deprecated (since := "2026-08-30")] alias comp_val := Functor.Elements.comp_hom
@[deprecated (since := "2026-08-30")] alias map_snd := Functor.Elements.Hom.map_val
@[deprecated (since := "2026-08-30")] alias π := Functor.Elements.π
@[deprecated (since := "2026-08-30")] alias map := NatTrans.mapElements
@[deprecated (since := "2026-08-30")] alias map_π := NatTrans.mapElements_comp_π
@[deprecated (since := "2026-08-30")] alias toStructuredArrow :=
  Functor.Elements.toStructuredArrow
@[deprecated (since := "2026-08-30")] alias fromStructuredArrow :=
  Functor.Elements.fromStructuredArrow
@[deprecated (since := "2026-08-30")] alias fromStructuredArrow_obj :=
  Functor.Elements.toStructuredArrow_obj
@[deprecated (since := "2026-08-30")] alias fromStructuredArrow_map :=
  Functor.Elements.toStructuredArrow_map
@[deprecated (since := "2026-08-30")] alias structuredArrowEquivalence :=
  Functor.Elements.structuredArrowEquivalence
@[deprecated (since := "2026-08-30")] alias toCostructuredArrow :=
  Functor.Elements.toCostructuredArrow
@[deprecated (since := "2026-08-30")] alias fromCostructuredArrow :=
  Functor.Elements.fromCostructuredArrow
@[deprecated (since := "2026-08-30")] alias fromCostructuredArrow_obj_mk :=
  Functor.Elements.fromCostructuredArrow_obj_mk
@[deprecated (since := "2026-08-30")] alias costructuredArrowYonedaEquivalence :=
  Functor.Elements.costructuredArrowYonedaEquivalence
@[deprecated (since := "2026-08-30")] alias costructuredArrow_yoneda_equivalence_naturality :=
  NatTrans.mapElements_op_comp_toCostructuredArrow
@[deprecated (since := "2026-08-30")] alias costructuredArrowYonedaEquivalenceFunctorProj :=
  Functor.Elements.costructuredArrowYonedaEquivalenceFunctorProj
@[deprecated (since := "2026-08-30")] alias costructuredArrowYonedaEquivalenceInverseπ :=
  Functor.Elements.costructuredArrowYonedaEquivalenceInverseπ
@[deprecated (since := "2026-08-30")] alias costructuredArrowULiftYonedaEquivalence :=
  Functor.Elements.costructuredArrowULiftYonedaEquivalence
@[deprecated (since := "2026-08-30")]
alias costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso :=
  Functor.Elements.costructuredArrowULiftYonedaEquivalenceFunctorCompProjIso

@[deprecated "No replacement (this is proven `by dsimp`)" (since := "2026-08-30")]
theorem to_comma_map_right (F : C ⥤ Type w) {X Y} (f : X ⟶ Y) :
    ((Functor.Elements.toStructuredArrow F).map f).right = f.hom := by
  dsimp

end CategoryOfElements

end CategoryTheory
