/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Hom
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.Data.ULift
public import Mathlib.Logic.Function.ULift

/-!
# The Yoneda embedding

Let `C : Type u₁` be a category (with `Category.{v₁} C`). We define
the Yoneda embedding as a fully faithful functor `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`,
In addition to `yoneda`, we also define `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)`
with the additional universe parameter `w`. When `C` is locally `w`-small,
one may also use `shrinkYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type w` from the file
`Mathlib/CategoryTheory/ShrinkYoneda.lean`.

The naturality of the bijection `yonedaEquiv` involved in the
Yoneda lemma is also expressed as a natural isomorphism
`yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Opposite Functor

universe w v v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u₁} [Category.{v₁} C]

/-- The Yoneda embedding, as a functor from `C` into presheaves on `C`. -/
@[simps obj_obj obj_map map_app, stacks 001O]
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj Y := (unop Y) ⟶ X
      map f := TypeCat.ofHom fun g ↦ f.unop ≫ g }
  map f :=
    { app _ := TypeCat.ofHom fun g ↦ g ≫ f }

/-- Unification hint for `(yoneda.obj X).obj (op Y) = Y ⟶ X`. -/
unif_hint yoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (yoneda.obj X).obj (op Y) ≟ Y' ⟶ X'

/-- Unification hint for `(yoneda.obj X).obj Y = unop Y ⟶ X`. -/
unif_hint yoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (yoneda.obj X).obj Y ≟ unop Y' ⟶ X'

/-- Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ, simps! obj_obj obj_map map_app]
def uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type (max w v₁) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{w}

/-- Unification hint for `(uliftYoneda.obj X).obj (op Y) ≃ ULift (Y ⟶ X)`. -/
unif_hint uliftYoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftYoneda.{w}.obj X).obj (op Y) ≟ ULift (Y' ⟶ X')

/-- Unification hint for `(uliftYoneda.obj X).obj Y = ULift (unop Y ⟶ X)`. -/
unif_hint uliftYoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftYoneda.{w}.obj X).obj Y ≟ ULift (unop Y' ⟶ X')

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftYoneda.{w} (C := C) ≅ yoneda`. -/
@[simps! inv_app_app hom_app_app]
def uliftYonedaIsoYoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftYoneda.{w} (C := C) ≅ yoneda :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso))

/-- The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
abbrev coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ := yoneda.flip

/-- Unification hint for `(coyoneda.obj (op X)).obj Y = X ⟶ Y`. -/
unif_hint coyoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (coyoneda.obj (op X)).obj Y ≟ X' ⟶ Y'

/-- Unification hint for `(coyoneda.obj Y).obj X = unop Y ⟶ X`. -/
unif_hint coyoneda_obj_obj_eq_hom' (X X' : C) (Y Y' : Cᵒᵖ) where
  X ≟ X'
  Y ≟ Y' ⊢
  (coyoneda.obj Y).obj X ≟ unop Y' ⟶ X'

/-- Variant of the Coyoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ]
abbrev uliftCoyoneda : Cᵒᵖ ⥤ C ⥤ Type (max w v₁) := uliftYoneda.{w}.flip

/-- Unification hint for `(uliftCoyoneda.{w}.obj (op X)).obj Y = ULift (Y ⟶ X)`. -/
unif_hint uliftCoyoneda_obj_obj_eq_hom (X X' Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftCoyoneda.{w}.obj (op X)).obj Y ≟ ULift (Y' ⟶ X')

/-- Unification hint for `(uliftCoyoneda.{w}.obj X).obj Y = ULift (unop Y ⟶ X)`. -/
unif_hint uliftCoyoneda_obj_obj_eq_hom' (X X' : Cᵒᵖ) (Y Y' : C) where
  X ≟ X'
  Y ≟ Y' ⊢
  (uliftCoyoneda.{w}.obj X).obj Y ≟ ULift (Y' ⟶ unop X')

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftCoyoneda.{w} (C := C) ≅ coyoneda`. -/
@[simps! inv_app_app hom_app_app]
def uliftCoyonedaIsoCoyoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftCoyoneda.{w} (C := C) ≅ coyoneda :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso))

namespace Yoneda

theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) :
    (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) := by
  simp

/-- The Yoneda embedding is fully faithful. -/
def fullyFaithful : (yoneda (C := C)).FullyFaithful where
  preimage f := f.app _ (𝟙 _)
  map_preimage := by -- this was automatic
    intro Z W f
    ext X x
    have := f.naturality_apply x.op (𝟙 Z)
    cat_disch

lemma fullyFaithful_preimage {X Y : C} (f : yoneda.obj X ⟶ yoneda.obj Y) :
    fullyFaithful.preimage f = f.app (op X) (𝟙 X) := rfl

/-- The Yoneda embedding is full. -/
@[stacks 001P]
instance yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full :=
  fullyFaithful.full

/-- The Yoneda embedding is faithful. -/
@[stacks 001P]
instance yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply Yoneda.ext
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
-- functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y))
    (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
    (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := TypeCat.ofHom p
        inv := TypeCat.ofHom q })

/-- If `yoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful yoneda f

end Yoneda

namespace ULiftYoneda

variable (C)

/-- When `C` is a category such that `Category.{v₁} C`, then
the functor `uliftYoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)` is fully faithful. -/
def fullyFaithful : (uliftYoneda.{w} (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

instance : (uliftYoneda.{w} (C := C)).Full :=
  (fullyFaithful C).full

instance : (uliftYoneda.{w} (C := C)).Faithful :=
  (fullyFaithful C).faithful

end ULiftYoneda

namespace Coyoneda

/-- The co-Yoneda embedding is fully faithful. -/
def fullyFaithful : (coyoneda (C := C)).FullyFaithful where
  preimage f := (f.app _ (𝟙 _)).op
  map_preimage := by
    intro Z W f
    ext X x
    have := f.naturality_apply x (𝟙 (unop Z))
    cat_disch

lemma fullyFaithful_preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) :
    fullyFaithful.preimage f = (f.app X.unop (𝟙 X.unop)).op := rfl

/-- The morphism `X ⟶ Y` corresponding to a natural transformation
`coyoneda.obj X ⟶ coyoneda.obj Y`. -/
def preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) : X ⟶ Y :=
  (f.app _ (𝟙 X.unop)).op

instance coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full :=
  fullyFaithful.full

instance coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

/-- Extensionality via Coyoneda. The typical usage would be
```
-- Goal is `X ≅ Y`
apply Coyoneda.ext
-- Goals are now functions `(X ⟶ Z) → (Y ⟶ Z)`, `(Y ⟶ Z) → (X ⟶ Z)`, and the fact that these
-- functions are inverses and natural in `Z`.
```
-/
def ext (X Y : C) (p : ∀ {Z : C}, (X ⟶ Z) → (Y ⟶ Z))
    (q : ∀ {Z : C}, (Y ⟶ Z) → (X ⟶ Z))
    (h₁ : ∀ {Z : C} (f : X ⟶ Z), q (p f) = f) (h₂ : ∀ {Z : C} (f : Y ⟶ Z), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Y ⟶ Z) (g : Z ⟶ Z'), q (f ≫ g) = q f ≫ g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents (fun Z =>
      { hom := TypeCat.ofHom q
        inv := TypeCat.ofHom p })) |>.unop

/-- If `coyoneda.map f` is an isomorphism, so was `f`.
-/
theorem isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful coyoneda f

/-- The identity functor on `Type` is isomorphic to the coyoneda functor coming from `PUnit`. -/
def punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  NatIso.ofComponents fun X =>
    { hom := TypeCat.ofHom fun f => f.hom ⟨⟩
      inv := TypeCat.ofHom fun x => TypeCat.ofHom fun _ => x }

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
@[simps! inv_app hom_app]
def objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X :=
  NatIso.ofComponents fun _ => (opEquiv _ _).toIso

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
def opIso : yoneda ⋙ (whiskeringLeft _ _ _).obj (opOp C) ≅ coyoneda :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ (opEquiv (op Y) X).toIso)
    (fun _ ↦ rfl)) (fun _ ↦ rfl)

namespace ULiftCoyoneda

variable (C)

/-- When `C` is a category such that `Category.{v₁} C`, then
the functor `uliftCoyoneda.{w} : C ⥤ Cᵒᵖ ⥤ Type (max w v₁)` is fully faithful. -/
def fullyFaithful : (uliftCoyoneda.{w} (C := C)).FullyFaithful :=
  Coyoneda.fullyFaithful.comp (fullyFaithfulULiftFunctor.whiskeringRight _)

instance : (uliftCoyoneda.{w} (C := C)).Full :=
  (fullyFaithful C).full

instance : (uliftCoyoneda.{w} (C := C)).Faithful :=
  (fullyFaithful C).faithful

end ULiftCoyoneda

end Coyoneda

namespace Functor

/-- The data which expresses that a functor `F : Cᵒᵖ ⥤ Type v` is representable by `Y : C`.

In the situation where `F` factors through a concrete category, it may be more convenient to use
the API in the file `Mathlib/CategoryTheory/ConcreteCategory/Representable.lean`. -/
structure RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    homEquiv (f ≫ g) = F.map f.op (homEquiv g) := by cat_disch

lemma RepresentableBy.comp_homEquiv_symm {F : Cᵒᵖ ⥤ Type v} {Y : C}
    (e : F.RepresentableBy Y) {X X' : C} (x : F.obj (op X')) (f : X ⟶ X') :
    f ≫ e.homEquiv.symm x = e.homEquiv.symm (F.map f.op x) :=
  e.homEquiv.injective (by simp [homEquiv_comp])

lemma RepresentableBy.homEquiv_unop_comp {F : Cᵒᵖ ⥤ Type*} {Y : C}
    (h : F.RepresentableBy Y) {X : Cᵒᵖ} {X' : C} (f : Opposite.op X' ⟶ X) (g : X' ⟶ Y) :
    h.homEquiv (f.unop ≫ g) = F.map f (h.homEquiv g) :=
  h.homEquiv_comp _ _

/-- If `F ≅ F'`, and `F` is representable, then `F'` is representable. -/
def RepresentableBy.ofIso {F F' : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    (e' : F ≅ F') : F'.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

/-- The data which expresses that a functor `F : C ⥤ Type v` is corepresentable by `X : C`. -/
structure CorepresentableBy (F : C ⥤ Type v) (X : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj Y`. -/
  homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y
  homEquiv_comp {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    homEquiv (f ≫ g) = F.map g (homEquiv f) := by cat_disch

lemma CorepresentableBy.homEquiv_symm_comp {F : C ⥤ Type v} {X : C}
    (e : F.CorepresentableBy X) {Y Y' : C} (y : F.obj Y) (g : Y ⟶ Y') :
    e.homEquiv.symm y ≫ g = e.homEquiv.symm (F.map g y) :=
  e.homEquiv.injective (by simp [homEquiv_comp])

/-- If `F ≅ F'`, and `F` is corepresentable, then `F'` is corepresentable. -/
def CorepresentableBy.ofIso {F F' : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    (e' : F ≅ F') :
    F'.CorepresentableBy X where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply e'.hom.naturality_apply

lemma RepresentableBy.homEquiv_eq {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    {X : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f.op (e.homEquiv (𝟙 Y)) := by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]

lemma CorepresentableBy.homEquiv_eq {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    {Y : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f (e.homEquiv (𝟙 X)) := by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

/-- Representing objects are unique up to isomorphism. -/
@[simps!]
def RepresentableBy.uniqueUpToIso {F : Cᵒᵖ ⥤ Type v} {Y Y' : C} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') : Y ≅ Y' :=
  let ε {X} := (@e.homEquiv X).trans e'.homEquiv.symm
  Yoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, comp_homEquiv_symm, homEquiv_comp])

/-- Corepresenting objects are unique up to isomorphism. -/
@[simps!]
def CorepresentableBy.uniqueUpToIso {F : C ⥤ Type v} {X X' : C} (e : F.CorepresentableBy X)
    (e' : F.CorepresentableBy X') : X ≅ X' :=
  let ε {Y} := (@e.homEquiv Y).trans e'.homEquiv.symm
  Coyoneda.ext _ _ ε ε.symm (by simp) (by simp)
    (by simp [ε, homEquiv_symm_comp, homEquiv_comp])

@[ext]
lemma RepresentableBy.ext {F : Cᵒᵖ ⥤ Type v} {Y : C} {e e' : F.RepresentableBy Y}
    (h : e.homEquiv (𝟙 Y) = e'.homEquiv (𝟙 Y)) : e = e' := by
  have : ∀ {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]
lemma CorepresentableBy.ext {F : C ⥤ Type v} {X : C} {e e' : F.CorepresentableBy X}
    (h : e.homEquiv (𝟙 X) = e'.homEquiv (𝟙 X)) : e = e' := by
  have : ∀ {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

/-- The obvious bijection `F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F)`
when `F : Cᵒᵖ ⥤ Type v₁` and `[Category.{v₁} C]`. -/
def representableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} :
    F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ by apply e.hom.naturality_apply }

/-- `yoneda.obj X` is represented by `X`. -/
protected def RepresentableBy.yoneda (X : C) : (yoneda.obj X).RepresentableBy X :=
  Functor.representableByEquiv.symm (Iso.refl _)

@[simp]
lemma RepresentableBy.coyoneda_homEquiv (X Y : C) :
    (RepresentableBy.yoneda X).homEquiv = Equiv.refl (Y ⟶ X) :=
  rfl

/-- The isomorphism `yoneda.obj Y ≅ F` induced by `e : F.RepresentableBy Y`. -/
def RepresentableBy.toIso {F : Cᵒᵖ ⥤ Type v₁} {Y : C} (e : F.RepresentableBy Y) :
    yoneda.obj Y ≅ F :=
  representableByEquiv e

/-- The obvious bijection `F.CorepresentableBy X ≃ (yoneda.obj Y ≅ F)`
when `F : C ⥤ Type v₁` and `[Category.{v₁} C]`. -/
def corepresentableByEquiv {F : C ⥤ Type v₁} {X : C} :
    F.CorepresentableBy X ≃ (coyoneda.obj (op X) ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    dsimp
    apply r.homEquiv_comp)
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ by apply e.hom.naturality_apply }

/-- `coyoneda.obj X` is represented by `X`. -/
protected def CorepresentableBy.coyoneda (X : Cᵒᵖ) :
    (coyoneda.obj X).CorepresentableBy X.unop :=
  Functor.corepresentableByEquiv.symm (Iso.refl _)

@[simp]
lemma CorepresentableBy.coyoneda_homEquiv (X : Cᵒᵖ) (Y : C) :
    (CorepresentableBy.coyoneda X).homEquiv = Equiv.refl (X.unop ⟶ Y) :=
  rfl

/-- The isomorphism `coyoneda.obj (op X) ≅ F` induced by `e : F.CorepresentableBy X`. -/
def CorepresentableBy.toIso {F : C ⥤ Type v₁} {X : C} (e : F.CorepresentableBy X) :
    coyoneda.obj (op X) ≅ F :=
  corepresentableByEquiv e

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
def RepresentableBy.ofIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (R : F.RepresentableBy X)
    (e : Y ≅ X) :
    F.RepresentableBy Y where
  homEquiv {Z} := e.homToEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
def CorepresentableBy.ofIsoObj {F : C ⥤ Type w} {X Y : C} (R : F.CorepresentableBy X)
    (e : Y ≅ X) :
    F.CorepresentableBy Y where
  homEquiv {Z} := e.homFromEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- If `Y` is isomorphic to `X`, representations of `F` by `X` are equivalent
to representations of `F` by `Y`. -/
@[simps]
def RepresentableBy.equivOfIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.RepresentableBy X ≃ F.RepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- If `Y` is isomorphic to `X`, corepresentations of `F` by `X` are equivalent
to corepresentations of `F` by `Y`. -/
@[simps]
def CorepresentableBy.equivOfIsoObj {F : C ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.CorepresentableBy X ≃ F.CorepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Representing `F` composed with universe lifting is the same as representing `F`. -/
@[simps]
def representableByUliftFunctorEquiv {F : Cᵒᵖ ⥤ Type v} {X : C} :
    (F ⋙ uliftFunctor.{w}).RepresentableBy X ≃ F.RepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Corepresenting `F` composed with universe lifting is the same as corepresenting `F`. -/
@[simps]
def corepresentableByUliftFunctorEquiv {F : C ⥤ Type v} {X : C} :
    (F ⋙ uliftFunctor.{w}).CorepresentableBy X ≃ F.CorepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

/-- Version of `representableByEquiv` with more general universe assumptions. -/
@[simps]
def RepresentableBy.equivUliftYonedaIso (F : Cᵒᵖ ⥤ Type (max w v₁)) (X : C) :
    F.RepresentableBy X ≃ (uliftYoneda.obj X ≅ F) where
  toFun R := NatIso.ofComponents (fun X ↦ equivEquivIso (Equiv.ulift.trans R.homEquiv)) <| by
    intro X Y f
    ext x
    exact R.homEquiv_comp f.unop _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f.op) ⟨g⟩) }

/-- Version of `corepresentableByEquiv` with more general universe assumptions. -/
@[simps]
def CorepresentableBy.equivUliftCoyonedaIso (F : C ⥤ Type (max w v₁)) (X : C) :
    F.CorepresentableBy X ≃ (uliftCoyoneda.obj (op X) ≅ F) where
  toFun R := NatIso.ofComponents (fun X ↦ equivEquivIso (Equiv.ulift.trans R.homEquiv)) <| by
    intro X Y f
    ext x
    exact R.homEquiv_comp f _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f) ⟨g⟩) }

/-- A functor `F : Cᵒᵖ ⥤ Type v` is representable if there is an object `Y` with a structure
`F.RepresentableBy Y`, i.e. there is a natural bijection `(X ⟶ Y) ≃ F.obj (op X)`,
which may also be rephrased as a natural isomorphism `yoneda.obj X ≅ F` when `Category.{v} C`. -/
@[stacks 001Q]
class IsRepresentable (F : Cᵒᵖ ⥤ Type v) : Prop where
  has_representation : ∃ (Y : C), Nonempty (F.RepresentableBy Y)

lemma RepresentableBy.isRepresentable {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) :
    F.IsRepresentable where
  has_representation := ⟨Y, ⟨e⟩⟩

/-- Alternative constructor for `F.IsRepresentable`, which takes as an input an
isomorphism `yoneda.obj X ≅ F`. -/
lemma IsRepresentable.mk' {F : Cᵒᵖ ⥤ Type v₁} {X : C} (e : yoneda.obj X ≅ F) :
    F.IsRepresentable :=
  (representableByEquiv.symm e).isRepresentable

instance {X : C} : IsRepresentable (yoneda.obj X) :=
  IsRepresentable.mk' (Iso.refl _)

instance {X : C} : IsRepresentable (uliftYoneda.{w}.obj X) :=
  RepresentableBy.isRepresentable (representableByUliftFunctorEquiv.symm (RepresentableBy.yoneda X))

/--
A functor `F : C ⥤ Type v₁` is corepresentable if there is object `X` so `F ≅ coyoneda.obj X`.
-/
@[stacks 001Q]
class IsCorepresentable (F : C ⥤ Type v) : Prop where
  has_corepresentation : ∃ (X : C), Nonempty (F.CorepresentableBy X)

lemma CorepresentableBy.isCorepresentable {F : C ⥤ Type v} {X : C}
    (e : F.CorepresentableBy X) : F.IsCorepresentable where
  has_corepresentation := ⟨X, ⟨e⟩⟩

/-- Alternative constructor for `F.IsCorepresentable`, which takes as an input an
isomorphism `coyoneda.obj (op X) ≅ F`. -/
lemma IsCorepresentable.mk' {F : C ⥤ Type v₁} {X : C} (e : coyoneda.obj (op X) ≅ F) :
    F.IsCorepresentable :=
  (corepresentableByEquiv.symm e).isCorepresentable

instance {X : Cᵒᵖ} : IsCorepresentable (coyoneda.obj X) :=
  IsCorepresentable.mk' (Iso.refl _)

instance {X : Cᵒᵖ} : IsCorepresentable (uliftCoyoneda.{w}.obj X) :=
  CorepresentableBy.isCorepresentable
    (corepresentableByUliftFunctorEquiv.symm (CorepresentableBy.coyoneda X))

-- instance : corepresentable (𝟭 (Type v₁)) :=
-- corepresentable_of_nat_iso (op punit) coyoneda.punit_iso
section Representable

variable (F : Cᵒᵖ ⥤ Type v) [hF : F.IsRepresentable]

/-- The representing object for the representable functor `F`. -/
noncomputable def reprX : C :=
  hF.has_representation.choose

/-- A chosen term in `F.RepresentableBy (reprX F)` when `F.IsRepresentable` holds. -/
noncomputable def representableBy : F.RepresentableBy F.reprX :=
  hF.has_representation.choose_spec.some

/-- Any representing object for a representable functor `F` is isomorphic to `reprX F`. -/
noncomputable def RepresentableBy.isoReprX {Y : C} (e : F.RepresentableBy Y) :
    Y ≅ F.reprX :=
  RepresentableBy.uniqueUpToIso e (representableBy F)

/-- The representing element for the representable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def reprx : F.obj (op F.reprX) :=
  F.representableBy.homEquiv (𝟙 _)

/-- An isomorphism between a representable `F` and a functor of the
form `C(-, F.reprX)`.  Note the components `F.reprW.app X`
definitionally have type `(X.unop ⟶ F.reprX) ≅ F.obj X`.
-/
noncomputable def reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] :
    yoneda.obj F.reprX ≅ F := F.representableBy.toIso

theorem reprW_hom_app (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    F.reprW.hom.app X f = F.map f.op F.reprx := by
  apply RepresentableBy.homEquiv_eq

/-- If `F` is representable, it is, modulo universe lifting, isomorphic to
`Hom(-, X)` for the representing object `X`. -/
noncomputable def uliftYonedaReprXIso (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable] :
    uliftYoneda.{v}.obj F.reprX ≅ F :=
  (RepresentableBy.equivUliftYonedaIso F _) F.representableBy

lemma uliftYonedaReprXIso_hom_app (F : Cᵒᵖ ⥤ Type (max v v₁)) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : ULift (unop X ⟶ F.reprX)) :
    F.uliftYonedaReprXIso.hom.app X f = F.map f.down.op F.reprx :=
  RepresentableBy.homEquiv_eq _ _

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [hF : F.IsCorepresentable]

/-- The representing object for the corepresentable functor `F`. -/
noncomputable def coreprX : C :=
  hF.has_corepresentation.choose

/-- A chosen term in `F.CorepresentableBy (coreprX F)` when `F.IsCorepresentable` holds. -/
noncomputable def corepresentableBy : F.CorepresentableBy F.coreprX :=
  hF.has_corepresentation.choose_spec.some

variable {F} in
/-- Any corepresenting object for a corepresentable functor `F` is isomorphic to `coreprX F`. -/
noncomputable def CorepresentableBy.isoCoreprX {Y : C} (e : F.CorepresentableBy Y) :
    Y ≅ F.coreprX :=
  CorepresentableBy.uniqueUpToIso e (corepresentableBy F)

/-- The representing element for the corepresentable functor `F`, sometimes called the universal
element of the functor.
-/
noncomputable def coreprx : F.obj F.coreprX :=
  F.corepresentableBy.homEquiv (𝟙 _)

/-- An isomorphism between a corepresentable `F` and a functor of the form
`C(F.corepr X, -)`. Note the components `F.coreprW.app X`
definitionally have type `F.corepr_X ⟶ X ≅ F.obj X`.
-/
noncomputable def coreprW (F : C ⥤ Type v₁) [F.IsCorepresentable] :
    coyoneda.obj (op F.coreprX) ≅ F :=
  F.corepresentableBy.toIso

theorem coreprW_hom_app (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X) :
    F.coreprW.hom.app X f = F.map f F.coreprx := by
  apply CorepresentableBy.homEquiv_eq

/-- If `F` is corepresentable, it is, modulo universe lifting, isomorphic to
`Hom(X, -)` for the corepresenting object `X`. -/
noncomputable def uliftCoyonedaCoreprXIso (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable] :
    uliftCoyoneda.{v}.obj (op F.coreprX) ≅ F :=
  (CorepresentableBy.equivUliftCoyonedaIso F _) F.corepresentableBy

lemma uliftCoyonedaCoreprXIso_hom_app (F : C ⥤ Type (max v v₁)) [F.IsCorepresentable]
    (X : C) (f : ULift (F.coreprX ⟶ X)) :
    F.uliftCoyonedaCoreprXIso.hom.app X f = F.map f.down F.coreprx :=
  CorepresentableBy.homEquiv_eq _ _

end Corepresentable

lemma isRepresentable_comp_uliftFunctor_iff {F : Cᵒᵖ ⥤ Type v} :
    (F ⋙ uliftFunctor.{w}).IsRepresentable ↔ F.IsRepresentable where
  mp | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨representableByUliftFunctorEquiv R⟩⟩
  mpr | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨representableByUliftFunctorEquiv.symm R⟩⟩

lemma isCorepresentable_comp_uliftFunctor_iff {F : C ⥤ Type v} :
    (F ⋙ uliftFunctor.{w}).IsCorepresentable ↔ F.IsCorepresentable where
  mp | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨corepresentableByUliftFunctorEquiv R⟩⟩
  mpr | ⟨X, ⟨R⟩⟩ => ⟨X, ⟨corepresentableByUliftFunctorEquiv.symm R⟩⟩

instance (F : Cᵒᵖ ⥤ Type v) [F.IsRepresentable] : (F ⋙ uliftFunctor.{w}).IsRepresentable :=
  isRepresentable_comp_uliftFunctor_iff.mpr ‹_›

instance (F : C ⥤ Type v) [F.IsCorepresentable] : (F ⋙ uliftFunctor.{w}).IsCorepresentable :=
  isCorepresentable_comp_uliftFunctor_iff.mpr ‹_›

end Functor

theorem isRepresentable_of_natIso (F : Cᵒᵖ ⥤ Type v) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable

theorem corepresentable_of_natIso (F : C ⥤ Type v) {G} (i : F ≅ G) [F.IsCorepresentable] :
    G.IsCorepresentable :=
  (F.corepresentableBy.ofIso i).isCorepresentable

/-- The identity functor on `Type v` is corepresented by `PUnit`. -/
def Functor.CorepresentableBy.id : (𝟭 (Type v)).CorepresentableBy PUnit :=
  corepresentableByEquiv.symm Coyoneda.punitIso

@[simp] lemma Functor.CorepresentableBy.id_homEquiv_apply (X : Type v)
    (a : PUnit ⟶ X) : dsimp% id.homEquiv a = a ⟨⟩ :=
  rfl

@[simp] lemma Functor.CorepresentableBy.id_homEquiv_symm_apply (X : Type v) (x : X)
    (a : PUnit) : dsimp% id.homEquiv.symm x a = x :=
  rfl

instance : Functor.IsCorepresentable (𝟭 (Type v)) :=
  Functor.CorepresentableBy.id.isCorepresentable

open Opposite

variable (C)

-- We need to help typeclass inference with some awkward universe levels here.
instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod'.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod'.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open Yoneda

section YonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app _ := TypeCat.ofHom fun f ↦ F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp

theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ) :
    (yonedaEquiv.symm x).app Y = TypeCat.ofHom fun f ↦ F.map f.op x :=
  rfl

theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) := by
  simp [yonedaEquiv, ← f.naturality_apply]

/-- Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
    than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
    can avoid the "motive is not type correct" error. -/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type v₁)
    (x : F.obj ⟨X⟩) : yoneda.map f ≫ yonedaEquiv.symm x = yonedaEquiv.symm ((F.map f.op) x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Cᵒᵖ ⥤ Type v₁} (f : F ⟶ F')
    (x : F.obj ⟨X⟩) : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app ⟨X⟩ x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = f.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
    than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
    can avoid the "motive is not type correct" error. -/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = f.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X) :
    yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
lemma hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

variable (C)

/-- The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

@[ext]
lemma yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) :
    (yonedaPairing C).map α = TypeCat.ofHom fun β ↦ yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Yoneda lemma asserts that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`. -/
@[stacks 001P]
def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        dsimp [yonedaEvaluation, yonedaEquiv]
        simp [← NatTrans.naturality_apply])

variable {C}

set_option backward.defeqAttrib.useBackward true in
/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅
      evaluation Cᵒᵖ (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [yonedaEquiv, ← NatTrans.naturality_apply])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The curried version of the Yoneda lemma. -/
def largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] :
    yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        simp [yonedaEquiv]))
    (by
      intro Y Z f
      ext F g
      simpa [← ULift.down_inj] using (yonedaEquiv_naturality _ _).symm)

/-- Version of the Yoneda lemma where the presheaf is fixed but the argument varies. -/
def yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

set_option backward.defeqAttrib.useBackward true in
/-- The curried version of yoneda lemma when `C` is small. -/
def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op
      ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← NatTrans.naturality_apply]))

lemma isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) :
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by cat_disch), hg⟩

lemma isIso_iff_yoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ isIso_of_yoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((yoneda.map f).app _))

lemma isIso_iff_isIso_yoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((yoneda.map f).app ⟨c⟩) := by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun _ ↦ (bijective_iff_isIso_ofHom _)

set_option backward.defeqAttrib.useBackward true in
/-- Yoneda's lemma as a bijection `(uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`. -/
@[simps! -isSimp apply symm_apply_app]
def uliftYonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)} :
    (uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X) where
  toFun τ := τ.app (op X) (ULift.up (𝟙 _))
  invFun x := { app Y := TypeCat.ofHom fun y ↦ F.map y.down.op x }
  left_inv τ := by
    ext ⟨Y⟩ ⟨y⟩
    simp [← NatTrans.naturality_apply]
  right_inv x := by simp

attribute [simp] uliftYonedaEquiv_symm_apply_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma uliftYonedaEquiv_naturality {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type (max w v₁)}
    (f : uliftYoneda.{w}.obj (unop X) ⟶ F) (g : X ⟶ Y) :
    F.map g (uliftYonedaEquiv.{w} f) = uliftYonedaEquiv.{w} (uliftYoneda.map g.unop ≫ f) := by
  simp [uliftYonedaEquiv, uliftYoneda, ← f.naturality_apply]

lemma uliftYonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type (max w v₁)}
    (α : uliftYoneda.{w}.obj X ⟶ F) (β : F ⟶ G) :
    uliftYonedaEquiv.{w} (α ≫ β) = β.app _ (uliftYonedaEquiv α) :=
  rfl

@[reassoc]
lemma uliftYonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type (max w v₁)}
    (t : F.obj X) :
    uliftYonedaEquiv.{w}.symm (F.map f t) =
      uliftYoneda.map f.unop ≫ uliftYonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := uliftYonedaEquiv.surjective t
  rw [uliftYonedaEquiv_naturality]
  simp

@[reassoc]
lemma uliftYonedaEquiv_symm_comp
    {F G : Cᵒᵖ ⥤ Type max w v₁} {X : Cᵒᵖ} (x : F.obj X) (f : F ⟶ G) :
    uliftYonedaEquiv.symm x ≫ f = uliftYonedaEquiv.symm (f.app _ x) :=
  uliftYonedaEquiv.injective (by rw [uliftYonedaEquiv_comp]; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma uliftYonedaEquiv_uliftYoneda_map {X Y : C} (f : X ⟶ Y) :
    DFunLike.coe (β := fun _ ↦ ULift.{w} (X ⟶ Y))
        uliftYonedaEquiv.{w} (uliftYoneda.map f) = ULift.up f := by
  simp [uliftYonedaEquiv, uliftYoneda]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftYoneda.obj X ⟶ P` agree. -/
lemma hom_ext_uliftYoneda {P Q : Cᵒᵖ ⥤ Type (max w v₁)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : uliftYoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa [-op_unop, uliftYonedaEquiv_comp] using
    congr_arg uliftYonedaEquiv.{w} (h _ (uliftYonedaEquiv.symm x))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A variant of the curried version of the Yoneda lemma with a raise in the universe level. -/
def uliftYonedaOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] :
    uliftYoneda.{w}.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftYonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftYonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (uliftYonedaEquiv_naturality _ _).symm)

end YonedaLemma

section CoyonedaLemma

variable {C}

/-- We have a type-level equivalence between natural transformations from the coyoneda embedding
and elements of `F.obj X.unop`, without any universe switching.
-/
def coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.obj X where
  toFun η := η.app X (𝟙 X)
  invFun ξ := { app _ := TypeCat.ofHom fun x ↦ F.map x ξ }
  left_inv := fun η ↦ by
    ext Y (x : X ⟶ Y)
    simp [← NatTrans.naturality_apply]
  right_inv := by intro ξ; simp

theorem coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv f = f.app X (𝟙 X) :=
  rfl

@[simp]
theorem coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl

lemma coyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g.op ≫ f) := by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  simp

lemma coyonedaEquiv_comp {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G) :
    coyonedaEquiv (α ≫ β) = β.app _ (coyonedaEquiv α) := by
  rfl

lemma coyonedaEquiv_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    coyonedaEquiv (coyoneda.map f.op) = f := by
  rw [coyonedaEquiv_apply]
  simp

lemma map_coyonedaEquiv {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = f.app Y g := by
  rw [coyonedaEquiv_naturality, coyonedaEquiv_comp, coyonedaEquiv_coyoneda_map]

lemma coyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj X) :
    coyonedaEquiv.symm (F.map f t) = coyoneda.map f.op ≫ coyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

variable (C)

/-- The "Coyoneda evaluation" functor, which sends `X : C` and `F : C ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]
theorem coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (coyonedaEvaluation C).obj P) :
    ((coyonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

/-- The "Coyoneda pairing" functor, which sends `X : C` and `F : C ⥤ Type`
to `coyoneda.rightOp.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

@[ext]
lemma coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P) :
    (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2 :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Coyoneda lemma asserts that the Coyoneda pairing
`(X : C, F : C ⥤ Type) ↦ (coyoneda.obj X ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`. -/
@[stacks 001P]
def coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        dsimp [coyonedaEquiv, coyonedaEvaluation]
        simp [← NatTrans.naturality_apply])

variable {C}

set_option backward.defeqAttrib.useBackward true in
/- Porting note: this used to be two calls to `tidy` -/
/-- The curried version of coyoneda lemma when `C` is small. -/
def curriedCoyonedaLemma {C : Type u₁} [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ≅ evaluation C (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← NatTrans.naturality_apply])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The curried version of the Coyoneda lemma. -/
def largeCurriedCoyonedaLemma {C : Type u₁} [Category.{v₁} C] :
    coyoneda.rightOp ⋙ coyoneda ≅
      evaluation C (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intro Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (coyonedaEquiv_naturality _ _).symm)

/-- Version of the Coyoneda lemma where the presheaf is fixed but the argument varies. -/
def coyonedaCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁) :
    coyoneda.rightOp ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

set_option backward.defeqAttrib.useBackward true in
/-- The curried version of coyoneda lemma when `C` is small. -/
def curriedCoyonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft C (C ⥤ Type u₁)ᵒᵖ (Type u₁)).obj coyoneda.rightOp
      ≅ 𝟭 (C ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← NatTrans.naturality_apply]))

lemma isIso_of_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) :
    IsIso f := by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]

lemma isIso_iff_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ isIso_of_coyoneda_map_bijective f hf⟩
  intro T
  rw [bijective_iff_isIso_ofHom]
  exact inferInstanceAs (IsIso ((coyoneda.map f.op).app _))

lemma isIso_iff_isIso_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((coyoneda.map f.op).app c) := by
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' fun _ ↦ bijective_iff_isIso_ofHom _

set_option backward.defeqAttrib.useBackward true in
/-- Coyoneda's lemma as a bijection `(uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)`
for any presheaf of type `F : Cᵒᵖ ⥤ Type (max w v₁)` for some
auxiliary universe `w`. -/
@[simps! -isSimp apply symm_apply_app]
def uliftCoyonedaEquiv {X : Cᵒᵖ} {F : C ⥤ Type (max w v₁)} :
    (uliftCoyoneda.{w}.obj X ⟶ F) ≃ F.obj X.unop where
  toFun τ := τ.app X.unop (ULift.up (𝟙 _))
  invFun x := { app Y := TypeCat.ofHom fun y ↦ F.map y.down x }
  left_inv τ := by
    ext Y ⟨x⟩
    simp [← comp_apply, ← τ.naturality]
  right_inv x := by simp

attribute [simp] uliftCoyonedaEquiv_symm_apply_app

set_option backward.isDefEq.respectTransparency false in
lemma uliftCoyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type max w v₁}
    (f : uliftCoyoneda.{w}.obj (op X) ⟶ F) (g : X ⟶ Y) :
    F.map g (uliftCoyonedaEquiv.{w} f) = uliftCoyonedaEquiv.{w} (uliftCoyoneda.map g.op ≫ f) := by
  simp [uliftCoyonedaEquiv, ← comp_apply, ← f.naturality]

lemma uliftCoyonedaEquiv_comp {X : Cᵒᵖ} {F G : C ⥤ Type (max w v₁)}
    (α : uliftCoyoneda.{w}.obj X ⟶ F) (β : F ⟶ G) :
    uliftCoyonedaEquiv.{w} (α ≫ β) = β.app _ (uliftCoyonedaEquiv α) :=
  rfl

@[reassoc]
lemma uliftCoyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type (max w v₁)}
    (t : F.obj X) :
    uliftCoyonedaEquiv.{w}.symm (F.map f t) =
      uliftCoyoneda.map f.op ≫ uliftCoyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := uliftCoyonedaEquiv.surjective t
  rw [uliftCoyonedaEquiv_naturality]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma uliftCoyonedaEquiv_uliftCoyoneda_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    DFunLike.coe (β := fun _ ↦ ULift.{w} (Y.unop ⟶ X.unop))
        uliftCoyonedaEquiv.{w} (uliftCoyoneda.map f) = ULift.up f.unop := by
  simp [uliftCoyonedaEquiv, uliftYoneda]

/-- Two morphisms of presheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `uliftCoyoneda.obj X ⟶ P` agree. -/
lemma hom_ext_uliftCoyoneda {P Q : C ⥤ Type (max w v₁)} {f g : P ⟶ Q}
    (h : ∀ (X : Cᵒᵖ) (p : uliftCoyoneda.{w}.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa [uliftCoyonedaEquiv]
    using congr_arg uliftCoyonedaEquiv.{w} (h _ (uliftCoyonedaEquiv.symm x))

set_option backward.isDefEq.respectTransparency false in
/-- A variant of the curried version of the Coyoneda lemma with a raise in the universe level. -/
def uliftCoyonedaRightOpCompCoyoneda {C : Type u₁} [Category.{v₁} C] :
    uliftCoyoneda.{w}.rightOp ⋙ coyoneda ≅
      evaluation C (Type (max v₁ w)) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| uliftCoyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using uliftCoyonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (uliftCoyonedaEquiv_naturality _ _).symm)

end CoyonedaLemma

section

variable {C}
variable {D : Type*} [Category.{v₁} D] (F : C ⥤ D)

/-- The natural transformation `yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X)`
when `F : C ⥤ D` and `X : C`. -/
def yonedaMap (X : C) : yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X) where
  app _ := TypeCat.ofHom fun f ↦ F.map f

@[simp]
lemma yonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    dsimp% (yonedaMap F Y).app X f = F.map f := rfl

end

section

variable {C}
variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- The natural transformation `uliftYoneda.obj X ⟶ F.op ⋙ uliftYoneda.obj (F.obj X)`
when `F : C ⥤ D` and `X : C`. -/
def uliftYonedaMap (X : C) :
    uliftYoneda.{max w v₂}.obj X ⟶ F.op ⋙ uliftYoneda.{max w v₁}.obj (F.obj X) where
  app _ := TypeCat.ofHom fun f ↦ ULift.up (F.map (ULift.down f))

@[simp]
lemma uliftYonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    dsimp% (uliftYonedaMap.{w} F Y).app X (ULift.up f) = ULift.up (F.map f) := rfl

end

section

variable {C : Type u₁} [Category.{v₁} C]

/-- A type-level equivalence between sections of a functor and morphisms from a terminal functor
to it. We use the constant functor on a given singleton type here as a specific choice of terminal
functor. -/
@[simps apply_app]
def Functor.sectionsEquivHom (F : C ⥤ Type u₂) (X : Type u₂) [Unique X] :
    F.sections ≃ ((const _).obj X ⟶ F) where
  toFun s :=
    { app j := TypeCat.ofHom fun _ ↦ s.1 j
      naturality _ _ _ := by ext x; simp }
  invFun τ := by
    refine ⟨fun j ↦ τ.app _ (default : X), fun φ ↦ ?_⟩
    simp [-const_obj_obj, ← comp_apply, -types_comp_apply, ← NatTrans.naturality]
    rfl
  right_inv τ := by
    ext _ (x : X)
    rw [Unique.eq_default x]
    rfl

lemma Functor.sectionsEquivHom_naturality {F G : C ⥤ Type u₂} (f : F ⟶ G) (X : Type u₂)
    [Unique X] (x : F.sections) :
    (G.sectionsEquivHom X) ((sectionsFunctor C).map f x) = (F.sectionsEquivHom X) x ≫ f := by
  rfl

lemma Functor.sectionsEquivHom_naturality_symm {F G : C ⥤ Type u₂} (f : F ⟶ G)
    (X : Type u₂) [Unique X] (τ : (const C).obj X ⟶ F) :
    (G.sectionsEquivHom X).symm (τ ≫ f) =
      (sectionsFunctor C).map f ((F.sectionsEquivHom X).symm τ) := by
  rfl

/-- A natural isomorphism between the sections functor `(C ⥤ Type) ⥤ Type` and the co-Yoneda
embedding of a terminal functor, specifically a constant functor on a given singleton type `X`. -/
@[simps! +dsimpLhs]
noncomputable def sectionsFunctorNatIsoCoyoneda (X : Type (max u₁ u₂)) [Unique X] :
    Functor.sectionsFunctor.{v₁, max u₁ u₂} C ≅ coyoneda.obj (op ((Functor.const C).obj X)) :=
  NatIso.ofComponents fun F ↦ (F.sectionsEquivHom X).toIso

end

namespace Functor.FullyFaithful

variable {C : Type u₁} [Category.{v₁} C]

/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[simps! hom_app inv_app]
def homNatIso {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F.op ⋙ uliftYoneda.{v₁}.obj (F.obj X) ≅ uliftYoneda.{v₂}.obj X :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[deprecated homNatIso (since := "2025-10-28")]
def homNatIsoMaxRight {D : Type u₂} [Category.{max v₁ v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful)
    (X : C) : F.op ⋙ yoneda.obj (F.obj X) ≅ uliftYoneda.{v₂}.obj X :=
  isoWhiskerLeft F.op (uliftYonedaIsoYoneda.symm.app _) ≪≫ hF.homNatIso _ ≪≫
    NatIso.ofComponents (fun _ => Equiv.toIso (Equiv.ulift.trans Equiv.ulift.symm))

set_option backward.isDefEq.respectTransparency false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[simps! +dsimpLhs]
def compUliftYonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    F ⋙ uliftYoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F.op ≅ uliftYoneda.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso _) fun f => by
    ext; exact Equiv.ulift.injective (hF.map_injective (by simp))

@[deprecated (since := "2025-10-20")] alias compYonedaCompWhiskeringLeft :=
  compUliftYonedaCompWhiskeringLeft

/-- `FullyFaithful.homEquiv` as a natural isomorphism. -/
@[deprecated compUliftYonedaCompWhiskeringLeft (since := "2025-10-28")]
def compYonedaCompWhiskeringLeftMaxRight {D : Type u₂} [Category.{max v₁ v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) : F ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ≅ uliftYoneda.{v₂} := by
  refine isoWhiskerLeft F (isoWhiskerRight uliftYonedaIsoYoneda.{v₁}.symm _) ≪≫
    hF.compUliftYonedaCompWhiskeringLeft ≪≫
    NatIso.ofComponents (fun _ => NatIso.ofComponents
      (fun _ => Equiv.toIso (Equiv.ulift.trans Equiv.ulift.symm)))

/-- `FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! hom_app inv_app]
def homNatIso' {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F ⋙ uliftCoyoneda.{v₁}.obj (op (F.obj X)) ≅ uliftCoyoneda.{v₂}.obj (op X) :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

set_option backward.isDefEq.respectTransparency false in
/-- `FullyFaithful.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps! +dsimpLhs]
def compUliftCoyonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    F.op ⋙ uliftCoyoneda.{v₁} ⋙ (whiskeringLeft _ _ _).obj F ≅ uliftCoyoneda.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso' _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

end Functor.FullyFaithful

end CategoryTheory
