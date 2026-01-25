/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Free groupoid on a category

This file defines the free groupoid on a category, the lifting of a functor to its unique
extension as a functor from the free groupoid, and proves uniqueness of this extension.

## Main results

Given a type `C` and a category instance on `C`:

- `CategoryTheory.FreeGroupoid C`: the underlying type of the free groupoid on `C`.
- `CategoryTheory.FreeGroupoid.instGroupoid`: the `Groupoid` instance on `FreeGroupoid C`.
- `CategoryTheory.FreeGroupoid.lift`: the lifting of a functor `C ⥤ G` where `G` is a
  groupoid, to a functor `CategoryTheory.FreeGroupoid C ⥤ G`.
- `CategoryTheory.FreeGroupoid.lift_spec` and
  `CategoryTheory.FreeGroupoid.lift_unique`:
  the proofs that, respectively, `CategoryTheory.FreeGroupoid.lift` indeed is a lifting
  and is the unique one.
- `CategoryTheory.Grpd.free`: the free functor from `Grpd` to `Cat`
- `CategoryTheory.Grpd.freeForgetAdjunction`: that `free` is left adjoint to
  `Grpd.forgetToCat`.

## Implementation notes

The free groupoid on a category `C` is first defined by taking the free groupoid `G`
on the underlying *quiver* of `C`. Then the free groupoid on the *category* `C` is defined as
the quotient of `G` by the relation that makes the inclusion prefunctor `C ⥤q G` a functor.

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

universe v u v₁ u₁ v₂ u₂

variable (C : Type u) [Category.{v} C]

open Quiver in
/-- The relation on the free groupoid on the underlying *quiver* of C that
promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
inductive FreeGroupoid.homRel : HomRel (Quiver.FreeGroupoid C) where
| map_id (X : C) : homRel ((FreeGroupoid.of C).map (𝟙 X)) (𝟙 ((FreeGroupoid.of C).obj X))
| map_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : homRel ((FreeGroupoid.of C).map (f ≫ g))
  ((FreeGroupoid.of C).map f ≫ (FreeGroupoid.of C).map g)

/-- The underlying type of the free groupoid on a category,
defined by quotienting the free groupoid on the underlying quiver of `C`
by the relation that promotes the prefunctor `C ⥤q FreeGroupoid C` into a functor
`C ⥤ Quotient (FreeGroupoid.homRel C)`. -/
def FreeGroupoid := Quotient (FreeGroupoid.homRel C)

instance [Nonempty C] : Nonempty (FreeGroupoid C) :=
  ⟨Quotient.mk (Quotient.mk ((Paths.of _).obj (Classical.arbitrary C)))⟩

instance : Groupoid (FreeGroupoid C) :=
  Quotient.groupoid (FreeGroupoid.homRel C)

namespace FreeGroupoid

/-- The localization functor from the category `C` to the groupoid `FreeGroupoid C` -/
def of : C ⥤ FreeGroupoid C where
  __ := Quiver.FreeGroupoid.of C ⋙q (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor
  map_id X := Quotient.sound _ (FreeGroupoid.homRel.map_id X)
  map_comp f g := Quotient.sound _ (FreeGroupoid.homRel.map_comp f g)

variable {C}

/-- Construct an object in the free groupoid on `C` by providing an object in `C`. -/
abbrev mk (X : C) : FreeGroupoid C := (of C).obj X

/-- Construct a morphism in the free groupoid on `C` by providing a morphism in `C`. -/
abbrev homMk {X Y : C} (f : X ⟶ Y) : mk X ⟶ mk Y := (of C).map f

lemma eq_mk (X : FreeGroupoid C) : X = .mk (X.as.as) := rfl

lemma of_obj_bijective : Function.Bijective (of C).obj where
  left _ _ h := by cases h; rfl
  right X := ⟨X.as.as, rfl⟩

section UniversalProperty

variable {G : Type u₁} [Groupoid.{v₁} G]

/-- The lift of a functor from `C` to a groupoid to a functor from
`FreeGroupoid C` to the groupoid -/
def lift (φ : C ⥤ G) : FreeGroupoid C ⥤ G :=
  Quotient.lift (FreeGroupoid.homRel C) (Quiver.FreeGroupoid.lift φ.toPrefunctor)
    (fun _ _ f g r ↦ by
      have {X Y : C} (f : X ⟶ Y) :=
        Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec φ.toPrefunctor) f
      induction r <;> cat_disch)

theorem lift_spec (φ : C ⥤ G) : of C ⋙ lift φ = φ :=
  Functor.toPrefunctor_injective (by
    change Quiver.FreeGroupoid.of C ⋙q
      (Quotient.functor (FreeGroupoid.homRel C)).toPrefunctor ⋙q
        (lift φ).toPrefunctor = φ.toPrefunctor
    simp [lift, Quotient.lift_spec, Quiver.FreeGroupoid.lift_spec])

@[simp]
lemma lift_obj_mk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) (X : C) :
    (lift φ).obj (mk X) = φ.obj X := rfl

@[simp]
lemma lift_map_homMk {E : Type u₂} [Groupoid.{v₂} E] (φ : C ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (lift φ).map (homMk f) = φ.map f := by
  simpa using Functor.congr_hom (lift_spec φ) f

theorem lift_unique (φ : C ⥤ G) (Φ : FreeGroupoid C ⥤ G) (hΦ : of C ⋙ Φ = φ) :
    Φ = lift φ := by
  apply Quotient.lift_unique
  apply Quiver.FreeGroupoid.lift_unique
  exact congr_arg Functor.toPrefunctor hΦ

theorem lift_id_comp_of : lift (𝟭 G) ⋙ of G = 𝟭 _ := by
  rw [lift_unique (of G) (lift (𝟭 G) ⋙ of G) (by rw [← Functor.assoc, lift_spec, Functor.id_comp])]
  symm; apply lift_unique
  rw [Functor.comp_id]

theorem lift_comp {H : Type u₂} [Groupoid.{v₂} H] (φ : C ⥤ G) (ψ : G ⥤ H) :
    lift (φ ⋙ ψ) = lift φ ⋙ ψ := by
  symm
  apply lift_unique
  rw [← Functor.assoc, lift_spec]

/-- The universal property of the free groupoid. -/
def strictUniversalPropertyFixedTarget :
    Localization.StrictUniversalPropertyFixedTarget (of C) ⊤ G where
  inverts _ := inferInstance
  lift F _ := lift F
  fac _ _ := lift_spec ..
  uniq F G h := by rw [lift_unique (of C ⋙ G) F h, ← lift_unique (of C ⋙ G) G rfl]

attribute [local instance] Localization.groupoid

instance : (of C).IsLocalization ⊤ :=
  .mk' _ _ strictUniversalPropertyFixedTarget strictUniversalPropertyFixedTarget

/-- In order to define a natural isomorphism `F ≅ G` with `F G : FreeGroupoid ⥤ D`,
it suffices to do so after precomposing with `FreeGroupoid.of C`. -/
def liftNatIso (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) : F₁ ≅ F₂ :=
  Localization.liftNatIso (of C) ⊤ (of C ⋙ F₁) (of C ⋙ F₂) _ _ τ

@[simp]
lemma liftNatIso_hom_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) :
    (liftNatIso F₁ F₂ τ).hom.app (mk X) = τ.hom.app X := by
  simp [liftNatIso]

@[simp]
lemma liftNatIso_inv_app (F₁ F₂ : FreeGroupoid C ⥤ G) (τ : of C ⋙ F₁ ≅ of C ⋙ F₂) (X) :
    (liftNatIso F₁ F₂ τ).inv.app (mk X) = τ.inv.app X := by
  simp [liftNatIso]

end UniversalProperty

section Functoriality

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- The functor between free groupoids induced by a functor between categories. -/
def map (φ : C ⥤ D) : FreeGroupoid C ⥤ FreeGroupoid D :=
  lift (φ ⋙ of D)

lemma of_comp_map (F : C ⥤ D) : of C ⋙ map F = F ⋙ of D := rfl

/-- The operation `of` is natural. -/
def ofCompMapIso (F : C ⥤ D) : of C ⋙ map F ≅ F ⋙ of D := Iso.refl _

variable (C) in
/-- The functor induced by the identity is the identity. -/
def mapId : map (𝟭 C) ≅ 𝟭 (FreeGroupoid C) :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
lemma mapId_hom_app (X) : (mapId C).hom.app X = 𝟙 X :=
  liftNatIso_hom_app ..

@[simp]
lemma mapId_inv_app (X) : (mapId C).inv.app X = 𝟙 X :=
  liftNatIso_inv_app ..

variable (C) in
theorem map_id : map (𝟭 C) = 𝟭 (FreeGroupoid C) := by
  symm; apply lift_unique; rfl

/-- The functor induced by a composition is the composition of the functors they induce. -/
def mapComp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') ≅ map φ ⋙ map φ' :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
lemma mapComp_hom_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').hom.app X = 𝟙 _ :=
  liftNatIso_hom_app ..

@[simp]
lemma mapComp_inv_app (φ : C ⥤ D) (φ' : D ⥤ E) (X) : (mapComp φ φ').inv.app X = 𝟙 _ :=
  liftNatIso_inv_app ..

theorem map_comp (φ : C ⥤ D) (φ' : D ⥤ E) : map (φ ⋙ φ') = map φ ⋙ map φ' := by
  symm; apply lift_unique; rfl

@[simp]
lemma map_obj_mk (φ : C ⥤ D) (X : C) : (map φ).obj (mk X) = mk (φ.obj X) := rfl

@[simp]
lemma map_map_homMk (φ : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (map φ).map (homMk f) = homMk (φ.map f) := rfl

variable {E : Type u₂} [Groupoid.{v₂} E]

lemma map_comp_lift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G = lift (F ⋙ G) := by
  apply lift_unique
  rw [← Functor.assoc, of_comp_map, Functor.assoc, lift_spec G]

/-- The operation `lift` is natural. -/
def mapCompLift (F : C ⥤ D) (G : D ⥤ E) : map F ⋙ lift G ≅ lift (F ⋙ G) :=
  liftNatIso _ _ (Iso.refl _)

@[simp]
lemma mapCompLift_hom_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).hom.app X = 𝟙 _ :=
  liftNatIso_hom_app ..

@[simp]
lemma mapCompLift_inv_app (F : C ⥤ D) (G : D ⥤ E) (X) : (mapCompLift F G).inv.app X = 𝟙 _ :=
  liftNatIso_inv_app ..

end Functoriality

/-- Functors out of the free groupoid biject with functors out of the original category. -/
@[simps]
def functorEquiv {D : Type*} [Groupoid D] : (FreeGroupoid C ⥤ D) ≃ (C ⥤ D) where
  toFun G := of C ⋙ G
  invFun F := lift F
  right_inv := lift_spec
  left_inv _ := (lift_unique _ _ rfl).symm

end FreeGroupoid

namespace Grpd

open FreeGroupoid

/-- The free groupoid construction on a category as a functor. -/
def free : Cat.{u, u} ⥤ Grpd.{u, u} where
  obj C := Grpd.of <| FreeGroupoid C
  map {C D} F := map F.toFunctor
  map_id C := by simp [map_id, id_eq_id]
  map_comp F G := by simp [Grpd.comp_eq_comp, map_comp]

@[simp]
lemma free_obj (C : Cat.{u, u}) : free.obj C = FreeGroupoid C :=
  rfl

@[simp]
lemma free_map {C D : Cat.{u, u}} (F : C ⟶ D) : free.map F = map F.toFunctor :=
  rfl

/-- The free-forgetful adjunction between `Grpd` and `Cat`. -/
def freeForgetAdjunction : free ⊣ Grpd.forgetToCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := FreeGroupoid.functorEquiv.trans (Functor.equivCatHom _ _)
      homEquiv_naturality_left_symm _ _ := (FreeGroupoid.map_comp_lift _ _).symm
      homEquiv_naturality_right _ _ := rfl }

variable {C : Type u} [Category.{u} C] {D : Type u} [Groupoid.{u} D]

@[simp]
lemma freeForgetAdjunction_homEquiv_apply (F : FreeGroupoid C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D) F).toFunctor = FreeGroupoid.of C ⋙ F :=
  rfl

@[simp]
lemma freeForgetAdjunction_homEquiv_symm_apply (F : C ⥤ D) :
    (freeForgetAdjunction.homEquiv (Cat.of C) (Grpd.of D)).symm F.toCatHom = map F ⋙ lift (𝟭 D) :=
  rfl

@[simp]
lemma freeForgetAdjunction_unit_app :
    (freeForgetAdjunction.unit.app (Cat.of C)).toFunctor = FreeGroupoid.of C :=
  rfl

@[simp]
lemma freeForgetAdjunction_counit_app :
    freeForgetAdjunction.counit.app (Grpd.of D) = lift (𝟭 D) :=
  rfl

instance : Reflective Grpd.forgetToCat where
  L := free
  adj := freeForgetAdjunction

end Grpd
end CategoryTheory
end
