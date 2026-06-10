/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.EqToHom

/-!
# Isomorphisms of categories

An `IsoCat C D` is an isomorphism of categories: a pair of functors `C ⥤ D` and `D ⥤ C`
whose composites are *equal* (not merely naturally isomorphic) to the identity functors.
This is a strict notion, stronger than an equivalence of categories `C ≌ D`.
We also define `IsIsomorphism` as a property saying that a functor is fully faithful and
bijective on objects. We develop basic api for these two concepts.

Unless the application explicitely demands an isomorphism, the equivalence of categories is
to be preferred.

## Main definitions

* `CategoryTheory.IsoCat`: the type of isomorphisms between categories `C` and `D`.
* `CategoryTheory.Functor.IsIsomorphism`: a typeclass expressing that a functor is full,
  faithful and bijective on objects, hence underlies an isomorphism of categories.
-/

@[expose] public section

namespace CategoryTheory

open Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

/-- An isomorphism of categories: a pair of functors whose composites are equal to the
identity functors. -/
structure IsoCat where
  /-- The forward functor of an isomorphism of categories. -/
  functor : C ⥤ D
  /-- The inverse functor of an isomorphism of categories. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is equal to the identity. -/
  unit_eq : 𝟭 C = functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is equal to the identity. -/
  counit_eq : inverse ⋙ functor = 𝟭 D

/-- The identity isomorphism of categories. -/
@[simps, refl]
def IsoCat.refl : IsoCat C C where
  functor := 𝟭 C
  inverse := 𝟭 C
  unit_eq := (Functor.comp_id _).symm
  counit_eq := Functor.comp_id _

/-- The inverse isomorphism of categories, obtained by swapping `functor` and `inverse`. -/
@[simps, symm]
def IsoCat.symm (e : IsoCat C D) : IsoCat D C where
  functor := e.inverse
  inverse := e.functor
  unit_eq := e.counit_eq.symm
  counit_eq := e.unit_eq.symm

/-- Composition of isomorphisms of categories. -/
@[trans]
def IsoCat.trans {E : Type u₃} [Category.{v₃} E]
    (e : IsoCat C D) (f : IsoCat D E) : IsoCat C E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unit_eq := by
    rw [Functor.assoc, ← Functor.assoc f.functor, ← f.unit_eq, Functor.id_comp]
    exact e.unit_eq
  counit_eq := by
    rw [Functor.assoc, ← Functor.assoc e.inverse, e.counit_eq, Functor.id_comp]
    exact f.counit_eq

variable {C} {D} in
/-- A functor `F : C ⥤ D` is an isomorphism of categories if it is full, faithful and
bijective on objects. Such a functor has a strict inverse `Functor.strictInv` and assembles
into an `IsoCat` via `Functor.asIsomorphism`. -/
protected class Functor.IsIso (F : C ⥤ D) : Prop where
  /-- A functor which is an isomorphism of categories is faithful. -/
  faithful : F.Faithful := by infer_instance
  /-- A functor which is an isomorphism of categories is full. -/
  full : F.Full := by infer_instance
  /-- A functor which is an isomorphism of categories is bijective on objects. -/
  bijectiveOnObjects : F.obj.Bijective := by infer_instance

variable {C} {D} (F : C ⥤ D) [h : F.IsIsomorphism]

instance : F.Full := h.full
instance : F.Faithful := h.faithful

/-- The bijection on objects induced by a functor that is an isomorphism of categories. -/
noncomputable def Functor.objEquiv : C ≃ D := .ofBijective _ h.bijectiveOnObjects

/-- The strict inverse of a functor that is an isomorphism of categories, defined using
`Functor.objEquiv` on objects and `Functor.preimage` on morphisms. -/
noncomputable def Functor.strictInv : D ⥤ C where
  obj := F.objEquiv.invFun
  map {X Y} f :=
    F.preimage (eqToHom (F.objEquiv.apply_symm_apply X) ≫ f ≫
      eqToHom (F.objEquiv.apply_symm_apply Y).symm)
  map_id X := by simp
  map_comp {X Y Z} f g := by simp [← Functor.preimage_comp]

set_option backward.defeqAttrib.useBackward true in
/-- A functor that is an isomorphism of categories assembles into an `IsoCat`,
with `Functor.strictInv` as its inverse. -/
noncomputable def Functor.asIsomorphism : IsoCat C D where
  functor := F
  inverse := F.strictInv
  unit_eq := by
    refine Functor.ext
      (fun X => ((Equiv.ofBijective _ h.bijectiveOnObjects).symm_apply_apply X).symm) ?_
    intro X Y f
    apply F.map_injective
    simp [Functor.strictInv, eqToHom_map]
  counit_eq := by
    refine Functor.ext
      (fun X => (Equiv.ofBijective _ h.bijectiveOnObjects).apply_symm_apply X) ?_
    intro X Y f
    simp [Functor.strictInv]

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence of categories underlying an `IsoCat`, with the unit and counit
isomorphisms induced by the defining equalities. -/
def IsoCat.toEquivalence (e : IsoCat C D) : C ≌ D where
  functor := e.functor
  inverse := e.inverse
  unitIso := eqToIso e.unit_eq
  counitIso := eqToIso e.counit_eq
  functor_unitIso_comp X := by simp [eqToHom_map]

/-- Promotes an equivalence of categories `e : C ≌ D` whose unit and counit isomorphisms are
given by equalities of objects into an `IsoCat C D`. -/
@[simps]
def Equivalence.toIsoCat (e : C ≌ D)
    (h : ∀ (X : C), e.inverse.obj (e.functor.obj X) = X)
    (h' : ∀ (Y : D), e.functor.obj (e.inverse.obj Y) = Y)
    (k : ∀ (X : C), e.unitIso.hom.app X = eqToHom (h X).symm := by cat_disch)
    (k' : ∀ (Y : D), e.counitIso.hom.app Y = eqToHom (h' Y) := by cat_disch) : IsoCat C D where
  functor := e.functor
  inverse := e.inverse
  unit_eq := Functor.ext_of_iso e.unitIso (by simp [h])
  counit_eq := Functor.ext_of_iso e.counitIso (by simp [h'])

instance IsoCat.isIsomorphismFunctor (e : IsoCat C D) : e.functor.IsIsomorphism where
  faithful := e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijectiveOnObjects := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unit_eq X).symm,
      Functor.congr_obj e.counit_eq⟩

end CategoryTheory
