/-
Copyright (c) 2026 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Isomorphisms of categories

An `IsoCat C D` is an isomorphism of categories: a pair of functors `C ⥤ D` and `D ⥤ C`
whose composites are *equal* (not merely naturally isomorphic) to the identity functors.
This is a strict notion, stronger than an equivalence of categories `C ≌ D`.
We also define `Functor.IsIso` as a property saying that a functor is fully faithful and
bijective on objects. We develop basic api for these two concepts.

Unless the application explicitely demands an isomorphism, the equivalence of categories is
to be preferred.

## Main definitions

* `CategoryTheory.IsoCat`: the type of isomorphisms between categories `C` and `D`.
* `CategoryTheory.Functor.IsIso`: a typeclass expressing that a functor is full,
  faithful and bijective on objects, hence underlies an isomorphism of categories.
-/

@[expose] public section

namespace CategoryTheory

open Functor NatIso Category

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
variable (F : C ⥤ D) (G : D ⥤ E)

variable (C) (D) in
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

variable (C) in
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
@[simps, trans]
def IsoCat.trans (e : IsoCat C D) (f : IsoCat D E) : IsoCat C E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unit_eq := by
    rw [Functor.assoc, ← Functor.assoc f.functor, ← f.unit_eq, Functor.id_comp]
    exact e.unit_eq
  counit_eq := by
    rw [Functor.assoc, ← Functor.assoc e.inverse, e.counit_eq, Functor.id_comp]
    exact f.counit_eq

namespace Functor

/-- A functor `F : C ⥤ D` is an isomorphism of categories if it is full, faithful and
bijective on objects. Such a functor has a strict inverse `Functor.strictInv` and assembles
into an `IsoCat` via `Functor.asIsomorphism`. -/
protected class IsIso (F : C ⥤ D) : Prop where
  /-- A functor which is an isomorphism of categories is faithful. -/
  faithful : F.Faithful := by infer_instance
  /-- A functor which is an isomorphism of categories is full. -/
  full : F.Full := by infer_instance
  /-- A functor which is an isomorphism of categories is bijective on objects. -/
  bijective_obj (F) : F.obj.Bijective

export Functor.IsIso (bijective_obj)

attribute [instance] Functor.IsIso.faithful Functor.IsIso.full

instance : (𝟭 C).IsIso where
  bijective_obj := Function.bijective_id

variable [F.IsIso] [G.IsIso]

/-- The bijection on objects induced by a functor that is an isomorphism of categories. -/
noncomputable def objEquiv : C ≃ D := .ofBijective _ (F.bijective_obj)

@[simp]
lemma objEquiv_symm_apply_apply (X : C) :
    F.objEquiv.symm (F.obj X) = X :=
  F.objEquiv.symm_apply_apply X

@[simp]
lemma objEquiv_apply_symm_apply (Y : D) :
    F.obj (F.objEquiv.symm Y) = Y :=
  F.objEquiv.apply_symm_apply Y

instance : F.IsEquivalence where
  essSurj := ⟨fun Y ↦ ⟨F.objEquiv.symm Y, ⟨eqToIso (by simp)⟩⟩⟩

/-- The strict inverse of a functor that is an isomorphism of categories, defined using
`Functor.objEquiv` on objects and `Functor.preimage` on morphisms. -/
@[no_expose]
noncomputable def strictInv : D ⥤ C where
  obj := F.objEquiv.symm
  map f := F.preimage (eqToHom (by simp) ≫ f ≫ eqToHom (by simp))
  map_comp _ _ := by simp [← preimage_comp]

set_option backward.defeqAttrib.useBackward true in
/-- A functor that is an isomorphism of categories assembles into an `IsoCat`,
with `Functor.strictInv` as its inverse. -/
noncomputable def asIsomorphism : IsoCat C D where
  functor := F
  inverse := F.strictInv
  unit_eq :=
    ext (fun x ↦ by simp [strictInv])
      (fun _ _ _ ↦ F.map_injective (by simp [eqToHom_map, strictInv]))
  counit_eq :=
    ext (fun x ↦ by simp [strictInv])
      (fun _ _ _ ↦ by simp [strictInv])

end Functor

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

instance IsoCat.isIso_functor (e : IsoCat C D) : e.functor.IsIso where
  faithful := e.toEquivalence.faithful_functor
  full := e.toEquivalence.full_functor
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨e.inverse.obj, fun X => (Functor.congr_obj e.unit_eq X).symm,
      Functor.congr_obj e.counit_eq⟩

instance (e : IsoCat C D) : e.inverse.IsIso := e.symm.isIso_functor

instance [F.IsIso] : F.strictInv.IsIso := F.asIsomorphism.symm.isIso_functor

instance [F.IsIso] [G.IsIso] : (F ⋙ G).IsIso :=
  (F.asIsomorphism.trans G.asIsomorphism).isIso_functor

end CategoryTheory
