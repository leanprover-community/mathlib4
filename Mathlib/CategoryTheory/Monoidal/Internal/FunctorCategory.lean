/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# `Mon (C ⥤ D) ≌ C ⥤ Mon D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `monFunctorCategoryEquivalence : Mon (C ⥤ D) ≌ C ⥤ Mon D`

The intended application is that as `Ring ≌ Mon Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon Ab) X ≌ Mon (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj ComonObj

namespace CategoryTheory.Monoidal

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory.{v₂} D]

namespace MonFunctorCategoryEquivalence

variable {C D}

/-- A monoid object in a functor category sends any object to a monoid object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [MonObj A] (X : C) : Mon D where
  X := A.obj X
  mon :=
  { one := η[A].app X
    mul := μ[A].app X
    one_mul := congr_app (one_mul A) X
    mul_one := congr_app (mul_one A) X
    mul_assoc := congr_app (mul_assoc A) X }

/-- A monoid object in a functor category induces a functor to the category of monoid objects. -/
@[simps]
def functorObj (A : C ⥤ D) [MonObj A] : C ⥤ Mon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isMonHom_hom :=
        { one_hom := by dsimp; rw [← η[A].naturality, tensorUnit_map]; dsimp; rw [Category.id_comp]
          mul_hom := by dsimp; rw [← μ[A].naturality, tensorObj_map] } }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

/-- Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simps]
def functor : Mon (C ⥤ D) ⥤ C ⥤ Mon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isMonHom_hom :=
        { one_hom := congr_app (IsMonHom.one_hom f.hom) X
          mul_hom := congr_app (IsMonHom.mul_hom f.hom) X } } }

/-- A functor to the category of monoid objects can be translated as a monoid object
in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ Mon D) : Mon (C ⥤ D) where
  X := F ⋙ Mon.forget D
  mon :=
  { one := { app X := η[(F.obj X).X] }
    mul := { app X := μ[(F.obj X).X] } }

/-- Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simps]
def inverse : (C ⥤ Mon D) ⥤ Mon (C ⥤ D) where
  obj := inverseObj
  map α := .mk'
    { app := fun X => (α.app X).hom
      naturality := fun _ _ f => congr_arg Mon.Hom.hom (α.naturality f) }

/-- The unit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
def unitIso : 𝟭 (Mon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
  { hom := .mk' { app := fun _ => 𝟙 _ }
    inv := .mk' { app := fun _ => 𝟙 _ } })

/-- The counit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Mon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }))

end MonFunctorCategoryEquivalence

open MonFunctorCategoryEquivalence

/-- When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simps]
def monFunctorCategoryEquivalence : Mon (C ⥤ D) ≌ C ⥤ Mon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

namespace ComonFunctorCategoryEquivalence

variable {C D}

/-- A comonoid object in a functor category sends any object to a comonoid object. -/
@[simps]
def functorObjObj (A : C ⥤ D) [ComonObj A] (X : C) : Comon D where
  X := A.obj X
  comon :=
  { counit := ε[A].app X
    comul := Δ[A].app X
    counit_comul := congr_app (counit_comul A) X
    comul_counit := congr_app (comul_counit A) X
    comul_assoc := congr_app (comul_assoc A) X }

/--
A comonoid object in a functor category induces a functor to the category of comonoid objects.
-/
@[simps]
def functorObj (A : (C ⥤ D)) [ComonObj A] : C ⥤ Comon D where
  obj := functorObjObj A
  map f :=
    { hom := A.map f
      isComonHom_hom.hom_counit := by
        dsimp; rw [ε[A].naturality, tensorUnit_map]; dsimp; rw [Category.comp_id]
      isComonHom_hom.hom_comul := by dsimp; rw [Δ[A].naturality, tensorObj_map] }
  map_id X := by ext; dsimp; rw [CategoryTheory.Functor.map_id]
  map_comp f g := by ext; dsimp; rw [Functor.map_comp]

/-- Functor translating a comonoid object in a functor category
to a functor into the category of comonoid objects.
-/
@[simps]
def functor : Comon (C ⥤ D) ⥤ C ⥤ Comon D where
  obj A := functorObj A.X
  map f :=
  { app := fun X =>
    { hom := f.hom.app X
      isComonHom_hom.hom_counit := congr_app (IsComonHom.hom_counit f.hom) X
      isComonHom_hom.hom_comul := congr_app (IsComonHom.hom_comul f.hom) X } }

/-- A functor to the category of comonoid objects can be translated as a comonoid object
in the functor category. -/
@[simps]
def inverseObj (F : C ⥤ Comon D) : Comon (C ⥤ D) where
  X := F ⋙ Comon.forget D
  comon :=
  { counit := { app X := ε[(F.obj X).X] }
    comul := { app X := Δ[(F.obj X).X] } }

/-- Functor translating a functor into the category of comonoid objects
to a comonoid object in the functor category
-/
@[simps]
private def inverse : (C ⥤ Comon D) ⥤ Comon (C ⥤ D) where
  obj := inverseObj
  map α :=
    { hom :=
      { app := fun X => (α.app X).hom
        naturality := fun _ _ f => congr_arg Comon.Hom.hom (α.naturality f) }
      isComonHom_hom.hom_counit := by ext x; dsimp; rw [IsComonHom.hom_counit (α.app x).hom]
      isComonHom_hom.hom_comul := by ext x; dsimp; rw [IsComonHom.hom_comul (α.app x).hom] }

/-- The unit for the equivalence `Comon (C ⥤ D) ≌ C ⥤ Comon D`.
-/
@[simps!]
private def unitIso : 𝟭 (Comon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
    { hom := .mk' { app := fun _ => 𝟙 _ }
      inv := .mk' { app := fun _ => 𝟙 _ } })

/-- The counit for the equivalence `Mon (C ⥤ D) ≌ C ⥤ Mon D`.
-/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ Comon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }) )

end ComonFunctorCategoryEquivalence

open ComonFunctorCategoryEquivalence

/-- When `D` is a monoidal category,
comonoid objects in `C ⥤ D` are the same thing
as functors from `C` into the comonoid objects of `D`.
-/
@[simps]
def comonFunctorCategoryEquivalence : Comon (C ⥤ D) ≌ C ⥤ Comon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

variable [BraidedCategory.{v₂} D]

namespace CommMonFunctorCategoryEquivalence

variable {C D}

/-- Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simps!]
def functor : CommMon (C ⥤ D) ⥤ C ⥤ CommMon D where
  obj A :=
<<<<<<< HEAD
    { obj X :=
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon_).obj X with
          comm := { mul_comm := congr_app (IsCommMon.mul_comm A.X) X } }
      map f :=
        CommMon_.homMk (((monFunctorCategoryEquivalence C D).functor.obj A.toMon_).map f) }
  map f :=
    { app X :=
        CommMon_.homMk (((monFunctorCategoryEquivalence C D).functor.map f.hom).app X) }
=======
    { (monFunctorCategoryEquivalence C D).functor.obj A.toMon with
      obj := fun X =>
        { ((monFunctorCategoryEquivalence C D).functor.obj A.toMon).obj X with
          comm := { mul_comm := congr_app (IsCommMonObj.mul_comm A.X) X } } }
  map f := { app := fun X => ((monFunctorCategoryEquivalence C D).functor.map f).app X }
>>>>>>> origin/master

/-- Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
@[simps!]
def inverse : (C ⥤ CommMon D) ⥤ CommMon (C ⥤ D) where
  obj F :=
<<<<<<< HEAD
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon_.forget₂Mon_ D) with
      comm := { mul_comm := by ext X; exact IsCommMon.mul_comm (F.obj X).X } }
  map α :=
    CommMon_.homMk ((monFunctorCategoryEquivalence C D).inverse.map (Functor.whiskerRight α _))
=======
    { (monFunctorCategoryEquivalence C D).inverse.obj (F ⋙ CommMon.forget₂Mon D) with
      comm := { mul_comm := by ext X; exact IsCommMonObj.mul_comm (F.obj X).X } }
  map α := (monFunctorCategoryEquivalence C D).inverse.map (Functor.whiskerRight α _)
>>>>>>> origin/master

/-- The unit for the equivalence `CommMon (C ⥤ D) ≌ C ⥤ CommMon D`.
-/
@[simps!]
<<<<<<< HEAD
def unitIso : 𝟭 (CommMon_ (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A => CommMon_.mkIso (Iso.refl _))
=======
def unitIso : 𝟭 (CommMon (C ⥤ D)) ≅ functor ⋙ inverse :=
  NatIso.ofComponents (fun A =>
    { hom := .mk' { app := fun _ => 𝟙 _ }
      inv := .mk' { app := fun _ => 𝟙 _ } })
>>>>>>> origin/master

/-- The counit for the equivalence `CommMon (C ⥤ D) ≌ C ⥤ CommMon D`.
-/
@[simps!]
<<<<<<< HEAD
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon_ D) :=
  NatIso.ofComponents (fun A ↦ NatIso.ofComponents (fun X ↦ Iso.refl _))
=======
def counitIso : inverse ⋙ functor ≅ 𝟭 (C ⥤ CommMon D) :=
  NatIso.ofComponents (fun A =>
    NatIso.ofComponents (fun X => { hom := { hom := 𝟙 _ }, inv := { hom := 𝟙 _ } }) )
>>>>>>> origin/master

end CommMonFunctorCategoryEquivalence

open CommMonFunctorCategoryEquivalence

/-- When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simps]
def commMonFunctorCategoryEquivalence : CommMon (C ⥤ D) ≌ C ⥤ CommMon D where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

end CategoryTheory.Monoidal
