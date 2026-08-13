/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.Basic
public import Mathlib.NumberTheory.CFT.ClassFormation.Sheaves
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Statement of the existence of the class formation for a local field

-/

universe u

@[expose] public section

open CategoryTheory Opposite

/-- The category of finite étale algebras over a commutative ring `R`. -/
abbrev EtaleAlgCat (R : Type u) [CommRing R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun (X : Under (CommRingCat.of R)) ↦
      RingHom.Etale X.hom.hom ∧ RingHom.Finite X.hom.hom)

variable (K : Type u) [Field K]

/-
namespace EtaleAlgCat

instance : GaloisCategory (EtaleAlgCat K)ᵒᵖ := by
  -- this has probably been proven by Christian Merten
  -- with a greater generality
  sorry

@[implicit_reducible]
def fieldFormationUnits : FieldFormation (EtaleAlgCat K)ᵒᵖ where
  sheaf.obj.obj X := .of (Additive (Units X.unop.obj.unop.obj.right))
  sheaf.obj.map f :=
    AddCommGrpCat.ofHom (Units.map (f.unop.hom.unop.hom.right.hom.toMonoidHom)).toAdditive
  sheaf.property := sorry
  isZero_H_one := sorry

end EtaleAlgCat

@[implicit_reducible]
def IsNonarchimedeanLocalField.classFormation
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ClassFormation (EtaleAlgCat K)ᵒᵖ where
  toFieldFormation := EtaleAlgCat.fieldFormationUnits K
  u := sorry
  addOrderOf_u := sorry
  zmultiples_u := sorry
  inflation_u := sorry
  restriction_u := sorry

-/
