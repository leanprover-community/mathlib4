/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
public import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-!
# Yoneda embedding of `CommGrp C`
-/

@[expose] public section

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] {X : C}

variable (X) in
/-- Abbreviation for an unbundled commutative group object. It is a group object that is a
commutative monoid object. -/
class abbrev CommGrpObj := GrpObj X, IsCommMonObj X

@[deprecated (since := "2025-09-13")] alias CommGrp_Class := CommGrpObj

variable (X) in
/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
def CommGrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ CommGrpCat.{w})
    (α : (F ⋙ forget _).RepresentableBy X) : CommGrpObj X where
  __ := GrpObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat GrpCat) α
  __ := IsCommMonObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat CommMonCat) α

@[deprecated (since := "2025-09-13")]
alias CommGrp_Class.ofRepresentableBy := CommGrpObj.ofRepresentableBy

/-- The yoneda embedding of `CommGrp C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrpObj (G : CommGrp C) : (Grp C)ᵒᵖ ⥤ CommGrpCat where
  obj H := .of (unop H ⟶ G.toGrp)
  map {H I} f := CommGrpCat.ofHom {
    toFun := (f.unop ≫ ·)
    map_one' := by ext; simp [Mon.Hom.hom_one]
    map_mul' g h := by ext; simpa using ((yonedaGrpObj G.X).map f.unop.1.op).hom.map_mul g.hom h.hom
  }

/-- The yoneda embedding of `CommGrp C` into presheaves of groups. -/
@[simps]
def yonedaCommGrpGrp : CommGrp C ⥤ (Grp C)ᵒᵖ ⥤ CommGrpCat where
  obj := yonedaCommGrpGrpObj
  map {X₁ X₂} ψ := {
    app Y := CommGrpCat.ofHom {
      toFun := (· ≫ ψ)
      map_one' := by ext; simp
      map_mul' f g := by
        ext; simpa using ((yonedaGrp.map ψ).app (op (unop Y).X)).hom.map_mul f.hom g.hom
    }
  }

end CategoryTheory
