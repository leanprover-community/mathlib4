/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# Yoneda embedding of `CommGrp C`
-/

assert_not_exists Field

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

universe w v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C] {X : C}

variable (X) in
/-- Abbreviation for an unbundled commutative group object. It is a group object that is a
commutative monoid object. -/
class abbrev CommGrpObj := GrpObj X, IsCommMonObj X

@[deprecated (since := "2025-09-13")] alias CommGrp_Class := CommGrpObj

section CommGrp

variable (X) in
/-- If `X` represents a presheaf of commutative groups, then `X` is a commutative group object. -/
def CommGrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ CommGrpCat.{w})
    (α : (F ⋙ forget _).RepresentableBy X) : CommGrpObj X where
  __ := GrpObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat GrpCat) α
  __ := IsCommMonObj.ofRepresentableBy X (F ⋙ forget₂ CommGrpCat CommMonCat) α

@[deprecated (since := "2025-09-13")]
alias CommGrp_Class.ofRepresentableBy := CommGrpObj.ofRepresentableBy

end CommGrp
