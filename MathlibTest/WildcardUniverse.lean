import Mathlib.Tactic.WildcardUniverse
import Mathlib.Tactic.TypeStar
import Mathlib.CategoryTheory.Functor.Basic

set_option linter.style.setOption false
set_option linter.style.commandStart false
set_option pp.universes true

section ULiftTests

/-- info: ULift.{u_1, u_2} : Type u_2 → Type (max u_2 u_1) -/
#guard_msgs in #check (ULift.!{*, *} : Type _ → Type _)

variable (X : Type*) (z : ULift.!{_} X)
def testInferred := z
/-- info: testInferred.{u_1, u_2} (X : Type u_1) (z : ULift.{u_2, u_1} X) : ULift.{u_2, u_1} X -/
#guard_msgs in #check testInferred

variable (y : ULift.!{*} X)
def testStarFirst := y
/-- info: testStarFirst.{u_2, u_1} (X : Type u_1) (y : ULift.{u_2, u_1} X) : ULift.{u_2, u_1} X -/
#guard_msgs in #check testStarFirst

universe v
variable (e : ULift.!{v, _} X)
def testExplicit := e
/-- info: testExplicit.{v, u_1} (X : Type u_1) (e : ULift.{v, u_1} X) : ULift.{v, u_1} X -/
#guard_msgs in #check testExplicit

/-- info: ULift.{u_3, u_4} : Type u_4 → Type (max u_4 u_3) -/
#guard_msgs in #check ULift.!{*, *}

end ULiftTests

section CategoryTests

open CategoryTheory

variable (C : Type*) [Category.!{*} C]

universe u
variable (D : Type u) [Category.!{*} D]

variable (E : Type 3) [Category.!{*} E]

def fooC := C ⥤ C
def fooD := D ⥤ D
def fooE := E ⥤ E

/-- info: fooC.{u_2, u_1} (C : Type u_1) [Category.{u_2, u_1} C] : Type (max u_2 u_1) -/
#guard_msgs in #check fooC

/-- info: fooD.{u_3, u} (D : Type u) [Category.{u_3, u} D] : Type (max u_3 u) -/
#guard_msgs in #check fooD

/-- info: fooE.{u_4} (E : Type 3) [Category.{u_4, 3} E] : Type (max u_4 3) -/
#guard_msgs in #check fooE

end CategoryTests

section CategoryProductTest

open CategoryTheory

variable (C D : Type*) [Category.!{*} (C × D)]

def fooProd := (C × D) ⥤ (C × D)

/--
info: fooProd.{u_3, u_1, u_2} (C : Type u_1) (D : Type u_2) [Category.{u_3, max u_2 u_1} (Prod.{u_1, u_2} C D)] :
  Type (max u_3 u_2 u_1)
-/
#guard_msgs in #check fooProd

end CategoryProductTest

section CategoryExplicitUniverseTest

open CategoryTheory

universe w

abbrev TypeWithParam := {n : Nat // ∃ X : Type w, Nonempty (Fin n ≃ X)}

variable [Category.!{*} TypeWithParam.{w}]

def ff := TypeWithParam.{w} ⥤ TypeWithParam.{w}

/-- info: ff.{u_1, w} [Category.{u_1, 0} TypeWithParam.{w}] : Type u_1 -/
#guard_msgs in #check ff

end CategoryExplicitUniverseTest
