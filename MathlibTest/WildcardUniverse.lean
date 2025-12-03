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

section NamedWildcardTests

open CategoryTheory

variable (C : Type*) [Category.!{w*} C]

def fooNamed := C ⥤ C

/-- info: fooNamed.{w_1, u_1} (C : Type u_1) [Category.{w_1, u_1} C] : Type (max w_1 u_1) -/
#guard_msgs in #check fooNamed

variable (x : ULift.!{z*, _} C)

def testNamedULift := x

/-- info: testNamedULift.{z_1, u_1} (C : Type u_1) (x : ULift.{z_1, u_1} C) : ULift.{z_1, u_1} C -/
#guard_msgs in #check testNamedULift

end NamedWildcardTests

section NamedWildcardWithUsage

open CategoryTheory

variable (C : Type*) [Category.!{v*} C]

def fooNamedV := C ⥤ C

/-- info: fooNamedV.{v_1, u_1} (C : Type u_1) [Category.{v_1, u_1} C] : Type (max v_1 u_1) -/
#guard_msgs in #check fooNamedV

variable (D : Type*) [Category.!{mor*} D]

def fooBothNamed := C ⥤ D

/--
info: fooBothNamed.{v_1, u_1, mor_1, u_2} (C : Type u_1) [Category.{v_1, u_1} C] (D : Type u_2) [Category.{mor_1, u_2} D] :
  Type (max v_1 mor_1 u_1 u_2)
-/
#guard_msgs in #check fooBothNamed

end NamedWildcardWithUsage

section MixedWildcardTests

open CategoryTheory

variable (A : Type*) [Category.!{*} A]
variable (B : Type*) [Category.!{w*} B]

def fooMixed := A ⥤ B

/--
info: fooMixed.{u_2, u_1, w_1, u_3} (A : Type u_1) [Category.{u_2, u_1} A] (B : Type u_3) [Category.{w_1, u_3} B] :
  Type (max u_2 w_1 u_1 u_3)
-/
#guard_msgs in #check fooMixed

end MixedWildcardTests

section MultipleUniverseArgsTests

/-- info: ULift.{a_1, u_1} : Type u_1 → Type (max u_1 a_1) -/
#guard_msgs in #check (ULift.!{a*, _} : Type _ → Type _)

/-- info: ULift.{b_1, c_1} : Type c_1 → Type (max c_1 b_1) -/
#guard_msgs in #check (ULift.!{b*, c*} : Type _ → Type _)

variable (X : Type*) (y : ULift.!{lift*} X)

def testNamedLift := y

/-- info: testNamedLift.{lift_1, u_1} (X : Type u_1) (y : ULift.{lift_1, u_1} X) : ULift.{lift_1, u_1} X -/
#guard_msgs in #check testNamedLift

end MultipleUniverseArgsTests

section ExplicitLevelTests

universe explicitU

variable (X : Type*) (y : ULift.!{explicitU, _} X)

def testExplicitLevel := y

/-- info: testExplicitLevel.{explicitU, u_1} (X : Type u_1) (y : ULift.{explicitU, u_1} X) : ULift.{explicitU, u_1} X -/
#guard_msgs in #check testExplicitLevel

variable (z : ULift.!{explicitU + 1, _} X)

def testExplicitLevelExpr := z

/--
info: testExplicitLevelExpr.{explicitU, u_1} (X : Type u_1) (z : ULift.{explicitU + 1, u_1} X) : ULift.{explicitU + 1, u_1} X
-/
#guard_msgs in #check testExplicitLevelExpr

/-- info: ULift.{0, 1} : Type 1 → Type 1 -/
#guard_msgs in #check (ULift.!{0, 1} : Type 1 → Type 1)

end ExplicitLevelTests

section InferredLevelTests

variable (X : Type 3) (y : ULift.!{_, _} X)

def testFullyInferred := y

/-- info: testFullyInferred.{u_1} (X : Type 3) (y : ULift.{u_1, 3} X) : ULift.{u_1, 3} X -/
#guard_msgs in #check testFullyInferred

end InferredLevelTests

section EmptyUniverseArgs

variable (X : Type*) (y : ULift.!{} X)

def testEmptyArgs := y

/-- info: testEmptyArgs.{u_1, u_2} (X : Type u_1) (y : ULift.{u_2, u_1} X) : ULift.{u_2, u_1} X -/
#guard_msgs in #check testEmptyArgs

end EmptyUniverseArgs

section PartialUniverseArgs

variable (X : Type*) (y : ULift.!{*} X)

def testPartialArgs := y

/-- info: testPartialArgs.{u_2, u_1} (X : Type u_1) (y : ULift.{u_2, u_1} X) : ULift.{u_2, u_1} X -/
#guard_msgs in #check testPartialArgs

end PartialUniverseArgs
