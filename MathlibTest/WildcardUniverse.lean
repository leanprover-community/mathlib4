module

import all Mathlib.Tactic.WildcardUniverse
import Mathlib.Tactic.TypeStar
import Mathlib.CategoryTheory.Functor.Basic

set_option pp.universes true

section Foo

universe u v w
axiom Foo : Type u → Type v → Type w

/-- info: Foo.{u, u_1, u_2} : Type u → Type u_1 → Type u_2 -/
#guard_msgs in #check Foo.{u}

/-- info: Foo.{v, u_1, u_2} : Type v → Type u_1 → Type u_2 -/
#guard_msgs in #check Foo.{v}

/-- info: Foo.{w, u_1, u_2} : Type w → Type u_1 → Type u_2 -/
#guard_msgs in #check Foo.{w}

/-- info: Foo.{u_1, u, u_2} : Type u_1 → Type u → Type u_2 -/
#guard_msgs in #check Foo.{*,u}

/-- info: Foo.{u_1, v, u_2} : Type u_1 → Type v → Type u_2 -/
#guard_msgs in #check Foo.{*,v}

/-- info: Foo.{q_1, v, u_1} : Type q_1 → Type v → Type u_1 -/
#guard_msgs in #check Foo.{q*,v}

/-- info: Foo.{q_1, r_1, u_1} : Type q_1 → Type r_1 → Type u_1 -/
#guard_msgs in #check Foo.{q*,r*}

/-- info: Foo.{q_1, u, r_1} : Type q_1 → Type u → Type r_1 -/
#guard_msgs in #check Foo.{q*,u,r*}

/-- info: Foo.{u, q_1, r_1} : Type u → Type q_1 → Type r_1 -/
#guard_msgs in #check Foo.{u,q*,r*}

end Foo

section ULiftTests

/-- info: ULift.{r_1, s_1} : Type s_1 → Type (max s_1 r_1) -/
#guard_msgs in #check (ULift.{*, *} : Type _ → Type _)

variable (X : Type*) (z : ULift.{_} X)
def testInferred := z
/-- info: testInferred.{u_1, u_2} (X : Type u_1) (z : ULift.{u_2, u_1} X) : ULift.{u_2, u_1} X -/
#guard_msgs in #check testInferred

variable (y : ULift.{*} X)
def testStarFirst := y
/-- info: testStarFirst.{r_1, u_1} (X : Type u_1) (y : ULift.{r_1, u_1} X) : ULift.{r_1, u_1} X -/
#guard_msgs in #check testStarFirst

universe v
variable (e : ULift.{v, _} X)
def testExplicit := e
/-- info: testExplicit.{v, u_1} (X : Type u_1) (e : ULift.{v, u_1} X) : ULift.{v, u_1} X -/
#guard_msgs in #check testExplicit

/-- info: ULift.{r_2, s_1} : Type s_1 → Type (max s_1 r_2) -/
#guard_msgs in #check ULift.{*, *}

end ULiftTests

section CategoryTests

open CategoryTheory

variable (C : Type*) [Category.{*} C]

universe u
variable (D : Type u) [Category.{*} D]

variable (E : Type 3) [Category.{*} E]

def fooC := C ⥤ C
def fooD := D ⥤ D
def fooE := E ⥤ E

/-- info: fooC.{v_1, u_1} (C : Type u_1) [Category.{v_1, u_1} C] : Type (max v_1 u_1) -/
#guard_msgs in #check fooC

/-- info: fooD.{v_2, u} (D : Type u) [Category.{v_2, u} D] : Type (max v_2 u) -/
#guard_msgs in #check fooD

/-- info: fooE.{v_3} (E : Type 3) [Category.{v_3, 3} E] : Type (max v_3 3) -/
#guard_msgs in #check fooE

end CategoryTests

section CategoryProductTest

open CategoryTheory

variable (C D : Type*) [Category.{*} (C × D)]

def fooProd := (C × D) ⥤ (C × D)

/--
info: fooProd.{v_1, u_1, u_2} (C : Type u_1) (D : Type u_2) [Category.{v_1, max u_2 u_1} (Prod.{u_1, u_2} C D)] :
  Type (max v_1 u_2 u_1)
-/
#guard_msgs in #check fooProd

end CategoryProductTest

section CategoryExplicitUniverseTest

open CategoryTheory

universe w

abbrev TypeWithParam := {n : Nat // ∃ X : Type w, Nonempty (Fin n ≃ X)}

variable [Category.{*} TypeWithParam.{w}]

def ff := TypeWithParam.{w} ⥤ TypeWithParam.{w}

/-- info: ff.{w, v_1} [Category.{v_1, 0} TypeWithParam.{w}] : Type v_1 -/
#guard_msgs in #check ff

end CategoryExplicitUniverseTest

section NamedWildcardTests

open CategoryTheory

variable (C : Type*) [Category.{w*} C]

def fooNamed := C ⥤ C

/-- info: fooNamed.{w_1, u_1} (C : Type u_1) [Category.{w_1, u_1} C] : Type (max w_1 u_1) -/
#guard_msgs in #check fooNamed

variable (x : ULift.{z*, _} C)

def testNamedULift := x

/-- info: testNamedULift.{z_1, u_1} (C : Type u_1) (x : ULift.{z_1, u_1} C) : ULift.{z_1, u_1} C -/
#guard_msgs in #check testNamedULift

end NamedWildcardTests

section NamedWildcardWithUsage

open CategoryTheory

variable (C : Type*) [Category.{v*} C]

def fooNamedV := C ⥤ C

/-- info: fooNamedV.{v_1, u_1} (C : Type u_1) [Category.{v_1, u_1} C] : Type (max v_1 u_1) -/
#guard_msgs in #check fooNamedV

variable (D : Type*) [Category.{mor*} D]

def fooBothNamed := C ⥤ D

/--
info: fooBothNamed.{v_1, u_1, mor_1, u_2} (C : Type u_1) [Category.{v_1, u_1} C] (D : Type u_2) [Category.{mor_1, u_2} D] :
  Type (max v_1 mor_1 u_1 u_2)
-/
#guard_msgs in #check fooBothNamed

end NamedWildcardWithUsage

section MixedWildcardTests

open CategoryTheory

variable (A : Type*) [Category.{*} A]
variable (B : Type*) [Category.{w*} B]

def fooMixed := A ⥤ B

/--
info: fooMixed.{v_1, u_1, w_1, u_2} (A : Type u_1) [Category.{v_1, u_1} A] (B : Type u_2) [Category.{w_1, u_2} B] :
  Type (max v_1 w_1 u_1 u_2)
-/
#guard_msgs in #check fooMixed

end MixedWildcardTests

section MultipleUniverseArgsTests

/-- info: ULift.{a_1, u_1} : Type u_1 → Type (max u_1 a_1) -/
#guard_msgs in #check (ULift.{a*, _} : Type _ → Type _)

/-- info: ULift.{b_1, c_1} : Type c_1 → Type (max c_1 b_1) -/
#guard_msgs in #check (ULift.{b*, c*} : Type _ → Type _)

variable (X : Type*) (y : ULift.{lift*} X)

def testNamedLift := y

/-- info: testNamedLift.{lift_1, u_1} (X : Type u_1) (y : ULift.{lift_1, u_1} X) : ULift.{lift_1, u_1} X -/
#guard_msgs in #check testNamedLift

end MultipleUniverseArgsTests

section ExplicitLevelTests

universe explicitU

variable (X : Type*) (y : ULift.{explicitU, _} X)

def testExplicitLevel := y

/-- info: testExplicitLevel.{explicitU, u_1} (X : Type u_1) (y : ULift.{explicitU, u_1} X) : ULift.{explicitU, u_1} X -/
#guard_msgs in #check testExplicitLevel

variable (z : ULift.{explicitU + 1, _} X)

def testExplicitLevelExpr := z

/--
info: testExplicitLevelExpr.{explicitU, u_1} (X : Type u_1) (z : ULift.{explicitU + 1, u_1} X) : ULift.{explicitU + 1, u_1} X
-/
#guard_msgs in #check testExplicitLevelExpr

/-- info: ULift.{0, 1} : Type 1 → Type 1 -/
#guard_msgs in #check (ULift.{0, 1} : Type 1 → Type 1)

end ExplicitLevelTests

section InferredLevelTests

variable (X : Type 3) (y : ULift.{_, _} X)

def testFullyInferred := y

/-- info: testFullyInferred.{u_1} (X : Type 3) (y : ULift.{u_1, 3} X) : ULift.{u_1, 3} X -/
#guard_msgs in #check testFullyInferred

end InferredLevelTests

section PartialUniverseArgs

variable (X : Type*) (y : ULift.{*} X)

def testPartialArgs := y

/-- info: testPartialArgs.{r_1, u_1} (X : Type u_1) (y : ULift.{r_1, u_1} X) : ULift.{r_1, u_1} X -/
#guard_msgs in #check testPartialArgs

end PartialUniverseArgs

section ReorganizeUniverseParamsTests

open Lean

/-!
This section contains direct unit tests for the `reorganizeUniverseParams` function,
which is responsible for reorganizing universe parameter names to ensure proper ordering.
-/

def mkMVar (id : Nat) : Level := .mvar { name := Name.mkNum .anonymous id }

open Lean Elab Command in
meta def testReorganize (a b c d) :=
  liftTermElabM <| guard <| reorganizeUniverseParams a b c = d

-- Empty inputs should return empty list
run_cmd testReorganize #[] #[] [] []

-- Single mvar (no reordering needed)
run_cmd testReorganize #[none] #[mkMVar 1] [] []

-- Single param with no dependencies
run_cmd testReorganize #[some .param] #[.param `u_1] [] [`u_1]

-- Single param already in list
run_cmd testReorganize #[some .param] #[.param `u_1] [`u_1] [`u_1]

-- Two independent params
run_cmd testReorganize #[some .param, some .param] #[.param `u_1, .param `u_2] [] [`u_2, `u_1]

-- Two params where first already exists
run_cmd testReorganize #[some .param, some .param] #[.param `u_1, .param `u_2] [`u_1] [`u_2, `u_1]

-- Two params where first depends on second (needs reordering)
run_cmd testReorganize #[some .param, some .param] #[.param `u_2, .param `u_1] [`u_1] [`u_1, `u_2]

-- Named wildcards - basic case
run_cmd
  testReorganize #[some <| .param `v, some <| .param `w] #[.param `v_1, .param `w_1] [] [`w_1, `v_1]

-- Named wildcards with dependency
run_cmd
  testReorganize #[some <| .param `v, some <| .param `w] #[.param `v_1, .param `w_1] [`v_1]
    [`w_1, `v_1]

-- Mixed mvar and param
run_cmd testReorganize #[none, some .param] #[mkMVar 1, .param `u_1] [] [`u_1]

-- Mixed param and mvar
run_cmd testReorganize #[some .param, none] #[.param `u_1, mkMVar 1] [] [`u_1]

-- Explicit level (should be ignored)
run_cmd Lean.Elab.Command.liftTermElabM do
  let zero ← `(level|0)
  guard <| reorganizeUniverseParams #[some <| .explicit zero, some .param]
    #[.zero, .param `u_1] [] = [`u_1]

-- Complex case - three params with dependencies
run_cmd
  testReorganize #[some .param, some .param, some .param] #[.param `u_3, .param `u_2, .param `u_1]
    [`u_1, `u_2] [`u_1, `u_2, `u_3]

-- Param depends on later level max
run_cmd
  testReorganize #[some .param, some .param] #[.param `u_1, .max (.param `v) (.param `u_1)]
    [`v] [`v, `u_1]

-- Param depends on later level imax
run_cmd
  testReorganize #[some .param, some .param] #[.param `u_1, .imax (.param `w) (.param `u_1)] [`w]
    [`w, `u_1]

-- Param depends on later level succ
run_cmd testReorganize #[some .param, some .param] #[.param `u_1, .succ (.param `u_1)] [] [`u_1]

-- Multiple dependencies in later levels
run_cmd
  testReorganize #[some .param, some .param] #[.param `u_3, .max (.param `u_1) (.param `u_2)]
    [`u_1, `u_2] [`u_1, `u_2, `u_3]

-- Chain of dependencie
run_cmd
  testReorganize #[some .param, some .param, some .param] #[.param `u_3, .param `u_2, .param `u_1]
    [`u_1] [`u_1, `u_2, `u_3]

-- All mvars (no params to reorganize)
run_cmd
  testReorganize #[none, none, none] #[mkMVar 1, mkMVar 2, mkMVar 3] [`u_1, `u_2] [`u_1, `u_2]

-- Param that doesn't depend on anything goes first
run_cmd testReorganize #[some .param, some .param] #[.param `u_2, .param `u_1] [] [`u_1, `u_2]

-- Complex named wildcards with multiple dependencies
run_cmd
  testReorganize #[some <| .param `v, some <| .param `w, some <| .param `u]
    #[.param `v_1, .param `w_1, .max (.param `v_1) (.param `w_1)] [] [`v_1, `w_1]

-- Existing params that aren't being added
run_cmd
  testReorganize #[some .param] #[.param `u_2] [`existing_1, `existing_2]
    [`u_2, `existing_1, `existing_2]

-- Insert after specific dependency
run_cmd
  testReorganize #[some .param, some .param] #[.param `new_1, .param `new_2] [`v, `w]
    [`new_2, `new_1, `v, `w]

-- Insert between existing params based on dependency
run_cmd
  testReorganize #[some .param, none] #[.param `u_3, .max (.param `u_1) (.param `u_2)]
    [`u_1, `u_2, `u_4] [`u_1, `u_2, `u_3, `u_4]

-- No later dependencies - param goes to front
run_cmd
  testReorganize #[some .param, none] #[.param `u_new, mkMVar 1] [`u_1, `u_2] [`u_new, `u_1, `u_2]

end ReorganizeUniverseParamsTests

section BaseNameExtractionTests

/-!
This section tests that `*` wildcards use the constant's actual universe parameter names
as base names, with numeric suffixes stripped.
-/

-- Test that ULift.{*} uses `r` as base name (ULift's first param is `r`)
variable (X : Type*) (ulift_test : ULift.{*} X)
def testULiftBaseName := ulift_test
/-- info: testULiftBaseName.{r_1, u_1} (X : Type u_1) (ulift_test : ULift.{r_1, u_1} X) : ULift.{r_1, u_1} X -/
#guard_msgs in #check testULiftBaseName

-- Test that Category.{*} uses `v` as base name (Category's first param is `v`)
open CategoryTheory
variable (C : Type*) [cat_test : Category.{*} C]
def testCategoryBaseName := cat_test
/-- info: testCategoryBaseName.{v_1, u_2} (C : Type u_2) [cat_test : Category.{v_1, u_2} C] : Category.{v_1, u_2} C -/
#guard_msgs in #check testCategoryBaseName

-- Test with Foo (which has params u, v, w) - first `*` should use `u`
universe u v w
axiom Foo2 : Type u → Type v → Type w

/-- info: Foo2.{u_3, v_2, w_1} : Type u_3 → Type v_2 → Type w_1 -/
#guard_msgs in #check Foo2.{*, *, *}

/-- info: Foo2.{u_3, v, w_1} : Type u_3 → Type v → Type w_1 -/
#guard_msgs in #check Foo2.{*, v, *}

end BaseNameExtractionTests

section ExplicitAppTests

/-!
This section tests the `@` prefix for explicit application mode.
-/

-- Define a function with implicit arguments for testing
universe eu ev
axiom ExplicitTest : {α : Type eu} → {β : Type ev} → α → β → α × β

/-- info: @ExplicitTest.{eu_1, ev_1} : {α : Type eu_1} → {β : Type ev_1} → α → β → Prod.{eu_1, ev_1} α β -/
#guard_msgs in #check @ExplicitTest.{*, *}

/-- info: ExplicitTest.{eu_1, ev_1} : ?m.1 → ?m.2 → Prod.{eu_1, ev_1} ?m.1 ?m.2 -/
#guard_msgs in #check ExplicitTest.{*, *}

-- Test applying with @ to provide implicit args explicitly
variable (A : Type eu) (B : Type ev) (a : A) (b : B)

/-- info: ExplicitTest.{eu, ev} a b : Prod.{eu, ev} A B -/
#guard_msgs in #check ExplicitTest.{eu, ev} a b

/-- info: ExplicitTest.{eu, ev} a b : Prod.{eu, ev} A B -/
#guard_msgs in #check @ExplicitTest.{eu, ev} A B a b

-- Test with named wildcards
/-- info: @ExplicitTest.{x_1, y_1} : {α : Type x_1} → {β : Type y_1} → α → β → Prod.{x_1, y_1} α β -/
#guard_msgs in #check @ExplicitTest.{x*, y*}

-- Test with named arguments using @
/-- info: ExplicitTest.{eu, ev} a b : Prod.{eu, ev} A B -/
#guard_msgs in #check @ExplicitTest.{eu, ev} (α := A) (β := B) a b

/-- info: ExplicitTest.{eu, ev} a b : Prod.{eu, ev} A B -/
#guard_msgs in #check @ExplicitTest.{eu, ev} (β := B) (α := A) a b

-- Test mixing positional and named arguments
/-- info: ExplicitTest.{eu, ev} a b : Prod.{eu, ev} A B -/
#guard_msgs in #check @ExplicitTest.{eu, ev} A (β := B) a b

-- Define another axiom with more arguments for thorough testing
axiom ExplicitTest2 : {α : Type eu} → {β : Type ev} → {γ : Type eu} → α → β → γ → α × β × γ

/--
info: @ExplicitTest2.{eu_1,
    ev_1} : {α : Type eu_1} →
  {β : Type ev_1} → {γ : Type eu_1} → α → β → γ → Prod.{eu_1, max eu_1 ev_1} α (Prod.{ev_1, eu_1} β γ)
-/
#guard_msgs in #check @ExplicitTest2.{*, *}

/-- info: ExplicitTest2.{eu_1, ev_1} : ?m.1 → ?m.2 → ?m.3 → Prod.{eu_1, max eu_1 ev_1} ?m.1 (Prod.{ev_1, eu_1} ?m.2 ?m.3) -/
#guard_msgs in #check ExplicitTest2.{*, *}

-- Test named arguments with ExplicitTest2
variable (C : Type eu) (c : C)

/-- info: ExplicitTest2.{eu, ev} a b c : Prod.{eu, max eu ev} A (Prod.{ev, eu} B C) -/
#guard_msgs in #check @ExplicitTest2.{eu, ev} (α := A) (β := B) (γ := C) a b c

/--
info: fun α =>
  @ExplicitTest2.{eu_1, ev} α
    B : (α : Type eu_1) → {γ : Type eu_1} → α → B → γ → Prod.{eu_1, max eu_1 ev} α (Prod.{ev, eu_1} B γ)
-/
#guard_msgs in #check @ExplicitTest2.{*, ev} (β := B)

end ExplicitAppTests
