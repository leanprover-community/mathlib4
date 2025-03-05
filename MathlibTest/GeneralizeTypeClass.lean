import Mathlib.Tactic.Linter.GeneralizeTypeClass
--import Mathlib.Algebra.Module.Defs
--import Mathlib.Algebra.Algebra.Defs
--import Mathlib.Topology.Algebra.Ring.Basic

class Parent where
  parent_thm : False
class Child extends Parent where
  child_thm : False
class Child2 extends Child where
  child2_thm : False

class abbrev ChildClassAbbrev := Child, Child2
abbrev ChildAbbrev := Child

/-- info: Generalize type class: Parent -/
#guard_msgs in
theorem basic1 [Child] : False := Parent.parent_thm

namespace ANameSpace
/-- info: Generalize type class: Parent -/
#guard_msgs in
theorem basic2 [C : Child] : False := C.parent_thm
/-- info: Generalize type class: Parent -/
#guard_msgs in
protected theorem basic3 [Child2] : False := Parent.parent_thm
end ANameSpace

/-- info: Generalize type class: Parent -/
#guard_msgs in
theorem basic4 [Child2] : False := Parent.parent_thm
/-- info: Generalize type class: Parent -/
#guard_msgs in
private theorem basic5 [Child2] : False := Parent.parent_thm
/-- info: Generalize type class: Parent -/
#guard_msgs in
theorem basic6 [ChildClassAbbrev] : False := Parent.parent_thm

/---/
#guard_msgs in
theorem basic7 [Child] : False := Child.child_thm
/---/
#guard_msgs in
theorem basic8 [C : Child] : False := C.child_thm

-- Ensure we don't 'generalize' type classes in hypotheses
class HypothesisParent where
  parent_thm : True
class HypothesisChild extends HypothesisParent where
  child_thm : False

/---/
#guard_msgs in
theorem dont_generalize_hypotheses_helper (_ : ∀ [HypothesisChild], False) : True := True.intro
theorem dont_generalize_hypotheses : True := by
  apply dont_generalize_hypotheses_helper
  intro inst
  exact inst.child_thm

class AnotherParent where
  parent_thm : False
class AnotherChild extends AnotherParent where
  child_thm : False

class MultipleParents extends Child, AnotherChild

/-- info: Generalize type class: AnotherParent
---
info: Generalize type class: Parent -/
#guard_msgs in
theorem multiple_parents [C : MultipleParents] : False := C.parent_thm

class ParentArg (T : Type) where
  parent_thm : False
class ParentArg2 (T : Type) where
  parent_thm2 : False
class ChildArg (T : Type) extends ParentArg T, ParentArg2 T where
  child_thm : False

class abbrev ChildArgClassAbbrev (T : Type) := ChildArg T

/-- info: Generalize type class: ParentArg -/
#guard_msgs in
theorem argument1 [C : ChildArgClassAbbrev Nat] : False := C.parent_thm
/-- info: Generalize type class: ParentArg
---
info: Generalize type class: ParentArg2 -/
#guard_msgs in
theorem argument2 [C : ChildArg Nat] : False := by
  try exact C.parent_thm
  try exact C.parent_thm2
/---/
#guard_msgs in
theorem argument3 [C : ChildArg Nat] : False := C.child_thm
/-- info: Generalize type class: ParentArg -/
#guard_msgs in
theorem argument4 [C : ChildArg Nat] : False := C.parent_thm
/-- info: Generalize type class: ParentArg2 -/
#guard_msgs in
theorem argument5 [C : ChildArg Nat] : False := C.parent_thm2

/-- info: Generalize type class: AddCommMonoid -/
#guard_msgs in
theorem ring_module1 [X : Semiring R] [AddCommGroup M] [Y : Module R M] : True := by
  let b := Y.add_smul
  exact True.intro
/---/
#guard_msgs in
theorem ring_module2 [X : CommRing R] [AddCommGroup M] [Y : Module R M] : True := by
  let a := X.toCommSemiring
  let b := Y.add_smul
  exact True.intro

namespace VariableTest

class NatParent where
  nat : Nat
class NatChild extends NatParent
def helper [N : NatChild] : Nat × Nat := ⟨0, N.nat⟩
variable {N₁ : NatChild}
/---/
#guard_msgs in
theorem variable1 [D : VariableTest.NatChild] : helper.1 = 0 := rfl

#print variable1

end VariableTest

------ TODO

section SectionTest
variable [B : Child]
/-- info: Generalize type class: Parent -/
--#guard_msgs in
theorem FAIL : False := Parent.parent_thm
end SectionTest


-----
theorem bad1 [Ring R] [AddCommMonoid M] [Module R M] : True := True.intro
theorem bad2 [CommRing R] [AddCommMonoid M] [Module R M] : True := True.intro

theorem good1 [Ring R] [AddCommGroup M] [Module R M] : True := True.intro
theorem good2 [CommRing R] [AddCommGroup M] [Module R M] : True := True.intro
-- TODO ././././Mathlib/Algebra/Module/Rat.lean:33
theorem good3 [AddCommMonoid M] [Module ℚ≥0 M] : True := True.intro
theorem good4 [Ring R] [Module R ℚ≥0] : True := True.intro

-- Algebra
theorem bad11 [CommRing R] [Semiring A] [Algebra R A] : True := True.intro
theorem bad12 [CommRing R] [CommSemiring A] [Algebra R A] : True := True.intro

theorem good11 [CommRing R] [Ring A] [Algebra R A] : True := True.intro
-- TODO: Why don't I try to generalize the second CommRing to Ring?
theorem good12 [CommRing R] [CommRing A] [Algebra R A] : True := True.intro

-- IsTopological*
theorem bad21 [TopologicalSpace B] [Ring B] [IsTopologicalSemiring B] : True := True.intro
theorem bad22 [TopologicalSpace B] [CommRing B] [IsTopologicalSemiring B] : True := True.intro

theorem good21 [TopologicalSpace B] [Ring B] [IsTopologicalRing B] : True := True.intro
theorem good22 [TopologicalSpace B] [Semiring B] [Ring B] [IsTopologicalRing B] : True := True.intro
theorem good23 [TopologicalSpace B] [CommRing B] [IsTopologicalRing B] : True := True.intro



-----
class Helper (X : outParam Type)
class P
class C extends P

instance [Helper X] [P] : C where

theorem myt [C] : False := sorry

theorem myt1 [C] : False := myt
--instance : C where
--set_option trace.Meta.synthInstance true
theorem myt2 [Helper X] [C] : False := myt

def foo [Helper X] [P] : C := inferInstance

set_option pp.all true
#print foo
