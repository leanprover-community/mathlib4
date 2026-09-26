module

public import Mathlib.Tactic.CategoryTheory.CatLemmas
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Discrete.Basic
public import MathlibTest.CategoryTheory.TheoremTransformRegistration

open CategoryTheory Lean Meta Elab Command

namespace Tests.CatLemmasErrors

variable {C : Type*} [Category* C]

def identityTemplate (C : Type*) [Category* C] : C ⥤ C := 𝟭 C
def anotherIdentity (C : Type*) [Category* C] : C ⥤ C := 𝟭 C

/-- error: unknown bundle selector 'reassoc' -/
#guard_msgs in
@[cat_lemmas (skip := [reassoc])]
lemma unknownSelector {X Y : C} (f : X ⟶ Y) : f = f := rfl

/-- error: `specialize_map` requires one explicit functor template -/
#guard_msgs in
@[transform_lemma specialize_map]
lemma missingTemplate {X Y : C} (f : X ⟶ Y) : f = f := rfl

/-- error: `@[specialize_map]` expects a declaration whose type reduces to `∀ .., C ⥤ D` -/
#guard_msgs in
@[cat_lemmas (specialize := [bad := Nat.succ])]
lemma invalidTemplate {X Y : C} (f : X ⟶ Y) : f = f := rfl

/-- error: distinct transformation paths generate the same name 'Tests.CatLemmasErrors.collision_map' -/
#guard_msgs in
@[cat_lemmas (specialize := [same := identityTemplate (suffix := "_map")])]
lemma collision {X Y : C} (f : X ⟶ Y) : f = f := rfl

-- Different templates are distinct requests even if their resulting propositions are equal.
/-- error: distinct transformation paths generate the same name 'Tests.CatLemmasErrors.templates_same' -/
#guard_msgs in
@[cat_lemmas (skip := [op, map])
  (specialize := [first := identityTemplate (suffix := "_same"),
                 second := anotherIdentity (suffix := "_same")])]
lemma templates {X Y : C} (f : X ⟶ Y) : f = f := rfl

lemma occupied_map : True := trivial

/-- error: private declaration `Tests.CatLemmasErrors.occupied_map` has already been declared -/
#guard_msgs in
@[cat_lemmas (skip := [op])]
lemma occupied {X Y : C} (f : X ⟶ Y) : f = f := rfl

-- A failed attempt must not overwrite the existing declaration.
example : True := occupied_map

def whiskeringTemplate {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (F : D ⥤ B) : (B ⥤ C) ⥤ D ⥤ C := (Functor.whiskeringLeft D B C).obj F

/--
error: request 'whisker' has no applicable branch:
`@[specialize_map]` could not unify the source of the functor with the source category of the lemma
-/
#guard_msgs in
@[cat_lemmas (specialize := [whisker := whiskeringTemplate])]
lemma incompatible {X Y : Discrete Unit} (f : X ⟶ Y) : f = f := rfl

lemma plain : True := trivial

-- A scheduler must not reinterpret an implementation exception as inapplicability.
/-- error: test transformation implementation error -/
#guard_msgs in
run_cmd liftTermElabM do
  let step : Mathlib.Tactic.CategoryTheory.CatLemmas.Step :=
    ⟨`broken, { transformation := `test_broken }, false⟩
  discard <| Mathlib.Tactic.CategoryTheory.CatLemmas.generate ``plain (← getRef) #[#[step]] {}

-- An explicit extra stage can use an imported registration, with no dispatcher changes.
lemma numbers {m n : Nat} (h : m = n) : m = n := h

run_cmd liftTermElabM do
  let request : Mathlib.Tactic.TheoremTransform.Request := { transformation := `test_zero_add }
  let step : Mathlib.Tactic.CategoryTheory.CatLemmas.Step := ⟨`normalize, request, true⟩
  let results ← Mathlib.Tactic.CategoryTheory.CatLemmas.generate
    ``numbers (← getRef) #[#[step]] {}
  guard <| results.map (·.name) == #[``numbers, (``numbers).appendAfter "_zeroAdd"]
  let some generated := results[1]? | throwError "missing generated result"
  guard <| generated.path.map (·.request) == #[request]

example {m n : Nat} (h : m = n) : m = n := numbers_zeroAdd h

end Tests.CatLemmasErrors
