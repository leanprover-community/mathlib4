import Mathlib.Tactic.Find
import Std.Tactic.GuardMsgs
import Std.Data.List.Lemmas
import Mathlib.Tactic.RunCmd

-- We want the following tests to be self-contained.
-- Therefore we erase all knowledge about imported definitios from find:

run_cmd do
  Mathlib.Tactic.Find.cachedIndex.1.cache.set (.inr (.pure (pure (.empty, .empty))))
  Mathlib.Tactic.Find.cachedIndex.2.cache.set (.inr (.pure (pure (.empty, .empty))))

/-- error: Cannot search: No constants or name fragments in search pattern. -/
#guard_msgs in
#find

/--
info: Found 0 definitions whose name contains "namefragmentsearch".
Of these, 0 have a name containing "namefragmentsearch".
-/
#guard_msgs in
#find "namefragmentsearch"

/-- We use this definition in all tests below to get reproducible results,
including the statistics about how many lemas were found in the index. -/
def my_true : Bool := true

theorem my_true_eq_true:
  my_true = true := rfl

theorem my_true_eq_True: -- intentionally capitalized
  my_true = true := rfl

/--
info: Found 2 definitions mentioning my_true.
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find my_true

/--
info: Found 3 definitions whose name contains "my_true".
Of these, 3 have a name containing "my_true".
• my_true
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find "my_true"

/--
info: Found 3 definitions whose name contains "y_tru".
Of these, 3 have a name containing "y_tru".
• my_true
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find "y_tru"

/--
info: Found 2 definitions mentioning my_true.
Of these, 2 have a name containing "eq".
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find my_true, "eq"

/--
info: Found 2 definitions mentioning my_true and Eq.
Of these, 2 match your patterns.
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find my_true = _

/--
info: Found 2 definitions mentioning my_true and Eq.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find (_ = my_true)

/-- error: unknown identifier 'doesn'texist' -/
#guard_msgs in
#find doesn'texist

/-- error: unknown identifier 'doesn'texist' -/
#guard_msgs in
#find (doesn'texist = _)

/-- error: Cannot search for _. Did you forget to put a term pattern in parentheses? -/
#guard_msgs in
#find my_true, _

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem non_linear_pattern_test1 {n m : Nat} :
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n () := by
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem non_linear_pattern_test2 {n m : Nat} :
  List.replicate n () ++ List.replicate m () = List.replicate (n + m) () := by
  sorry

/--
info: Found 2 definitions mentioning List.replicate and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find List.replicate ?n _ ++ List.replicate ?n _

/--
info: Found 2 definitions mentioning List.replicate and HAppend.hAppend.
Of these, 2 match your patterns.
• non_linear_pattern_test2
• non_linear_pattern_test1
-/
#guard_msgs in
#find List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, Eq and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find |- _ = List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, Eq and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test2
-/
#guard_msgs in
#find |- List.replicate ?n _ ++ List.replicate ?m _ = _

theorem hyp_ordering_test1 {n : Nat} (h : 0 < n) (_ : n + n = 6 * n): 0 ≤ n := Nat.le_of_lt h
theorem hyp_ordering_test2 {n : Nat} (_ : n + n = 6 * n) (h : 0 < n) : 0 ≤ n := Nat.le_of_lt h

/--
info: Found 2 definitions mentioning LE.le, LT.lt and OfNat.ofNat.
Of these, 2 match your patterns.
• hyp_ordering_test1
• hyp_ordering_test2
-/
#guard_msgs in
#find ⊢ 0 < ?n → _ ≤ ?n


-- Regression test

section LinearPatternTest
namespace LinearPatternTest

class Star (R : Type _) where star : R → R
export Star(star)

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem star_comm_self' {R} [Mul R] [Star R] (x : R) : star x * x = x * star x := sorry

/--
info: Found 1 definitions mentioning LinearPatternTest.Star.star.
Of these, 1 match your patterns.
• star_comm_self'
-/
#guard_msgs in
#find star _

/--
info: Found 1 definitions mentioning HMul.hMul, LinearPatternTest.Star.star and Eq.
Of these, 1 match your patterns.
• star_comm_self'
-/
#guard_msgs in
#find star ?a * ?a = ?a * star ?_

/--
info: Found 1 definitions mentioning HMul.hMul, LinearPatternTest.Star.star and Eq.
Of these, 1 match your patterns.
• star_comm_self'
-/
#guard_msgs in
#find star ?a * ?a = ?b * star ?b


end LinearPatternTest

section ListMapTest

open Mathlib.Tactic.Find
open Lean Elab Command

elab s:"#assert_match " name_s:ident concl:(turnstyle)? query:term : command => liftTermElabM do
    let pat ← Mathlib.Tactic.Find.elabTerm' query none
    let name := Lean.TSyntax.getId name_s
    let matcher ←
      if concl.isSome
      then matchConclusion pat
      else matchAnywhere pat
    let c := (← getEnv).constants.find! name
    unless ← matcher c do
      logErrorAt s "Pattern does not match when it should!"

#assert_match List.map (?a -> ?b) -> List ?a -> List ?b
#assert_match List.map List ?a → (?a -> ?b) -> List ?b
#assert_match List.map |- (?a -> ?b) -> List ?a -> List ?b

end ListMapTest

section DefaltingTest

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
lemma test_with_zero {α} [Zero α] [HMul α α α] [LE α] {a : α}: 0 ≤ a * a := sorry

-- Tests the defaulting does not kick in below

#assert_match test_with_zero |- 0 ≤ ?a * ?a



/-- error: Name pattern is too general -/
#guard_msgs in
#find ""

/-- error: Name pattern is too general -/
#guard_msgs in
#find "."

/--
info: Found 2 definitions whose name contains "my_true_eq_True".
Of these, 2 have a name containing "my_true_eq_True".
• my_true_eq_True
• my_true_eq_true
-/
#guard_msgs in
#find "my_true_eq_True" -- checks for case-insensitivity


-- Check that |- only allows Sort-typed things

/--
info: Found 0 definitions mentioning And and True.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find And True

/-- error: Conclusion pattern is of type Bool, should be of type `Sort` -/
#guard_msgs in
#find |- true

/-- error: Conclusion pattern is of type Prop → Prop, should be of type `Sort` -/
#guard_msgs in
#find |- And True

/--
info: Found 0 definitions mentioning And, True and my_true.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find |- And True True, my_true


-- Searching for qualified names

def Namespaced.TestDefinition := true

theorem TestDefinition_eq_true:
  Namespaced.TestDefinition = true := rfl

/--
error: unknown identifier 'TestDefinition'
---
info: Try this: Namespaced.TestDefinition
-/
#guard_msgs in
#find TestDefinition


-- Handlig duplcats

def NamespacedA.AnotherTestDefinition := true
def NamespacedB.AnotherTestDefinition := true
def NamespacedC.AnotherTestDefinition := true
theorem NamespcedA.AnotherTestDefinition_eq_true:
  NamespacedA.AnotherTestDefinition = true := rfl
theorem NamespcedB.AnotherTestDefinition_eq_true:
  NamespacedB.AnotherTestDefinition = true := rfl

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try this: NamespacedA.AnotherTestDefinition
---
info: Try this: NamespacedB.AnotherTestDefinition
---
info: Try this: NamespacedC.AnotherTestDefinition
-/
#guard_msgs in
#find AnotherTestDefinition

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try this: "some string before", NamespacedA.AnotherTestDefinition, some (Expr after)
---
info: Try this: "some string before", NamespacedB.AnotherTestDefinition, some (Expr after)
---
info: Try this: "some string before", NamespacedC.AnotherTestDefinition, some (Expr after)
-/
#guard_msgs in
#find "some string before", AnotherTestDefinition, some (Expr after)

-- doesn't give suggestions (yet)

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try this: "some string before", NamespacedA.AnotherTestDefinition = _, some (Expr after)
---
info: Try this: "some string before", NamespacedB.AnotherTestDefinition = _, some (Expr after)
---
info: Try this: "some string before", NamespacedC.AnotherTestDefinition = _, some (Expr after)
-/
#guard_msgs in
#find "some string before", AnotherTestDefinition = _, some (Expr after)

/--
error: unknown identifier 'AnotherTestDefinition'
---
info: Try this: "some string before", |- NamespacedA.AnotherTestDefinition = _, some (Expr after)
---
info: Try this: "some string before", |- NamespacedB.AnotherTestDefinition = _, some (Expr after)
---
info: Try this: "some string before", |- NamespacedC.AnotherTestDefinition = _, some (Expr after)
-/
#guard_msgs in
#find "some string before", |- AnotherTestDefinition = _, some (Expr after)

-- The following check checks that a type error (or other error) at an identifier
-- that can be resolved doesn't make #find look for possible candidates

/--
error: application type mismatch
  Nat.add 0 my_true
argument
  my_true
has type
  Bool : Type
but is expected to have type
  ℕ : Type
-/
#guard_msgs in
#find Nat.add 0 my_true
