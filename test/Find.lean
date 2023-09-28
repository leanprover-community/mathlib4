import Mathlib.Tactic.Find
import Std.Tactic.GuardMsgs
import Std.Data.List.Lemmas
import Mathlib.Tactic.RunCmd

-- Recall that `#find` caches an index of imported lemmas on disk
-- If you are modifying the way that `#find` indexes lemmas,
-- while testing you will probably want to delete
-- `build/lib/MathlibExtras/Find.extra`
-- so that the cache is rebuilt.
--
-- The tests below are set up to only depend on local definitions (using `uniquenameforthistest`)
-- so that this test file does not need to to be updated when Mathlib changes.


/-- warning: Cannot search: No constants or name fragments in search pattern. -/
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
def uniquenameforthistest : Bool := true

theorem uniquenameforthistest_eq_true:
  uniquenameforthistest = true := rfl

/--
info: Found 1 definitions mentioning uniquenameforthistest.
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find uniquenameforthistest

/--
info: Found 2 definitions whose name contains "uniquenameforthistest".
Of these, 2 have a name containing "uniquenameforthistest".
• uniquenameforthistest
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find "uniquenameforthistest"

/--
info: Found 2 definitions whose name contains "uenameforthis".
Of these, 2 have a name containing "uenameforthis".
• uniquenameforthistest
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find "uenameforthis"

/--
info: Found 1 definitions mentioning uniquenameforthistest.
Of these, 1 have a name containing "eq".
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find uniquenameforthistest, "eq"

/--
info: Found 1 definitions mentioning uniquenameforthistest and Eq.
Of these, 1 match your patterns.
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find uniquenameforthistest = _

/--
info: Found 1 definitions mentioning uniquenameforthistest and Eq.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find (_ = uniquenameforthistest)

/-- error: unknown identifier 'uniquenameforthistestthatdoesn'texist' -/
#guard_msgs in
#find uniquenameforthistestthatdoesn'texist

/-- error: unknown identifier 'uniquenameforthistestthatdoesn'texist' -/
#guard_msgs in
#find (uniquenameforthistestthatdoesn'texist = _)

/-- error: Cannot search for _. Did you forget to put a term pattern in parentheses? -/
#guard_msgs in
#find uniquenameforthistest, _

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem non_linear_pattern_test1 {n m : Nat} (_ : uniquenameforthistest = true) :
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n () := by
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem non_linear_pattern_test2 {n m : Nat} (_ : uniquenameforthistest = true) :
  List.replicate n () ++ List.replicate m () = List.replicate (n + m) () := by
  sorry

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find uniquenameforthistest, List.replicate ?n _ ++ List.replicate ?n _

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest and HAppend.hAppend.
Of these, 2 match your patterns.
• non_linear_pattern_test1
• non_linear_pattern_test2
-/
#guard_msgs in
#find uniquenameforthistest, List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest, Eq and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find uniquenameforthistest, |- _ = List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest, Eq and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test2
-/
#guard_msgs in
#find uniquenameforthistest, |- List.replicate ?n _ ++ List.replicate ?m _ = _

theorem hyp_ordering_test1 {n : Nat} (_ : uniquenameforthistest = true) (h : 0 < n) :
  0 ≤ n := Nat.le_of_lt h

theorem hyp_ordering_test2 {n : Nat} (h : 0 < n) (_ : uniquenameforthistest = true) :
  0 ≤ n := Nat.le_of_lt h

/--
info: Found 2 definitions mentioning LE.le, LT.lt, OfNat.ofNat, uniquenameforthistest and Eq.
Of these, 2 match your patterns.
• hyp_ordering_test1
• hyp_ordering_test2
-/
#guard_msgs in
#find ⊢ uniquenameforthistest = _ → 0 < ?n → _ ≤ ?n


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

-- The following does not work for some strange reason

/--
info: Found 1 definitions mentioning HMul.hMul, LinearPatternTest.Star.star and Eq.
Of these, 1 match your patterns.
• star_comm_self'
-/
#guard_msgs in
#find star ?a * ?a = ?a * star ?a


end LinearPatternTest

section ListMapTest

open Mathlib.Tactic.Find
open Lean Elab Command

elab s:"#assert_match " name_s:ident concl:(turnstyle)? query:term : command => liftTermElabM do
    let pat ← Lean.Elab.Term.elabTerm query none
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

/-- error: Name pattern is too general -/
#guard_msgs in
#find ""

/-- error: Name pattern is too general -/
#guard_msgs in
#find "."

/--
info: Found 2 definitions whose name contains "uniquenameforThisTest".
Of these, 2 have a name containing "uniquenameforThisTest".
• uniquenameforthistest
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find "uniquenameforThisTest" -- checks for case-insensitivity


-- Check that |- only allows Sort-typed things

/--
info: Found 0 definitions mentioning And, True and uniquenameforthistest.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find uniquenameforthistest, And True

/-- error: Conclusion pattern is of type Bool, should be of type `Sort` -/
#guard_msgs in
#find uniquenameforthistest, |- true

/-- error: Conclusion pattern is of type Prop → Prop, should be of type `Sort` -/
#guard_msgs in
#find uniquenameforthistest, |- And True

/--
info: Found 0 definitions mentioning And, True and uniquenameforthistest.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find |- And True True, uniquenameforthistest
