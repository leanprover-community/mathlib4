import Mathlib.Tactic.Find
import Std.Tactic.GuardMsgs
import Std.Data.List.Lemmas

/-- warning: Cannot search: No constants in search pattern. -/
#guard_msgs in
#find

/-- warning: Cannot search: No constants in search pattern. -/
#guard_msgs in
#find "foobar"

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
info: Found 1 definitions mentioning uniquenameforthistest.
Of these, 1 have a name containing "eq".
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find uniquenameforthistest "eq"

/--
info: Found 1 definitions mentioning uniquenameforthistest and Eq.
Of these, 1 match your patterns.
• uniquenameforthistest_eq_true
-/
#guard_msgs in
#find (uniquenameforthistest = _)

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
#find uniquenameforthistest (List.replicate ?n _ ++ List.replicate ?n _)

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest and HAppend.hAppend.
Of these, 2 match your patterns.
• non_linear_pattern_test1
• non_linear_pattern_test2
-/
#guard_msgs in
#find uniquenameforthistest (List.replicate ?n _ ++ List.replicate ?m _)

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest, Eq and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find uniquenameforthistest |- (_ = List.replicate ?n _ ++ List.replicate ?m _)

/--
info: Found 2 definitions mentioning List.replicate, uniquenameforthistest, Eq and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test2
-/
#guard_msgs in
#find uniquenameforthistest |- (List.replicate ?n _ ++ List.replicate ?m _ = _)

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
#find ⊢ (uniquenameforthistest = _ → 0 < ?n → _ ≤ ?n)
