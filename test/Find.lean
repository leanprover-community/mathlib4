import Mathlib.Tactic.Find
import Std.Tactic.GuardExpr
import Std.Data.List.Lemmas

/-- warning: Cannot search: No constants in search pattern. -/
#guard_msgs in
#find

/-- warning: Cannot search: No constants in search pattern. -/
#guard_msgs in
#find "foobar"

/-- We use this definition in all tests below to get reproducible results,
including the statistics about how many lemas were found in the index. -/
def uniqnameforthistest : Bool := true

lemma hopefullyuniquenamefortestingfind_eq_true:
  uniqnameforthistest = true := rfl

/--
info: Found 1 definitions mentioning uniqnameforthistest.
• hopefullyuniquenamefortestingfind_eq_true
-/
#guard_msgs in
#find uniqnameforthistest

/--
info: Found 1 definitions mentioning uniqnameforthistest.
Of these, 1 have a name containing "eq".
• hopefullyuniquenamefortestingfind_eq_true
-/
#guard_msgs in
#find uniqnameforthistest "eq"

/--
info: Found 1 definitions mentioning Eq and uniqnameforthistest.
Of these, 1 match your patterns.
• hopefullyuniquenamefortestingfind_eq_true
-/
#guard_msgs in
#find (uniqnameforthistest = _)

/--
info: Found 1 definitions mentioning Eq and uniqnameforthistest.
Of these, 0 match your patterns.
-/
#guard_msgs in
#find (_ = uniqnameforthistest)



/-- warning: declaration uses 'sorry' -/
#guard_msgs in
lemma non_linear_pattern_test1 {n m : ℕ} (_ : uniqnameforthistest = true) :
  List.replicate (2 * n) () = List.replicate n () ++ List.replicate n () := by
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
lemma non_linear_pattern_test2 {n m : ℕ} (_ : uniqnameforthistest = true) :
  List.replicate n () ++ List.replicate m () = List.replicate (n + m) () := by
  sorry

/--
info: Found 2 definitions mentioning List.replicate, uniqnameforthistest and HAppend.hAppend.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find uniqnameforthistest (List.replicate ?n _ ++ List.replicate ?n _

/--
info: Found 2 definitions mentioning List.replicate, uniqnameforthistest and HAppend.hAppend.
Of these, 2 match your patterns.
• non_linear_pattern_test1
• non_linear_pattern_test2
-/
#guard_msgs in
#find uniqnameforthistest (List.replicate ?n _ ++ List.replicate ?m _

/--
info: Found 2 definitions mentioning List.replicate, Eq, HAppend.hAppend and uniqnameforthistest.
Of these, 1 match your patterns.
• non_linear_pattern_test1
-/
#guard_msgs in
#find uniqnameforthistest |- (_ = List.replicate ?n _ ++ List.replicate ?m _)

/--
info: Found 2 definitions mentioning List.replicate, Eq, HAppend.hAppend and uniqnameforthistest.
Of these, 1 match your patterns.
• non_linear_pattern_test2
-/
#guard_msgs in
#find uniqnameforthistest |- (List.replicate ?n _ ++ List.replicate ?m _ = _)

lemma hyp_ordering_test1 {n : ℕ} (_ : uniqnameforthistest = true) (h : 0 < n) :
  0 ≤ n := Nat.le_of_lt h

lemma hyp_ordering_test2 {n : ℕ} (h : 0 < n) (_ : uniqnameforthistest = true) :
  0 ≤ n := Nat.le_of_lt h

/--
info: Found 2 definitions mentioning LE.le, LT.lt, OfNat.ofNat, Eq and uniqnameforthistest.
Of these, 2 match your patterns.
• hyp_ordering_test1
• hyp_ordering_test2
-/
#guard_msgs in
#find ⊢ (uniqnameforthistest = _ → 0 < ?n → _ ≤ ?n)
