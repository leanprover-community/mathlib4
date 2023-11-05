import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.AssertNoSorry
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Quot
import Mathlib.Data.Nat.Prime

set_option autoImplicit true

-- Enable this option for tracing:
-- set_option trace.Tactic.librarySearch true
-- And this option to trace all candidate lemmas before application.
-- set_option trace.Tactic.librarySearch.lemmas true
-- It may also be useful to enable
-- set_option trace.Meta.Tactic.solveByElim true

-- Recall that `apply?` caches the discrimination tree on disk.
-- If you are modifying the way that `apply?` indexes lemmas,
-- while testing you will probably want to delete
-- `build/lib/MathlibExtras/LibrarySearch.extra`
-- so that the cache is rebuilt.

-- We need to set this here, as the lakefile does not enable this during testing.
-- https://github.com/leanprover-community/mathlib4/issues/6440
set_option pp.unicode.fun true

noncomputable section

/-- info: Try this: exact Nat.lt.base x -/
#guard_msgs in
example (x : Nat) : x ≠ x.succ := ne_of_lt (by apply?)

/-- info: Try this: exact Nat.succ_pos 1 -/
#guard_msgs in
example : 0 ≠ 1 + 1 := ne_of_lt (by apply?)

/-- info: Try this: exact Nat.add_comm x y -/
#guard_msgs in
example (x y : Nat) : x + y = y + x := by apply?

/-- info: Try this: exact fun a ↦ Nat.add_le_add_right a k -/
#guard_msgs in
example (n m k : Nat) : n ≤ m → n + k ≤ m + k := by apply?

/-- info: Try this: exact Nat.mul_dvd_mul_left a w -/
#guard_msgs in
example (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c := by apply?

-- Could be any number of results (`Int.one`, `Int.zero`, etc)
#guard_msgs (drop info) in
example : Int := by apply?

/-- info: Try this: Nat.lt.base x -/
#guard_msgs in
example : x < x + 1 := exact?%

/-- info: Try this: exact p -/
#guard_msgs in
example (P : Prop) (p : P) : P := by apply?
/-- info: Try this: exact (np p).elim -/
#guard_msgs in
example (P : Prop) (p : P) (np : ¬P) : false := by apply?
/-- info: Try this: exact h x rfl -/
#guard_msgs in
example (X : Type) (P : Prop) (x : X) (h : ∀ x : X, x = x → P) : P := by apply?

-- Could be any number of results (`fun x ↦ x`, `id`, etc)
#guard_msgs (drop info) in
example (α : Prop) : α → α := by apply?

-- Note: these examples no longer work after we turned off lemmas with discrimination key `#[*]`.
-- example (p : Prop) : (¬¬p) → p := by apply? -- says: `exact not_not.mp`
-- example (a b : Prop) (h : a ∧ b) : a := by apply? -- says: `exact h.left`
-- example (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by apply? -- say: `exact Function.mtr`

/-- info: Try this: exact Nat.add_comm a b -/
#guard_msgs in
example (a b : ℕ) : a + b = b + a :=
by apply?

/-- info: Try this: exact Nat.mul_sub_left_distrib n m k -/
#guard_msgs in
example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by apply?

/-- info: Try this: exact (Nat.mul_sub_left_distrib n m k).symm -/
#guard_msgs in
example (n m k : ℕ) : n * m - n * k = n * (m - k) :=
by apply?

/-- info: Try this: exact eq_comm -/
#guard_msgs in
example {α : Type} (x y : α) : x = y ↔ y = x := by apply?

/-- info: Try this: exact Nat.add_pos_left ha b -/
#guard_msgs in
example (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by apply?

/-- info: Try this: exact Nat.add_pos_left ha b -/
#guard_msgs in
-- Verify that if maxHeartbeats is 0 we don't stop immediately.
set_option maxHeartbeats 0 in
example (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by apply?

section synonym

/-- info: Try this: exact Nat.add_pos_left ha b -/
#guard_msgs in
example (a b : ℕ) (ha : a > 0) (_hb : 0 < b) : 0 < a + b := by apply?

/-- info: Try this: exact Nat.le_of_dvd w h -/
#guard_msgs in
example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by apply?

/-- info: Try this: exact Nat.le_of_dvd w h -/
#guard_msgs in
example (a b : ℕ) (h : a ∣ b) (w : b > 0) : b ≥ a := by apply?

-- TODO: A lemma with head symbol `¬` can be used to prove `¬ p` or `⊥`
/-- info: Try this: exact Nat.not_lt_zero a -/
#guard_msgs in
example (a : ℕ) : ¬ (a < 0) := by apply?
/-- info: Try this: exact Nat.not_succ_le_zero a h -/
#guard_msgs in
example (a : ℕ) (h : a < 0) : False := by apply?

-- An inductive type hides the constructor's arguments enough
-- so that `apply?` doesn't accidentally close the goal.
inductive P : ℕ → Prop
  | gt_in_head {n : ℕ} : n < 0 → P n

-- This lemma with `>` as its head symbol should also be found for goals with head symbol `<`.
theorem lemma_with_gt_in_head (a : ℕ) (h : P a) : 0 > a := by cases h; assumption

-- This lemma with `false` as its head symbols should also be found for goals with head symbol `¬`.
theorem lemma_with_false_in_head (a b : ℕ) (_h1 : a < b) (h2 : P a) : False := by
  apply Nat.not_lt_zero; cases h2; assumption

/-- info: Try this: exact lemma_with_gt_in_head a h -/
#guard_msgs in
example (a : ℕ) (h : P a) : 0 > a := by apply?
/-- info: Try this: exact lemma_with_gt_in_head a h -/
#guard_msgs in
example (a : ℕ) (h : P a) : a < 0 := by apply?

/-- info: Try this: exact lemma_with_false_in_head a b h1 h2 -/
#guard_msgs in
example (a b : ℕ) (h1 : a < b) (h2 : P a) : False := by apply?

-- TODO this no longer works:
-- example (a b : ℕ) (h1 : a < b) : ¬ (P a) := by apply? -- says `exact lemma_with_false_in_head a b h1`

end synonym

/-- info: Try this: exact fun P ↦ iff_not_self -/
#guard_msgs in
example : ∀ P : Prop, ¬(P ↔ ¬P) := by apply?

-- We even find `iff` results:
/-- info: Try this: exact (Nat.dvd_add_left h₁).mp h₂ -/
#guard_msgs in
example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b := by apply?

-- Note: these examples no longer work after we turned off lemmas with discrimination key `#[*]`.
-- example {α : Sort u} (h : Empty) : α := by apply? -- says `exact Empty.elim h`
-- example (f : A → C) (g : B → C) : (A ⊕ B) → C := by apply? -- says `exact Sum.elim f g`
-- example (n : ℕ) (r : ℚ) : ℚ := by apply? using n, r -- exact nsmulRec n r

opaque f : ℕ → ℕ
axiom F (a b : ℕ) : f a ≤ f b ↔ a ≤ b

/-- info: Try this: exact (F a b).mpr h -/
#guard_msgs in
example (a b : ℕ) (h : a ≤ b) : f a ≤ f b := by apply?

/-- info: Try this: exact List.join L -/
#guard_msgs in
example (L _M : List (List ℕ)) : List ℕ := by apply? using L

-- Could be any number of results
#guard_msgs (drop info) in
example (P _Q : List ℕ) (h : ℕ) : List ℕ := by apply? using h, P

-- Could be any number of results
#guard_msgs (drop info) in
example (l : List α) (f : α → β ⊕ γ) : List β × List γ := by
  apply? using f -- partitionMap f l

-- Could be any number of results (`Nat.mul n m`, `Nat.add n m`, etc)
#guard_msgs (drop info) in
example (n m : ℕ) : ℕ := by apply? using n, m

-- Could be any number of results
#guard_msgs (drop info) in
example (P Q : List ℕ) (_h : ℕ) : List ℕ := by apply? using P, Q

-- Check that we don't use sorryAx:
-- (see https://github.com/leanprover-community/mathlib4/issues/226)

theorem Bool_eq_iff {A B : Bool} : (A = B) = (A ↔ B) :=
  by (cases A <;> cases B <;> simp)

/-- info: Try this: exact Bool_eq_iff -/
#guard_msgs in
theorem Bool_eq_iff2 {A B : Bool} : (A = B) = (A ↔ B) :=
  by apply? -- exact Bool_eq_iff

assert_no_sorry Bool_eq_iff2

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/library_search.20regression/near/354025788
/-- info: Try this: exact surjective_quot_mk r -/
#guard_msgs in
example {r : α → α → Prop} : Function.Surjective (Quot.mk r) := by exact?

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/library_search.20failing.20to.20apply.20symm
/-- info: Try this: exact Iff.symm Nat.prime_iff -/
#guard_msgs in
lemma prime_of_prime (n : ℕ) : Prime n ↔ Nat.Prime n := by
  exact?

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/exact.3F.20recent.20regression.3F/near/387691588
lemma ex' (x : ℕ) (_h₁ : x = 0) (h : 2 * 2 ∣ x) : 2 ∣ x := by
  exact? says exact dvd_of_mul_left_dvd h
