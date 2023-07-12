import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.AssertNoSorry
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Quot
import Mathlib.Data.Nat.Prime

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

noncomputable section

example (x : Nat) : x ≠ x.succ := ne_of_lt (by apply?)
example : 0 ≠ 1 + 1 := ne_of_lt (by apply?)
example (x y : Nat) : x + y = y + x := by apply?
example (n m k : Nat) : n ≤ m → n + k ≤ m + k := by apply?
example (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c := by apply?

example (x y : Nat) : True := by
  observe h : x + y = y + x
  guard_hyp h : x + y = y + x
  trivial

example : Int := by apply?

example : x < x + 1 := exact?%

example (P : Prop) (p : P) : P := by apply?
example (P : Prop) (p : P) (np : ¬P) : false := by apply?
example (X : Type) (P : Prop) (x : X) (h : ∀ x : X, x = x → P) : P := by apply?

example (α : Prop) : α → α := by apply? -- says: `exact id`

-- Note: these examples no longer work after we turned off lemmas with discrimination key `#[*]`.
-- example (p : Prop) : (¬¬p) → p := by apply? -- says: `exact not_not.mp`
-- example (a b : Prop) (h : a ∧ b) : a := by apply? -- says: `exact h.left`
-- example (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by apply? -- say: `exact Function.mtr`

example (a b : ℕ) : a + b = b + a :=
by apply? -- says: `exact add_comm a b`

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by apply? -- says: `exact Nat.mul_sub_left_distrib n m k`

example (n m k : ℕ) : n * m - n * k = n * (m - k) :=
by apply? -- says: `exact Eq.symm (mul_tsub n m k)`

example {α : Type} (x y : α) : x = y ↔ y = x := by apply? -- says: `exact eq_comm`

example (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by apply?

-- Verify that if maxHeartbeats is 0 we don't stop immediately.
set_option maxHeartbeats 0 in
example (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by apply?

section synonym

example (a b : ℕ) (ha : a > 0) (_hb : 0 < b) : 0 < a + b := by apply?

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by apply? -- says: `exact Nat.le_of_dvd w h`

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : b ≥ a := by apply? -- says: `exact Nat.le_of_dvd w h`

-- TODO: A lemma with head symbol `¬` can be used to prove `¬ p` or `⊥`
example (a : ℕ) : ¬ (a < 0) := by apply? -- says `exact not_lt_bot`
example (a : ℕ) (h : a < 0) : False := by apply? -- says `exact Nat.not_succ_le_zero a h`

-- An inductive type hides the constructor's arguments enough
-- so that `apply?` doesn't accidentally close the goal.
inductive P : ℕ → Prop
  | gt_in_head {n : ℕ} : n < 0 → P n

-- This lemma with `>` as its head symbol should also be found for goals with head symbol `<`.
theorem lemma_with_gt_in_head (a : ℕ) (h : P a) : 0 > a := by cases h; assumption

-- This lemma with `false` as its head symbols should also be found for goals with head symbol `¬`.
theorem lemma_with_false_in_head (a b : ℕ) (_h1 : a < b) (h2 : P a) : False := by
  apply Nat.not_lt_zero; cases h2; assumption

example (a : ℕ) (h : P a) : 0 > a := by apply? -- says `exact lemma_with_gt_in_head a h`
example (a : ℕ) (h : P a) : a < 0 := by apply? -- says `exact lemma_with_gt_in_head a h`

example (a b : ℕ) (h1 : a < b) (h2 : P a) : False := by apply? -- says `exact lemma_with_false_in_head a b h1 h2`

-- TODO example (a b : ℕ) (h1 : a < b) : ¬ (P a) := by apply? -- says `exact lemma_with_false_in_head a b h1`

end synonym


example : ∀ P : Prop, ¬(P ↔ ¬P) := by apply?

-- We even find `iff` results:
example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b := by apply? -- says `exact (Nat.dvd_add_iff_left h₁).mpr h₂`

-- Note: these examples no longer work after we turned off lemmas with discrimination key `#[*]`.
-- example {α : Sort u} (h : Empty) : α := by apply? -- says `exact Empty.elim h`
-- example (f : A → C) (g : B → C) : (A ⊕ B) → C := by apply? -- says `exact Sum.elim f g`
-- example (n : ℕ) (r : ℚ) : ℚ := by apply? using n, r -- exact nsmulRec n r

opaque f : ℕ → ℕ
axiom F (a b : ℕ) : f a ≤ f b ↔ a ≤ b
example (a b : ℕ) (h : a ≤ b) : f a ≤ f b := by apply?

example (L _M : List (List ℕ)) : List ℕ := by apply? using L

example (P _Q : List ℕ) (h : ℕ) : List ℕ := by apply? using h, P

example (l : List α) (f : α → β ⊕ γ) : List β × List γ := by
  apply? using f -- partitionMap f l

example (n m : ℕ) : ℕ := by apply? using n, m -- exact rightAdd n m

example (P Q : List ℕ) (_h : ℕ) : List ℕ :=
by apply? using P, Q -- exact P ∩ Q

-- Check that we don't use sorryAx:
-- (see https://github.com/leanprover-community/mathlib4/issues/226)

theorem Bool_eq_iff {A B : Bool} : (A = B) = (A ↔ B) :=
  by (cases A <;> cases B <;> simp)

theorem Bool_eq_iff2 {A B : Bool} : (A = B) = (A ↔ B) :=
  by apply? -- exact Bool_eq_iff

assert_no_sorry Bool_eq_iff2

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/library_search.20regression/near/354025788
example {r : α → α → Prop} : Function.Surjective (Quot.mk r) := by exact?

-- Example from https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/library_search.20failing.20to.20apply.20symm
lemma prime_of_prime (n : ℕ) : Prime n ↔ Nat.Prime n := by
  exact?
