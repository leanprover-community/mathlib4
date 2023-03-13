import Mathlib.Tactic.LibrarySearch
import Mathlib.Util.AssertNoSorry
import Mathlib.Algebra.Order.Ring.Canonical

noncomputable section

example (x : Nat) : x ≠ x.succ := ne_of_lt (by library_search)
example : 0 ≠ 1 + 1 := ne_of_lt (by library_search)
example (x y : Nat) : x + y = y + x := by library_search
example (n m k : Nat) : n ≤ m → n + k ≤ m + k := by library_search
example (ha : a > 0) (w : b ∣ c) : a * b ∣ a * c := by library_search

example : Int := by library_search

example : x < x + 1 := library_search%

example (P : Prop) (p : P) : P := by library_search
example (P : Prop) (p : P) (np : ¬P) : false := by library_search
example (X : Type) (P : Prop) (x : X) (h : ∀ x : X, x = x → P) : P := by library_search

example (α : Prop) : α → α := by library_search -- says: `exact id`

example (p : Prop) : (¬¬p) → p := by library_search -- says: `exact not_not.mp`
example (a b : Prop) (h : a ∧ b) : a := by library_search -- says: `exact h.left`

example (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by library_search

example (a b : ℕ) : a + b = b + a :=
by library_search -- says: `exact add_comm a b`

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- says: `exact Nat.mul_sub_left_distrib n m k`

example (n m k : ℕ) : n * m - n * k = n * (m - k) :=
by library_search -- says: `exact Eq.symm (mul_tsub n m k)`

example {α : Type} (x y : α) : x = y ↔ y = x := by library_search -- says: `exact eq_comm`

example (a b : ℕ) (ha : 0 < a) (_hb : 0 < b) : 0 < a + b := by library_search

section synonym

example (a b : ℕ) (ha : a > 0) (_hb : 0 < b) : 0 < a + b := by library_search

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by library_search -- says: `exact Nat.le_of_dvd w h`

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : b ≥ a := by library_search -- says: `exact Nat.le_of_dvd w h`

-- TODO: A lemma with head symbol `¬` can be used to prove `¬ p` or `⊥`
example (a : ℕ) : ¬ (a < 0) := by library_search -- says `exact not_lt_bot`
example (a : ℕ) (h : a < 0) : False := by library_search -- says `exact Nat.not_succ_le_zero a h`

-- An inductive type hides the constructor's arguments enough
-- so that `library_search` doesn't accidentally close the goal.
inductive P : ℕ → Prop
| gt_in_head {n : ℕ} : n < 0 → P n

-- This lemma with `>` as its head symbol should also be found for goals with head symbol `<`.
theorem lemma_with_gt_in_head (a : ℕ) (h : P a) : 0 > a := by cases h; assumption

-- This lemma with `false` as its head symbols should also be found for goals with head symbol `¬`.
theorem lemma_with_false_in_head (a b : ℕ) (_h1 : a < b) (h2 : P a) : False :=
by apply Nat.not_lt_zero; cases h2; assumption

example (a : ℕ) (h : P a) : 0 > a := by library_search -- says `exact lemma_with_gt_in_head a h`
example (a : ℕ) (h : P a) : a < 0 := by library_search -- says `exact lemma_with_gt_in_head a h`

example (a b : ℕ) (h1 : a < b) (h2 : P a) : False := by library_search -- says `exact lemma_with_false_in_head a b h1 h2`

-- TODO example (a b : ℕ) (h1 : a < b) : ¬ (P a) := by library_search -- says `exact lemma_with_false_in_head a b h1`

end synonym


example : ∀ P : Prop, ¬(P ↔ ¬P) := by library_search

-- We even find `iff` results:

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b := by library_search -- says `exact (Nat.dvd_add_iff_left h₁).mpr h₂`

example {α : Sort u} (h : Empty) : α := by library_search
example {α : Type _} (h : Empty) : α := by library_search

example (f : A → C) (g : B → C) : (A ⊕ B) → C := by library_search

opaque f : ℕ → ℕ
axiom F (a b : ℕ) : f a ≤ f b ↔ a ≤ b
example (a b : ℕ) (h : a ≤ b) : f a ≤ f b := by library_search

theorem nonzero_gt_one (n : ℕ) : ¬ n = 0 → n ≥ 1 := by library_search   -- `exact nat.pos_of_ne_zero`

example (L _M : List (List ℕ)) : List ℕ := by library_search using L

example (P _Q : List ℕ) (h : ℕ) : List ℕ := by library_search using h, P

example (l : List α) (f : α → β ⊕ γ) : List β × List γ := by
  library_search using f -- partitionMap f l

example (n m : ℕ) : ℕ := by library_search using n, m -- exact rightAdd n m

example (P Q : List ℕ) (_h : ℕ) : List ℕ :=
by library_search using P, Q -- exact P ∩ Q

example (n : ℕ) (r : ℚ) : ℚ :=
by library_search using n, r -- exact nsmulRec n r

-- Check that we don't use sorryAx:
-- (see https://github.com/leanprover-community/mathlib4/issues/226)

theorem Bool_eq_iff {A B: Bool} : (A = B) = (A ↔ B) :=
  by (cases A <;> cases B <;> simp)

theorem Bool_eq_iff2 {A B: Bool} : (A = B) = (A ↔ B) :=
  by library_search -- exact Bool_eq_iff

assert_no_sorry Bool_eq_iff2
