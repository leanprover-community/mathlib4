/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.GCongr.CoreAttrs
import Mathlib.Tactic.PushNeg
import Mathlib.Util.AssertExists

/-!
# Basic operations on the natural numbers

This file builds on `Data.Nat.Init` by adding basic lemmas on natural numbers
depending on Mathlib definitions.

See note [foundational algebra order theory].

## TODO

Split this file into:
* `Data.Nat.Init` (or maybe `Data.Nat.Batteries`?) for lemmas that could go to Batteries
* `Data.Nat.Basic` for the lemmas that require mathlib definitions
-/

library_note "foundational algebra order theory"/--
Batteries has a home-baked development of the algebraic and order theoretic theory of `ℕ` and `ℤ
which, in particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness
libraries in mathlib (naturals and integers show up as indices/offsets in lists, cardinality in
finsets, powers in groups, ...).

Less basic uses of `ℕ` and `ℤ` should however use the typeclass-mediated development.

The relevant files are:
* `Data.Nat.Defs` for the continuation of the home-baked development on `ℕ`
* `Data.Int.Defs` for the continuation of the home-baked development on `ℤ`
* `Algebra.Group.Nat` for the monoid instances on `ℕ`
* `Algebra.Group.Int` for the group instance on `ℤ`
* `Algebra.Ring.Nat` for the semiring instance on `ℕ`
* `Algebra.Ring.Int` for the ring instance on `ℤ`
* `Algebra.Order.Group.Nat` for the ordered monoid instance on `ℕ`
* `Algebra.Order.Group.Int` for the ordered group instance on `ℤ`
* `Algebra.Order.Ring.Nat` for the ordered semiring instance on `ℕ`
* `Algebra.Order.Ring.Int` for the ordered ring instance on `ℤ`
-/

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d m n k : ℕ} {p : ℕ → Prop}

-- TODO: Move the `LinearOrder ℕ` instance to `Order.Nat` (https://github.com/leanprover-community/mathlib4/pull/13092).
instance instLinearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance

-- Shortcut instances
instance : Preorder ℕ := inferInstance
instance : PartialOrder ℕ := inferInstance
instance : Min ℕ := inferInstance
instance : Max ℕ := inferInstance
instance : Ord ℕ := inferInstance

instance instNontrivial : Nontrivial ℕ := ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

attribute [gcongr] Nat.succ_le_succ Nat.div_le_div_right Nat.div_le_div_left Nat.div_le_div

/-! ### `succ`, `pred` -/

lemma succ_injective : Injective Nat.succ := @succ.inj

lemma succ_ne_succ : succ m ≠ succ n ↔ m ≠ n := succ_injective.ne_iff

/-! ### `div` -/

protected lemma div_mul_div_le (a b c d : ℕ) :
    (a / b) * (c / d) ≤ (a * c) / (b * d) := by
  if hb : b = 0 then simp [hb] else
  if hd : d = 0 then simp [hd] else
  have hbd : b * d ≠ 0 := Nat.mul_ne_zero hb hd
  rw [le_div_iff_mul_le (Nat.pos_of_ne_zero hbd)]
  transitivity ((a / b) * b) * ((c / d) * d)
  · apply Nat.le_of_eq; simp only [Nat.mul_assoc, Nat.mul_left_comm]
  · apply Nat.mul_le_mul <;> apply div_mul_le_self

/-!
### `pow`

#### TODO

* Rename `Nat.pow_le_pow_of_le_left` to `Nat.pow_le_pow_left`, protect it, remove the alias
* Rename `Nat.pow_le_pow_of_le_right` to `Nat.pow_le_pow_right`, protect it, remove the alias
-/

lemma pow_left_injective (hn : n ≠ 0) : Injective (fun a : ℕ ↦ a ^ n) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

protected lemma pow_right_injective (ha : 2 ≤ a) : Injective (a ^ ·) := by
  simp [Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

protected lemma pow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (pow_left_injective hn).eq_iff
protected lemma pow_right_inj (ha : 2 ≤ a) : a ^ m = a ^ n ↔ m = n :=
  (Nat.pow_right_injective ha).eq_iff

@[simp] protected lemma pow_eq_one : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · simpa [hn] using Nat.pow_left_inj hn (b := 1)

/-- For `a > 1`, `a ^ b = a` iff `b = 1`. -/
lemma pow_eq_self_iff {a b : ℕ} (ha : 1 < a) : a ^ b = a ↔ b = 1 :=
  (Nat.pow_right_injective ha).eq_iff' a.pow_one

@[simp] protected lemma pow_le_one_iff (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  rw [← not_lt, one_lt_pow_iff hn, not_lt]

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

-- Porting note: The type ascriptions of these two lemmas need to be changed,
-- as mathport wrote a lambda that wasn't there in mathlib3, that prevents `simp` applying them.

lemma leRecOn_injective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Injective (@next n)) : Injective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x y H
    rwa [leRecOn_self, leRecOn_self] at H
  | step hnm ih =>
    intro x y H
    rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
    exact ih (Hnext _ H)

lemma leRecOn_surjective {C : ℕ → Sort*} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Surjective (@next n)) : Surjective (@leRecOn C n m hnm next) := by
  induction hnm with
  | refl =>
    intro x
    refine ⟨x, ?_⟩
    rw [leRecOn_self]
  | step hnm ih =>
    intro x
    obtain ⟨w, rfl⟩ := Hnext _ x
    obtain ⟨x, rfl⟩ := ih w
    refine ⟨x, ?_⟩
    rw [leRecOn_succ]


/-- A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n ≥ k`. -/
lemma set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk

/-- A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`. -/
lemma set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)

/-! ### `mod`, `dvd` -/

attribute [simp] Nat.dvd_zero

-- TODO: update `Nat.dvd_sub` in core
lemma dvd_sub' (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n := by
  rcases le_total n m with H | H
  · exact dvd_sub H h₁ h₂
  · rw [Nat.sub_eq_zero_iff_le.mpr H]
    exact Nat.dvd_zero k

end Nat
