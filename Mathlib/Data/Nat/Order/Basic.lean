/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits

#align_import data.nat.order.basic from "leanprover-community/mathlib"@"3ed3f98a1e836241990d3d308f1577e434977130"


/-!
# The natural numbers as a linearly ordered commutative semiring

We also have a variety of lemmas which have been deferred from `Data.Nat.Basic` because it is
easier to prove them with this ordered semiring instance available.

You may find that some theorems can be moved back to `Data.Nat.Basic` by modifying their proofs.
-/


universe u v

namespace Nat

/-! ### instances -/

instance orderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
#align nat.order_bot Nat.orderBot

instance linearOrderedCommSemiring : LinearOrderedCommSemiring ℕ :=
  { Nat.commSemiring, Nat.linearOrder with
    lt := Nat.lt, add_le_add_left := @Nat.add_le_add_left,
    le_of_add_le_add_left := @Nat.le_of_add_le_add_left,
    zero_le_one := Nat.le_of_lt (Nat.zero_lt_succ 0),
    mul_lt_mul_of_pos_left := @Nat.mul_lt_mul_of_pos_left,
    mul_lt_mul_of_pos_right := @Nat.mul_lt_mul_of_pos_right,
    exists_pair_ne := ⟨0, 1, ne_of_lt Nat.zero_lt_one⟩ }

instance linearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ :=
  { Nat.linearOrderedCommSemiring, (inferInstance : CommMonoidWithZero ℕ) with
    mul_le_mul_left := fun _ _ h c => Nat.mul_le_mul_left c h }

/-! Extra instances to short-circuit type class resolution and ensure computability -/


-- Not using `inferInstance` avoids `Classical.choice` in the following two
instance linearOrderedSemiring : LinearOrderedSemiring ℕ :=
  inferInstance

instance strictOrderedSemiring : StrictOrderedSemiring ℕ :=
  inferInstance

instance strictOrderedCommSemiring : StrictOrderedCommSemiring ℕ :=
  inferInstance

instance orderedSemiring : OrderedSemiring ℕ :=
  StrictOrderedSemiring.toOrderedSemiring'

instance orderedCommSemiring : OrderedCommSemiring ℕ :=
  StrictOrderedCommSemiring.toOrderedCommSemiring'

instance linearOrderedCancelAddCommMonoid : LinearOrderedCancelAddCommMonoid ℕ :=
  inferInstance

instance canonicallyOrderedCommSemiring : CanonicallyOrderedCommSemiring ℕ :=
  { Nat.nontrivial, Nat.orderBot, (inferInstance : OrderedAddCommMonoid ℕ),
    (inferInstance : LinearOrderedSemiring ℕ), (inferInstance : CommSemiring ℕ) with
    exists_add_of_le := fun {_ _} h => (Nat.le.dest h).imp fun _ => Eq.symm,
    le_self_add := Nat.le_add_right,
    eq_zero_or_eq_zero_of_mul_eq_zero := Nat.eq_zero_of_mul_eq_zero }

instance canonicallyLinearOrderedAddMonoid : CanonicallyLinearOrderedAddMonoid ℕ :=
  { (inferInstance : CanonicallyOrderedAddMonoid ℕ), Nat.linearOrder with }

variable {m n k l : ℕ}

/-! ### Equalities and inequalities involving zero and one -/

theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  Nat.add_one_le_iff.trans pos_iff_ne_zero
#align nat.one_le_iff_ne_zero Nat.one_le_iff_ne_zero

theorem one_lt_iff_ne_zero_and_ne_one : ∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by decide
            -- 🎉 no goals
  | 1 => by decide
            -- 🎉 no goals
  | n + 2 => by simp
                -- 🎉 no goals
#align nat.one_lt_iff_ne_zero_and_ne_one Nat.one_lt_iff_ne_zero_and_ne_one

#align nat.mul_ne_zero Nat.mul_ne_zero

-- Porting note: already in Std
#align nat.mul_eq_zero Nat.mul_eq_zero

--Porting note: removing `simp` attribute
protected theorem zero_eq_mul : 0 = m * n ↔ m = 0 ∨ n = 0 := by rw [eq_comm, Nat.mul_eq_zero]
                                                                -- 🎉 no goals
#align nat.zero_eq_mul Nat.zero_eq_mul

theorem eq_zero_of_double_le (h : 2 * n ≤ n) : n = 0 :=
  add_right_eq_self.mp <| le_antisymm ((two_mul n).symm.trans_le h) le_add_self
#align nat.eq_zero_of_double_le Nat.eq_zero_of_double_le

theorem eq_zero_of_mul_le (hb : 2 ≤ n) (h : n * m ≤ m) : m = 0 :=
  eq_zero_of_double_le <| le_trans (Nat.mul_le_mul_right _ hb) h
#align nat.eq_zero_of_mul_le Nat.eq_zero_of_mul_le

theorem zero_max : max 0 n = n :=
  max_eq_right (zero_le _)
#align nat.zero_max Nat.zero_max

@[simp]
theorem min_eq_zero_iff : min m n = 0 ↔ m = 0 ∨ n = 0 := min_eq_bot
#align nat.min_eq_zero_iff Nat.min_eq_zero_iff

@[simp]
theorem max_eq_zero_iff : max m n = 0 ↔ m = 0 ∧ n = 0 := max_eq_bot
#align nat.max_eq_zero_iff Nat.max_eq_zero_iff

theorem add_eq_max_iff : m + n = max m n ↔ m = 0 ∨ n = 0 := by
  rw [← min_eq_zero_iff]
  -- ⊢ m + n = max m n ↔ min m n = 0
  cases' le_total m n with H H <;> simp [H]
  -- ⊢ m + n = max m n ↔ min m n = 0
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.add_eq_max_iff Nat.add_eq_max_iff

theorem add_eq_min_iff : m + n = min m n ↔ m = 0 ∧ n = 0 := by
  rw [← max_eq_zero_iff]
  -- ⊢ m + n = min m n ↔ max m n = 0
  cases' le_total m n with H H <;> simp [H]
  -- ⊢ m + n = min m n ↔ max m n = 0
                                   -- 🎉 no goals
                                   -- 🎉 no goals
#align nat.add_eq_min_iff Nat.add_eq_min_iff

theorem one_le_of_lt (h : n < m) : 1 ≤ m :=
  lt_of_le_of_lt (Nat.zero_le _) h
#align nat.one_le_of_lt Nat.one_le_of_lt

theorem eq_one_of_mul_eq_one_right (H : m * n = 1) : m = 1 :=
  eq_one_of_dvd_one ⟨n, H.symm⟩
#align nat.eq_one_of_mul_eq_one_right Nat.eq_one_of_mul_eq_one_right

theorem eq_one_of_mul_eq_one_left (H : m * n = 1) : n = 1 :=
  eq_one_of_mul_eq_one_right (by rwa [mul_comm])
                                 -- 🎉 no goals
#align nat.eq_one_of_mul_eq_one_left Nat.eq_one_of_mul_eq_one_left

/-! ### `succ` -/


theorem two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by simp
            -- 🎉 no goals
  | 1 => by simp
            -- 🎉 no goals
  | n + 2 => by simp
                -- 🎉 no goals
#align nat.two_le_iff Nat.two_le_iff

@[simp]
theorem lt_one_iff {n : ℕ} : n < 1 ↔ n = 0 :=
  lt_succ_iff.trans nonpos_iff_eq_zero
#align nat.lt_one_iff Nat.lt_one_iff

/-! ### `add` -/

#align nat.add_pos_left Nat.add_pos_left
#align nat.add_pos_right Nat.add_pos_right

theorem add_pos_iff_pos_or_pos (m n : ℕ) : 0 < m + n ↔ 0 < m ∨ 0 < n :=
  Iff.intro
    (by
      intro h
      -- ⊢ 0 < m ∨ 0 < n
      cases' m with m
      -- ⊢ 0 < zero ∨ 0 < n
      · simp [zero_add] at h
        -- ⊢ 0 < zero ∨ 0 < n
        exact Or.inr h
        -- 🎉 no goals
      exact Or.inl (succ_pos _))
      -- 🎉 no goals
    (by
      intro h; cases' h with mpos npos
      -- ⊢ 0 < m + n
               -- ⊢ 0 < m + n
      · apply add_pos_left mpos
        -- 🎉 no goals
      apply add_pos_right _ npos)
      -- 🎉 no goals
#align nat.add_pos_iff_pos_or_pos Nat.add_pos_iff_pos_or_pos

theorem add_eq_one_iff : m + n = 1 ↔ m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 := by
  cases n <;> simp [succ_eq_add_one, ← add_assoc, succ_inj']
  -- ⊢ m + zero = 1 ↔ m = 0 ∧ zero = 1 ∨ m = 1 ∧ zero = 0
              -- 🎉 no goals
              -- 🎉 no goals
#align nat.add_eq_one_iff Nat.add_eq_one_iff

theorem add_eq_two_iff : m + n = 2 ↔ m = 0 ∧ n = 2 ∨ m = 1 ∧ n = 1 ∨ m = 2 ∧ n = 0 := by
  cases n <;>
  -- ⊢ m + zero = 2 ↔ m = 0 ∧ zero = 2 ∨ m = 1 ∧ zero = 1 ∨ m = 2 ∧ zero = 0
  simp [(succ_ne_zero 1).symm, (show 2 = Nat.succ 1 from rfl),
    succ_eq_add_one, ← add_assoc, succ_inj', add_eq_one_iff]
#align nat.add_eq_two_iff Nat.add_eq_two_iff

theorem add_eq_three_iff :
    m + n = 3 ↔ m = 0 ∧ n = 3 ∨ m = 1 ∧ n = 2 ∨ m = 2 ∧ n = 1 ∨ m = 3 ∧ n = 0 := by
  cases n <;>
  -- ⊢ m + zero = 3 ↔ m = 0 ∧ zero = 3 ∨ m = 1 ∧ zero = 2 ∨ m = 2 ∧ zero = 1 ∨ m =  …
  simp [(succ_ne_zero 1).symm, succ_eq_add_one, (show 3 = Nat.succ 2 from rfl),
    ← add_assoc, succ_inj', add_eq_two_iff]
#align nat.add_eq_three_iff Nat.add_eq_three_iff

theorem le_add_one_iff : m ≤ n + 1 ↔ m ≤ n ∨ m = n + 1 :=
  ⟨fun h =>
    match Nat.eq_or_lt_of_le h with
    | Or.inl h => Or.inr h
    | Or.inr h => Or.inl <| Nat.le_of_succ_le_succ h,
    Or.rec (fun h => le_trans h <| Nat.le_add_right _ _) le_of_eq⟩
#align nat.le_add_one_iff Nat.le_add_one_iff

theorem le_and_le_add_one_iff : n ≤ m ∧ m ≤ n + 1 ↔ m = n ∨ m = n + 1 := by
  rw [le_add_one_iff, and_or_left, ← le_antisymm_iff, eq_comm, and_iff_right_of_imp]
  -- ⊢ m = n + 1 → n ≤ m
  rintro rfl
  -- ⊢ n ≤ n + 1
  exact n.le_succ
  -- 🎉 no goals
#align nat.le_and_le_add_one_iff Nat.le_and_le_add_one_iff

theorem add_succ_lt_add (hab : m < n) (hcd : k < l) : m + k + 1 < n + l := by
  rw [add_assoc]
  -- ⊢ m + (k + 1) < n + l
  exact add_lt_add_of_lt_of_le hab (Nat.succ_le_iff.2 hcd)
  -- 🎉 no goals
#align nat.add_succ_lt_add Nat.add_succ_lt_add

/-! ### `pred` -/


theorem pred_le_iff : pred m ≤ n ↔ m ≤ succ n :=
  ⟨le_succ_of_pred_le, by
    cases m
    -- ⊢ zero ≤ succ n → pred zero ≤ n
    · exact fun _ => zero_le n
      -- 🎉 no goals
    exact le_of_succ_le_succ⟩
    -- 🎉 no goals
#align nat.pred_le_iff Nat.pred_le_iff

/-! ### `sub`

Most lemmas come from the `OrderedSub` instance on `ℕ`. -/


instance : OrderedSub ℕ := by
  constructor
  -- ⊢ ∀ (a b c : ℕ), a - b ≤ c ↔ a ≤ c + b
  intro m n k
  -- ⊢ m - n ≤ k ↔ m ≤ k + n
  induction' n with n ih generalizing k
  -- ⊢ m - zero ≤ k ↔ m ≤ k + zero
  · simp
    -- 🎉 no goals
  · simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]
    -- 🎉 no goals

theorem lt_pred_iff : n < pred m ↔ succ n < m :=
  show n < m - 1 ↔ n + 1 < m from lt_tsub_iff_right
#align nat.lt_pred_iff Nat.lt_pred_iff

theorem lt_of_lt_pred (h : m < n - 1) : m < n :=
  lt_of_succ_lt (lt_pred_iff.1 h)
#align nat.lt_of_lt_pred Nat.lt_of_lt_pred

theorem le_or_le_of_add_eq_add_pred (h : k + l = m + n - 1) : m ≤ k ∨ n ≤ l := by
  cases' le_or_lt m k with h' h' <;> [left; right]
  -- ⊢ m ≤ k
  · exact h'
    -- 🎉 no goals
  · replace h' := add_lt_add_right h' l
    -- ⊢ n ≤ l
    rw [h] at h'
    -- ⊢ n ≤ l
    cases' n.eq_zero_or_pos with hn hn
    -- ⊢ n ≤ l
    · rw [hn]
      -- ⊢ 0 ≤ l
      exact zero_le l
      -- 🎉 no goals
    rw [n.add_sub_assoc (Nat.succ_le_of_lt hn), add_lt_add_iff_left] at h'
    -- ⊢ n ≤ l
    exact Nat.le_of_pred_lt h'
    -- 🎉 no goals
#align nat.le_or_le_of_add_eq_add_pred Nat.le_or_le_of_add_eq_add_pred

/-- A version of `Nat.sub_succ` in the form `_ - 1` instead of `Nat.pred _`. -/
theorem sub_succ' (m n : ℕ) : m - n.succ = m - n - 1 :=
  rfl
#align nat.sub_succ' Nat.sub_succ'

/-! ### `mul` -/

theorem succ_mul_pos (m : ℕ) (hn : 0 < n) : 0 < succ m * n :=
  mul_pos (succ_pos m) hn
#align nat.succ_mul_pos Nat.succ_mul_pos

theorem mul_self_le_mul_self (h : m ≤ n) : m * m ≤ n * n :=
  mul_le_mul h h (zero_le _) (zero_le _)
#align nat.mul_self_le_mul_self Nat.mul_self_le_mul_self

theorem mul_self_lt_mul_self : ∀ {m n : ℕ}, m < n → m * m < n * n
  | 0, _, h => mul_pos h h
  | succ _, _, h => mul_lt_mul h (le_of_lt h) (succ_pos _) (zero_le _)
#align nat.mul_self_lt_mul_self Nat.mul_self_lt_mul_self

theorem mul_self_le_mul_self_iff : m ≤ n ↔ m * m ≤ n * n :=
  ⟨mul_self_le_mul_self, le_imp_le_of_lt_imp_lt mul_self_lt_mul_self⟩
#align nat.mul_self_le_mul_self_iff Nat.mul_self_le_mul_self_iff

theorem mul_self_lt_mul_self_iff : m < n ↔ m * m < n * n :=
  le_iff_le_iff_lt_iff_lt.1 mul_self_le_mul_self_iff
#align nat.mul_self_lt_mul_self_iff Nat.mul_self_lt_mul_self_iff

theorem le_mul_self : ∀ n : ℕ, n ≤ n * n
  | 0 => le_rfl
  | n + 1 => by simp
                -- 🎉 no goals
#align nat.le_mul_self Nat.le_mul_self

theorem le_mul_of_pos_left (h : 0 < n) : m ≤ n * m := by
  conv =>
    lhs
    rw [← one_mul m]
  exact mul_le_mul_of_nonneg_right h.nat_succ_le (zero_le _)
  -- 🎉 no goals
#align nat.le_mul_of_pos_left Nat.le_mul_of_pos_left

theorem le_mul_of_pos_right (h : 0 < n) : m ≤ m * n := by
  conv =>
    lhs
    rw [← mul_one m]
  exact mul_le_mul_of_nonneg_left h.nat_succ_le (zero_le _)
  -- 🎉 no goals
#align nat.le_mul_of_pos_right Nat.le_mul_of_pos_right

theorem mul_self_inj : m * m = n * n ↔ m = n :=
  le_antisymm_iff.trans
    (le_antisymm_iff.trans (and_congr mul_self_le_mul_self_iff mul_self_le_mul_self_iff)).symm
#align nat.mul_self_inj Nat.mul_self_inj

theorem le_add_pred_of_pos (n : ℕ) {i : ℕ} (hi : i ≠ 0) : n ≤ i + (n - 1) := by
  refine le_trans ?_ add_tsub_le_assoc
  -- ⊢ n ≤ i + n - 1
  simp [add_comm, Nat.add_sub_assoc, one_le_iff_ne_zero.2 hi]
  -- 🎉 no goals
#align nat.le_add_pred_of_pos Nat.le_add_pred_of_pos

@[simp]
theorem lt_mul_self_iff : ∀ {n : ℕ}, n < n * n ↔ 1 < n
  | 0 => iff_of_false (lt_irrefl _) zero_le_one.not_lt
  | n + 1 => lt_mul_iff_one_lt_left n.succ_pos
#align nat.lt_mul_self_iff Nat.lt_mul_self_iff

theorem add_sub_one_le_mul (hm : m ≠ 0) (hn : n ≠ 0) : m + n - 1 ≤ m * n := by
  cases m
  -- ⊢ zero + n - 1 ≤ zero * n
  · cases hm rfl
    -- 🎉 no goals
  · rw [succ_add, succ_sub_one, succ_mul]
    -- ⊢ n✝ + n ≤ n✝ * n + n
    exact add_le_add_right (le_mul_of_one_le_right' $ succ_le_iff.2 $ pos_iff_ne_zero.2 hn) _
    -- 🎉 no goals
#align nat.add_sub_one_le_mul Nat.add_sub_one_le_mul

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/


/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_elim]
theorem diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
    (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) : ∀ a b, a < b → P a b
  | 0, b + 1, _ => hb _
  | a + 1, b + 1, h => by
    apply hd _ _ ((add_lt_add_iff_right _).1 h)
    -- ⊢ P (a + 1) b
    · have this : a + 1 = b ∨ a + 1 < b := by rwa [← le_iff_eq_or_lt, ← Nat.lt_succ_iff]
      -- ⊢ P (a + 1) b
      have wf : (a + 1) + b < (a + 1) + (b + 1) := by simp
      -- ⊢ P (a + 1) b
      rcases this with (rfl | h)
      -- ⊢ P (a + 1) (a + 1)
      · exact ha _
        -- 🎉 no goals
      apply diag_induction P ha hb hd (a + 1) b h
      -- 🎉 no goals
    have _ : a + (b + 1) < (a + 1) + (b + 1) := by simp
    -- ⊢ P a (b + 1)
    apply diag_induction P ha hb hd a (b + 1)
    -- ⊢ a < b + 1
    apply lt_of_le_of_lt (Nat.le_succ _) h
    -- 🎉 no goals
  termination_by _ a b c => a + b
  decreasing_by { assumption }
                -- 🎉 no goals
                -- 🎉 no goals
#align nat.diag_induction Nat.diag_induction

/-- A subset of `ℕ` containing `k : ℕ` and closed under `Nat.succ` contains every `n ≥ k`. -/
theorem set_induction_bounded {S : Set ℕ} (hk : k ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S)
    (hnk : k ≤ n) : n ∈ S :=
  @leRecOn (fun n => n ∈ S) k n hnk @h_ind hk
#align nat.set_induction_bounded Nat.set_induction_bounded

/-- A subset of `ℕ` containing zero and closed under `Nat.succ` contains all of `ℕ`. -/
theorem set_induction {S : Set ℕ} (hb : 0 ∈ S) (h_ind : ∀ k : ℕ, k ∈ S → k + 1 ∈ S) (n : ℕ) :
    n ∈ S :=
  set_induction_bounded hb h_ind (zero_le n)
#align nat.set_induction Nat.set_induction

/-! ### `div` -/


protected theorem div_le_of_le_mul' (h : m ≤ k * n) : m / k ≤ n :=
  (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0, Nat.div_zero]; apply zero_le) fun k0 =>
                                            -- ⊢ 0 ≤ n
                                                                   -- 🎉 no goals
    le_of_mul_le_mul_left
      (calc
        k * (m / k) ≤ m % k + k * (m / k) := Nat.le_add_left _ _
        _ = m := mod_add_div _ _
        _ ≤ k * n := h) k0
#align nat.div_le_of_le_mul' Nat.div_le_of_le_mul'

protected theorem div_le_self' (m n : ℕ) : m / n ≤ m :=
  (Nat.eq_zero_or_pos n).elim (fun n0 => by rw [n0, Nat.div_zero]; apply zero_le) fun n0 =>
                                            -- ⊢ 0 ≤ m
                                                                   -- 🎉 no goals
    Nat.div_le_of_le_mul' <|
      calc
        m = 1 * m := (one_mul _).symm
        _ ≤ n * m := Nat.mul_le_mul_right _ n0
#align nat.div_le_self' Nat.div_le_self'

protected theorem div_lt_of_lt_mul (h : m < n * k) : m / n < k :=
  lt_of_mul_lt_mul_left
    (calc
      n * (m / n) ≤ m % n + n * (m / n) := Nat.le_add_left _ _
      _ = m := mod_add_div _ _
      _ < n * k := h
      )
    (Nat.zero_le n)
#align nat.div_lt_of_lt_mul Nat.div_lt_of_lt_mul

theorem eq_zero_of_le_div (hn : 2 ≤ n) (h : m ≤ m / n) : m = 0 :=
  eq_zero_of_mul_le hn <| by
    rw [mul_comm]; exact (Nat.le_div_iff_mul_le' (lt_of_lt_of_le (by decide) hn)).1 h
    -- ⊢ m * n ≤ m
                   -- 🎉 no goals
#align nat.eq_zero_of_le_div Nat.eq_zero_of_le_div

theorem div_mul_div_le_div (m n k : ℕ) : m / k * n / m ≤ n / k :=
  if hm0 : m = 0 then by simp [hm0]
                         -- 🎉 no goals
  else
    calc
      m / k * n / m ≤ n * m / k / m :=
        Nat.div_le_div_right (by rw [mul_comm]; exact mul_div_le_mul_div_assoc _ _ _)
                                 -- ⊢ n * (m / k) ≤ n * m / k
                                                -- 🎉 no goals
      _ = n / k := by
        { rw [Nat.div_div_eq_div_mul, mul_comm n, mul_comm k,
            Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hm0)] }
#align nat.div_mul_div_le_div Nat.div_mul_div_le_div

theorem eq_zero_of_le_half (h : n ≤ n / 2) : n = 0 :=
  eq_zero_of_le_div le_rfl h
#align nat.eq_zero_of_le_half Nat.eq_zero_of_le_half

theorem mul_div_mul_comm_of_dvd_dvd (hmk : k ∣ m) (hnl : l ∣ n) :
    m * n / (k * l) = m / k * (n / l) := by
  rcases k.eq_zero_or_pos with (rfl | hk0); · simp
  -- ⊢ m * n / (0 * l) = m / 0 * (n / l)
                                              -- 🎉 no goals
  rcases l.eq_zero_or_pos with (rfl | hl0); · simp
  -- ⊢ m * n / (k * 0) = m / k * (n / 0)
                                              -- 🎉 no goals
  obtain ⟨_, rfl⟩ := hmk
  -- ⊢ k * w✝ * n / (k * l) = k * w✝ / k * (n / l)
  obtain ⟨_, rfl⟩ := hnl
  -- ⊢ k * w✝¹ * (l * w✝) / (k * l) = k * w✝¹ / k * (l * w✝ / l)
  rw [mul_mul_mul_comm, Nat.mul_div_cancel_left _ hk0, Nat.mul_div_cancel_left _ hl0,
    Nat.mul_div_cancel_left _ (mul_pos hk0 hl0)]
#align nat.mul_div_mul_comm_of_dvd_dvd Nat.mul_div_mul_comm_of_dvd_dvd

theorem le_half_of_half_lt_sub {a b : ℕ} (h : a / 2 < a - b) : b ≤ a / 2 := by
  rw [Nat.le_div_iff_mul_le two_pos]
  -- ⊢ b * 2 ≤ a
  rw [Nat.div_lt_iff_lt_mul two_pos, Nat.mul_sub_right_distrib, lt_tsub_iff_right, mul_two a] at h
  -- ⊢ b * 2 ≤ a
  exact le_of_lt (Nat.lt_of_add_lt_add_left h)
  -- 🎉 no goals
#align nat.le_half_of_half_lt_sub Nat.le_half_of_half_lt_sub

theorem half_le_of_sub_le_half {a b : ℕ} (h : a - b ≤ a / 2) : a / 2 ≤ b := by
  rw [Nat.le_div_iff_mul_le two_pos, Nat.mul_sub_right_distrib, tsub_le_iff_right, mul_two,
    add_le_add_iff_left] at h
  rw [← Nat.mul_div_left b two_pos]
  -- ⊢ a / 2 ≤ b * 2 / 2
  exact Nat.div_le_div_right h
  -- 🎉 no goals
#align nat.half_le_of_sub_le_half Nat.half_le_of_sub_le_half

/-! ### `mod`, `dvd` -/


theorem two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  conv =>
    rhs
    rw [← Nat.mod_add_div n 2, hn, @add_tsub_cancel_left]
#align nat.two_mul_odd_div_two Nat.two_mul_odd_div_two

theorem div_dvd_of_dvd (h : n ∣ m) : m / n ∣ m :=
  ⟨n, (Nat.div_mul_cancel h).symm⟩
#align nat.div_dvd_of_dvd Nat.div_dvd_of_dvd

protected theorem div_div_self (h : n ∣ m) (hm : m ≠ 0) : m / (m / n) = n := by
  rcases h with ⟨_, rfl⟩
  -- ⊢ n * w✝ / (n * w✝ / n) = n
  rw [mul_ne_zero_iff] at hm
  -- ⊢ n * w✝ / (n * w✝ / n) = n
  rw [mul_div_right _ (Nat.pos_of_ne_zero hm.1), mul_div_left _ (Nat.pos_of_ne_zero hm.2)]
  -- 🎉 no goals
#align nat.div_div_self Nat.div_div_self

--Porting note: later `simp [mod_zero]` can be changed to `simp` once `mod_zero` is given
--a `simp` attribute.
theorem mod_mul_right_div_self (m n k : ℕ) : m % (n * k) / n = m / n % k := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn); simp [mod_zero]
  -- ⊢ m % (0 * k) / 0 = m / 0 % k
                                               -- ⊢ m % (n * k) / n = m / n % k
  rcases Nat.eq_zero_or_pos k with (rfl | hk); simp [mod_zero]
  -- ⊢ m % (n * 0) / n = m / n % 0
                                               -- ⊢ m % (n * k) / n = m / n % k
  conv_rhs => rw [← mod_add_div m (n * k)]
  -- ⊢ m % (n * k) / n = (m % (n * k) + n * k * (m / (n * k))) / n % k
  rw [mul_assoc, add_mul_div_left _ _ hn, add_mul_mod_self_left,
    mod_eq_of_lt (Nat.div_lt_of_lt_mul (mod_lt _ (mul_pos hn hk)))]
#align nat.mod_mul_right_div_self Nat.mod_mul_right_div_self

theorem mod_mul_left_div_self (m n k : ℕ) : m % (k * n) / n = m / n % k := by
  rw [mul_comm k, mod_mul_right_div_self]
  -- 🎉 no goals
#align nat.mod_mul_left_div_self Nat.mod_mul_left_div_self

theorem not_dvd_of_pos_of_lt (h1 : 0 < n) (h2 : n < m) : ¬m ∣ n := by
  rintro ⟨k, rfl⟩
  -- ⊢ False
  rcases Nat.eq_zero_or_pos k with (rfl | hk)
  -- ⊢ False
  · exact lt_irrefl 0 h1
    -- 🎉 no goals
  · exact not_lt.2 (le_mul_of_pos_right hk) h2
    -- 🎉 no goals
#align nat.not_dvd_of_pos_of_lt Nat.not_dvd_of_pos_of_lt

/-- If `m` and `n` are equal mod `k`, `m - n` is zero mod `k`. -/
theorem sub_mod_eq_zero_of_mod_eq (h : m % k = n % k) : (m - n) % k = 0 := by
  rw [← Nat.mod_add_div m k, ← Nat.mod_add_div n k, ← h, tsub_add_eq_tsub_tsub,
    @add_tsub_cancel_left, ← mul_tsub k, Nat.mul_mod_right]
#align nat.sub_mod_eq_zero_of_mod_eq Nat.sub_mod_eq_zero_of_mod_eq

@[simp]
theorem one_mod (n : ℕ) : 1 % (n + 2) = 1 :=
  Nat.mod_eq_of_lt (add_lt_add_right n.succ_pos 1)
#align nat.one_mod Nat.one_mod

theorem dvd_sub_mod (k : ℕ) : n ∣ k - k % n :=
  ⟨k / n, tsub_eq_of_eq_add_rev (Nat.mod_add_div k n).symm⟩
#align nat.dvd_sub_mod Nat.dvd_sub_mod

theorem add_mod_eq_ite :
    (m + n) % k = if k ≤ m % k + n % k then m % k + n % k - k else m % k + n % k := by
  cases k; simp [mod_zero]
  -- ⊢ (m + n) % zero = if zero ≤ m % zero + n % zero then m % zero + n % zero - ze …
           -- ⊢ (m + n) % succ n✝ = if succ n✝ ≤ m % succ n✝ + n % succ n✝ then m % succ n✝  …
  rw [Nat.add_mod]
  -- ⊢ (m % succ n✝ + n % succ n✝) % succ n✝ = if succ n✝ ≤ m % succ n✝ + n % succ  …
  split_ifs with h
  -- ⊢ (m % succ n✝ + n % succ n✝) % succ n✝ = m % succ n✝ + n % succ n✝ - succ n✝
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt]
    -- ⊢ m % succ n✝ + n % succ n✝ - succ n✝ < succ n✝
    exact
      (tsub_lt_iff_right h).mpr (Nat.add_lt_add (m.mod_lt (zero_lt_succ _))
        (n.mod_lt (zero_lt_succ _)))
  · exact Nat.mod_eq_of_lt (lt_of_not_ge h)
    -- 🎉 no goals
#align nat.add_mod_eq_ite Nat.add_mod_eq_ite

theorem div_mul_div_comm (hmn : n ∣ m) (hkl : l ∣ k) : m / n * (k / l) = m * k / (n * l) :=
  have exi1 : ∃ x, m = n * x := hmn
  have exi2 : ∃ y, k = l * y := hkl
  if hn : n = 0 then by simp [hn]
                        -- 🎉 no goals
  else
    have : 0 < n := Nat.pos_of_ne_zero hn
    if hl : l = 0 then by simp [hl]
                          -- 🎉 no goals
    else by
      have : 0 < l := Nat.pos_of_ne_zero hl
      -- ⊢ m / n * (k / l) = m * k / (n * l)
      cases' exi1 with x hx
      -- ⊢ m / n * (k / l) = m * k / (n * l)
      cases' exi2 with y hy
      -- ⊢ m / n * (k / l) = m * k / (n * l)
      rw [hx, hy, Nat.mul_div_cancel_left, Nat.mul_div_cancel_left]
      apply Eq.symm
      apply Nat.div_eq_of_eq_mul_left
      apply mul_pos
      repeat' assumption
      -- ⊢ n * x * (l * y) = x * y * (n * l)
      -- Porting note: this line was `cc` in Lean3
      simp only [mul_comm, mul_left_comm, mul_assoc]
      -- 🎉 no goals
#align nat.div_mul_div_comm Nat.div_mul_div_comm

theorem div_eq_self : m / n = m ↔ m = 0 ∨ n = 1 := by
  constructor
  -- ⊢ m / n = m → m = 0 ∨ n = 1
  · intro
    -- ⊢ m = 0 ∨ n = 1
    match n with
    | 0 => simp_all
    | 1 =>
      right
      rfl
    | n+2 =>
      left
      have : m / (n + 2) ≤ m / 2 := div_le_div_left (by simp) (by decide)
      refine eq_zero_of_le_half ?_
      simp_all
  · rintro (rfl | rfl) <;> simp
    -- ⊢ 0 / n = 0
                           -- 🎉 no goals
                           -- 🎉 no goals
#align nat.div_eq_self Nat.div_eq_self

theorem div_eq_sub_mod_div : m / n = (m - m % n) / n := by
  by_cases n0 : n = 0
  -- ⊢ m / n = (m - m % n) / n
  · rw [n0, Nat.div_zero, Nat.div_zero]
    -- 🎉 no goals
  · have : m - m % n = n * (m / n) := by
      rw [tsub_eq_iff_eq_add_of_le (Nat.mod_le _ _), add_comm, mod_add_div]
    rw [this, mul_div_right _ (Nat.pos_of_ne_zero n0)]
    -- 🎉 no goals
#align nat.div_eq_sub_mod_div Nat.div_eq_sub_mod_div

/-- `m` is not divisible by `n` if it is between `n * k` and `n * (k + 1)` for some `k`. -/
theorem not_dvd_of_between_consec_multiples (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  rintro ⟨d, rfl⟩
  -- ⊢ False
  exact Monotone.ne_of_lt_of_lt_nat (Covariant.monotone_of_const n) k h1 h2 d rfl
  -- 🎉 no goals
#align nat.not_dvd_of_between_consec_multiples Nat.not_dvd_of_between_consec_multiples

/-! ### `find` -/


section Find

variable {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]

--Porting note: removing `simp` attribute as `simp` can prove it
theorem find_pos (h : ∃ n : ℕ, p n) : 0 < Nat.find h ↔ ¬p 0 := by
  rw [pos_iff_ne_zero, Ne, Nat.find_eq_zero]
  -- 🎉 no goals
#align nat.find_pos Nat.find_pos

theorem find_add {hₘ : ∃ m, p (m + n)} {hₙ : ∃ n, p n} (hn : n ≤ Nat.find hₙ) :
    Nat.find hₘ + n = Nat.find hₙ := by
  refine ((le_find_iff _ _).2 fun m hm hpm => hm.not_le ?_).antisymm ?_
  -- ⊢ Nat.find hₘ + n ≤ m
  · have hnm : n ≤ m := hn.trans (find_le hpm)
    -- ⊢ Nat.find hₘ + n ≤ m
    refine add_le_of_le_tsub_right_of_le hnm (find_le ?_)
    -- ⊢ p (m - n + n)
    rwa [tsub_add_cancel_of_le hnm]
    -- 🎉 no goals
  · rw [← tsub_le_iff_right]
    -- ⊢ Nat.find hₙ - n ≤ Nat.find hₘ
    refine (le_find_iff _ _).2 fun m hm hpm => hm.not_le ?_
    -- ⊢ Nat.find hₙ - n ≤ m
    rw [tsub_le_iff_right]
    -- ⊢ Nat.find hₙ ≤ m + n
    exact find_le hpm
    -- 🎉 no goals
#align nat.find_add Nat.find_add

end Find

/-! ### `find_greatest` -/


section FindGreatest

variable {P Q : ℕ → Prop} [DecidablePred P]

theorem findGreatest_eq_iff :
    Nat.findGreatest P k = m ↔ m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n⦄, m < n → n ≤ k → ¬P n := by
  induction' k with k ihk generalizing m
  -- ⊢ Nat.findGreatest P zero = m ↔ m ≤ zero ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n →  …
  · rw [eq_comm, Iff.comm]
    -- ⊢ (m ≤ zero ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ zero → ¬P n) ↔ m = Nat.fi …
    simp only [zero_eq, nonpos_iff_eq_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    -- ⊢ m = 0 → (¬m = 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n = 0 → ¬P n
    rintro rfl
    -- ⊢ (¬0 = 0 → P 0) ∧ ∀ ⦃n : ℕ⦄, 0 < n → n = 0 → ¬P n
    exact ⟨fun h => (h rfl).elim, fun n hlt heq => (hlt.ne heq.symm).elim⟩
    -- 🎉 no goals
  · by_cases hk : P (k + 1)
    -- ⊢ Nat.findGreatest P (succ k) = m ↔ m ≤ succ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m  …
    · rw [findGreatest_eq hk]
      -- ⊢ k + 1 = m ↔ m ≤ succ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ succ k → ¬P n
      constructor
      -- ⊢ k + 1 = m → m ≤ succ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ succ k → ¬P n
      · rintro rfl
        -- ⊢ k + 1 ≤ succ k ∧ (k + 1 ≠ 0 → P (k + 1)) ∧ ∀ ⦃n : ℕ⦄, k + 1 < n → n ≤ succ k …
        exact ⟨le_rfl, fun _ => hk, fun n hlt hle => (hlt.not_le hle).elim⟩
        -- 🎉 no goals
      · rintro ⟨hle, h0, hm⟩
        -- ⊢ k + 1 = m
        rcases Decidable.eq_or_lt_of_le hle with (rfl | hlt)
        -- ⊢ k + 1 = succ k
        exacts [rfl, (hm hlt le_rfl hk).elim]
        -- 🎉 no goals
    · rw [findGreatest_of_not hk, ihk]
      -- ⊢ (m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ k → ¬P n) ↔ m ≤ succ k ∧ (m  …
      constructor
      -- ⊢ (m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ k → ¬P n) → m ≤ succ k ∧ (m  …
      · rintro ⟨hle, hP, hm⟩
        -- ⊢ m ≤ succ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ succ k → ¬P n
        refine ⟨hle.trans k.le_succ, hP, fun n hlt hle => ?_⟩
        -- ⊢ ¬P n
        rcases Decidable.eq_or_lt_of_le hle with (rfl | hlt')
        -- ⊢ ¬P (succ k)
        exacts [hk, hm hlt <| lt_succ_iff.1 hlt']
        -- 🎉 no goals
      · rintro ⟨hle, hP, hm⟩
        -- ⊢ m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n : ℕ⦄, m < n → n ≤ k → ¬P n
        refine ⟨lt_succ_iff.1 (hle.lt_of_ne ?_), hP, fun n hlt hle => hm hlt (hle.trans k.le_succ)⟩
        -- ⊢ m ≠ succ k
        rintro rfl
        -- ⊢ False
        exact hk (hP k.succ_ne_zero)
        -- 🎉 no goals
#align nat.find_greatest_eq_iff Nat.findGreatest_eq_iff

theorem findGreatest_eq_zero_iff : Nat.findGreatest P k = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ k → ¬P n := by
  simp [findGreatest_eq_iff]
  -- 🎉 no goals
#align nat.find_greatest_eq_zero_iff Nat.findGreatest_eq_zero_iff

theorem findGreatest_spec (hmb : m ≤ n) (hm : P m) : P (Nat.findGreatest P n) := by
  by_cases h : Nat.findGreatest P n = 0
  -- ⊢ P (Nat.findGreatest P n)
  · cases m
    -- ⊢ P (Nat.findGreatest P n)
    · rwa [h]
      -- 🎉 no goals
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
    -- 🎉 no goals
  · exact (findGreatest_eq_iff.1 rfl).2.1 h
    -- 🎉 no goals
#align nat.find_greatest_spec Nat.findGreatest_spec

theorem findGreatest_le (n : ℕ) : Nat.findGreatest P n ≤ n :=
  (findGreatest_eq_iff.1 rfl).1
#align nat.find_greatest_le Nat.findGreatest_le

theorem le_findGreatest (hmb : m ≤ n) (hm : P m) : m ≤ Nat.findGreatest P n :=
  le_of_not_lt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm
#align nat.le_find_greatest Nat.le_findGreatest

theorem findGreatest_mono_right (P : ℕ → Prop) [DecidablePred P] :
    Monotone (Nat.findGreatest P) := by
  refine monotone_nat_of_le_succ fun n => ?_
  -- ⊢ Nat.findGreatest P n ≤ Nat.findGreatest P (n + 1)
  rw [findGreatest_succ]
  -- ⊢ Nat.findGreatest P n ≤ if P (n + 1) then n + 1 else Nat.findGreatest P n
  split_ifs
  -- ⊢ Nat.findGreatest P n ≤ n + 1
  · exact (findGreatest_le n).trans (le_succ _)
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align nat.find_greatest_mono_right Nat.findGreatest_mono_right

theorem findGreatest_mono_left [DecidablePred Q] (hPQ : P ≤ Q) :
    Nat.findGreatest P ≤ Nat.findGreatest Q := by
  intro n
  -- ⊢ Nat.findGreatest P n ≤ Nat.findGreatest Q n
  induction' n with n hn
  -- ⊢ Nat.findGreatest P zero ≤ Nat.findGreatest Q zero
  · rfl
    -- 🎉 no goals
  by_cases h : P (n + 1)
  -- ⊢ Nat.findGreatest P (succ n) ≤ Nat.findGreatest Q (succ n)
  · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
    -- 🎉 no goals
  · rw [findGreatest_of_not h]
    -- ⊢ Nat.findGreatest P n ≤ Nat.findGreatest Q (succ n)
    exact hn.trans (Nat.findGreatest_mono_right _ <| le_succ _)
    -- 🎉 no goals
#align nat.find_greatest_mono_left Nat.findGreatest_mono_left

theorem findGreatest_mono [DecidablePred Q] (hPQ : P ≤ Q) (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest Q n :=
  (Nat.findGreatest_mono_right _ hmn).trans <| findGreatest_mono_left hPQ _
#align nat.find_greatest_mono Nat.findGreatest_mono

theorem findGreatest_is_greatest (hk : Nat.findGreatest P n < k) (hkb : k ≤ n) : ¬P k :=
  (findGreatest_eq_iff.1 rfl).2.2 hk hkb
#align nat.find_greatest_is_greatest Nat.findGreatest_is_greatest

theorem findGreatest_of_ne_zero (h : Nat.findGreatest P n = m) (h0 : m ≠ 0) : P m :=
  (findGreatest_eq_iff.1 h).2.1 h0
#align nat.find_greatest_of_ne_zero Nat.findGreatest_of_ne_zero

end FindGreatest

/-! ### `bit0` and `bit1` -/
section Bit

set_option linter.deprecated false

protected theorem bit0_le {n m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m :=
  add_le_add h h
#align nat.bit0_le Nat.bit0_le

protected theorem bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
  succ_le_succ (add_le_add h h)
#align nat.bit1_le Nat.bit1_le

theorem bit_le : ∀ (b : Bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
  | true, _, _, h => Nat.bit1_le h
  | false, _, _, h => Nat.bit0_le h
#align nat.bit_le Nat.bit_le

theorem bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
  | true, _, _, h => le_of_lt <| Nat.bit0_lt_bit1 h
  | false, _, _, h => Nat.bit0_le h
#align nat.bit0_le_bit Nat.bit0_le_bit

theorem bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
  | false, _, _, h => le_of_lt <| Nat.bit0_lt_bit1 h
  | true, _, _, h => Nat.bit1_le h
#align nat.bit_le_bit1 Nat.bit_le_bit1

theorem bit_lt_bit0 : ∀ (b) {m n : ℕ}, m < n → bit b m < bit0 n
  | true, _, _, h => Nat.bit1_lt_bit0 h
  | false, _, _, h => Nat.bit0_lt h
#align nat.bit_lt_bit0 Nat.bit_lt_bit0

theorem bit_lt_bit (a b) (h : m < n) : bit a m < bit b n :=
  lt_of_lt_of_le (bit_lt_bit0 _ h) (bit0_le_bit _ le_rfl)
#align nat.bit_lt_bit Nat.bit_lt_bit

@[simp]
theorem bit0_le_bit1_iff : bit0 m ≤ bit1 n ↔ m ≤ n :=
  ⟨fun h => by
    rwa [← Nat.lt_succ_iff, n.bit1_eq_succ_bit0,
    ← n.bit0_succ_eq, bit0_lt_bit0, Nat.lt_succ_iff] at h,
    fun h => le_of_lt (Nat.bit0_lt_bit1 h)⟩
#align nat.bit0_le_bit1_iff Nat.bit0_le_bit1_iff

@[simp]
theorem bit0_lt_bit1_iff : bit0 m < bit1 n ↔ m ≤ n :=
  ⟨fun h => bit0_le_bit1_iff.1 (le_of_lt h), Nat.bit0_lt_bit1⟩
#align nat.bit0_lt_bit1_iff Nat.bit0_lt_bit1_iff

@[simp]
theorem bit1_le_bit0_iff : bit1 m ≤ bit0 n ↔ m < n :=
  ⟨fun h => by rwa [m.bit1_eq_succ_bit0, succ_le_iff, bit0_lt_bit0] at h, fun h =>
               -- 🎉 no goals
    le_of_lt (Nat.bit1_lt_bit0 h)⟩
#align nat.bit1_le_bit0_iff Nat.bit1_le_bit0_iff

@[simp]
theorem bit1_lt_bit0_iff : bit1 m < bit0 n ↔ m < n :=
  ⟨fun h => bit1_le_bit0_iff.1 (le_of_lt h), Nat.bit1_lt_bit0⟩
#align nat.bit1_lt_bit0_iff Nat.bit1_lt_bit0_iff

-- Porting note: temporarily porting only needed portions
/-
@[simp]
theorem one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n := by
  convert bit1_le_bit0_iff
  rfl
#align nat.one_le_bit0_iff Nat.one_le_bit0_iff

@[simp]
theorem one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n := by
  convert bit1_lt_bit0_iff
  rfl
#align nat.one_lt_bit0_iff Nat.one_lt_bit0_iff

@[simp]
theorem bit_le_bit_iff : ∀ {b : Bool}, bit b m ≤ bit b n ↔ m ≤ n
  | false => bit0_le_bit0
  | true => bit1_le_bit1
#align nat.bit_le_bit_iff Nat.bit_le_bit_iff

@[simp]
theorem bit_lt_bit_iff : ∀ {b : Bool}, bit b m < bit b n ↔ m < n
  | false => bit0_lt_bit0
  | true => bit1_lt_bit1
#align nat.bit_lt_bit_iff Nat.bit_lt_bit_iff

@[simp]
theorem bit_le_bit1_iff : ∀ {b : Bool}, bit b m ≤ bit1 n ↔ m ≤ n
  | false => bit0_le_bit1_iff
  | true => bit1_le_bit1
#align nat.bit_le_bit1_iff Nat.bit_le_bit1_iff
-/

end Bit

/-! ### decidability of predicates -/


instance decidableLoHi (lo hi : ℕ) (P : ℕ → Prop) [H : DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x < hi → P x) :=
  decidable_of_iff (∀ x < hi - lo, P (lo + x))
    ⟨fun al x hl hh => by
      have := al (x - lo) ((tsub_lt_tsub_iff_right hl).mpr hh)
      -- ⊢ P x
      rwa [add_tsub_cancel_of_le hl] at this, fun al x h =>
      -- 🎉 no goals
      al _ (Nat.le_add_right _ _) (lt_tsub_iff_left.mp h)⟩
#align nat.decidable_lo_hi Nat.decidableLoHi

instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
  decidable_of_iff (∀ x, lo ≤ x → x < hi + 1 → P x) <|
    ball_congr fun _ _ => imp_congr lt_succ_iff Iff.rfl
#align nat.decidable_lo_hi_le Nat.decidableLoHiLe

end Nat
