/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Defs

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"

/-!
# Basic operations on the natural numbers

This file contains:
- instances on the natural numbers
- some basic lemmas about natural numbers
- extra recursors:
  * `le_rec_on`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
- decidability instances on predicates about the natural numbers

Many theorems that used to live in this file have been moved to `Data.Nat.Order`,
so that this file requires fewer imports.
For each section here there is a corresponding section in that file with additional results.
It may be possible to move some of these results here, by tweaking their proofs.


-/


universe u v

namespace Nat

/-! ### instances -/

instance nontrivial : Nontrivial ℕ :=
  ⟨⟨0, 1, Nat.zero_ne_one⟩⟩

instance commSemiring : CommSemiring ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  mul_comm := Nat.mul_comm
  natCast n := n
  natCast_zero := rfl
  natCast_succ n := rfl
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ _ _ := by dsimp only; rw [Nat.add_comm, Nat.right_distrib, Nat.one_mul]
                       -- ⊢ (x✝¹ + 1) * x✝ = x✝ + x✝¹ * x✝
                                   -- 🎉 no goals
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := Nat.pow_succ'

/-! Extra instances to short-circuit type class resolution and ensure computability -/


instance addCommMonoid : AddCommMonoid ℕ :=
  inferInstance

instance addMonoid : AddMonoid ℕ :=
  inferInstance

instance monoid : Monoid ℕ :=
  inferInstance

instance commMonoid : CommMonoid ℕ :=
  inferInstance

instance commSemigroup : CommSemigroup ℕ :=
  inferInstance

instance semigroup : Semigroup ℕ :=
  inferInstance

instance addCommSemigroup : AddCommSemigroup ℕ :=
  inferInstance

instance addSemigroup : AddSemigroup ℕ :=
  inferInstance

instance distrib : Distrib ℕ :=
  inferInstance

instance semiring : Semiring ℕ :=
  inferInstance

protected theorem nsmul_eq_mul (m n : ℕ) : m • n = m * n :=
  rfl
#align nat.nsmul_eq_mul Nat.nsmul_eq_mul

-- Moved to core
#align nat.eq_of_mul_eq_mul_right Nat.eq_of_mul_eq_mul_right

instance cancelCommMonoidWithZero : CancelCommMonoidWithZero ℕ :=
  { (inferInstance : CommMonoidWithZero ℕ) with
    mul_left_cancel_of_ne_zero :=
      fun h1 h2 => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) h2 }
#align nat.cancel_comm_monoid_with_zero Nat.cancelCommMonoidWithZero

attribute [simp]
  Nat.not_lt_zero Nat.succ_ne_zero Nat.succ_ne_self Nat.zero_ne_one Nat.one_ne_zero
  -- Nat.zero_ne_bit1 Nat.bit1_ne_zero Nat.bit0_ne_one Nat.one_ne_bit0 Nat.bit0_ne_bit1
  -- Nat.bit1_ne_bit0

variable {m n k : ℕ}

/-!
### Recursion and `forall`/`exists`
-/

-- Porting note:
-- this doesn't work as a simp lemma in Lean 4
-- @[simp]
theorem and_forall_succ {p : ℕ → Prop} : (p 0 ∧ ∀ n, p (n + 1)) ↔ ∀ n, p n :=
  ⟨fun h n => Nat.casesOn n h.1 h.2, fun h => ⟨h _, fun _ => h _⟩⟩
#align nat.and_forall_succ Nat.and_forall_succ

-- Porting note:
-- this doesn't work as a simp lemma in Lean 4
-- @[simp]
theorem or_exists_succ {p : ℕ → Prop} : (p 0 ∨ ∃ n, p (n + 1)) ↔ ∃ n, p n :=
  ⟨fun h => h.elim (fun h0 => ⟨0, h0⟩) fun ⟨n, hn⟩ => ⟨n + 1, hn⟩, by
    rintro ⟨_ | n, hn⟩
    -- ⊢ p 0 ∨ ∃ n, p (n + 1)
    exacts [Or.inl hn, Or.inr ⟨n, hn⟩]⟩
    -- 🎉 no goals
#align nat.or_exists_succ Nat.or_exists_succ

/-! ### `succ` -/


theorem _root_.LT.lt.nat_succ_le {n m : ℕ} (h : n < m) : succ n ≤ m :=
  succ_le_of_lt h
#align has_lt.lt.nat_succ_le LT.lt.nat_succ_le

-- Moved to Std
#align nat.succ_eq_one_add Nat.succ_eq_one_add

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬a < b) : a = b :=
  have h3 : a ≤ b := le_of_lt_succ h1
  Or.elim (eq_or_lt_of_not_lt h2) (fun h => h) fun h => absurd h (not_lt_of_ge h3)
#align nat.eq_of_lt_succ_of_not_lt Nat.eq_of_lt_succ_of_not_lt

theorem eq_of_le_of_lt_succ {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n + 1) : m = n :=
  Nat.le_antisymm (le_of_succ_le_succ h₂) h₁
#align nat.eq_of_le_of_lt_succ Nat.eq_of_le_of_lt_succ

-- Moved to Std
#align nat.one_add Nat.one_add

@[simp]
theorem succ_pos' {n : ℕ} : 0 < succ n :=
  succ_pos n
#align nat.succ_pos' Nat.succ_pos'

-- Moved to Std
#align nat.succ_inj' Nat.succ_inj'

theorem succ_injective : Function.Injective Nat.succ := fun _ _ => succ.inj
#align nat.succ_injective Nat.succ_injective

theorem succ_ne_succ {n m : ℕ} : succ n ≠ succ m ↔ n ≠ m :=
  succ_injective.ne_iff
#align nat.succ_ne_succ Nat.succ_ne_succ

-- Porting note: no longer a simp lemma, as simp can prove this
theorem succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 :=
  succ_ne_succ.mpr n.succ_ne_zero
#align nat.succ_succ_ne_one Nat.succ_succ_ne_one

@[simp]
theorem one_lt_succ_succ (n : ℕ) : 1 < n.succ.succ :=
  succ_lt_succ <| succ_pos n
#align nat.one_lt_succ_succ Nat.one_lt_succ_succ

-- Porting note: Nat.succ_le_succ_iff is in Std

theorem max_succ_succ {m n : ℕ} : max (succ m) (succ n) = succ (max m n) := by
  by_cases h1 : m ≤ n
  -- ⊢ max (succ m) (succ n) = succ (max m n)
  rw [max_eq_right h1, max_eq_right (succ_le_succ h1)]
  -- ⊢ max (succ m) (succ n) = succ (max m n)
  · rw [not_le] at h1
    -- ⊢ max (succ m) (succ n) = succ (max m n)
    have h2 := le_of_lt h1
    -- ⊢ max (succ m) (succ n) = succ (max m n)
    rw [max_eq_left h2, max_eq_left (succ_le_succ h2)]
    -- 🎉 no goals
#align nat.max_succ_succ Nat.max_succ_succ

theorem not_succ_lt_self {n : ℕ} : ¬succ n < n :=
  not_lt_of_ge (Nat.le_succ _)
#align nat.not_succ_lt_self Nat.not_succ_lt_self

theorem lt_succ_iff {m n : ℕ} : m < succ n ↔ m ≤ n :=
  ⟨le_of_lt_succ, lt_succ_of_le⟩
#align nat.lt_succ_iff Nat.lt_succ_iff

theorem succ_le_iff {m n : ℕ} : succ m ≤ n ↔ m < n :=
  ⟨lt_of_succ_le, succ_le_of_lt⟩
#align nat.succ_le_iff Nat.succ_le_iff

theorem lt_iff_add_one_le {m n : ℕ} : m < n ↔ m + 1 ≤ n := by rw [succ_le_iff]
                                                              -- 🎉 no goals
#align nat.lt_iff_add_one_le Nat.lt_iff_add_one_le

-- Just a restatement of `Nat.lt_succ_iff` using `+1`.
theorem lt_add_one_iff {a b : ℕ} : a < b + 1 ↔ a ≤ b :=
  lt_succ_iff
#align nat.lt_add_one_iff Nat.lt_add_one_iff

-- A flipped version of `lt_add_one_iff`.
theorem lt_one_add_iff {a b : ℕ} : a < 1 + b ↔ a ≤ b := by simp only [add_comm, lt_succ_iff]
                                                           -- 🎉 no goals
#align nat.lt_one_add_iff Nat.lt_one_add_iff

-- This is true reflexively, by the definition of `≤` on ℕ,
-- but it's still useful to have, to convince Lean to change the syntactic type.
theorem add_one_le_iff {a b : ℕ} : a + 1 ≤ b ↔ a < b :=
  Iff.refl _
#align nat.add_one_le_iff Nat.add_one_le_iff

theorem one_add_le_iff {a b : ℕ} : 1 + a ≤ b ↔ a < b := by simp only [add_comm, add_one_le_iff]
                                                           -- 🎉 no goals
#align nat.one_add_le_iff Nat.one_add_le_iff

theorem of_le_succ {n m : ℕ} (H : n ≤ m.succ) : n ≤ m ∨ n = m.succ :=
  H.lt_or_eq_dec.imp le_of_lt_succ id
#align nat.of_le_succ Nat.of_le_succ

#align nat.succ_lt_succ_iff Nat.succ_lt_succ_iff

theorem div_le_iff_le_mul_add_pred {m n k : ℕ} (n0 : 0 < n) : m / n ≤ k ↔ m ≤ n * k + (n - 1) := by
  rw [← lt_succ_iff, div_lt_iff_lt_mul n0, succ_mul, mul_comm]
  -- ⊢ m < n * k + n ↔ m ≤ n * k + (n - 1)
  cases n
  -- ⊢ m < zero * k + zero ↔ m ≤ zero * k + (zero - 1)
  · cases n0
    -- 🎉 no goals

  exact lt_succ_iff
  -- 🎉 no goals
#align nat.div_le_iff_le_mul_add_pred Nat.div_le_iff_le_mul_add_pred

theorem two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  -- Porting note: was `by decide`
  | n + 3, _, _, _ => by rw [Nat.lt_iff_add_one_le]; convert Nat.le_add_left 3 n
                         -- ⊢ 2 + 1 ≤ n + 3
                                                     -- 🎉 no goals
#align nat.two_lt_of_ne Nat.two_lt_of_ne

theorem forall_lt_succ {P : ℕ → Prop} {n : ℕ} : (∀ m < n + 1, P m) ↔ (∀ m < n, P m) ∧ P n := by
  simp only [lt_succ_iff, Decidable.le_iff_eq_or_lt, forall_eq_or_imp, and_comm]
  -- 🎉 no goals
#align nat.forall_lt_succ Nat.forall_lt_succ

theorem exists_lt_succ {P : ℕ → Prop} {n : ℕ} : (∃ m < n + 1, P m) ↔ (∃ m < n, P m) ∨ P n := by
  rw [← not_iff_not]
  -- ⊢ (¬∃ m, m < n + 1 ∧ P m) ↔ ¬((∃ m, m < n ∧ P m) ∨ P n)
  push_neg
  -- ⊢ (∀ (m : ℕ), m < n + 1 → ¬P m) ↔ (∀ (m : ℕ), m < n → ¬P m) ∧ ¬P n
  exact forall_lt_succ
  -- 🎉 no goals
#align nat.exists_lt_succ Nat.exists_lt_succ

/-! ### `add` -/

-- Sometimes a bare `Nat.add` or similar appears as a consequence of unfolding
-- during pattern matching. These lemmas package them back up as typeclass
-- mediated operations.
@[simp]
theorem add_def {a b : ℕ} : Nat.add a b = a + b :=
  rfl
#align nat.add_def Nat.add_def

@[simp]
theorem mul_def {a b : ℕ} : Nat.mul a b = a * b :=
  rfl
#align nat.mul_def Nat.mul_def

theorem exists_eq_add_of_le (h : m ≤ n) : ∃ k : ℕ, n = m + k :=
  ⟨n - m, (add_sub_of_le h).symm⟩
#align nat.exists_eq_add_of_le Nat.exists_eq_add_of_le

theorem exists_eq_add_of_le' (h : m ≤ n) : ∃ k : ℕ, n = k + m :=
  ⟨n - m, (Nat.sub_add_cancel h).symm⟩
#align nat.exists_eq_add_of_le' Nat.exists_eq_add_of_le'

theorem exists_eq_add_of_lt (h : m < n) : ∃ k : ℕ, n = m + k + 1 :=
  ⟨n - (m + 1), by rw [add_right_comm, add_sub_of_le h]⟩
                   -- 🎉 no goals
#align nat.exists_eq_add_of_lt Nat.exists_eq_add_of_lt

/-! ### `pred` -/

@[simp]
theorem add_succ_sub_one (n m : ℕ) : n + succ m - 1 = n + m := by rw [add_succ, succ_sub_one]
                                                                  -- 🎉 no goals
#align nat.add_succ_sub_one Nat.add_succ_sub_one

@[simp]
theorem succ_add_sub_one (n m : ℕ) : succ n + m - 1 = n + m := by rw [succ_add, succ_sub_one]
                                                                  -- 🎉 no goals
#align nat.succ_add_sub_one Nat.succ_add_sub_one

theorem pred_eq_sub_one (n : ℕ) : pred n = n - 1 :=
  rfl
#align nat.pred_eq_sub_one Nat.pred_eq_sub_one

theorem pred_eq_of_eq_succ {m n : ℕ} (H : m = n.succ) : m.pred = n := by simp [H]
                                                                         -- 🎉 no goals
#align nat.pred_eq_of_eq_succ Nat.pred_eq_of_eq_succ

@[simp]
theorem pred_eq_succ_iff {n m : ℕ} : pred n = succ m ↔ n = m + 2 := by
  cases n <;> constructor <;> rintro ⟨⟩ <;> rfl
  -- ⊢ pred zero = succ m ↔ zero = m + 2
              -- ⊢ pred zero = succ m → zero = m + 2
              -- ⊢ pred (succ n✝) = succ m → succ n✝ = m + 2
                              -- 🎉 no goals
                              -- 🎉 no goals
                              -- ⊢ succ (succ m) = m + 2
                              -- ⊢ pred (succ (Nat.add m 1)) = succ m
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align nat.pred_eq_succ_iff Nat.pred_eq_succ_iff

theorem pred_sub (n m : ℕ) : pred n - m = pred (n - m) := by
  rw [← Nat.sub_one, Nat.sub_sub, one_add, sub_succ]
  -- 🎉 no goals
#align nat.pred_sub Nat.pred_sub

-- Moved to Std
#align nat.le_pred_of_lt Nat.le_pred_of_lt

theorem le_of_pred_lt {m n : ℕ} : pred m < n → m ≤ n :=
  match m with
  | 0 => le_of_lt
  | _ + 1 => id
#align nat.le_of_pred_lt Nat.le_of_pred_lt

/-- This ensures that `simp` succeeds on `pred (n + 1) = n`. -/
@[simp]
theorem pred_one_add (n : ℕ) : pred (1 + n) = n := by rw [add_comm, add_one, Nat.pred_succ]
                                                      -- 🎉 no goals
#align nat.pred_one_add Nat.pred_one_add

/-! ### `mul` -/


theorem two_mul_ne_two_mul_add_one {n m} : 2 * n ≠ 2 * m + 1 :=
  mt (congr_arg (· % 2))
    (by rw [add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)
        -- ⊢ ¬0 = 1
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
#align nat.two_mul_ne_two_mul_add_one Nat.two_mul_ne_two_mul_add_one

theorem mul_ne_mul_left {a b c : ℕ} (ha : 0 < a) : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective₀ ha.ne').ne_iff
#align nat.mul_ne_mul_left Nat.mul_ne_mul_left

theorem mul_ne_mul_right {a b c : ℕ} (ha : 0 < a) : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective₀ ha.ne').ne_iff
#align nat.mul_ne_mul_right Nat.mul_ne_mul_right

theorem mul_right_eq_self_iff {a b : ℕ} (ha : 0 < a) : a * b = a ↔ b = 1 :=
  suffices a * b = a * 1 ↔ b = 1 by rwa [mul_one] at this
                                    -- 🎉 no goals
  mul_right_inj' ha.ne'
#align nat.mul_right_eq_self_iff Nat.mul_right_eq_self_iff

theorem mul_left_eq_self_iff {a b : ℕ} (hb : 0 < b) : a * b = b ↔ a = 1 := by
  rw [mul_comm, Nat.mul_right_eq_self_iff hb]
  -- 🎉 no goals
#align nat.mul_left_eq_self_iff Nat.mul_left_eq_self_iff

theorem lt_succ_iff_lt_or_eq {n i : ℕ} : n < i.succ ↔ n < i ∨ n = i :=
  lt_succ_iff.trans Decidable.le_iff_lt_or_eq
#align nat.lt_succ_iff_lt_or_eq Nat.lt_succ_iff_lt_or_eq

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

-- Porting note: The type ascriptions of these two theorems need to be changed,
-- as mathport wrote a lambda that wasn't there in mathlib3, that prevents `simp` applying them.

@[simp]
theorem rec_zero {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
    Nat.rec h0 h 0 = h0 :=
  rfl
#align nat.rec_zero Nat.rec_zero

@[simp]
theorem rec_add_one {C : ℕ → Sort u} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) :=
  rfl
#align nat.rec_add_one Nat.rec_add_one

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `leRecOn`. -/
@[elab_as_elim]
def leRecOn {C : ℕ → Sort u} {n : ℕ} : ∀ {m : ℕ}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m
  | 0, H, _, x => Eq.recOn (Nat.eq_zero_of_le_zero H) x
  | m + 1, H, next, x =>
    Or.by_cases (of_le_succ H) (fun h : n ≤ m => next <| leRecOn h (@next) x)
      fun h : n = m + 1 => Eq.recOn h x
#align nat.le_rec_on Nat.leRecOn

theorem leRecOn_self {C : ℕ → Sort u} {n} {h : n ≤ n} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h next x : C n) = x := by
  cases n <;> unfold leRecOn Eq.recOn
  -- ⊢ leRecOn h (fun {k} => next) x = x
              -- ⊢ (_ : zero = 0) ▸ x = x
              -- ⊢ (Or.by_cases (_ : succ n✝ ≤ n✝ ∨ succ n✝ = succ n✝) (fun h => (fun {k} => ne …
  · simp
    -- 🎉 no goals
  · unfold Or.by_cases
    -- ⊢ (if hp : succ n✝ ≤ n✝ then (fun h => (fun {k} => next) (leRecOn h (fun {k} = …
    rw [dif_neg (Nat.not_succ_le_self _)]
    -- 🎉 no goals
#align nat.le_rec_on_self Nat.leRecOn_self

theorem leRecOn_succ {C : ℕ → Sort u} {n m} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next} (x : C n) :
    (leRecOn h2 (@next) x : C (m + 1)) = next (leRecOn h1 (@next) x : C m) := by
  conv =>
    lhs
    rw [leRecOn, Or.by_cases, dif_pos h1]
#align nat.le_rec_on_succ Nat.leRecOn_succ

theorem leRecOn_succ' {C : ℕ → Sort u} {n} {h : n ≤ n + 1} {next : ∀ {k}, C k → C (k + 1)}
    (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x := by rw [leRecOn_succ (le_refl n), leRecOn_self]
                                                  -- 🎉 no goals
#align nat.le_rec_on_succ' Nat.leRecOn_succ'

theorem leRecOn_trans {C : ℕ → Sort u} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
    (leRecOn (le_trans hnm hmk) (@next) x : C k) = leRecOn hmk (@next) (leRecOn hnm (@next) x) := by
  induction' hmk with k hmk ih
  -- ⊢ leRecOn (_ : n ≤ m) next x = leRecOn (_ : Nat.le m m) next (leRecOn hnm next …
  · rw [leRecOn_self]
    -- 🎉 no goals

  rw [leRecOn_succ (le_trans hnm hmk), ih, leRecOn_succ]
  -- 🎉 no goals
#align nat.le_rec_on_trans Nat.leRecOn_trans

theorem leRecOn_succ_left {C : ℕ → Sort u} {n m} (h1 : n ≤ m) (h2 : n + 1 ≤ m)
    {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) := by
  rw [Subsingleton.elim h1 (le_trans (le_succ n) h2), leRecOn_trans (le_succ n) h2, leRecOn_succ']
  -- 🎉 no goals
#align nat.le_rec_on_succ_left Nat.leRecOn_succ_left

theorem leRecOn_injective {C : ℕ → Sort u} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Function.Injective (@next n)) :
    Function.Injective (@leRecOn C n m hnm next) := by
  induction' hnm with m hnm ih
  -- ⊢ Function.Injective (leRecOn (_ : Nat.le n n) fun {k} => next)
  · intro x y H
    -- ⊢ x = y
    rwa [leRecOn_self, leRecOn_self] at H
    -- 🎉 no goals

  intro x y H
  -- ⊢ x = y
  rw [leRecOn_succ hnm, leRecOn_succ hnm] at H
  -- ⊢ x = y
  exact ih (Hnext _ H)
  -- 🎉 no goals
#align nat.le_rec_on_injective Nat.leRecOn_injective

theorem leRecOn_surjective {C : ℕ → Sort u} {n m} (hnm : n ≤ m) (next : ∀ {k}, C k → C (k + 1))
    (Hnext : ∀ n, Function.Surjective (@next n)) :
    Function.Surjective (@leRecOn C n m hnm next) := by
  induction' hnm with m hnm ih
  -- ⊢ Function.Surjective (leRecOn (_ : Nat.le n n) fun {k} => next)
  · intro x
    -- ⊢ ∃ a, leRecOn (_ : Nat.le n n) (fun {k} => next) a = x
    use x
    -- ⊢ leRecOn (_ : Nat.le n n) (fun {k} => next) x = x
    rw [leRecOn_self]
    -- 🎉 no goals

  intro x
  -- ⊢ ∃ a, leRecOn (_ : Nat.le n (succ m)) (fun {k} => next) a = x
  rcases Hnext _ x with ⟨w, rfl⟩
  -- ⊢ ∃ a, leRecOn (_ : Nat.le n (succ m)) (fun {k} => next) a = next w
  rcases ih w with ⟨x, rfl⟩
  -- ⊢ ∃ a, leRecOn (_ : Nat.le n (succ m)) (fun {k} => next) a = next (leRecOn hnm …
  use x
  -- ⊢ leRecOn (_ : Nat.le n (succ m)) (fun {k} => next) x = next (leRecOn hnm (fun …
  rw [leRecOn_succ]
  -- 🎉 no goals
#align nat.le_rec_on_surjective Nat.leRecOn_surjective

/-- Recursion principle based on `<`. -/
@[elab_as_elim]
protected def strongRec' {p : ℕ → Sort u} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ n : ℕ, p n
  | n => H n fun m _ => Nat.strongRec' H m
#align nat.strong_rec' Nat.strongRec'

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_elim]
def strongRecOn' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
  Nat.strongRec' h n
#align nat.strong_rec_on' Nat.strongRecOn'

theorem strongRecOn'_beta {P : ℕ → Sort*} {h} {n : ℕ} :
    (strongRecOn' n h : P n) = h n fun m _ => (strongRecOn' m h : P m) := by
  simp only [strongRecOn']
  -- ⊢ Nat.strongRec' h n = h n fun m x => Nat.strongRec' h m
  rw [Nat.strongRec']
  -- 🎉 no goals
#align nat.strong_rec_on_beta' Nat.strongRecOn'_beta

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `le_rec_on`.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`). -/
@[elab_as_elim]
theorem le_induction {m} {P : ∀ (n : Nat) (_ : m ≤ n), Prop} (base : P m le_rfl)
    (succ : ∀ (n : Nat) (hn : m ≤ n), P n hn → P (n + 1) (hn.trans <| Nat.le_succ _)) :
    ∀ (n : Nat) (hn : m ≤ n), P n hn := by
  apply Nat.le.rec
  -- ⊢ P m (_ : Nat.le m m)
  · exact base
    -- 🎉 no goals
  · intros n hn
    -- ⊢ P n hn → P (Nat.succ n) (_ : Nat.le m (Nat.succ n))
    apply succ n hn
    -- 🎉 no goals
#align nat.le_induction Nat.le_induction

/-- Decreasing induction: if `P (k+1)` implies `P k`, then `P n` implies `P m` for all `m ≤ n`.
Also works for functions to `Sort*`. For a version assuming only the assumption for `k < n`, see
`decreasing_induction'`. -/
@[elab_as_elim]
def decreasingInduction {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n)
    (hP : P n) : P m :=
  leRecOn mn (fun {k} ih hsk => ih <| h k hsk) (fun h => h) hP
#align nat.decreasing_induction Nat.decreasingInduction

@[simp]
theorem decreasingInduction_self {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {n : ℕ} (nn : n ≤ n)
    (hP : P n) :
    (decreasingInduction h nn hP : P n) = hP := by
  dsimp only [decreasingInduction]
  -- ⊢ leRecOn nn (fun {k} ih hsk => ih (h k hsk)) (fun h => h) hP = hP
  rw [leRecOn_self]
  -- 🎉 no goals
#align nat.decreasing_induction_self Nat.decreasingInduction_self

theorem decreasingInduction_succ {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n)
    (msn : m ≤ n + 1) (hP : P (n + 1)) :
    (decreasingInduction h msn hP : P m) = decreasingInduction h mn (h n hP) := by
  dsimp only [decreasingInduction]
  -- ⊢ leRecOn msn (fun {k} ih hsk => ih (h k hsk)) (fun h => h) hP = leRecOn mn (f …
  rw [leRecOn_succ]
  -- 🎉 no goals
#align nat.decreasing_induction_succ Nat.decreasingInduction_succ

@[simp]
theorem decreasingInduction_succ' {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m : ℕ}
    (msm : m ≤ m + 1) (hP : P (m + 1)) : (decreasingInduction h msm hP : P m) = h m hP := by
  dsimp only [decreasingInduction]
  -- ⊢ leRecOn msm (fun {k} ih hsk => ih (h k hsk)) (fun h => h) hP = h m hP
  rw [leRecOn_succ']
  -- 🎉 no goals
#align nat.decreasing_induction_succ' Nat.decreasingInduction_succ'

theorem decreasingInduction_trans {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m n k : ℕ}
    (mn : m ≤ n) (nk : n ≤ k) (hP : P k) :
    (decreasingInduction h (le_trans mn nk) hP : P m) =
    decreasingInduction h mn (decreasingInduction h nk hP) := by
  induction' nk with k nk ih
  -- ⊢ decreasingInduction h (_ : m ≤ n) hP = decreasingInduction h mn (decreasingI …
  · rw [decreasingInduction_self]
    -- 🎉 no goals
  · rw [decreasingInduction_succ h (le_trans mn nk), ih, decreasingInduction_succ]
    -- 🎉 no goals
#align nat.decreasing_induction_trans Nat.decreasingInduction_trans

theorem decreasingInduction_succ_left {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m n : ℕ}
    (smn : m + 1 ≤ n) (mn : m ≤ n) (hP : P n) :
    (decreasingInduction h mn hP : P m) = h m (decreasingInduction h smn hP) := by
  rw [Subsingleton.elim mn (le_trans (le_succ m) smn), decreasingInduction_trans,
    decreasingInduction_succ']
  apply Nat.le_succ
  -- 🎉 no goals
#align nat.decreasing_induction_succ_left Nat.decreasingInduction_succ_left

/-- Given `P : ℕ → ℕ → Sort*`, if for all `a b : ℕ` we can extend `P` from the rectangle
strictly below `(a,b)` to `P a b`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
def strongSubRecursion {P : ℕ → ℕ → Sort*} (H : ∀ a b, (∀ x y, x < a → y < b → P x y) → P a b) :
    ∀ n m : ℕ, P n m
  | n, m => H n m fun x y _ _ => strongSubRecursion H x y
#align nat.strong_sub_recursion Nat.strongSubRecursion

-- Porting note:
-- we can't put this on the definition itself because of
-- https://github.com/leanprover/lean4/issues/1900
attribute [elab_as_elim] strongSubRecursion

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P i 0` and `P 0 i` for all `i : ℕ`,
and for any `x y : ℕ` we can extend `P` from `(x,y+1)` and `(x+1,y)` to `(x+1,y+1)`
then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
def pincerRecursion {P : ℕ → ℕ → Sort*} (Ha0 : ∀ a : ℕ, P a 0) (H0b : ∀ b : ℕ, P 0 b)
    (H : ∀ x y : ℕ, P x y.succ → P x.succ y → P x.succ y.succ) : ∀ n m : ℕ, P n m
  | a, 0 => Ha0 a
  | 0, b => H0b b
  | Nat.succ a, Nat.succ b => H _ _ (pincerRecursion Ha0 H0b H _ _) (pincerRecursion Ha0 H0b H _ _)
termination_by pincerRecursion Ha0 Hab H n m => n + m
#align nat.pincer_recursion Nat.pincerRecursion

-- Porting note:
-- we can't put this on the definition itself because of
-- https://github.com/leanprover/lean4/issues/1900
attribute [elab_as_elim] pincerRecursion

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`. -/
@[elab_as_elim]
def leRecOn' {C : ℕ → Sort*} {n : ℕ} :
    ∀ {m : ℕ}, n ≤ m → (∀ ⦃k⦄, n ≤ k → C k → C (k + 1)) → C n → C m
  | 0, H, _, x => Eq.recOn (Nat.eq_zero_of_le_zero H) x
  | m + 1, H, next, x =>
    Or.by_cases (of_le_succ H) (fun h : n ≤ m => next h <| leRecOn' h next x)
      fun h : n = m + 1 => Eq.recOn h x
#align nat.le_rec_on' Nat.leRecOn'

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`. Weakens the assumptions of `decreasing_induction`. -/
@[elab_as_elim]
def decreasingInduction' {P : ℕ → Sort*} {m n : ℕ} (h : ∀ k < n, m ≤ k → P (k + 1) → P k)
    (mn : m ≤ n) (hP : P n) :
    P m := by
  revert h hP
  -- ⊢ ((k : ℕ) → k < n → m ≤ k → P (k + 1) → P k) → P n → P m
  refine' leRecOn' mn _ _
  -- ⊢ ⦃k : ℕ⦄ → m ≤ k → (((k_1 : ℕ) → k_1 < k → m ≤ k_1 → P (k_1 + 1) → P k_1) → P …
  · intro n mn ih h hP
    -- ⊢ P m
    apply ih
    -- ⊢ (k : ℕ) → k < n → m ≤ k → P (k + 1) → P k
    · exact fun k hk => h k (Nat.lt.step hk)
      -- 🎉 no goals
    · exact h n (lt_succ_self n) mn hP
      -- 🎉 no goals
  · intro _ hP
    -- ⊢ P m
    exact hP
    -- 🎉 no goals
#align nat.decreasing_induction' Nat.decreasingInduction'

/-! ### `div` -/

attribute [simp] Nat.div_self

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
theorem div_lt_self' (n b : ℕ) : (n + 1) / (b + 2) < n + 1 :=
  Nat.div_lt_self (Nat.succ_pos n) (Nat.succ_lt_succ (Nat.succ_pos _))
#align nat.div_lt_self' Nat.div_lt_self'

theorem le_div_iff_mul_le' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y :=
  le_div_iff_mul_le k0
#align nat.le_div_iff_mul_le' Nat.le_div_iff_mul_le'

theorem div_lt_iff_lt_mul' {x y : ℕ} {k : ℕ} (k0 : 0 < k) : x / k < y ↔ x < y * k :=
  lt_iff_lt_of_le_iff_le <| le_div_iff_mul_le' k0
#align nat.div_lt_iff_lt_mul' Nat.div_lt_iff_lt_mul'

theorem one_le_div_iff {a b : ℕ} (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by
  rw [le_div_iff_mul_le hb, one_mul]
  -- 🎉 no goals
#align nat.one_le_div_iff Nat.one_le_div_iff

theorem div_lt_one_iff {a b : ℕ} (hb : 0 < b) : a / b < 1 ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| one_le_div_iff hb
#align nat.div_lt_one_iff Nat.div_lt_one_iff

protected theorem div_le_div_right {n m : ℕ} (h : n ≤ m) {k : ℕ} : n / k ≤ m / k :=
  ((Nat.eq_zero_or_pos k).elim fun k0 => by simp [k0]) fun hk =>
                                            -- 🎉 no goals
    (le_div_iff_mul_le' hk).2 <| le_trans (Nat.div_mul_le_self _ _) h
#align nat.div_le_div_right Nat.div_le_div_right

theorem lt_of_div_lt_div {m n k : ℕ} : m / k < n / k → m < n :=
  lt_imp_lt_of_le_imp_le fun h => Nat.div_le_div_right h
#align nat.lt_of_div_lt_div Nat.lt_of_div_lt_div

protected theorem div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
  Nat.pos_of_ne_zero fun h =>
    lt_irrefl a
      (calc
        a = a % b := by simpa [h] using (mod_add_div a b).symm
                        -- 🎉 no goals
        _ < b := Nat.mod_lt a hb
        _ ≤ a := hba
        )
#align nat.div_pos Nat.div_pos

theorem lt_mul_of_div_lt {a b c : ℕ} (h : a / c < b) (w : 0 < c) : a < b * c :=
  lt_of_not_ge <| not_le_of_gt h ∘ (Nat.le_div_iff_mul_le w).2
#align nat.lt_mul_of_div_lt Nat.lt_mul_of_div_lt

theorem mul_div_le_mul_div_assoc (a b c : ℕ) : a * (b / c) ≤ a * b / c :=
  if hc0 : c = 0 then by simp [hc0]
                         -- 🎉 no goals
  else
    (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc0)).2
      (by rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
          -- ⊢ a * (b / c * c) ≤ a * b
                          -- 🎉 no goals
#align nat.mul_div_le_mul_div_assoc Nat.mul_div_le_mul_div_assoc

protected theorem eq_mul_of_div_eq_right {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : a = b * c := by
  rw [← H2, Nat.mul_div_cancel' H1]
  -- 🎉 no goals
#align nat.eq_mul_of_div_eq_right Nat.eq_mul_of_div_eq_right

protected theorem div_eq_iff_eq_mul_right {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = b * c :=
  ⟨Nat.eq_mul_of_div_eq_right H', Nat.div_eq_of_eq_mul_right H⟩
#align nat.div_eq_iff_eq_mul_right Nat.div_eq_iff_eq_mul_right

protected theorem div_eq_iff_eq_mul_left {a b c : ℕ} (H : 0 < b) (H' : b ∣ a) :
    a / b = c ↔ a = c * b := by
  rw [mul_comm]
  -- ⊢ a / b = c ↔ a = b * c
  exact Nat.div_eq_iff_eq_mul_right H H'
  -- 🎉 no goals
#align nat.div_eq_iff_eq_mul_left Nat.div_eq_iff_eq_mul_left

protected theorem eq_mul_of_div_eq_left {a b c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : a = c * b := by
  rw [mul_comm, Nat.eq_mul_of_div_eq_right H1 H2]
  -- 🎉 no goals
#align nat.eq_mul_of_div_eq_left Nat.eq_mul_of_div_eq_left

protected theorem mul_div_cancel_left' {a b : ℕ} (Hd : a ∣ b) : a * (b / a) = b := by
  rw [mul_comm, Nat.div_mul_cancel Hd]
  -- 🎉 no goals
#align nat.mul_div_cancel_left' Nat.mul_div_cancel_left'

#align nat.mul_div_mul_left Nat.mul_div_mul_left
#align nat.mul_div_mul_right Nat.mul_div_mul_right

theorem lt_div_mul_add {a b : ℕ} (hb : 0 < b) : a < a / b * b + b := by
  rw [← Nat.succ_mul, ← Nat.div_lt_iff_lt_mul hb]
  -- ⊢ a / b < succ (a / b)
  exact Nat.lt_succ_self _
  -- 🎉 no goals
#align nat.lt_div_mul_add Nat.lt_div_mul_add

@[simp]
protected theorem div_left_inj {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b := by
  refine ⟨fun h => ?_, congr_arg fun n => n / d⟩
  -- ⊢ a = b
  rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, h]
  -- 🎉 no goals
#align nat.div_left_inj Nat.div_left_inj

/-! ### `mod`, `dvd` -/


theorem mod_eq_iff_lt {a b : ℕ} (h : b ≠ 0) : a % b = a ↔ a < b := by
  cases b
  -- ⊢ a % zero = a ↔ a < zero
  contradiction
  -- ⊢ a % succ n✝ = a ↔ a < succ n✝
  exact ⟨fun h => h.ge.trans_lt (mod_lt _ (succ_pos _)), mod_eq_of_lt⟩
  -- 🎉 no goals
#align nat.mod_eq_iff_lt Nat.mod_eq_iff_lt

@[simp]
theorem mod_succ_eq_iff_lt {a b : ℕ} : a % b.succ = a ↔ a < b.succ :=
  mod_eq_iff_lt (succ_ne_zero _)
#align nat.mod_succ_eq_iff_lt Nat.mod_succ_eq_iff_lt

-- Porting note `Nat.div_add_mod` is now in core.

theorem mod_add_div' (m k : ℕ) : m % k + m / k * k = m := by
  rw [mul_comm]
  -- ⊢ m % k + k * (m / k) = m
  exact mod_add_div _ _
  -- 🎉 no goals
#align nat.mod_add_div' Nat.mod_add_div'

theorem div_add_mod' (m k : ℕ) : m / k * k + m % k = m := by
  rw [mul_comm]
  -- ⊢ k * (m / k) + m % k = m
  exact div_add_mod _ _
  -- 🎉 no goals
#align nat.div_add_mod' Nat.div_add_mod'

/-- See also `Nat.divModEquiv` for a similar statement as an `Equiv`. -/
protected theorem div_mod_unique {n k m d : ℕ} (h : 0 < k) :
    n / k = d ∧ n % k = m ↔ m + k * d = n ∧ m < k :=
  ⟨fun ⟨e₁, e₂⟩ => e₁ ▸ e₂ ▸ ⟨mod_add_div _ _, mod_lt _ h⟩, fun ⟨h₁, h₂⟩ =>
    h₁ ▸ by
      rw [add_mul_div_left _ _ h, add_mul_mod_self_left]
      -- ⊢ m / k + d = d ∧ m % k = m
      simp [div_eq_of_lt, mod_eq_of_lt, h₂]⟩
      -- 🎉 no goals
#align nat.div_mod_unique Nat.div_mod_unique

protected theorem dvd_add_left {k m n : ℕ} (h : k ∣ n) : k ∣ m + n ↔ k ∣ m :=
  (Nat.dvd_add_iff_left h).symm
#align nat.dvd_add_left Nat.dvd_add_left

protected theorem dvd_add_right {k m n : ℕ} (h : k ∣ m) : k ∣ m + n ↔ k ∣ n :=
  (Nat.dvd_add_iff_right h).symm
#align nat.dvd_add_right Nat.dvd_add_right

protected theorem mul_dvd_mul_iff_left {a b c : ℕ} (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha.ne']
                           -- 🎉 no goals
#align nat.mul_dvd_mul_iff_left Nat.mul_dvd_mul_iff_left

protected theorem mul_dvd_mul_iff_right {a b c : ℕ} (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc.ne']
                           -- 🎉 no goals
#align nat.mul_dvd_mul_iff_right Nat.mul_dvd_mul_iff_right

@[simp]
theorem mod_mod_of_dvd (n : Nat) {m k : Nat} (h : m ∣ k) : n % k % m = n % m := by
  conv =>
  rhs
  rw [← mod_add_div n k]
  rcases h with ⟨t, rfl⟩
  -- ⊢ n % (m * t) % m = (n % (m * t) + m * t * (n / (m * t))) % m
  rw [mul_assoc, add_mul_mod_self_left]
  -- 🎉 no goals
#align nat.mod_mod_of_dvd Nat.mod_mod_of_dvd

-- Moved to Std
#align nat.mod_mod Nat.mod_mod
#align nat.mod_add_mod Nat.mod_add_mod
#align nat.add_mod_mod Nat.add_mod_mod
#align nat.add_mod Nat.add_mod

theorem add_mod_eq_add_mod_right {m n k : ℕ} (i : ℕ) (H : m % n = k % n) :
    (m + i) % n = (k + i) % n := by
  rw [← mod_add_mod, ← mod_add_mod k, H]
  -- 🎉 no goals
#align nat.add_mod_eq_add_mod_right Nat.add_mod_eq_add_mod_right

theorem add_mod_eq_add_mod_left {m n k : ℕ} (i : ℕ) (H : m % n = k % n) :
    (i + m) % n = (i + k) % n := by
  rw [add_comm, add_mod_eq_add_mod_right _ H, add_comm]
  -- 🎉 no goals
#align nat.add_mod_eq_add_mod_left Nat.add_mod_eq_add_mod_left

-- Moved to Std
#align nat.mul_mod Nat.mul_mod

theorem mul_dvd_of_dvd_div {a b c : ℕ} (hab : c ∣ b) (h : a ∣ b / c) : c * a ∣ b :=
  have h1 : ∃ d, b / c = a * d := h
  let ⟨d, hd⟩ := h1
  have h3 : b = a * d * c := Nat.eq_mul_of_div_eq_left hab hd
  -- Porting note: was `cc`
  show ∃ d, b = c * a * d from ⟨d, by rwa [mul_comm, ←mul_assoc] at h3⟩
                                      -- 🎉 no goals
#align nat.mul_dvd_of_dvd_div Nat.mul_dvd_of_dvd_div

theorem eq_of_dvd_of_div_eq_one {a b : ℕ} (w : a ∣ b) (h : b / a = 1) : a = b := by
  rw [← Nat.div_mul_cancel w, h, one_mul]
  -- 🎉 no goals
#align nat.eq_of_dvd_of_div_eq_one Nat.eq_of_dvd_of_div_eq_one

theorem eq_zero_of_dvd_of_div_eq_zero {a b : ℕ} (w : a ∣ b) (h : b / a = 0) : b = 0 := by
  rw [← Nat.div_mul_cancel w, h, zero_mul]
  -- 🎉 no goals
#align nat.eq_zero_of_dvd_of_div_eq_zero Nat.eq_zero_of_dvd_of_div_eq_zero

theorem div_le_div_left {a b c : ℕ} (h₁ : c ≤ b) (h₂ : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_le h₂).2 <| le_trans (Nat.mul_le_mul_left _ h₁) (div_mul_le_self _ _)
#align nat.div_le_div_left Nat.div_le_div_left

theorem lt_iff_le_pred : ∀ {m n : ℕ}, 0 < n → (m < n ↔ m ≤ n - 1)
  | _, _ + 1, _ => lt_succ_iff
#align nat.lt_iff_le_pred Nat.lt_iff_le_pred

-- Moved to Std
#align nat.mul_div_le Nat.mul_div_le

theorem lt_mul_div_succ (m : ℕ) {n : ℕ} (n0 : 0 < n) : m < n * (m / n + 1) := by
  rw [mul_comm, ← Nat.div_lt_iff_lt_mul' n0]
  -- ⊢ m / n < m / n + 1
  exact lt_succ_self _
  -- 🎉 no goals
#align nat.lt_mul_div_succ Nat.lt_mul_div_succ

theorem mul_add_mod (a b c : ℕ) : (a * b + c) % b = c % b := by simp [Nat.add_mod]
                                                                -- 🎉 no goals
#align nat.mul_add_mod Nat.mul_add_mod

theorem mul_add_mod_of_lt {a b c : ℕ} (h : c < b) : (a * b + c) % b = c := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  -- 🎉 no goals
#align nat.mul_add_mod_of_lt Nat.mul_add_mod_of_lt

theorem pred_eq_self_iff {n : ℕ} : n.pred = n ↔ n = 0 := by
  cases n <;> simp [(Nat.succ_ne_self _).symm]
  -- ⊢ pred zero = zero ↔ zero = 0
              -- 🎉 no goals
              -- 🎉 no goals
#align nat.pred_eq_self_iff Nat.pred_eq_self_iff

/-! ### `find` -/


section Find

variable {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]

theorem find_eq_iff (h : ∃ n : ℕ, p n) : Nat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  -- ⊢ Nat.find h = m → p m ∧ ∀ (n : ℕ), n < m → ¬p n
  · rintro rfl
    -- ⊢ p (Nat.find h) ∧ ∀ (n : ℕ), n < Nat.find h → ¬p n
    exact ⟨Nat.find_spec h, fun _ => Nat.find_min h⟩
    -- 🎉 no goals
  · rintro ⟨hm, hlt⟩
    -- ⊢ Nat.find h = m
    exact le_antisymm (Nat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| Nat.find_spec h)
    -- 🎉 no goals
#align nat.find_eq_iff Nat.find_eq_iff

@[simp]
theorem find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨Nat.find h, h2, Nat.find_spec h⟩,
   fun ⟨_, hmn, hm⟩ => (Nat.find_min' h hm).trans_lt hmn⟩
#align nat.find_lt_iff Nat.find_lt_iff

@[simp]
theorem find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← lt_succ_iff, find_lt_iff]
  -- 🎉 no goals
#align nat.find_le_iff Nat.find_le_iff

@[simp]
theorem le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.find h ↔ ∀ m < n, ¬p m := by
  simp_rw [← not_lt, find_lt_iff, not_exists, not_and]
  -- 🎉 no goals
#align nat.le_find_iff Nat.le_find_iff

@[simp]
theorem lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]
  -- 🎉 no goals
#align nat.lt_find_iff Nat.lt_find_iff

@[simp]
theorem find_eq_zero (h : ∃ n : ℕ, p n) : Nat.find h = 0 ↔ p 0 := by simp [find_eq_iff]
                                                                     -- 🎉 no goals
#align nat.find_eq_zero Nat.find_eq_zero

theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    Nat.find hp ≤ Nat.find hq :=
  Nat.find_min' _ (h _ (Nat.find_spec hq))
#align nat.find_mono Nat.find_mono

theorem find_le {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩
#align nat.find_le Nat.find_le

theorem find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 := by
  refine' (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn => _⟩
  -- ⊢ ¬p n
  cases' n with n
  -- ⊢ ¬p zero
  exacts [h0, @Nat.find_min (fun n => p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
  -- 🎉 no goals
#align nat.find_comp_succ Nat.find_comp_succ

end Find

/-! ### `find_greatest` -/


section FindGreatest

/-- `find_greatest P b` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
protected def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n
#align nat.find_greatest Nat.findGreatest

variable {P Q : ℕ → Prop} [DecidablePred P] {b : ℕ}

@[simp]
theorem findGreatest_zero : Nat.findGreatest P 0 = 0 :=
  rfl
#align nat.find_greatest_zero Nat.findGreatest_zero

theorem findGreatest_succ (n : ℕ) :
    Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n :=
  rfl
#align nat.find_greatest_succ Nat.findGreatest_succ

@[simp]
theorem findGreatest_eq : ∀ {b}, P b → Nat.findGreatest P b = b
  | 0, _ => rfl
  | n + 1, h => by simp [Nat.findGreatest, h]
                   -- 🎉 no goals
#align nat.find_greatest_eq Nat.findGreatest_eq

@[simp]
theorem findGreatest_of_not (h : ¬P (b + 1)) :
    Nat.findGreatest P (b + 1) = Nat.findGreatest P b := by
  simp [Nat.findGreatest, h]
  -- 🎉 no goals
#align nat.find_greatest_of_not Nat.findGreatest_of_not

end FindGreatest

/-! ### decidability of predicates -/

instance decidableBallLT :
    ∀ (n : Nat) (P : ∀ k < n, Prop) [∀ n h, Decidable (P n h)], Decidable (∀ n h, P n h)
| 0, P, _ => isTrue fun n h => by cases h
                                  -- 🎉 no goals
| (n+1), P, H => by
  cases' decidableBallLT n fun k h => P k (lt_succ_of_lt h) with h h
  -- ⊢ Decidable (∀ (n_1 : ℕ) (h : n_1 < n + 1), P n_1 h)
  · refine' isFalse (mt _ h)
    -- ⊢ (∀ (n_1 : ℕ) (h : n_1 < n + 1), P n_1 h) → ∀ (n_1 : ℕ) (h : n_1 < n), P n_1  …
    intro hn k h
    -- ⊢ P k (_ : k < succ n)
    apply hn
    -- 🎉 no goals
  by_cases p : P n (lt_succ_self n)
  -- ⊢ Decidable (∀ (n_1 : ℕ) (h : n_1 < n + 1), P n_1 h)
  · exact
      isTrue fun k h' =>
        (le_of_lt_succ h').lt_or_eq_dec.elim (h _) fun e =>
          match k, e, h' with
          | _, rfl, _ => p
  · exact isFalse (mt (fun hn => hn _ _) p)
    -- 🎉 no goals
#align nat.decidable_ball_lt Nat.decidableBallLT

instance decidableForallFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    Decidable (∀ i, P i) :=
  decidable_of_iff (∀ k h, P ⟨k, h⟩) ⟨fun a ⟨k, h⟩ => a k h, fun a k h => a ⟨k, h⟩⟩
#align nat.decidable_forall_fin Nat.decidableForallFin

instance decidableBallLe (n : ℕ) (P : ∀ k ≤ n, Prop) [∀ n h, Decidable (P n h)] :
    Decidable (∀ n h, P n h) :=
  decidable_of_iff (∀ (k) (h : k < succ n), P k (le_of_lt_succ h))
    ⟨fun a k h => a k (lt_succ_of_le h), fun a k _ => a k _⟩
#align nat.decidable_ball_le Nat.decidableBallLe

instance decidableExistsLT {P : ℕ → Prop} [h : DecidablePred P] :
    DecidablePred fun n => ∃ m : ℕ, m < n ∧ P m
  | 0 => isFalse (by simp)
                     -- 🎉 no goals
  | n + 1 =>
    @decidable_of_decidable_of_iff _ _ (@instDecidableOr _ _ (decidableExistsLT n) (h n))
      (by simp only [lt_succ_iff_lt_or_eq, or_and_right, exists_or, exists_eq_left]; apply Iff.refl)
          -- ⊢ (∃ m, m < n ∧ ?m.69800 n m) ∨ P n ↔ (∃ x, x < n ∧ P x) ∨ P n
                                                                                     -- 🎉 no goals
#align nat.decidable_exists_lt Nat.decidableExistsLT

instance decidableExistsLe {P : ℕ → Prop} [DecidablePred P] :
    DecidablePred fun n => ∃ m : ℕ, m ≤ n ∧ P m :=
  fun n => decidable_of_iff (∃ m, m < n + 1 ∧ P m)
    (exists_congr fun _ => and_congr_left' lt_succ_iff)
#align nat.decidable_exists_le Nat.decidableExistsLe

end Nat
