/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Cyclic

#align_import group_theory.specific_groups.quaternion from "leanprover-community/mathlib"@"879155bff5af618b9062cbb2915347dafd749ad6"

/-!
# Quaternion Groups

We define the (generalised) quaternion groups `QuaternionGroup n` of order `4n`, also known as
dicyclic groups, with elements `a i` and `xa i` for `i : ZMod n`. The (generalised) quaternion
groups can be defined by the presentation
$\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We write `a i` for
$a^i$ and `xa i` for $x * a^i$. For `n=2` the quaternion group `QuaternionGroup 2` is isomorphic to
the unit integral quaternions `(Quaternion ℤ)ˣ`.

## Main definition

`QuaternionGroup n`: The (generalised) quaternion group of order `4n`.

## Implementation notes

This file is heavily based on `DihedralGroup` by Shing Tak Lam.

In mathematics, the name "quaternion group" is reserved for the cases `n ≥ 2`. Since it would be
inconvenient to carry around this condition we define `QuaternionGroup` also for `n = 0` and
`n = 1`. `QuaternionGroup 0` is isomorphic to the infinite dihedral group, while
`QuaternionGroup 1` is isomorphic to a cyclic group of order `4`.

## References

* https://en.wikipedia.org/wiki/Dicyclic_group
* https://en.wikipedia.org/wiki/Quaternion_group

## TODO

Show that `QuaternionGroup 2 ≃* (Quaternion ℤ)ˣ`.

-/


/-- The (generalised) quaternion group `QuaternionGroup n` of order `4n`. It can be defined by the
presentation $\langle a, x | a^{2n} = 1, x^2 = a^n, x^{-1}ax=a^{-1}\rangle$. We write `a i` for
$a^i$ and `xa i` for $x * a^i$.
-/
inductive QuaternionGroup (n : ℕ) : Type
  | a : ZMod (2 * n) → QuaternionGroup n
  | xa : ZMod (2 * n) → QuaternionGroup n
  deriving DecidableEq
#align quaternion_group QuaternionGroup

namespace QuaternionGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : QuaternionGroup n → QuaternionGroup n → QuaternionGroup n
  | a i, a j => a (i + j)
  | a i, xa j => xa (j - i)
  | xa i, a j => xa (i + j)
  | xa i, xa j => a (n + j - i)

/-- The identity `1` is given by `aⁱ`.
-/
private def one : QuaternionGroup n :=
  a 0

instance : Inhabited (QuaternionGroup n) :=
  ⟨one⟩

/-- The inverse of an element of the quaternion group.
-/
private def inv : QuaternionGroup n → QuaternionGroup n
  | a i => a (-i)
  | xa i => xa (n + i)

/-- The group structure on `QuaternionGroup n`.
-/
instance : Group (QuaternionGroup n) where
  mul := mul
  mul_assoc := by
    rintro (i | i) (j | j) (k | k) <;> simp only [(· * ·), mul] <;> ring_nf
                                       -- ⊢ a (i + j + k) = a (i + (j + k))
                                       -- ⊢ xa (k - (i + j)) = xa (k - j - i)
                                       -- ⊢ xa (j - i + k) = xa (j + k - i)
                                       -- ⊢ a (↑n + k - (j - i)) = a (i + (↑n + k - j))
                                       -- ⊢ xa (i + j + k) = xa (i + (j + k))
                                       -- ⊢ a (↑n + k - (i + j)) = a (↑n + (k - j) - i)
                                       -- ⊢ a (↑n + j - i + k) = a (↑n + (j + k) - i)
                                       -- ⊢ xa (k - (↑n + j - i)) = xa (i + (↑n + k - j))
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- ⊢ xa (k + (-↑n - j) + i) = xa (k + (↑n - j) + i)
    congr
    -- ⊢ -↑n = ↑n
    calc
      -(n : ZMod (2 * n)) = 0 - n := by rw [zero_sub]
      _ = 2 * n - n := by norm_cast; simp
      _ = n := by ring
  one := one
  one_mul := by
    rintro (i | i)
    -- ⊢ 1 * a i = a i
    · exact congr_arg a (zero_add i)
      -- 🎉 no goals
    · exact congr_arg xa (sub_zero i)
      -- 🎉 no goals
  mul_one := by
    rintro (i | i)
    -- ⊢ a i * 1 = a i
    · exact congr_arg a (add_zero i)
      -- 🎉 no goals
    · exact congr_arg xa (add_zero i)
      -- 🎉 no goals
  inv := inv
  mul_left_inv := by
    rintro (i | i)
    -- ⊢ (a i)⁻¹ * a i = 1
    · exact congr_arg a (neg_add_self i)
      -- 🎉 no goals
    · exact congr_arg a (sub_self (n + i))
      -- 🎉 no goals

@[simp]
theorem a_mul_a (i j : ZMod (2 * n)) : a i * a j = a (i + j) :=
  rfl
#align quaternion_group.a_mul_a QuaternionGroup.a_mul_a

@[simp]
theorem a_mul_xa (i j : ZMod (2 * n)) : a i * xa j = xa (j - i) :=
  rfl
#align quaternion_group.a_mul_xa QuaternionGroup.a_mul_xa

@[simp]
theorem xa_mul_a (i j : ZMod (2 * n)) : xa i * a j = xa (i + j) :=
  rfl
#align quaternion_group.xa_mul_a QuaternionGroup.xa_mul_a

@[simp]
theorem xa_mul_xa (i j : ZMod (2 * n)) : xa i * xa j = a ((n : ZMod (2 * n)) + j - i) :=
  rfl
#align quaternion_group.xa_mul_xa QuaternionGroup.xa_mul_xa

theorem one_def : (1 : QuaternionGroup n) = a 0 :=
  rfl
#align quaternion_group.one_def QuaternionGroup.one_def

private def fintypeHelper : Sum (ZMod (2 * n)) (ZMod (2 * n)) ≃ QuaternionGroup n where
  invFun i :=
    match i with
    | a j => Sum.inl j
    | xa j => Sum.inr j
  toFun i :=
    match i with
    | Sum.inl j => a j
    | Sum.inr j => xa j
  left_inv := by rintro (x | x) <;> rfl
                                    -- 🎉 no goals
                                    -- 🎉 no goals
  right_inv := by rintro (x | x) <;> rfl
                                     -- 🎉 no goals
                                     -- 🎉 no goals

/-- The special case that more or less by definition `QuaternionGroup 0` is isomorphic to the
infinite dihedral group. -/
def quaternionGroupZeroEquivDihedralGroupZero : QuaternionGroup 0 ≃* DihedralGroup 0 where
  toFun i :=
    -- Porting note: Originally `QuaternionGroup.recOn i DihedralGroup.r DihedralGroup.sr`
    match i with
    | a j => DihedralGroup.r j
    | xa j => DihedralGroup.sr j
  invFun i :=
    match i with
    | DihedralGroup.r j => a j
    | DihedralGroup.sr j => xa j
  left_inv := by rintro (k | k) <;> rfl
                                    -- 🎉 no goals
                                    -- 🎉 no goals
  right_inv := by rintro (k | k) <;> rfl
                                     -- 🎉 no goals
                                     -- 🎉 no goals
  map_mul' := by rintro (k | k) (l | l) <;> simp
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
                                            -- 🎉 no goals
#align quaternion_group.quaternion_group_zero_equiv_dihedral_group_zero QuaternionGroup.quaternionGroupZeroEquivDihedralGroupZero

/-- If `0 < n`, then `QuaternionGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (QuaternionGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Nontrivial (QuaternionGroup n) :=
  ⟨⟨a 0, xa 0, by revert n; simp⟩⟩ -- Porting note: `revert n; simp` was `decide`
                  -- ⊢ ∀ {n : ℕ}, a 0 ≠ xa 0
                            -- 🎉 no goals

/-- If `0 < n`, then `QuaternionGroup n` has `4n` elements.
-/
theorem card [NeZero n] : Fintype.card (QuaternionGroup n) = 4 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]
  -- ⊢ n + n + (n + n) = 4 * n
  ring
  -- 🎉 no goals
#align quaternion_group.card QuaternionGroup.card

@[simp]
theorem a_one_pow (k : ℕ) : (a 1 : QuaternionGroup n) ^ k = a k := by
  induction' k with k IH
  -- ⊢ a 1 ^ Nat.zero = a ↑Nat.zero
  · rw [Nat.cast_zero]; rfl
    -- ⊢ a 1 ^ Nat.zero = a 0
                        -- 🎉 no goals
  · rw [pow_succ, IH, a_mul_a]
    -- ⊢ a (1 + ↑k) = a ↑(Nat.succ k)
    congr 1
    -- ⊢ 1 + ↑k = ↑(Nat.succ k)
    norm_cast
    -- ⊢ ↑(1 + k) = ↑(Nat.succ k)
    rw [Nat.one_add]
    -- 🎉 no goals
#align quaternion_group.a_one_pow QuaternionGroup.a_one_pow

-- @[simp] -- Porting note: simp changes this to `a 0 = 1`, so this is no longer a good simp lemma.
theorem a_one_pow_n : (a 1 : QuaternionGroup n) ^ (2 * n) = 1 := by
  rw [a_one_pow, one_def]
  -- ⊢ a ↑(2 * n) = a 0
  congr 1
  -- ⊢ ↑(2 * n) = 0
  exact ZMod.nat_cast_self _
  -- 🎉 no goals
#align quaternion_group.a_one_pow_n QuaternionGroup.a_one_pow_n

@[simp]
theorem xa_sq (i : ZMod (2 * n)) : xa i ^ 2 = a n := by simp [sq]
                                                        -- 🎉 no goals
#align quaternion_group.xa_sq QuaternionGroup.xa_sq

@[simp]
theorem xa_pow_four (i : ZMod (2 * n)) : xa i ^ 4 = 1 := by
  rw [pow_succ, pow_succ, sq, xa_mul_xa, xa_mul_a, xa_mul_xa, add_sub_cancel, add_sub_assoc,
    add_sub_cancel']
  norm_cast
  -- ⊢ a ↑(n + n) = 1
  rw [← two_mul]
  -- ⊢ a ↑(2 * n) = 1
  simp [one_def]
  -- 🎉 no goals
#align quaternion_group.xa_pow_four QuaternionGroup.xa_pow_four

/-- If `0 < n`, then `xa i` has order 4.
-/
@[simp]
theorem orderOf_xa [NeZero n] (i : ZMod (2 * n)) : orderOf (xa i) = 4 := by
  change _ = 2 ^ 2
  -- ⊢ orderOf (xa i) = 2 ^ 2
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  -- ⊢ orderOf (xa i) = 2 ^ 2
  apply orderOf_eq_prime_pow
  -- ⊢ ¬xa i ^ 2 ^ 1 = 1
  · intro h
    -- ⊢ False
    simp only [pow_one, xa_sq] at h
    -- ⊢ False
    injection h with h'
    -- ⊢ False
    apply_fun ZMod.val at h'
    -- ⊢ False
    apply_fun (· / n) at h'
    -- ⊢ False
    simp only [ZMod.val_nat_cast, ZMod.val_zero, Nat.zero_div, Nat.mod_mul_left_div_self,
      Nat.div_self (NeZero.pos n)] at h'
  · norm_num
    -- 🎉 no goals
#align quaternion_group.order_of_xa QuaternionGroup.orderOf_xa

/-- In the special case `n = 1`, `Quaternion 1` is a cyclic group (of order `4`). -/
theorem quaternionGroup_one_isCyclic : IsCyclic (QuaternionGroup 1) := by
  apply isCyclic_of_orderOf_eq_card
  -- ⊢ orderOf ?x = Fintype.card (QuaternionGroup 1)
  rw [card, mul_one]
  exact orderOf_xa 0
  -- 🎉 no goals
#align quaternion_group.quaternion_group_one_is_cyclic QuaternionGroup.quaternionGroup_one_isCyclic

/-- If `0 < n`, then `a 1` has order `2 * n`.
-/
@[simp]
theorem orderOf_a_one : orderOf (a 1 : QuaternionGroup n) = 2 * n := by
  cases' eq_zero_or_neZero n with hn hn
  -- ⊢ orderOf (a 1) = 2 * n
  · subst hn
    -- ⊢ orderOf (a 1) = 2 * 0
    simp_rw [mul_zero, orderOf_eq_zero_iff']
    -- ⊢ ∀ (n : ℕ), 0 < n → QuaternionGroup.a 1 ^ n ≠ 1
    intro n h
    -- ⊢ a 1 ^ n ≠ 1
    rw [one_def, a_one_pow]
    -- ⊢ a ↑n ≠ a 0
    apply mt a.inj
    -- ⊢ ¬↑n = 0
    haveI : CharZero (ZMod (2 * 0)) := ZMod.charZero
    -- ⊢ ¬↑n = 0
    simpa using h.ne'
    -- 🎉 no goals
  apply (Nat.le_of_dvd
    (NeZero.pos _) (orderOf_dvd_of_pow_eq_one (@a_one_pow_n n))).lt_or_eq.resolve_left
  intro h
  -- ⊢ False
  have h1 : (a 1 : QuaternionGroup n) ^ orderOf (a 1) = 1 := pow_orderOf_eq_one _
  -- ⊢ False
  rw [a_one_pow] at h1
  -- ⊢ False
  injection h1 with h2
  -- ⊢ False
  rw [← ZMod.val_eq_zero, ZMod.val_nat_cast, Nat.mod_eq_of_lt h] at h2
  -- ⊢ False
  exact absurd h2.symm (orderOf_pos _).ne
  -- 🎉 no goals
#align quaternion_group.order_of_a_one QuaternionGroup.orderOf_a_one

/-- If `0 < n`, then `a i` has order `(2 * n) / gcd (2 * n) i`.
-/
theorem orderOf_a [NeZero n] (i : ZMod (2 * n)) :
    orderOf (a i) = 2 * n / Nat.gcd (2 * n) i.val := by
  conv_lhs => rw [← ZMod.nat_cast_zmod_val i]
  -- ⊢ orderOf (a ↑(ZMod.val i)) = 2 * n / Nat.gcd (2 * n) (ZMod.val i)
  rw [← a_one_pow, orderOf_pow, orderOf_a_one]
  -- 🎉 no goals
#align quaternion_group.order_of_a QuaternionGroup.orderOf_a

theorem exponent : Monoid.exponent (QuaternionGroup n) = 2 * lcm n 2 := by
  rw [← normalize_eq 2, ← lcm_mul_left, normalize_eq]
  -- ⊢ Monoid.exponent (QuaternionGroup n) = lcm (2 * n) (2 * 2)
  norm_num
  -- ⊢ Monoid.exponent (QuaternionGroup n) = lcm (2 * n) 4
  cases' eq_zero_or_neZero n with hn hn
  -- ⊢ Monoid.exponent (QuaternionGroup n) = lcm (2 * n) 4
  · subst hn
    -- ⊢ Monoid.exponent (QuaternionGroup 0) = lcm (2 * 0) 4
    simp only [lcm_zero_left, mul_zero]
    -- ⊢ Monoid.exponent (QuaternionGroup 0) = 0
    exact Monoid.exponent_eq_zero_of_order_zero orderOf_a_one
    -- 🎉 no goals
  apply Nat.dvd_antisymm
  -- ⊢ Monoid.exponent (QuaternionGroup n) ∣ lcm (2 * n) 4
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    -- ⊢ ∀ (g : QuaternionGroup n), g ^ lcm (2 * n) 4 = 1
    rintro (m | m)
    -- ⊢ a m ^ lcm (2 * n) 4 = 1
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_a]
      -- ⊢ 2 * n / Nat.gcd (2 * n) (ZMod.val m) ∣ lcm (2 * n) 4
      refine' Nat.dvd_trans ⟨gcd (2 * n) m.val, _⟩ (dvd_lcm_left (2 * n) 4)
      -- ⊢ 2 * n = 2 * n / Nat.gcd (2 * n) (ZMod.val m) * gcd (2 * n) (ZMod.val m)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * n) m.val)).symm
      -- 🎉 no goals
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_xa]
      -- ⊢ 4 ∣ lcm (2 * n) 4
      exact dvd_lcm_right (2 * n) 4
      -- 🎉 no goals
  · apply lcm_dvd
    -- ⊢ 2 * n ∣ Monoid.exponent (QuaternionGroup n)
    · convert Monoid.order_dvd_exponent (a 1)
      -- ⊢ 2 * n = orderOf (a 1)
      exact orderOf_a_one.symm
      -- 🎉 no goals
    · convert Monoid.order_dvd_exponent (xa (0 : ZMod (2 * n)))
      -- ⊢ 4 = orderOf (xa 0)
      exact (orderOf_xa 0).symm
      -- 🎉 no goals
#align quaternion_group.exponent QuaternionGroup.exponent

end QuaternionGroup
