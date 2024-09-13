/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Units
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.NeZero
import Mathlib.Order.BoundedOrder

/-!
# Canonically ordered monoids
-/

universe u

variable {α : Type u}

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `OrderedAddCommGroup`s. -/
class CanonicallyOrderedAddCommMonoid (α : Type*) extends OrderedAddCommMonoid α, OrderBot α where
  /-- For `a ≤ b`, there is a `c` so `b = a + c`. -/
  protected exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a + c
  /-- For any `a` and `b`, `a ≤ a + b` -/
  protected le_self_add : ∀ a b : α, a ≤ a + b

-- see Note [lower instance priority]
attribute [instance 100] CanonicallyOrderedAddCommMonoid.toOrderBot

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `OrderDual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[to_additive]
class CanonicallyOrderedCommMonoid (α : Type*) extends OrderedCommMonoid α, OrderBot α where
  /-- For `a ≤ b`, there is a `c` so `b = a * c`. -/
  protected exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a * c
  /-- For any `a` and `b`, `a ≤ a * b` -/
  protected le_self_mul : ∀ a b : α, a ≤ a * b

-- see Note [lower instance priority]
attribute [instance 100] CanonicallyOrderedCommMonoid.toOrderBot

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyOrderedCommMonoid.existsMulOfLE (α : Type u)
    [h : CanonicallyOrderedCommMonoid α] : ExistsMulOfLE α :=
  { h with }

section CanonicallyOrderedCommMonoid

variable [CanonicallyOrderedCommMonoid α] {a b c d : α}

@[to_additive]
theorem le_self_mul : a ≤ a * c :=
  CanonicallyOrderedCommMonoid.le_self_mul _ _

@[to_additive]
theorem le_mul_self : a ≤ b * a := by
  rw [mul_comm]
  exact le_self_mul

@[to_additive (attr := simp)]
theorem self_le_mul_right (a b : α) : a ≤ a * b :=
  le_self_mul

@[to_additive (attr := simp)]
theorem self_le_mul_left (a b : α) : a ≤ b * a :=
  le_mul_self

@[to_additive]
theorem le_of_mul_le_left : a * b ≤ c → a ≤ c :=
  le_self_mul.trans

@[to_additive]
theorem le_of_mul_le_right : a * b ≤ c → b ≤ c :=
  le_mul_self.trans

@[to_additive]
theorem le_mul_of_le_left : a ≤ b → a ≤ b * c :=
  le_self_mul.trans'

@[to_additive]
theorem le_mul_of_le_right : a ≤ c → a ≤ b * c :=
  le_mul_self.trans'

@[to_additive]
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
  ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

@[to_additive]
theorem le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a := by
  simp only [mul_comm _ a, le_iff_exists_mul]

@[to_additive (attr := simp) zero_le]
theorem one_le (a : α) : 1 ≤ a :=
  le_iff_exists_mul.mpr ⟨a, (one_mul _).symm⟩

@[to_additive]
theorem bot_eq_one : (⊥ : α) = 1 :=
  le_antisymm bot_le (one_le ⊥)

@[to_additive] instance CanonicallyOrderedCommMonoid.toUniqueUnits : Unique αˣ where
  uniq a := Units.ext ((mul_eq_one_iff_of_one_le (α := α) (one_le _) <| one_le _).1 a.mul_inv).1

@[deprecated (since := "2024-07-24")] alias mul_eq_one_iff := mul_eq_one
@[deprecated (since := "2024-07-24")] alias add_eq_zero_iff := add_eq_zero

@[to_additive (attr := simp)]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  (one_le a).le_iff_eq

@[to_additive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  (one_le a).lt_iff_ne.trans ne_comm

@[to_additive]
theorem eq_one_or_one_lt (a : α) : a = 1 ∨ 1 < a := (one_le a).eq_or_lt.imp_left Eq.symm

@[to_additive]
lemma one_not_mem_iff {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, 1 < x :=
  bot_eq_one (α := α) ▸ bot_not_mem_iff

@[to_additive (attr := simp) add_pos_iff]
theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

@[to_additive]
theorem exists_one_lt_mul_of_lt (h : a < b) : ∃ (c : _) (_ : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc, lt_irrefl] at h

@[to_additive]
theorem le_mul_left (h : a ≤ c) : a ≤ b * c :=
  calc
    a = 1 * a := by simp
    _ ≤ b * c := mul_le_mul' (one_le _) h

@[to_additive]
theorem le_mul_right (h : a ≤ b) : a ≤ b * c :=
  calc
    a = a * 1 := by simp
    _ ≤ b * c := mul_le_mul' h (one_le _)

@[to_additive]
theorem lt_iff_exists_mul [CovariantClass α α (· * ·) (· < ·)] : a < b ↔ ∃ c > 1, b = a * c := by
  rw [lt_iff_le_and_ne, le_iff_exists_mul, ← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm, and_congr_left_iff, gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'

end CanonicallyOrderedCommMonoid

theorem pos_of_gt {M : Type*} [CanonicallyOrderedAddCommMonoid M] {n m : M} (h : n < m) : 0 < m :=
  lt_of_le_of_lt (zero_le _) h

namespace NeZero

theorem pos {M} (a : M) [CanonicallyOrderedAddCommMonoid M] [NeZero a] : 0 < a :=
  (zero_le a).lt_of_ne <| NeZero.out.symm

theorem of_gt {M} [CanonicallyOrderedAddCommMonoid M] {x y : M} (h : x < y) : NeZero y :=
  of_pos <| pos_of_gt h

-- 1 < p is still an often-used `Fact`, due to `Nat.Prime` implying it, and it implying `Nontrivial`
-- on `ZMod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
instance (priority := 10) of_gt' {M : Type*} [CanonicallyOrderedAddCommMonoid M] [One M] {y : M}
  -- Porting note: Fact.out has different type signature from mathlib3
  [Fact (1 < y)] : NeZero y := of_gt <| @Fact.out (1 < y) _

end NeZero

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
class CanonicallyLinearOrderedAddCommMonoid (α : Type*)
  extends CanonicallyOrderedAddCommMonoid α, LinearOrderedAddCommMonoid α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[to_additive]
class CanonicallyLinearOrderedCommMonoid (α : Type*)
  extends CanonicallyOrderedCommMonoid α, LinearOrderedCommMonoid α

attribute [to_additive existing] CanonicallyLinearOrderedCommMonoid.toLinearOrderedCommMonoid

section CanonicallyLinearOrderedCommMonoid

variable [CanonicallyLinearOrderedCommMonoid α]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyLinearOrderedCommMonoid.semilatticeSup : SemilatticeSup α :=
  { LinearOrder.toLattice with }

@[to_additive]
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

@[to_additive]
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_comm _ c] using min_mul_distrib c a b

-- Porting note (#10618): no longer `@[simp]`, as `simp` can prove this.
@[to_additive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_left (one_le a)

-- Porting note (#10618): no longer `@[simp]`, as `simp` can prove this.
@[to_additive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_right (one_le a)

/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[to_additive (attr := simp)
  "In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma"]
theorem bot_eq_one' : (⊥ : α) = 1 :=
  bot_eq_one

end CanonicallyLinearOrderedCommMonoid
