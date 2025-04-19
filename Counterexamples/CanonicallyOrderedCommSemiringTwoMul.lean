/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Ring.Subsemiring.Order
import Mathlib.Data.ZMod.Basic

/-!

A canonically ordered commutative semiring with two different elements `a` and `b` such that
`a ≠ b` and `2 * a = 2 * b`.  Thus, multiplication by a fixed non-zero element of a canonically
ordered semiring need not be injective.  In particular, multiplying by a strictly positive element
need not be strictly monotone.

Recall that a canonically ordered commutative semiring is a commutative semiring with a partial
ordering that is "canonical" in the sense that the inequality `a ≤ b` holds if and only if there is
a `c` such that `a + c = b`.  There are several compatibility conditions among
addition/multiplication and the order relation.  The point of the counterexample is to show that
monotonicity of multiplication cannot be strengthened to **strict** monotonicity.

Reference:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology
-/



namespace Counterexample

theorem mem_zmod_2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases a with ⟨_ | _, _ | _ | _ | _⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem add_self_zmod_2 (a : ZMod 2) : a + a = 0 := by rcases mem_zmod_2 a with (rfl | rfl) <;> rfl

namespace Nxzmod2

variable {a b : ℕ × ZMod 2}

/-- The preorder relation on `ℕ × ℤ/2ℤ` where we only compare the first coordinate,
except that we leave incomparable each pair of elements with the same first component.
For instance, `∀ α, β ∈ ℤ/2ℤ`, the inequality `(1,α) ≤ (2,β)` holds,
whereas, `∀ n ∈ ℤ`, the elements `(n,0)` and `(n,1)` are incomparable. -/
instance preN2 : PartialOrder (ℕ × ZMod 2) where
  le x y := x = y ∨ x.1 < y.1
  le_refl a := Or.inl rfl
  le_trans x y z xy yz := by
    rcases xy with (rfl | xy)
    · exact yz
    · rcases yz with (rfl | yz)
      · exact Or.inr xy
      · exact Or.inr (xy.trans yz)
  le_antisymm := by
    intro a b ab ba
    obtain ab | ab := ab
    · exact ab
    · obtain ba | ba := ba
      · exact ba.symm
      · exact (Nat.lt_asymm ab ba).elim

instance csrN2 : CommSemiring (ℕ × ZMod 2) := by infer_instance

instance csrN21 : AddCancelCommMonoid (ℕ × ZMod 2) :=
  { Nxzmod2.csrN2 with add_left_cancel := fun a _ _ h => (add_right_inj a).mp h }

/-- A strict inequality forces the first components to be different. -/
@[simp]
theorem lt_def : a < b ↔ a.1 < b.1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨rfl | a1, h1⟩
    · exact (not_or.mp h1).1.elim rfl
    · exact a1
  refine ⟨Or.inr h, not_or.mpr ⟨fun k => ?_, not_lt.mpr h.le⟩⟩
  rw [k] at h
  exact Nat.lt_asymm h h

theorem add_left_cancel : ∀ a b c : ℕ × ZMod 2, a + b = a + c → b = c := fun a _ _ h =>
  (add_right_inj a).mp h

theorem add_le_add_left : ∀ a b : ℕ × ZMod 2, a ≤ b → ∀ c : ℕ × ZMod 2, c + a ≤ c + b := by
  rintro a b (rfl | ab) c
  · rfl
  · exact Or.inr (by simpa)

theorem le_of_add_le_add_left : ∀ a b c : ℕ × ZMod 2, a + b ≤ a + c → b ≤ c := by
  rintro a b c (bc | bc)
  · exact le_of_eq ((add_right_inj a).mp bc)
  · exact Or.inr (by simpa using bc)

instance : ZeroLEOneClass (ℕ × ZMod 2) :=
  ⟨by dsimp only [LE.le]; decide⟩

theorem mul_lt_mul_of_pos_left : ∀ a b c : ℕ × ZMod 2, a < b → 0 < c → c * a < c * b :=
  fun _ _ _ ab c0 => lt_def.mpr ((mul_lt_mul_left (lt_def.mp c0)).mpr (lt_def.mp ab))

theorem mul_lt_mul_of_pos_right : ∀ a b c : ℕ × ZMod 2, a < b → 0 < c → a * c < b * c :=
  fun _ _ _ ab c0 => lt_def.mpr ((mul_lt_mul_right (lt_def.mp c0)).mpr (lt_def.mp ab))

instance isorN2 : IsStrictOrderedRing (ℕ × ZMod 2) :=
  { add_le_add_left := add_le_add_left
    le_of_add_le_add_left := le_of_add_le_add_left
    zero_le_one := zero_le_one
    mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left
    mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right }

end Nxzmod2

namespace ExL

open Nxzmod2 Subtype

/-- Initially, `L` was defined as the subsemiring closure of `(1,0)`. -/
def L : Type :=
  { l : ℕ × ZMod 2 // l ≠ (0, 1) }

theorem add_L {a b : ℕ × ZMod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) : a + b ≠ (0, 1) := by
  rcases a with ⟨a, a2⟩
  rcases b with ⟨b, b2⟩
  match b with
  | 0 =>
    rcases mem_zmod_2 b2 with (rfl | rfl)
    · simp [ha, -Prod.mk.injEq]
    · cases hb rfl
  | b + 1 =>
    simp [(a + b).succ_ne_zero]

theorem mul_L {a b : ℕ × ZMod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) : a * b ≠ (0, 1) := by
  rcases a with ⟨a, a2⟩
  rcases b with ⟨b, b2⟩
  cases b
  · rcases mem_zmod_2 b2 with (rfl | rfl) <;> rcases mem_zmod_2 a2 with (rfl | rfl) <;>
      simp only [Prod.mk_mul_mk, mul_zero, mul_one, ne_eq, Prod.mk.injEq, zero_ne_one, and_false,
        not_false_eq_true, not_true_eq_false]
    exact hb rfl
  cases a
  · rcases mem_zmod_2 b2 with (rfl | rfl) <;> rcases mem_zmod_2 a2 with (rfl | rfl) <;>
      simp only [Prod.mk_mul_mk, mul_zero, zero_mul, mul_one, ne_eq, Prod.mk.injEq, zero_ne_one,
        and_false, not_false_eq_true, not_true_eq_false]
    exact ha rfl
  · simp [mul_ne_zero _ _, Nat.succ_ne_zero _]

/-- The subsemiring corresponding to the elements of `L`, used to transfer instances. -/
def lSubsemiring : Subsemiring (ℕ × ZMod 2) where
  carrier := {l | l ≠ (0, 1)}
  zero_mem' := by decide
  one_mem' := by decide
  add_mem' := add_L
  mul_mem' := mul_L

instance : CommSemiring L :=
  lSubsemiring.toCommSemiring

instance : PartialOrder L :=
  Subtype.partialOrder _

instance : IsOrderedRing L :=
  lSubsemiring.toIsOrderedRing

instance inhabited : Inhabited L :=
  ⟨1⟩

theorem bot_le : ∀ a : L, 0 ≤ a := by
  rintro ⟨⟨an, a2⟩, ha⟩
  cases an
  · rcases mem_zmod_2 a2 with (rfl | rfl)
    · rfl
    · exact (ha rfl).elim
  · refine Or.inr ?_
    exact Nat.succ_pos _

instance orderBot : OrderBot L where
  bot := 0
  bot_le := bot_le

theorem exists_add_of_le : ∀ a b : L, a ≤ b → ∃ c, b = a + c := by
  rintro a ⟨b, _⟩ (⟨rfl, rfl⟩ | h)
  · exact ⟨0, (add_zero _).symm⟩
  · exact
      ⟨⟨b - a.1, fun H => (tsub_pos_of_lt h).ne' (Prod.mk_inj.1 H).1⟩,
        Subtype.ext <| Prod.ext (add_tsub_cancel_of_le h.le).symm (add_sub_cancel _ _).symm⟩

theorem le_self_add : ∀ a b : L, a ≤ a + b := by
  rintro a ⟨⟨bn, b2⟩, hb⟩
  obtain rfl | h := Nat.eq_zero_or_pos bn
  · obtain rfl | rfl := mem_zmod_2 b2
    · exact Or.inl (Prod.ext (add_zero _).symm (add_zero _).symm)
    · exact (hb rfl).elim
  · exact Or.inr ((lt_add_iff_pos_right _).mpr h)

theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : L, a * b = 0 → a = 0 ∨ b = 0 := by
  rintro ⟨⟨a, a2⟩, ha⟩ ⟨⟨b, b2⟩, hb⟩ ab1
  injection ab1 with ab
  injection ab with abn ab2
  rw [mul_eq_zero] at abn
  rcases abn with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · refine Or.inl ?_
    rcases mem_zmod_2 a2 with (rfl | rfl)
    · rfl
    · exact (ha rfl).elim
  · refine Or.inr ?_
    rcases mem_zmod_2 b2 with (rfl | rfl)
    · rfl
    · exact (hb rfl).elim

instance : CommSemiring L := inferInstance

instance : PartialOrder L := inferInstance

instance : IsOrderedRing L := inferInstance

instance : CanonicallyOrderedAdd L where
  exists_add_of_le := @(exists_add_of_le)
  le_self_add := le_self_add

instance : NoZeroDivisors L where
  eq_zero_or_eq_zero_of_mul_eq_zero := @(eq_zero_or_eq_zero_of_mul_eq_zero)

/-- The elements `(1,0)` and `(1,1)` of `L` are different, but their doubles coincide.
-/
example : ∃ a b : L, a ≠ b ∧ 2 * a = 2 * b := by
  refine ⟨⟨(1, 0), by simp⟩, 1, fun h : (⟨(1, 0), _⟩ : L) = ⟨⟨1, 1⟩, _⟩ => ?_, rfl⟩
  obtain F : (0 : ZMod 2) = 1 := congr_arg (fun j : L => j.1.2) h
  cases F

end ExL

end Counterexample
