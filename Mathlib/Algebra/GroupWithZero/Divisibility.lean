/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Divisibility.Units

#align_import algebra.group_with_zero.divisibility from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

-/


variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
  Dvd.elim h fun c H' => H'.trans (zero_mul c)
#align eq_zero_of_zero_dvd eq_zero_of_zero_dvd

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp]
theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    rw [h]
    exact ⟨0, by simp⟩⟩
#align zero_dvd_iff zero_dvd_iff

@[simp]
theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by simp)
#align dvd_zero dvd_zero

end SemigroupWithZero

/-- Given two elements `b`, `c` of a `CancelMonoidWithZero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [CancelMonoidWithZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by rw [mul_assoc, mul_right_inj' ha]
#align mul_dvd_mul_iff_left mul_dvd_mul_iff_left

/-- Given two elements `a`, `b` of a commutative `CancelMonoidWithZero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [CancelCommMonoidWithZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by rw [mul_right_comm, mul_left_inj' hc]
#align mul_dvd_mul_iff_right mul_dvd_mul_iff_right

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- `DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def DvdNotUnit (a b : α) : Prop :=
  a ≠ 0 ∧ ∃ x, ¬IsUnit x ∧ b = a * x
#align dvd_not_unit DvdNotUnit

theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine' ⟨c, _, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd
#align dvd_not_unit_of_dvd_of_not_dvd dvdNotUnit_of_dvd_of_not_dvd

end CommMonoidWithZero

theorem dvd_and_not_dvd_iff [CancelCommMonoidWithZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
          ⟨e, mul_left_cancel₀ hx0 <| by conv =>
            lhs
            rw [he, hdx]
            simp [mul_assoc]⟩)⟩⟩
#align dvd_and_not_dvd_iff dvd_and_not_dvd_iff

section MonoidWithZero

variable [MonoidWithZero α]

theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 := by
  rcases h₂ with ⟨u, rfl⟩
  exact left_ne_zero_of_mul h₁
#align ne_zero_of_dvd_ne_zero ne_zero_of_dvd_ne_zero

end MonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] [Subsingleton αˣ] {a b : α}

theorem dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  rintro ⟨c, rfl⟩ ⟨d, hcd⟩
  rw [mul_assoc, eq_comm, mul_right_eq_self₀, mul_eq_one] at hcd
  obtain ⟨rfl, -⟩ | rfl := hcd <;> simp
#align dvd_antisymm dvd_antisymm

-- porting note: `attribute [protected]` is currently unsupported
-- attribute [protected] Nat.dvd_antisymm --This lemma is in core, so we protect it here

theorem dvd_antisymm' : a ∣ b → b ∣ a → b = a :=
  flip dvd_antisymm
#align dvd_antisymm' dvd_antisymm'

alias dvd_antisymm ← Dvd.dvd.antisymm
#align has_dvd.dvd.antisymm Dvd.dvd.antisymm

alias dvd_antisymm' ← Dvd.dvd.antisymm'
#align has_dvd.dvd.antisymm' Dvd.dvd.antisymm'

theorem eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b :=
  ((h _).2 dvd_rfl).antisymm <| (h _).1 dvd_rfl
#align eq_of_forall_dvd eq_of_forall_dvd

theorem eq_of_forall_dvd' (h : ∀ c, c ∣ a ↔ c ∣ b) : a = b :=
  ((h _).1 dvd_rfl).antisymm <| (h _).2 dvd_rfl
#align eq_of_forall_dvd' eq_of_forall_dvd'

end CancelCommMonoidWithZero
