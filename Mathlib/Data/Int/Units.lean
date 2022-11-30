/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Data.Nat.Units
import Mathbin.Data.Int.Basic
import Mathbin.Algebra.Ring.Units

/-!
# Lemmas about units in `ℤ`.
-/


namespace Int

/-! ### units -/


@[simp]
theorem units_nat_abs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← nat_abs_mul, Units.mul_inv] <;> rfl, by
        rw [← nat_abs_mul, Units.inv_mul] <;> rfl⟩
#align int.units_nat_abs Int.units_nat_abs

theorem units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff, units_nat_abs] using nat_abs_eq u
#align int.units_eq_one_or Int.units_eq_one_or

theorem is_unit_eq_one_or {a : ℤ} : IsUnit a → a = 1 ∨ a = -1
  | ⟨x, hx⟩ => hx ▸ (units_eq_one_or _).imp (congr_arg coe) (congr_arg coe)
#align int.is_unit_eq_one_or Int.is_unit_eq_one_or

theorem is_unit_iff {a : ℤ} : IsUnit a ↔ a = 1 ∨ a = -1 := by
  refine' ⟨fun h => is_unit_eq_one_or h, fun h => _⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact is_unit_one.neg
#align int.is_unit_iff Int.is_unit_iff

theorem is_unit_eq_or_eq_neg {a b : ℤ} (ha : IsUnit a) (hb : IsUnit b) : a = b ∨ a = -b := by
  rcases is_unit_eq_one_or hb with (rfl | rfl)
  · exact is_unit_eq_one_or ha
  · rwa [or_comm', neg_neg, ← is_unit_iff]
#align int.is_unit_eq_or_eq_neg Int.is_unit_eq_or_eq_neg

theorem eq_one_or_neg_one_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = 1 ∨ z = -1 :=
  is_unit_iff.mp (isUnit_of_mul_eq_one z w h)
#align int.eq_one_or_neg_one_of_mul_eq_one Int.eq_one_or_neg_one_of_mul_eq_one

theorem eq_one_or_neg_one_of_mul_eq_one' {z w : ℤ} (h : z * w = 1) :
    z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 := by
  have h' : w * z = 1 := mul_comm z w ▸ h
  rcases eq_one_or_neg_one_of_mul_eq_one h with (rfl | rfl) <;>
      rcases eq_one_or_neg_one_of_mul_eq_one h' with (rfl | rfl) <;>
    tauto
#align int.eq_one_or_neg_one_of_mul_eq_one' Int.eq_one_or_neg_one_of_mul_eq_one'

theorem mul_eq_one_iff_eq_one_or_neg_one {z w : ℤ} : z * w = 1 ↔ z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 :=
  by
  refine' ⟨eq_one_or_neg_one_of_mul_eq_one', fun h => Or.elim h (fun H => _) fun H => _⟩ <;>
      rcases H with ⟨rfl, rfl⟩ <;>
    rfl
#align int.mul_eq_one_iff_eq_one_or_neg_one Int.mul_eq_one_iff_eq_one_or_neg_one

theorem eq_one_or_neg_one_of_mul_eq_neg_one' {z w : ℤ} (h : z * w = -1) :
    z = 1 ∧ w = -1 ∨ z = -1 ∧ w = 1 := by
  rcases is_unit_eq_one_or (is_unit.mul_iff.mp (int.is_unit_iff.mpr (Or.inr h))).1 with (rfl | rfl)
  · exact Or.inl ⟨rfl, one_mul w ▸ h⟩
  · exact Or.inr ⟨rfl, neg_inj.mp (neg_one_mul w ▸ h)⟩
#align int.eq_one_or_neg_one_of_mul_eq_neg_one' Int.eq_one_or_neg_one_of_mul_eq_neg_one'

theorem mul_eq_neg_one_iff_eq_one_or_neg_one {z w : ℤ} :
    z * w = -1 ↔ z = 1 ∧ w = -1 ∨ z = -1 ∧ w = 1 := by
  refine' ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h => Or.elim h (fun H => _) fun H => _⟩ <;>
      rcases H with ⟨rfl, rfl⟩ <;>
    rfl
#align int.mul_eq_neg_one_iff_eq_one_or_neg_one Int.mul_eq_neg_one_iff_eq_one_or_neg_one

theorem is_unit_iff_nat_abs_eq {n : ℤ} : IsUnit n ↔ n.natAbs = 1 := by
  simp [nat_abs_eq_iff, is_unit_iff, Nat.cast_zero]
#align int.is_unit_iff_nat_abs_eq Int.is_unit_iff_nat_abs_eq

alias is_unit_iff_nat_abs_eq ↔ is_unit.nat_abs_eq _

@[norm_cast]
theorem of_nat_is_unit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by
  rw [Nat.is_unit_iff, is_unit_iff_nat_abs_eq, nat_abs_of_nat]
#align int.of_nat_is_unit Int.of_nat_is_unit

theorem is_unit_mul_self {a : ℤ} (ha : IsUnit a) : a * a = 1 :=
  (is_unit_eq_one_or ha).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl
#align int.is_unit_mul_self Int.is_unit_mul_self

theorem is_unit_add_is_unit_eq_is_unit_add_is_unit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [is_unit_iff] at ha hb hc hd
  cases ha <;> cases hb <;> cases hc <;> cases hd <;> subst ha <;> subst hb <;> subst hc <;>
      subst hd <;>
    tidy
#align int.is_unit_add_is_unit_eq_is_unit_add_is_unit Int.is_unit_add_is_unit_eq_is_unit_add_is_unit

theorem eq_one_or_neg_one_of_mul_eq_neg_one {z w : ℤ} (h : z * w = -1) : z = 1 ∨ z = -1 :=
  Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1
#align int.eq_one_or_neg_one_of_mul_eq_neg_one Int.eq_one_or_neg_one_of_mul_eq_neg_one

end Int

