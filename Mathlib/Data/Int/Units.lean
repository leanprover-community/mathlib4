/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Nat.Units
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Units

#align_import data.int.units from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"

/-!
# Lemmas about units in `ℤ`.
-/


namespace Int

/-! ### units -/

@[simp]
theorem units_natAbs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
                                 -- ⊢ natAbs 1 = 1
                                                                   -- 🎉 no goals
        rw [← natAbs_mul, Units.inv_mul]; rfl⟩
        -- ⊢ natAbs 1 = 1
                                          -- 🎉 no goals
#align int.units_nat_abs Int.units_natAbs

theorem units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff, units_natAbs] using natAbs_eq u
  -- 🎉 no goals
#align int.units_eq_one_or Int.units_eq_one_or

theorem isUnit_eq_one_or {a : ℤ} : IsUnit a → a = 1 ∨ a = -1
  | ⟨_, hx⟩ => hx ▸ (units_eq_one_or _).imp (congr_arg Units.val) (congr_arg Units.val)
#align int.is_unit_eq_one_or Int.isUnit_eq_one_or

theorem isUnit_iff {a : ℤ} : IsUnit a ↔ a = 1 ∨ a = -1 := by
  refine' ⟨fun h => isUnit_eq_one_or h, fun h => _⟩
  -- ⊢ IsUnit a
  rcases h with (rfl | rfl)
  -- ⊢ IsUnit 1
  · exact isUnit_one
    -- 🎉 no goals
  · exact isUnit_one.neg
    -- 🎉 no goals
#align int.is_unit_iff Int.isUnit_iff

theorem isUnit_eq_or_eq_neg {a b : ℤ} (ha : IsUnit a) (hb : IsUnit b) : a = b ∨ a = -b := by
  rcases isUnit_eq_one_or hb with (rfl | rfl)
  -- ⊢ a = 1 ∨ a = -1
  · exact isUnit_eq_one_or ha
    -- 🎉 no goals
  · rwa [or_comm, neg_neg, ← isUnit_iff]
    -- 🎉 no goals
#align int.is_unit_eq_or_eq_neg Int.isUnit_eq_or_eq_neg

theorem eq_one_or_neg_one_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = 1 ∨ z = -1 :=
  isUnit_iff.mp (isUnit_of_mul_eq_one z w h)
#align int.eq_one_or_neg_one_of_mul_eq_one Int.eq_one_or_neg_one_of_mul_eq_one

theorem eq_one_or_neg_one_of_mul_eq_one' {z w : ℤ} (h : z * w = 1) :
    z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 := by
  have h' : w * z = 1 := mul_comm z w ▸ h
  -- ⊢ z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1
  rcases eq_one_or_neg_one_of_mul_eq_one h with (rfl | rfl) <;>
  -- ⊢ 1 = 1 ∧ w = 1 ∨ 1 = -1 ∧ w = -1
      rcases eq_one_or_neg_one_of_mul_eq_one h' with (rfl | rfl) <;> tauto
      -- ⊢ 1 = 1 ∧ 1 = 1 ∨ 1 = -1 ∧ 1 = -1
      -- ⊢ -1 = 1 ∧ 1 = 1 ∨ -1 = -1 ∧ 1 = -1
                                                                     -- 🎉 no goals
                                                                     -- 🎉 no goals
                                                                     -- 🎉 no goals
                                                                     -- 🎉 no goals
#align int.eq_one_or_neg_one_of_mul_eq_one' Int.eq_one_or_neg_one_of_mul_eq_one'

theorem eq_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = w :=
  (eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))
#align int.eq_of_mul_eq_one Int.eq_of_mul_eq_one

theorem mul_eq_one_iff_eq_one_or_neg_one {z w : ℤ} :
    z * w = 1 ↔ z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 := by
  refine' ⟨eq_one_or_neg_one_of_mul_eq_one', fun h => Or.elim h (fun H => _) fun H => _⟩ <;>
  -- ⊢ z * w = 1
      rcases H with ⟨rfl, rfl⟩ <;>
      -- ⊢ 1 * 1 = 1
      -- ⊢ -1 * -1 = 1
    rfl
    -- 🎉 no goals
    -- 🎉 no goals
#align int.mul_eq_one_iff_eq_one_or_neg_one Int.mul_eq_one_iff_eq_one_or_neg_one

theorem eq_one_or_neg_one_of_mul_eq_neg_one' {z w : ℤ} (h : z * w = -1) :
    z = 1 ∧ w = -1 ∨ z = -1 ∧ w = 1 := by
  rcases isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1 with (rfl | rfl)
  -- ⊢ 1 = 1 ∧ w = -1 ∨ 1 = -1 ∧ w = 1
  · exact Or.inl ⟨rfl, one_mul w ▸ h⟩
    -- 🎉 no goals
  · exact Or.inr ⟨rfl, neg_inj.mp (neg_one_mul w ▸ h)⟩
    -- 🎉 no goals
#align int.eq_one_or_neg_one_of_mul_eq_neg_one' Int.eq_one_or_neg_one_of_mul_eq_neg_one'

theorem mul_eq_neg_one_iff_eq_one_or_neg_one {z w : ℤ} :
    z * w = -1 ↔ z = 1 ∧ w = -1 ∨ z = -1 ∧ w = 1 := by
  refine' ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h => Or.elim h (fun H => _) fun H => _⟩ <;>
  -- ⊢ z * w = -1
      rcases H with ⟨rfl, rfl⟩ <;>
      -- ⊢ 1 * -1 = -1
      -- ⊢ -1 * 1 = -1
    rfl
    -- 🎉 no goals
    -- 🎉 no goals
#align int.mul_eq_neg_one_iff_eq_one_or_neg_one Int.mul_eq_neg_one_iff_eq_one_or_neg_one

theorem isUnit_iff_natAbs_eq {n : ℤ} : IsUnit n ↔ n.natAbs = 1 := by
  simp [natAbs_eq_iff, isUnit_iff, Nat.cast_zero]
  -- 🎉 no goals
#align int.is_unit_iff_nat_abs_eq Int.isUnit_iff_natAbs_eq

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq
#align int.is_unit.nat_abs_eq Int.IsUnit.natAbs_eq

-- Porting note: `rw` didn't work on `natAbs_ofNat`, so had to change to `simp`,
-- presumably because `(n : ℤ)` is `Nat.cast` and not just `ofNat`
@[norm_cast]
theorem ofNat_isUnit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by
  simp [isUnit_iff_natAbs_eq]
  -- 🎉 no goals
#align int.of_nat_is_unit Int.ofNat_isUnit

theorem isUnit_mul_self {a : ℤ} (ha : IsUnit a) : a * a = 1 :=
  (isUnit_eq_one_or ha).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl
#align int.is_unit_mul_self Int.isUnit_mul_self

-- Porting note: this was proven in mathlib3 with `tidy` which hasn't been ported yet
theorem isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [isUnit_iff] at ha hb hc hd
  -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
  cases ha <;> cases hb <;> cases hc <;> cases hd <;>
  -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
               -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
               -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                            -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                            -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                            -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                            -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
                                         -- ⊢ a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c
      subst a <;> subst b <;> subst c <;> subst d <;>
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ 1 + b = c + d ↔ 1 = c ∧ b = d ∨ 1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
      -- ⊢ -1 + b = c + d ↔ -1 = c ∧ b = d ∨ -1 = d ∧ b = c
                  -- ⊢ 1 + 1 = c + d ↔ 1 = c ∧ 1 = d ∨ 1 = d ∧ 1 = c
                  -- ⊢ 1 + 1 = c + d ↔ 1 = c ∧ 1 = d ∨ 1 = d ∧ 1 = c
                  -- ⊢ 1 + 1 = c + d ↔ 1 = c ∧ 1 = d ∨ 1 = d ∧ 1 = c
                  -- ⊢ 1 + 1 = c + d ↔ 1 = c ∧ 1 = d ∨ 1 = d ∧ 1 = c
                  -- ⊢ 1 + -1 = c + d ↔ 1 = c ∧ -1 = d ∨ 1 = d ∧ -1 = c
                  -- ⊢ 1 + -1 = c + d ↔ 1 = c ∧ -1 = d ∨ 1 = d ∧ -1 = c
                  -- ⊢ 1 + -1 = c + d ↔ 1 = c ∧ -1 = d ∨ 1 = d ∧ -1 = c
                  -- ⊢ 1 + -1 = c + d ↔ 1 = c ∧ -1 = d ∨ 1 = d ∧ -1 = c
                  -- ⊢ -1 + 1 = c + d ↔ -1 = c ∧ 1 = d ∨ -1 = d ∧ 1 = c
                  -- ⊢ -1 + 1 = c + d ↔ -1 = c ∧ 1 = d ∨ -1 = d ∧ 1 = c
                  -- ⊢ -1 + 1 = c + d ↔ -1 = c ∧ 1 = d ∨ -1 = d ∧ 1 = c
                  -- ⊢ -1 + 1 = c + d ↔ -1 = c ∧ 1 = d ∨ -1 = d ∧ 1 = c
                  -- ⊢ -1 + -1 = c + d ↔ -1 = c ∧ -1 = d ∨ -1 = d ∧ -1 = c
                  -- ⊢ -1 + -1 = c + d ↔ -1 = c ∧ -1 = d ∨ -1 = d ∧ -1 = c
                  -- ⊢ -1 + -1 = c + d ↔ -1 = c ∧ -1 = d ∨ -1 = d ∧ -1 = c
                  -- ⊢ -1 + -1 = c + d ↔ -1 = c ∧ -1 = d ∨ -1 = d ∧ -1 = c
                              -- ⊢ 1 + 1 = 1 + d ↔ 1 = 1 ∧ 1 = d ∨ 1 = d ∧ 1 = 1
                              -- ⊢ 1 + 1 = 1 + d ↔ 1 = 1 ∧ 1 = d ∨ 1 = d ∧ 1 = 1
                              -- ⊢ 1 + 1 = -1 + d ↔ 1 = -1 ∧ 1 = d ∨ 1 = d ∧ 1 = -1
                              -- ⊢ 1 + 1 = -1 + d ↔ 1 = -1 ∧ 1 = d ∨ 1 = d ∧ 1 = -1
                              -- ⊢ 1 + -1 = 1 + d ↔ 1 = 1 ∧ -1 = d ∨ 1 = d ∧ -1 = 1
                              -- ⊢ 1 + -1 = 1 + d ↔ 1 = 1 ∧ -1 = d ∨ 1 = d ∧ -1 = 1
                              -- ⊢ 1 + -1 = -1 + d ↔ 1 = -1 ∧ -1 = d ∨ 1 = d ∧ -1 = -1
                              -- ⊢ 1 + -1 = -1 + d ↔ 1 = -1 ∧ -1 = d ∨ 1 = d ∧ -1 = -1
                              -- ⊢ -1 + 1 = 1 + d ↔ -1 = 1 ∧ 1 = d ∨ -1 = d ∧ 1 = 1
                              -- ⊢ -1 + 1 = 1 + d ↔ -1 = 1 ∧ 1 = d ∨ -1 = d ∧ 1 = 1
                              -- ⊢ -1 + 1 = -1 + d ↔ -1 = -1 ∧ 1 = d ∨ -1 = d ∧ 1 = -1
                              -- ⊢ -1 + 1 = -1 + d ↔ -1 = -1 ∧ 1 = d ∨ -1 = d ∧ 1 = -1
                              -- ⊢ -1 + -1 = 1 + d ↔ -1 = 1 ∧ -1 = d ∨ -1 = d ∧ -1 = 1
                              -- ⊢ -1 + -1 = 1 + d ↔ -1 = 1 ∧ -1 = d ∨ -1 = d ∧ -1 = 1
                              -- ⊢ -1 + -1 = -1 + d ↔ -1 = -1 ∧ -1 = d ∨ -1 = d ∧ -1 = -1
                              -- ⊢ -1 + -1 = -1 + d ↔ -1 = -1 ∧ -1 = d ∨ -1 = d ∧ -1 = -1
                                          -- ⊢ 1 + 1 = 1 + 1 ↔ 1 = 1 ∧ 1 = 1 ∨ 1 = 1 ∧ 1 = 1
                                          -- ⊢ 1 + 1 = 1 + -1 ↔ 1 = 1 ∧ 1 = -1 ∨ 1 = -1 ∧ 1 = 1
                                          -- ⊢ 1 + 1 = -1 + 1 ↔ 1 = -1 ∧ 1 = 1 ∨ 1 = 1 ∧ 1 = -1
                                          -- ⊢ 1 + 1 = -1 + -1 ↔ 1 = -1 ∧ 1 = -1 ∨ 1 = -1 ∧ 1 = -1
                                          -- ⊢ 1 + -1 = 1 + 1 ↔ 1 = 1 ∧ -1 = 1 ∨ 1 = 1 ∧ -1 = 1
                                          -- ⊢ 1 + -1 = 1 + -1 ↔ 1 = 1 ∧ -1 = -1 ∨ 1 = -1 ∧ -1 = 1
                                          -- ⊢ 1 + -1 = -1 + 1 ↔ 1 = -1 ∧ -1 = 1 ∨ 1 = 1 ∧ -1 = -1
                                          -- ⊢ 1 + -1 = -1 + -1 ↔ 1 = -1 ∧ -1 = -1 ∨ 1 = -1 ∧ -1 = -1
                                          -- ⊢ -1 + 1 = 1 + 1 ↔ -1 = 1 ∧ 1 = 1 ∨ -1 = 1 ∧ 1 = 1
                                          -- ⊢ -1 + 1 = 1 + -1 ↔ -1 = 1 ∧ 1 = -1 ∨ -1 = -1 ∧ 1 = 1
                                          -- ⊢ -1 + 1 = -1 + 1 ↔ -1 = -1 ∧ 1 = 1 ∨ -1 = 1 ∧ 1 = -1
                                          -- ⊢ -1 + 1 = -1 + -1 ↔ -1 = -1 ∧ 1 = -1 ∨ -1 = -1 ∧ 1 = -1
                                          -- ⊢ -1 + -1 = 1 + 1 ↔ -1 = 1 ∧ -1 = 1 ∨ -1 = 1 ∧ -1 = 1
                                          -- ⊢ -1 + -1 = 1 + -1 ↔ -1 = 1 ∧ -1 = -1 ∨ -1 = -1 ∧ -1 = 1
                                          -- ⊢ -1 + -1 = -1 + 1 ↔ -1 = -1 ∧ -1 = 1 ∨ -1 = 1 ∧ -1 = -1
                                          -- ⊢ -1 + -1 = -1 + -1 ↔ -1 = -1 ∧ -1 = -1 ∨ -1 = -1 ∧ -1 = -1
    simp
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align int.is_unit_add_is_unit_eq_is_unit_add_is_unit Int.isUnit_add_isUnit_eq_isUnit_add_isUnit

theorem eq_one_or_neg_one_of_mul_eq_neg_one {z w : ℤ} (h : z * w = -1) : z = 1 ∨ z = -1 :=
  Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1
#align int.eq_one_or_neg_one_of_mul_eq_neg_one Int.eq_one_or_neg_one_of_mul_eq_neg_one

end Int
