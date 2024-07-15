/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Common

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"
#align_import data.int.units from "leanprover-community/mathlib"@"641b6a82006416ec431b2987b354af9311fed4f2"

/-!
# The integers form a group

This file contains the additive group and multiplicative monoid instances on the integers.

See note [foundational algebra order theory].
-/

assert_not_exists Ring
assert_not_exists DenselyOrdered
assert_not_exists Set.range

open Nat

namespace Int

/-! ### Instances -/

instance instCommMonoid : CommMonoid ℤ where
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  mul_assoc := Int.mul_assoc

instance instAddCommGroup : AddCommGroup ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = n * x + x
    by rw [Int.add_mul, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [ofNat_eq_coe, ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [negSucc_coe, ofNat_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/

instance instAddCommMonoid    : AddCommMonoid ℤ    := by infer_instance
instance instAddMonoid        : AddMonoid ℤ        := by infer_instance
instance instMonoid           : Monoid ℤ           := by infer_instance
instance instCommSemigroup    : CommSemigroup ℤ    := by infer_instance
instance instSemigroup        : Semigroup ℤ        := by infer_instance
instance instAddGroup         : AddGroup ℤ         := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℤ := by infer_instance
instance instAddSemigroup     : AddSemigroup ℤ     := by infer_instance

/-! ### Miscellaneous lemmas -/

section Multiplicative

open Multiplicative

lemma toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := mul_comm _ _
#align int.to_add_pow Int.toAdd_pow

lemma toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : toAdd (a ^ b) = toAdd a * b := mul_comm _ _
#align int.to_add_zpow Int.toAdd_zpow

@[simp] lemma ofAdd_mul (a b : ℤ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_zpow ..).symm
#align int.of_add_mul Int.ofAdd_mul

end Multiplicative

/-! #### Units -/

variable {u v : ℤ}

lemma units_natAbs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul, Units.inv_mul]; rfl⟩
#align int.units_nat_abs Int.units_natAbs

@[simp] lemma natAbs_of_isUnit (hu : IsUnit u) : natAbs u = 1 := units_natAbs hu.unit

lemma isUnit_eq_one_or (hu : IsUnit u) : u = 1 ∨ u = -1 := by
  simpa only [natAbs_of_isUnit hu] using natAbs_eq u
#align int.is_unit_eq_one_or Int.isUnit_eq_one_or

lemma isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u ≠ v ↔ u = -v := by
  obtain rfl | rfl := isUnit_eq_one_or hu <;> obtain rfl | rfl := isUnit_eq_one_or hv <;> decide

lemma isUnit_eq_or_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u = v ∨ u = -v :=
  or_iff_not_imp_left.2 (isUnit_ne_iff_eq_neg hu hv).1
#align int.is_unit_eq_or_eq_neg Int.isUnit_eq_or_eq_neg

lemma isUnit_iff : IsUnit u ↔ u = 1 ∨ u = -1 := by
  refine ⟨fun h ↦ isUnit_eq_one_or h, fun h ↦ ?_⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩
#align int.is_unit_iff Int.isUnit_iff

lemma eq_one_or_neg_one_of_mul_eq_one (h : u * v = 1) : u = 1 ∨ u = -1 :=
  isUnit_iff.1 (isUnit_of_mul_eq_one u v h)
#align int.eq_one_or_neg_one_of_mul_eq_one Int.eq_one_or_neg_one_of_mul_eq_one

lemma eq_one_or_neg_one_of_mul_eq_one' (h : u * v = 1) : u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  have h' : v * u = 1 := mul_comm u v ▸ h
  obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h <;>
      obtain rfl | rfl := eq_one_or_neg_one_of_mul_eq_one h' <;> tauto
#align int.eq_one_or_neg_one_of_mul_eq_one' Int.eq_one_or_neg_one_of_mul_eq_one'

lemma eq_of_mul_eq_one (h : u * v = 1) : u = v :=
  (eq_one_or_neg_one_of_mul_eq_one' h).elim
    (and_imp.2 (·.trans ·.symm)) (and_imp.2 (·.trans ·.symm))
#align int.eq_of_mul_eq_one Int.eq_of_mul_eq_one

lemma mul_eq_one_iff_eq_one_or_neg_one : u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  refine ⟨eq_one_or_neg_one_of_mul_eq_one', fun h ↦ Or.elim h (fun H ↦ ?_) fun H ↦ ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl
#align int.mul_eq_one_iff_eq_one_or_neg_one Int.mul_eq_one_iff_eq_one_or_neg_one

lemma eq_one_or_neg_one_of_mul_eq_neg_one' (h : u * v = -1) : u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  obtain rfl | rfl := isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h
#align int.eq_one_or_neg_one_of_mul_eq_neg_one' Int.eq_one_or_neg_one_of_mul_eq_neg_one'

lemma mul_eq_neg_one_iff_eq_one_or_neg_one : u * v = -1 ↔ u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  refine ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h ↦ Or.elim h (fun H ↦ ?_) fun H ↦ ?_⟩ <;>
    obtain ⟨rfl, rfl⟩ := H <;> rfl
#align int.mul_eq_neg_one_iff_eq_one_or_neg_one Int.mul_eq_neg_one_iff_eq_one_or_neg_one

lemma isUnit_iff_natAbs_eq : IsUnit u ↔ u.natAbs = 1 := by simp [natAbs_eq_iff, isUnit_iff]
#align int.is_unit_iff_nat_abs_eq Int.isUnit_iff_natAbs_eq

alias ⟨IsUnit.natAbs_eq, _⟩ := isUnit_iff_natAbs_eq
#align int.is_unit.nat_abs_eq Int.IsUnit.natAbs_eq

-- Porting note: `rw` didn't work on `natAbs_ofNat`, so had to change to `simp`,
-- presumably because `(n : ℤ)` is `Nat.cast` and not just `ofNat`
@[norm_cast]
lemma ofNat_isUnit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by simp [isUnit_iff_natAbs_eq]
#align int.of_nat_is_unit Int.ofNat_isUnit

lemma isUnit_mul_self (hu : IsUnit u) : u * u = 1 :=
  (isUnit_eq_one_or hu).elim (fun h ↦ h.symm ▸ rfl) fun h ↦ h.symm ▸ rfl
#align int.is_unit_mul_self Int.isUnit_mul_self

-- Porting note: this was proven in mathlib3 with `tidy` which hasn't been ported yet
lemma isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [isUnit_iff] at ha hb hc hd
  cases ha <;> cases hb <;> cases hc <;> cases hd <;>
      subst a <;> subst b <;> subst c <;> subst d <;>
    simp (config := {decide := true})
#align int.is_unit_add_is_unit_eq_is_unit_add_is_unit Int.isUnit_add_isUnit_eq_isUnit_add_isUnit

lemma eq_one_or_neg_one_of_mul_eq_neg_one (h : u * v = -1) : u = 1 ∨ u = -1 :=
  Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1
#align int.eq_one_or_neg_one_of_mul_eq_neg_one Int.eq_one_or_neg_one_of_mul_eq_neg_one

/-! #### Parity -/

variable {m n : ℤ}

@[simp] lemma emod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by
  cases' emod_two_eq_zero_or_one n with h h <;> simp [h]
#align int.mod_two_ne_one Int.emod_two_ne_one

@[simp] lemma one_emod_two : (1 : Int) % 2 = 1 := rfl

-- `EuclideanDomain.mod_eq_zero` uses (2 ∣ n) as normal form
@[local simp] lemma emod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by
  cases' emod_two_eq_zero_or_one n with h h <;> simp [h]
#align int.mod_two_ne_zero Int.emod_two_ne_zero

lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, (emod_add_ediv n 2).symm.trans (by simp [← Int.two_mul, h])⟩
#align int.even_iff Int.even_iff

lemma not_even_iff : ¬Even n ↔ n % 2 = 1 := by rw [even_iff, emod_two_ne_zero]
#align int.not_even_iff Int.not_even_iff

@[simp] lemma two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 :=
  (even_iff_exists_two_nsmul _).symm.not.trans not_even_iff
#align int.two_dvd_ne_zero Int.two_dvd_ne_zero

instance : DecidablePred (Even : ℤ → Prop) := fun _ ↦ decidable_of_iff _ even_iff.symm

/-- `IsSquare` can be decided on `ℤ` by checking against the square root. -/
instance : DecidablePred (IsSquare : ℤ → Prop) :=
  fun m ↦ decidable_of_iff' (sqrt m * sqrt m = m) <| by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp] lemma not_even_one : ¬Even (1 : ℤ) := by simp [even_iff]
#align int.not_even_one Int.not_even_one

@[parity_simps] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases' emod_two_eq_zero_or_one m with h₁ h₁ <;>
  cases' emod_two_eq_zero_or_one n with h₂ h₂ <;>
  simp [even_iff, h₁, h₂, Int.add_emod, one_add_one_eq_two, emod_self]
#align int.even_add Int.even_add

lemma two_not_dvd_two_mul_add_one (n : ℤ) : ¬2 ∣ 2 * n + 1 := by simp [add_emod]
#align int.two_not_dvd_two_mul_add_one Int.two_not_dvd_two_mul_add_one

@[parity_simps]
lemma even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by simp [sub_eq_add_neg, parity_simps]
#align int.even_sub Int.even_sub

@[parity_simps] lemma even_add_one : Even (n + 1) ↔ ¬Even n := by simp [even_add]
#align int.even_add_one Int.even_add_one

@[parity_simps] lemma even_sub_one : Even (n - 1) ↔ ¬Even n := by simp [even_sub]

@[parity_simps] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  cases' emod_two_eq_zero_or_one m with h₁ h₁ <;>
  cases' emod_two_eq_zero_or_one n with h₂ h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]
#align int.even_mul Int.even_mul

@[parity_simps] lemma even_pow {n : ℕ} : Even (m ^ n) ↔ Even m ∧ n ≠ 0 := by
  induction' n with n ih <;> simp [*, even_mul, pow_succ]; tauto
#align int.even_pow Int.even_pow

lemma even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m := even_pow.trans <| and_iff_left h
#align int.even_pow' Int.even_pow'

@[simp, norm_cast] lemma even_coe_nat (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  rw_mod_cast [even_iff, Nat.even_iff]
#align int.even_coe_nat Int.even_coe_nat

lemma two_mul_ediv_two_of_even : Even n → 2 * (n / 2) = n :=
  fun h ↦ Int.mul_ediv_cancel' ((even_iff_exists_two_nsmul _).mp h)
#align int.two_mul_div_two_of_even Int.two_mul_ediv_two_of_even

lemma ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n :=
  fun h ↦ Int.ediv_mul_cancel ((even_iff_exists_two_nsmul _).mp h)
#align int.div_two_mul_two_of_even Int.ediv_two_mul_two_of_even

-- Here are examples of how `parity_simps` can be used with `Int`.
example (m n : ℤ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp (config := {decide := true}) [*, (by decide : ¬2 = 0), parity_simps]

example : ¬Even (25394535 : ℤ) := by decide

end Int

-- TODO: Do we really need this lemma? This is just `smul_eq_mul`
lemma zsmul_int_int (a b : ℤ) : a • b = a * b := rfl
#align zsmul_int_int zsmul_int_int

lemma zsmul_int_one (n : ℤ) : n • (1 : ℤ) = n := mul_one _
#align zsmul_int_one zsmul_int_one
