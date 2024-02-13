/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.SetTheory.Cardinal.Basic

#align_import set_theory.cardinal.basic from "leanprover-community/mathlib"@"3ff3f2d6a3118b8711063de7111a0d77a53219a8"

/-!
# Projection from cardinal numbers to natural numbers

In this file we define `Cardinal.toNat` to be the natural projection `Cardinal → ℕ`,
sending all infinite cardinals to zero.
We also prove basic lemmas about this definition.
-/

universe u v
open Function
open scoped BigOperators

namespace Cardinal

variable {α : Type u} {c : Cardinal}

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
noncomputable def toNat : ZeroHom Cardinal ℕ where
  toFun c := if h : c < aleph0.{v} then Classical.choose (lt_aleph0.1 h) else 0
  map_zero' := by
    have h : 0 < ℵ₀ := nat_lt_aleph0 0
    dsimp only
    rw [dif_pos h, ← Cardinal.natCast_inj, ← Classical.choose_spec (lt_aleph0.1 h),
      Nat.cast_zero]
#align cardinal.to_nat Cardinal.toNat

@[simp]
lemma toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ ≤ c := by
  simp only [toNat, ZeroHom.coe_mk, dite_eq_right_iff, or_iff_not_imp_right, not_le]
  refine' forall_congr' fun h => _
  rw [← @Nat.cast_eq_zero Cardinal, ← Classical.choose_spec (p := fun n : ℕ ↦ c = n)]

lemma toNat_ne_zero : toNat c ≠ 0 ↔ c ≠ 0 ∧ c < ℵ₀ := by simp [not_or]
@[simp] lemma toNat_pos : 0 < toNat c ↔ c ≠ 0 ∧ c < ℵ₀ := pos_iff_ne_zero.trans toNat_ne_zero

theorem toNat_apply_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) :
    toNat c = Classical.choose (lt_aleph0.1 h) :=
  dif_pos h
#align cardinal.to_nat_apply_of_lt_aleph_0 Cardinal.toNat_apply_of_lt_aleph0

theorem toNat_apply_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : toNat c = 0 :=
  dif_neg h.not_lt
#align cardinal.to_nat_apply_of_aleph_0_le Cardinal.toNat_apply_of_aleph0_le

theorem cast_toNat_of_lt_aleph0 {c : Cardinal} (h : c < ℵ₀) : ↑(toNat c) = c := by
  rw [toNat_apply_of_lt_aleph0 h, ← Classical.choose_spec (lt_aleph0.1 h)]
#align cardinal.cast_to_nat_of_lt_aleph_0 Cardinal.cast_toNat_of_lt_aleph0

theorem cast_toNat_of_aleph0_le {c : Cardinal} (h : ℵ₀ ≤ c) : ↑(toNat c) = (0 : Cardinal) := by
  rw [toNat_apply_of_aleph0_le h, Nat.cast_zero]
#align cardinal.cast_to_nat_of_aleph_0_le Cardinal.cast_toNat_of_aleph0_le

/-- Two finite cardinals are equal iff they are equal their to_nat are equal -/
theorem toNat_eq_iff_eq_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c = toNat d ↔ c = d := by
  rw [← natCast_inj, cast_toNat_of_lt_aleph0 hc, cast_toNat_of_lt_aleph0 hd]
#align cardinal.to_nat_eq_iff_eq_of_lt_aleph_0 Cardinal.toNat_eq_iff_eq_of_lt_aleph0

theorem toNat_le_iff_le_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c ≤ toNat d ↔ c ≤ d := by
  rw [← natCast_le, cast_toNat_of_lt_aleph0 hc, cast_toNat_of_lt_aleph0 hd]
#align cardinal.to_nat_le_iff_le_of_lt_aleph_0 Cardinal.toNat_le_iff_le_of_lt_aleph0

theorem toNat_lt_iff_lt_of_lt_aleph0 {c d : Cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
    toNat c < toNat d ↔ c < d := by
  rw [← natCast_lt, cast_toNat_of_lt_aleph0 hc, cast_toNat_of_lt_aleph0 hd]
#align cardinal.to_nat_lt_iff_lt_of_lt_aleph_0 Cardinal.toNat_lt_iff_lt_of_lt_aleph0

theorem toNat_le_of_le_of_lt_aleph0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c ≤ d) :
    toNat c ≤ toNat d :=
  (toNat_le_iff_le_of_lt_aleph0 (hcd.trans_lt hd) hd).mpr hcd
#align cardinal.to_nat_le_of_le_of_lt_aleph_0 Cardinal.toNat_le_of_le_of_lt_aleph0

theorem toNat_lt_of_lt_of_lt_aleph0 {c d : Cardinal} (hd : d < ℵ₀) (hcd : c < d) :
    toNat c < toNat d :=
  (toNat_lt_iff_lt_of_lt_aleph0 (hcd.trans hd) hd).mpr hcd
#align cardinal.to_nat_lt_of_lt_of_lt_aleph_0 Cardinal.toNat_lt_of_lt_of_lt_aleph0

@[simp]
theorem toNat_cast (n : ℕ) : Cardinal.toNat n = n := by
  rw [toNat_apply_of_lt_aleph0 (nat_lt_aleph0 n), ← natCast_inj]
  exact (Classical.choose_spec (lt_aleph0.1 (nat_lt_aleph0 n))).symm
#align cardinal.to_nat_cast Cardinal.toNat_cast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] :
    Cardinal.toNat (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  toNat_cast n

/-- `toNat` has a right-inverse: coercion. -/
theorem toNat_rightInverse : Function.RightInverse ((↑) : ℕ → Cardinal) toNat :=
  toNat_cast
#align cardinal.to_nat_right_inverse Cardinal.toNat_rightInverse

theorem toNat_surjective : Surjective toNat :=
  toNat_rightInverse.surjective
#align cardinal.to_nat_surjective Cardinal.toNat_surjective


@[simp]
theorem mk_toNat_of_infinite [h : Infinite α] : toNat #α = 0 :=
  dif_neg (infinite_iff.1 h).not_lt
#align cardinal.mk_to_nat_of_infinite Cardinal.mk_toNat_of_infinite

@[simp]
theorem aleph0_toNat : toNat ℵ₀ = 0 :=
  toNat_apply_of_aleph0_le le_rfl
#align cardinal.aleph_0_to_nat Cardinal.aleph0_toNat

theorem mk_toNat_eq_card [Fintype α] : toNat #α = Fintype.card α := by simp
#align cardinal.mk_to_nat_eq_card Cardinal.mk_toNat_eq_card

-- Porting note : simp can prove this
-- @[simp]
theorem zero_toNat : toNat 0 = 0 := by rw [← toNat_cast 0, Nat.cast_zero]
#align cardinal.zero_to_nat Cardinal.zero_toNat

@[simp]
theorem one_toNat : toNat 1 = 1 := by rw [← toNat_cast 1, Nat.cast_one]
#align cardinal.one_to_nat Cardinal.one_toNat

theorem toNat_eq_iff {c : Cardinal} {n : ℕ} (hn : n ≠ 0) : toNat c = n ↔ c = n :=
  ⟨fun h =>
    (cast_toNat_of_lt_aleph0
            (lt_of_not_ge (hn ∘ h.symm.trans ∘ toNat_apply_of_aleph0_le))).symm.trans
      (congr_arg _ h),
    fun h => (congr_arg toNat h).trans (toNat_cast n)⟩
#align cardinal.to_nat_eq_iff Cardinal.toNat_eq_iff

/-- A version of `toNat_eq_iff` for literals -/
theorem toNat_eq_ofNat {c : Cardinal} {n : ℕ} [Nat.AtLeastTwo n] :
    toNat c = OfNat.ofNat n ↔ c = OfNat.ofNat n :=
  toNat_eq_iff <| Nat.cast_ne_zero.mpr <| OfNat.ofNat_ne_zero n

@[simp]
theorem toNat_eq_one {c : Cardinal} : toNat c = 1 ↔ c = 1 := by
  rw [toNat_eq_iff one_ne_zero, Nat.cast_one]
#align cardinal.to_nat_eq_one Cardinal.toNat_eq_one

theorem toNat_eq_one_iff_unique {α : Type*} : toNat #α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  toNat_eq_one.trans eq_one_iff_unique
#align cardinal.to_nat_eq_one_iff_unique Cardinal.toNat_eq_one_iff_unique

@[simp]
theorem toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} c) = toNat c := by
  apply natCast_injective
  cases' lt_or_ge c ℵ₀ with hc hc
  · rw [cast_toNat_of_lt_aleph0, ← lift_natCast.{u,v}, cast_toNat_of_lt_aleph0 hc]
    rwa [lift_lt_aleph0]
  · rw [cast_toNat_of_aleph0_le, ← lift_natCast.{u,v}, cast_toNat_of_aleph0_le hc, lift_zero]
    rwa [aleph0_le_lift]
#align cardinal.to_nat_lift Cardinal.toNat_lift

theorem toNat_congr {β : Type v} (e : α ≃ β) : toNat #α = toNat #β := by
  -- Porting note: Inserted universe hint below
  rw [← toNat_lift, (lift_mk_eq.{_,_,v}).mpr ⟨e⟩, toNat_lift]
#align cardinal.to_nat_congr Cardinal.toNat_congr

@[simp]
theorem toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x * toNat y := by
  rcases eq_or_ne x 0 with (rfl | hx1)
  · rw [zero_mul, zero_toNat, zero_mul]
  rcases eq_or_ne y 0 with (rfl | hy1)
  · rw [mul_zero, zero_toNat, mul_zero]
  cases' lt_or_le x ℵ₀ with hx2 hx2
  · cases' lt_or_le y ℵ₀ with hy2 hy2
    · lift x to ℕ using hx2
      lift y to ℕ using hy2
      rw [← Nat.cast_mul, toNat_cast, toNat_cast, toNat_cast]
    · rw [toNat_apply_of_aleph0_le hy2, mul_zero, toNat_apply_of_aleph0_le]
      exact aleph0_le_mul_iff'.2 (Or.inl ⟨hx1, hy2⟩)
  · rw [toNat_apply_of_aleph0_le hx2, zero_mul, toNat_apply_of_aleph0_le]
    exact aleph0_le_mul_iff'.2 (Or.inr ⟨hx2, hy1⟩)
#align cardinal.to_nat_mul Cardinal.toNat_mul

/-- `Cardinal.toNat` as a `MonoidWithZeroHom`. -/
@[simps]
noncomputable def toNatHom : Cardinal →*₀ ℕ where
  toFun := toNat
  map_zero' := zero_toNat
  map_one' := one_toNat
  map_mul' := toNat_mul
#align cardinal.to_nat_hom Cardinal.toNatHom

theorem toNat_finset_prod (s : Finset α) (f : α → Cardinal) :
    toNat (∏ i in s, f i) = ∏ i in s, toNat (f i) :=
  map_prod toNatHom _ _
#align cardinal.to_nat_finset_prod Cardinal.toNat_finset_prod

@[simp]
theorem toNat_add_of_lt_aleph0 {a : Cardinal.{u}} {b : Cardinal.{v}} (ha : a < ℵ₀) (hb : b < ℵ₀) :
    toNat (lift.{v, u} a + lift.{u, v} b) = toNat a + toNat b := by
  apply Cardinal.natCast_injective
  replace ha : lift.{v, u} a < ℵ₀ := by rwa [lift_lt_aleph0]
  replace hb : lift.{u, v} b < ℵ₀ := by rwa [lift_lt_aleph0]
  rw [Nat.cast_add, ← toNat_lift.{v, u} a, ← toNat_lift.{u, v} b, cast_toNat_of_lt_aleph0 ha,
    cast_toNat_of_lt_aleph0 hb, cast_toNat_of_lt_aleph0 (add_lt_aleph0 ha hb)]
#align cardinal.to_nat_add_of_lt_aleph_0 Cardinal.toNat_add_of_lt_aleph0

end Cardinal
