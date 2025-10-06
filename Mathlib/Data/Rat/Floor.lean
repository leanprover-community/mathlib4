/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

assert_not_exists Finset

open Int

namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

@[deprecated Rat.le_floor_iff (since := "2025-09-02")]
protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ Rat.floor r ↔ (z : ℚ) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp only [Rat.floor_def]
    rw [mk'_eq_divInt]
    have h' := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h)
    conv =>
      rhs
      rw [intCast_eq_divInt, Rat.divInt_le_divInt zero_lt_one h', mul_one]
    exact Int.le_ediv_iff_mul_le h'

instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/--
This variant of `floor_def` uses the `Int.floor` (for any `FloorRing`) rather than `Rat.floor`.
-/
protected theorem floor_def' {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def q

/--
This variant of `ceil_def` uses the `Int.ceil` (for any `FloorRing`) rather than `Rat.ceil`.
-/
protected theorem ceil_def' (q : ℚ) : ⌈q⌉ = -(-q.num / ↑q.den) := by
  change -⌊-q⌋ = _
  rw [Rat.floor_def', num_neg_eq_neg_num, den_neg_eq_den]


@[norm_cast]
theorem floor_intCast_div_natCast (n : ℤ) (d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋ = n / (↑d : ℤ) := by
  rw [Rat.floor_def']
  obtain rfl | hd := eq_zero_or_pos (a := d)
  · simp
  set q := (n : ℚ) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.den := by
    rw [q_eq]
    exact mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (mod_cast hd.ne')
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  refine (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left ?_ <| Int.natCast_nonneg q.den).symm
  rwa [← d_eq_c_mul_denom, Int.natCast_pos]

@[norm_cast]
theorem ceil_intCast_div_natCast (n : ℤ) (d : ℕ) : ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / (↑d : ℤ)) := by
  conv_lhs => rw [← neg_neg ⌈_⌉, ← floor_neg]
  rw [← neg_div, ← Int.cast_neg, floor_intCast_div_natCast]

@[norm_cast]
theorem floor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋ = n / d :=
  floor_intCast_div_natCast n d

@[norm_cast]
theorem ceil_natCast_div_natCast (n d : ℕ) : ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / d) :=
  ceil_intCast_div_natCast n d

@[norm_cast]
theorem natFloor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋₊ = n / d := by
  rw [← Int.ofNat_inj, Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]

@[simp, norm_cast]
theorem round_cast (x : ℚ) : round (x : α) = round x := by
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp
  rw [round_eq, round_eq, ← this, floor_cast]

@[simp, norm_cast]
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract (x : α) := by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

section NormNum

open Mathlib.Meta.NormNum Qq

theorem isNat_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isNat_intFloor_ofIsNNRat (r : α) (n : ℕ) (d : ℕ) :
    IsNNRat r n d → IsNat ⌊r⌋ (n / d) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← Int.ofNat_ediv_ofNat, ← floor_natCast_div_natCast n d,
    ← floor_cast (α := α), Rat.cast_div, cast_natCast, cast_natCast]

theorem isInt_intFloor_ofIsRat_neg (r : α) (n : ℕ) (d : ℕ) :
    IsRat r (.negOfNat n) d → IsInt ⌊r⌋ (.negOfNat (-(-n / d) : ℤ).toNat) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [← ceil_intCast_div_natCast n d, Int.cast_natCast]
  rw [@negOfNat_eq (toNat _), ofNat_eq_coe,
    natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg)),
    ← Int.cast_natCast n, ceil_intCast_div_natCast n d, neg_neg, ← ofNat_eq_coe, ← negOfNat_eq,
    ← floor_intCast_div_natCast (.negOfNat n) d, ← floor_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast]

/-- `norm_num` extension for `Int.floor` -/
@[norm_num ⌊_⌋]
def evalIntFloor : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intFloor $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- floor always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intFloor _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit ⌊q⌋₊
      letI : $z =Q $n / $d := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intFloor_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit (-⌊q⌋).toNat
      letI : $z =Q (-(-$n / $d) : ℤ).toNat := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intFloor_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

theorem isNat_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isNat_intCeil_ofIsNNRat (r : α) (n : ℕ) (d : ℕ) :
    IsNNRat r n d → IsNat ⌈r⌉ (-(-n / d) : ℤ).toNat := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv]
  rw [← ceil_intCast_div_natCast n d, ← ceil_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast, Int.cast_natCast,
    Int.natCast_toNat_eq_self.mpr (ceil_nonneg (div_nonneg n.cast_nonneg d.cast_nonneg))]

theorem isInt_intCeil_ofIsRat_neg (r : α) (n : ℕ) (d : ℕ) :
    IsRat r (.negOfNat n) d → IsInt ⌈r⌉ (.negOfNat (n / d)) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [@negOfNat_eq (n / d), ofNat_eq_coe, ← ofNat_ediv_ofNat, ← floor_natCast_div_natCast n d,
    floor_natCast_div_natCast n d, ← neg_neg (n : ℤ), ← ofNat_eq_coe, ← negOfNat_eq,
    ← ceil_intCast_div_natCast (.negOfNat n) d, ← ceil_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast]

/-- `norm_num` extension for `Int.ceil` -/
@[norm_num ⌈_⌉]
def evalIntCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intCeil $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- ceil always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit ⌈q⌉₊
      letI : $z =Q (-(-$n / $d) : ℤ).toNat := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intCeil_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit (-⌈q⌉).toNat
      letI : $z =Q $n / $d := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intCeil_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

end NormNum

end Rat

theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [Int.emod_def, Rat.floor_intCast_div_natCast]

theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.Coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.Coprime d := by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

namespace Rat

theorem num_lt_succ_floor_mul_den (q : ℚ) : q.num < (⌊q⌋ + 1) * q.den := by
  suffices (q.num : ℚ) < (⌊q⌋ + 1) * q.den from mod_cast this
  suffices (q.num : ℚ) < (q - fract q + 1) * q.den by
    have : (⌊q⌋ : ℚ) = q - fract q := eq_sub_of_add_eq <| floor_add_fract q
    rwa [this]
  suffices (q.num : ℚ) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * q.den = q.num + (1 - fract q) * q.den := by
      calc
        (q - fract q + 1) * q.den = (q + (1 - fract q)) * q.den := by ring
        _ = q * q.den + (1 - fract q) * q.den := by rw [add_mul]
        _ = q.num + (1 - fract q) * q.den := by simp
    rwa [this]
  suffices 0 < (1 - fract q) * q.den by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact mod_cast q.pos)

theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : (fract q⁻¹).num < q.num := by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := Rat.num_pos.mpr q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_inv : ℚ := q.den / q.num with q_inv_def
  have q_inv_eq : q⁻¹ = q_inv := by rw [q_inv_def, inv_def, divInt_eq_div, Int.cast_natCast]
  suffices (q_inv - ⌊q_inv⌋).num < q.num by rwa [q_inv_eq]
  suffices ((q.den - q.num * ⌊q_inv⌋ : ℚ) / q.num).num < q.num by
    simp only [gt_iff_lt, q_inv]
    field_simp
    simp [q_inv, this]
  suffices (q.den : ℤ) - q.num * ⌊q_inv⌋ < q.num by
    -- use that `q.num` and `q.den` are coprime to show that the numerator stays unreduced
    have : ((q.den - q.num * ⌊q_inv⌋ : ℚ) / q.num).num = q.den - q.num * ⌊q_inv⌋ := by
      suffices ((q.den : ℤ) - q.num * ⌊q_inv⌋).natAbs.Coprime q.num.natAbs from
        mod_cast Rat.num_div_eq_of_coprime q_num_pos this
      have tmp := Nat.coprime_sub_mul_floor_rat_div_of_coprime q.reduced.symm
      simpa only [Nat.cast_natAbs, abs_of_nonneg q_num_pos.le] using tmp
    rwa [this]
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.den < q⁻¹.den := by
    have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.den := Rat.num_lt_succ_floor_mul_den q⁻¹
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.den + q⁻¹.den := by rwa [right_distrib, one_mul] at this
    rwa [← sub_lt_iff_lt_add'] at this
  -- use that `q.num` and `q.den` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.den ∧ q_inv.den = q.num.natAbs := by
    have coprime_q_denom_q_num : q.den.Coprime q.num.natAbs := q.reduced.symm
    have : Int.natAbs q.den = q.den := by simp
    rw [← this] at coprime_q_denom_q_num
    rw [q_inv_def]
    constructor
    · exact mod_cast Rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
    · suffices (((q.den : ℚ) / q.num).den : ℤ) = q.num.natAbs by exact mod_cast this
      rw [q_num_abs_eq_q_num]
      exact mod_cast Rat.den_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq

end Rat
