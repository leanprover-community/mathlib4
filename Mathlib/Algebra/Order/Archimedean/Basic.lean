/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Monoid.Units
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Int.LeastGreatest
public import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Group.Basic

/-!
# Archimedean groups and fields.

This file defines the archimedean property for ordered groups and proves several results connected
to this notion. Being archimedean means that for all elements `x` and `y>0` there exists a natural
number `n` such that `x ≤ n • y`.

## Main definitions

* `Archimedean` is a typeclass for an ordered additive commutative monoid to have the archimedean
  property.
* `MulArchimedean` is a typeclass for an ordered commutative monoid to have the "mul-archimedean
  property" where for `x` and `y > 1`, there exists a natural number `n` such that `x ≤ y ^ n`.
* `Archimedean.floorRing` defines a floor function on an archimedean linearly ordered ring making
  it into a `floorRing`.

## Main statements

* `ℕ`, `ℤ`, and `ℚ` are archimedean.
-/

@[expose] public section

assert_not_exists Finset

open Int Set

variable {G M R K : Type*}

/-- An ordered additive commutative monoid is called `Archimedean` if for any two elements `x`, `y`
such that `0 < y`, there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (M) [AddCommMonoid M] [PartialOrder M] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : M) {y : M}, 0 < y → ∃ n : ℕ, x ≤ n • y

section MulArchimedean

/-- An ordered commutative monoid is called `MulArchimedean` if for any two elements `x`, `y`
such that `1 < y`, there exists a natural number `n` such that `x ≤ y ^ n`. -/
@[to_additive Archimedean]
class MulArchimedean (M) [CommMonoid M] [PartialOrder M] : Prop where
  /-- For any two elements `x`, `y` such that `1 < y`, there exists a natural number `n`
  such that `x ≤ y ^ n`. -/
  arch : ∀ (x : M) {y : M}, 1 < y → ∃ n : ℕ, x ≤ y ^ n

end MulArchimedean

@[to_additive]
lemma MulArchimedean.comap [CommMonoid G] [LinearOrder G] [CommMonoid M] [PartialOrder M]
    [MulArchimedean M] (f : G →* M) (hf : StrictMono f) :
    MulArchimedean G where
  arch x _ h := by
    refine (MulArchimedean.arch (f x) (by simpa using hf h)).imp ?_
    simp [← map_pow, hf.le_iff_le]

@[to_additive]
instance OrderDual.instMulArchimedean [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    [MulArchimedean G] :
    MulArchimedean Gᵒᵈ :=
  ⟨fun x y hy =>
    have hy : (ofDual y) < 1 := hy
    let ⟨n, hn⟩ := MulArchimedean.arch (ofDual x)⁻¹ (one_lt_inv'.2 hy)
    ⟨n, by rwa [inv_pow, inv_le_inv_iff] at hn⟩⟩

instance Additive.instArchimedean [CommGroup G] [PartialOrder G] [MulArchimedean G] :
    Archimedean (Additive G) :=
  ⟨fun x _ hy ↦ MulArchimedean.arch x.toMul hy⟩

instance Multiplicative.instMulArchimedean [AddCommGroup G] [PartialOrder G] [Archimedean G] :
    MulArchimedean (Multiplicative G) :=
  ⟨fun x _ hy ↦ Archimedean.arch x.toAdd hy⟩

@[to_additive]
theorem exists_lt_pow [CommMonoid M] [PartialOrder M] [MulArchimedean M] [MulLeftStrictMono M]
    {a : M} (ha : 1 < a) (b : M) : ∃ n : ℕ, b < a ^ n :=
  let ⟨k, hk⟩ := MulArchimedean.arch b ha
  ⟨k + 1, hk.trans_lt <| pow_lt_pow_right' ha k.lt_succ_self⟩

section LinearOrderedCommGroup

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

/-- An archimedean decidable linearly ordered `CommGroup` has a version of the floor: for
`a > 1`, any `g` in the group lies between some two consecutive powers of `a`. -/
@[to_additive /-- An archimedean decidable linearly ordered `AddCommGroup` has a version of the
floor: for `a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/]
theorem existsUnique_zpow_near_of_one_lt {a : G} (ha : 1 < a) (g : G) :
    ∃! k : ℤ, a ^ k ≤ g ∧ g < a ^ (k + 1) := by
  let s : Set ℤ := { n : ℤ | a ^ n ≤ g }
  obtain ⟨k, hk : g⁻¹ ≤ a ^ k⟩ := MulArchimedean.arch g⁻¹ ha
  have h_ne : s.Nonempty := ⟨-k, by simpa [s] using inv_le_inv' hk⟩
  obtain ⟨k, hk⟩ := MulArchimedean.arch g ha
  have h_bdd : ∀ n ∈ s, n ≤ (k : ℤ) := by
    intro n hn
    apply (zpow_le_zpow_iff_right ha).mp
    rw [← zpow_natCast] at hk
    exact le_trans hn hk
  obtain ⟨m, hm, hm'⟩ := Int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne
  have hm'' : g < a ^ (m + 1) := by
    contrapose! hm'
    exact ⟨m + 1, hm', lt_add_one _⟩
  refine ⟨m, ⟨hm, hm''⟩, fun n hn => (hm' n hn.1).antisymm <| Int.le_of_lt_add_one ?_⟩
  rw [← zpow_lt_zpow_iff_right ha]
  exact lt_of_le_of_lt hm hn.2

@[to_additive]
theorem existsUnique_zpow_near_of_one_lt' {a : G} (ha : 1 < a) (g : G) :
    ∃! k : ℤ, 1 ≤ g / a ^ k ∧ g / a ^ k < a := by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

@[to_additive]
theorem existsUnique_div_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ico c (c * a) := by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
theorem existsUnique_mul_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ico c (c * a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, mem_Ico, zpow_neg, ← div_eq_mul_inv, le_div_iff_mul_le, one_mul,
      mul_comm c, div_lt_iff_lt_mul, mul_assoc] using existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
theorem existsUnique_add_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ioc c (c * a) :=
  (Equiv.addRight (1 : ℤ)).bijective.existsUnique_iff.2 <| by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

@[to_additive]
theorem existsUnique_sub_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ioc c (c * a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

@[to_additive]
theorem exists_pow_lt {a : G} (ha : a < 1) (b : G) : ∃ n : ℕ, a ^ n < b :=
  (exists_lt_pow (one_lt_inv'.mpr ha) b⁻¹).imp <| by simp

end LinearOrderedCommGroup

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_nat_ge (x : R) :
    ∃ n : ℕ, x ≤ n := by
  nontriviality R
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

instance (priority := 100) : IsDirectedOrder R :=
  ⟨fun x y ↦
    let ⟨m, hm⟩ := exists_nat_ge x; let ⟨n, hn⟩ := exists_nat_ge y
    let ⟨k, hmk, hnk⟩ := exists_ge_ge m n
    ⟨k, hm.trans <| Nat.mono_cast hmk, hn.trans <| Nat.mono_cast hnk⟩⟩

end OrderedSemiring

section StrictOrderedSemiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

lemma exists_nat_gt (x : R) : ∃ n : ℕ, x < n :=
  (exists_lt_nsmul zero_lt_one x).imp fun n hn ↦ by rwa [← nsmul_one]

theorem add_one_pow_unbounded_of_pos (x : R) (hy : 0 < y) : ∃ n : ℕ, x < (y + 1) ^ n :=
  have : 0 ≤ 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h ↦
    calc
      x ≤ n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ ≤ (1 + y) ^ n :=
        one_add_mul_le_pow_of_sq_nonneg (pow_nonneg hy.le _) (pow_nonneg this _)
          (add_nonneg zero_le_two hy.le) _
      _ = (y + 1) ^ n := by rw [add_comm]

lemma pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : R) (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n := by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

end StrictOrderedSemiring

section OrderedRing

variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_int_ge (x : R) : ∃ n : ℤ, x ≤ n := let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

theorem exists_int_le (x : R) : ∃ n : ℤ, n ≤ x :=
  let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

instance (priority := 100) : IsCodirectedOrder R where
  directed a b :=
    let ⟨m, hm⟩ := exists_int_le a; let ⟨n, hn⟩ := exists_int_le b
    ⟨(min m n : ℤ), le_trans (Int.cast_mono <| min_le_left _ _) hm,
      le_trans (Int.cast_mono <| min_le_right _ _) hn⟩

end OrderedRing

section StrictOrderedRing
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem exists_int_gt (x : R) : ∃ n : ℤ, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

theorem exists_int_lt (x : R) : ∃ n : ℤ, (n : R) < x :=
  let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

/-- See `exists_floor'` for a more general version which only assumes the element is bounded by
two integers. -/
theorem exists_floor (x : R) : ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : R) ≤ x := by
  apply exists_floor'
  · obtain ⟨n, hn⟩ := exists_int_lt x
    exact ⟨n, hn.le⟩
  · obtain ⟨n, hn⟩ := exists_int_gt x
    exact ⟨n, hn.le⟩

end StrictOrderedRing

section LinearOrderedSemiring
variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] [ExistsAddOfLE R]
  {x y : R}

/-- Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one. -/
theorem exists_nat_pow_near (hx : 1 ≤ x) (hy : 1 < y) : ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt _ hy
  classical exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
      have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
      ⟨Nat.pred n, le_of_not_gt (Nat.find_min h hltn), by rwa [hnsp]⟩

end LinearOrderedSemiring

section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

lemma exists_nat_one_div_lt (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : K) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  use n
  rw [div_lt_iff₀, ← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

variable [ExistsAddOfLE K]

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,
but with ≤ and < the other way around. -/
theorem exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  classical
  have he : ∃ m : ℤ, y ^ m ≤ x := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
    use -N
    rw [zpow_neg y ↑N, zpow_natCast]
    exact ((inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN).le
  have hb : ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b := by
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy
    refine ⟨M, fun m hm ↦ ?_⟩
    contrapose! hM
    rw [← zpow_natCast]
    exact le_trans (zpow_le_zpow_right₀ hy.le hM.le) hm
  obtain ⟨n, hn₁, hn₂⟩ := Int.exists_greatest_of_bdd hb he
  exact ⟨n, hn₁, lt_of_not_ge fun hge => (Int.lt_succ _).not_ge (hn₂ _ hge)⟩

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ico_zpow`,
but with ≤ and < the other way around. -/
theorem exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) :=
  let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt_comm₀ (zpow_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv_comm₀ hx (zpow_pos hyp _)]⟩

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
theorem exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : ∃ n : ℕ, y ^ n < x := by
  by_cases! y_pos : y ≤ 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rcases pow_unbounded_of_one_lt x⁻¹ ((one_lt_inv₀ y_pos).2 hy) with ⟨q, hq⟩
  exact ⟨q, by rwa [inv_pow, inv_lt_inv₀ hx (pow_pos y_pos _)] at hq⟩

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
theorem exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
    ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n := by
  rcases exists_nat_pow_near (one_le_inv_iff₀.2 ⟨xpos, hx⟩) (one_lt_inv_iff₀.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine ⟨n, ?_, ?_⟩
  · rwa [inv_pow, inv_lt_inv₀ xpos (pow_pos ypos _)] at h'n
  · rwa [inv_pow, inv_le_inv₀ (pow_pos ypos _) xpos] at hn

/-- If `a < b * c`, `0 < b ≤ 1` and `0 < c < 1`, then there is a power `c ^ n` with `n : ℕ`
strictly between `a` and `b`. -/
lemma exists_pow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hb₁ : b ≤ 1)
    (hc₀ : 0 < c) (hc₁ : c < 1) :
    ∃ n : ℕ, a < c ^ n ∧ c ^ n < b := by
  have := exists_pow_lt_of_lt_one hb₀ hc₁
  refine ⟨Nat.find this, h.trans_le ?_, Nat.find_spec this⟩
  by_contra! H
  have hn : Nat.find this ≠ 0 := by
    intro hf
    simp only [hf, pow_zero] at H
    exact (H.trans <| (mul_lt_of_lt_one_right hb₀ hc₁).trans_le hb₁).false
  rw [(Nat.succ_pred_eq_of_ne_zero hn).symm, pow_succ, mul_lt_mul_iff_left₀ hc₀] at H
  exact Nat.find_min this (Nat.sub_one_lt hn) H

/-- If `a < b * c`, `b` is positive and `0 < c < 1`, then there is a power `c ^ n` with `n : ℤ`
strictly between `a` and `b`. -/
lemma exists_zpow_btwn_of_lt_mul {a b c : K} (h : a < b * c) (hb₀ : 0 < b) (hc₀ : 0 < c)
    (hc₁ : c < 1) :
    ∃ n : ℤ, a < c ^ n ∧ c ^ n < b := by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb₀ hc₁
    exact ⟨n, ha.trans_lt (zpow_pos hc₀ _), mod_cast hn⟩
  · rcases le_or_gt b 1 with hb₁ | hb₁
    · obtain ⟨n, hn⟩ := exists_pow_btwn_of_lt_mul h hb₀ hb₁ hc₀ hc₁
      exact ⟨n, mod_cast hn⟩
    · rcases lt_or_ge a 1 with ha₁ | ha₁
      · refine ⟨0, ?_⟩
        rw [zpow_zero]
        exact ⟨ha₁, hb₁⟩
      · have : b⁻¹ < a⁻¹ * c := by rwa [lt_inv_mul_iff₀' ha, inv_mul_lt_iff₀ hb₀]
        obtain ⟨n, hn₁, hn₂⟩ :=
          exists_pow_btwn_of_lt_mul this (inv_pos_of_pos ha) (inv_le_one_of_one_le₀ ha₁) hc₀ hc₁
        refine ⟨-n, ?_, ?_⟩
        · rwa [lt_inv_comm₀ (pow_pos hc₀ n) ha, ← zpow_natCast, ← zpow_neg] at hn₂
        · rwa [inv_lt_comm₀ hb₀ (pow_pos hc₀ n), ← zpow_natCast, ← zpow_neg] at hn₁

end LinearOrderedSemifield

section LinearOrderedField
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem archimedean_iff_nat_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x < n :=
  ⟨@exists_nat_gt K _ _ _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

theorem archimedean_iff_nat_le : Archimedean K ↔ ∀ x : K, ∃ n : ℕ, x ≤ n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩

theorem archimedean_iff_int_lt : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x < n :=
  ⟨@exists_int_gt K _ _ _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

theorem archimedean_iff_int_le : Archimedean K ↔ ∀ x : K, ∃ n : ℤ, x ≤ n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

theorem archimedean_iff_rat_lt : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x < q where
  mp _ x :=
    let ⟨n, h⟩ := exists_nat_gt x
    ⟨n, by rwa [Rat.cast_natCast]⟩
  mpr H := archimedean_iff_nat_lt.2 fun x ↦
    let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h <| mod_cast Nat.le_ceil _⟩

theorem archimedean_iff_rat_le : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

instance : Archimedean ℚ :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

variable [Archimedean K] {x y ε : K}

theorem exists_rat_gt (x : K) : ∃ q : ℚ, x < q := archimedean_iff_rat_lt.mp ‹_› _

theorem exists_rat_lt (x : K) : ∃ q : ℚ, (q : K) < x :=
  let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩

theorem exists_div_btwn {x y : K} {n : ℕ} (h : x < y) (nh : (y - x)⁻¹ < n) :
    ∃ z : ℤ, x < (z : K) / n ∧ (z : K) / n < y := by
  obtain ⟨z, zh⟩ := exists_floor (x * n)
  refine ⟨z + 1, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  rw [div_lt_iff₀ n0']
  refine ⟨(lt_div_iff₀ n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
  rw [Int.cast_add, Int.cast_one]
  grw [(zh _).1 le_rfl]
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff₀' (sub_pos.2 h), one_div]

theorem exists_rat_btwn {x y : K} (h : x < y) : ∃ q : ℚ, x < q ∧ q < y := by
  obtain ⟨n, nh⟩ := exists_nat_gt (y - x)⁻¹
  obtain ⟨z, zh, zh'⟩ := exists_div_btwn h nh
  refine ⟨(z : ℚ) / n, ?_, ?_⟩ <;> simpa

theorem exists_rat_mem_uIoo {x y : K} (h : x ≠ y) : ∃ q : ℚ, ↑q ∈ Set.uIoo x y :=
  exists_rat_btwn (min_lt_max.mpr h)

theorem exists_pow_btwn {n : ℕ} (hn : n ≠ 0) {x y : K} (h : x < y) (hy : 0 < y) :
    ∃ q : K, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  have ⟨δ, δ_pos, cont⟩ := uniform_continuous_npow_on_bounded (max 1 y)
    (sub_pos.mpr <| max_lt_iff.mpr ⟨h, hy⟩) n
  have ex : ∃ m : ℕ, y ≤ (m * δ) ^ n := by
    have ⟨m, hm⟩ := exists_nat_ge (y / δ + 1 / δ)
    refine ⟨m, le_trans ?_ (le_self_pow₀ ?_ hn)⟩ <;> rw [← div_le_iff₀ δ_pos]
    · exact (lt_add_of_pos_right _ <| by positivity).le.trans hm
    · exact (le_add_of_nonneg_left <| by positivity).trans hm
  let m := Nat.find ex
  have m_pos : 0 < m := (Nat.find_pos _).mpr <| by simpa [zero_pow hn] using hy
  let q := m.pred * δ
  have qny : q ^ n < y := lt_of_not_ge (Nat.find_min ex <| Nat.pred_lt m_pos.ne')
  have q1y : |q| < max 1 y := (abs_eq_self.mpr <| by positivity).trans_lt <| lt_max_iff.mpr
    (or_iff_not_imp_left.mpr fun q1 ↦ (le_self_pow₀ (le_of_not_gt q1) hn).trans_lt qny)
  have xqn : max x 0 < q ^ n :=
    calc _ = y - (y - max x 0) := by rw [sub_sub_cancel]
      _ ≤ (m * δ) ^ n - (y - max x 0) := sub_le_sub_right (Nat.find_spec ex) _
      _ < (m * δ) ^ n - ((m * δ) ^ n - q ^ n) := by
        refine sub_lt_sub_left ((le_abs_self _).trans_lt <| cont _ _ q1y.le ?_) _
        rw [← Nat.succ_pred_eq_of_pos m_pos, Nat.cast_succ, ← sub_mul,
          add_sub_cancel_left, one_mul, abs_eq_self.mpr (by positivity)]
      _ = q ^ n := sub_sub_cancel ..
  exact ⟨q, lt_of_le_of_ne (by positivity) fun q0 ↦
    (le_sup_right.trans_lt xqn).ne <| q0 ▸ (zero_pow hn).symm, le_sup_left.trans_lt xqn, qny⟩

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
theorem exists_rat_pow_btwn {n : ℕ} (hn : n ≠ 0) {x y : K} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) ^ n < y := by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : K) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_pow_btwn hn hq₁₂ this
  refine ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans ?_, hy₂.trans' ?_⟩ <;> assumption_mod_cast

theorem le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : K) < x → (q : K) ≤ y) : x ≤ y :=
  le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hy.not_ge <| h _ hx

theorem le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
  le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hx.not_ge <| h _ hy

theorem le_iff_forall_rat_lt_imp_le : x ≤ y ↔ ∀ q : ℚ, (q : K) < x → (q : K) ≤ y :=
  ⟨fun hxy _ hqx ↦ hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

theorem le_iff_forall_lt_rat_imp_le : x ≤ y ↔ ∀ q : ℚ, y < q → x ≤ q :=
  ⟨fun hxy _ hqx ↦ hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

theorem eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : K) < x ↔ (q : K) < y) : x = y :=
  (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm <|
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le

theorem eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
  (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm <|
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le

theorem exists_pos_rat_lt {x : K} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : K) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0

theorem exists_rat_near (x : K) (ε0 : 0 < ε) : ∃ q : ℚ, |x - q| < ε :=
  let ⟨q, h₁, h₂⟩ :=
    exists_rat_btwn <| ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end LinearOrderedField

instance : Archimedean ℕ :=
  ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n, nsmul_eq_mul, Nat.cast_id, mul_one]
    exact Nat.le_mul_of_pos_right n m0⟩⟩

instance : Archimedean ℤ :=
  ⟨fun n m m0 =>
    ⟨n.toNat,
      le_trans (Int.self_le_toNat _) <| by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.natCast_nonneg n.toNat)⟩⟩

instance Nonneg.instArchimedean [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Archimedean M] :
    Archimedean { x : M // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : M) (hy : (0 : M) < y)
    ⟨n, mod_cast hr⟩⟩

instance Nonneg.instMulArchimedean [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R] [ExistsAddOfLE R] :
    MulArchimedean { x : R // 0 ≤ x } :=
  ⟨fun x _ hy ↦ (pow_unbounded_of_one_lt x hy).imp fun _ h ↦ h.le⟩

instance : Archimedean NNRat := Nonneg.instArchimedean
instance : MulArchimedean NNRat := Nonneg.instMulArchimedean

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
@[implicit_reducible]
noncomputable def Archimedean.floorRing (R) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Archimedean R] : FloorRing R :=
  .ofBounded _ exists_nat_ge

-- see Note [lower instance priority]
/-- A linear ordered field that is a floor ring is archimedean. -/
instance (priority := 100) FloorRing.archimedean (K) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] :
    Archimedean K := by
  rw [archimedean_iff_int_le]
  exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩

@[to_additive]
instance Units.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M] :
    MulArchimedean Mˣ :=
  ⟨fun x {_} h ↦ MulArchimedean.arch x.val h⟩

instance WithBot.instArchimedean (M) [AddCommMonoid M] [PartialOrder M] [Archimedean M] :
    Archimedean (WithBot M) := by
  constructor
  intro x y hxy
  cases y with
  | bot => exact absurd hxy bot_le.not_gt
  | coe y =>
    cases x with
    | bot => refine ⟨0, bot_le⟩
    | coe x => simpa [← WithBot.coe_nsmul] using (Archimedean.arch x (by simpa using hxy))

instance WithZero.instMulArchimedean (M) [CommMonoid M] [PartialOrder M] [MulArchimedean M] :
    MulArchimedean (WithZero M) := by
  constructor
  intro x y hxy
  cases y with
  | zero => exact absurd hxy (zero_le _).not_gt
  | coe y =>
    cases x with
    | zero => refine ⟨0, zero_le _⟩
    | coe x => simpa [← WithZero.coe_pow] using (MulArchimedean.arch x (by simpa using hxy))
