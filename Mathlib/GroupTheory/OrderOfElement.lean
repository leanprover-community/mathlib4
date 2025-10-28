/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Julian Kuelshammer
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Order.Group.Action
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Set.Infinite

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `IsOfFinOrder` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `IsOfFinAddOrder` is the additive analogue of `IsOfFinOrder`.
* `orderOf x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `addOrderOf` is the additive analogue of `orderOf`.

## Tags
order of an element
-/

assert_not_exists Field

open Function Fintype Nat Pointwise Subgroup Submonoid
open scoped Finset

variable {G H A α β : Type*}

section Monoid
variable [Monoid G] {a b x y : G} {n m : ℕ}

section IsOfFinOrder

@[to_additive]
theorem isPeriodicPt_mul_iff_pow_eq_one (x : G) : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1 := by
  rw [IsPeriodicPt, IsFixedPt, mul_left_iterate_apply_one]

/-- `IsOfFinOrder` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`. -/
@[to_additive /-- `IsOfFinAddOrder` is a predicate on an element `a` of an
additive monoid to be of finite order, i.e. there exists `n ≥ 1` such that `n • a = 0`. -/]
def IsOfFinOrder (x : G) : Prop :=
  (1 : G) ∈ periodicPts (x * ·)

theorem isOfFinAddOrder_ofMul_iff : IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x :=
  Iff.rfl

theorem isOfFinOrder_ofAdd_iff {α : Type*} [AddMonoid α] {x : α} :
    IsOfFinOrder (Multiplicative.ofAdd x) ↔ IsOfFinAddOrder x := Iff.rfl

@[to_additive]
theorem isOfFinOrder_iff_pow_eq_one : IsOfFinOrder x ↔ ∃ n, 0 < n ∧ x ^ n = 1 := by
  simp [IsOfFinOrder, mem_periodicPts, isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.exists_pow_eq_one, _⟩ := isOfFinOrder_iff_pow_eq_one

@[to_additive]
lemma isOfFinOrder_iff_zpow_eq_one {G} [DivisionMonoid G] {x : G} :
    IsOfFinOrder x ↔ ∃ (n : ℤ), n ≠ 0 ∧ x ^ n = 1 := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn, hn'⟩ ↦ ⟨n, Int.natCast_ne_zero_iff_pos.mpr hn, zpow_natCast x n ▸ hn'⟩,
    fun ⟨n, hn, hn'⟩ ↦ ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩⟩
  rcases (Int.natAbs_eq_iff (a := n)).mp rfl with h | h
  · rwa [h, zpow_natCast] at hn'
  · rwa [h, zpow_neg, inv_eq_one, zpow_natCast] at hn'

/-- See also `injective_pow_iff_not_isOfFinOrder`. -/
@[to_additive /-- See also `injective_nsmul_iff_not_isOfFinAddOrder`. -/]
theorem not_isOfFinOrder_of_injective_pow {x : G} (h : Injective fun n : ℕ => x ^ n) :
    ¬IsOfFinOrder x := by
  simp_rw [isOfFinOrder_iff_pow_eq_one, not_exists, not_and]
  intro n hn_pos hnx
  rw [← pow_zero x] at hnx
  rw [h hnx] at hn_pos
  exact irrefl 0 hn_pos

/-- 1 is of finite order in any monoid. -/
@[to_additive (attr := simp) /-- 0 is of finite order in any additive monoid. -/]
theorem IsOfFinOrder.one : IsOfFinOrder (1 : G) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.one_pos, one_pow 1⟩

@[to_additive]
lemma IsOfFinOrder.pow {n : ℕ} : IsOfFinOrder a → IsOfFinOrder (a ^ n) := by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨m, hm, ha⟩
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩

@[to_additive]
lemma IsOfFinOrder.of_pow {n : ℕ} (h : IsOfFinOrder (a ^ n)) (hn : n ≠ 0) : IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one] at *
  rcases h with ⟨m, hm, ha⟩
  exact ⟨n * m, mul_pos hn.bot_lt hm, by rwa [pow_mul]⟩

@[to_additive (attr := simp)]
lemma isOfFinOrder_pow {n : ℕ} : IsOfFinOrder (a ^ n) ↔ IsOfFinOrder a ∨ n = 0 := by
  rcases Decidable.eq_or_ne n 0 with rfl | hn
  · simp
  · exact ⟨fun h ↦ .inl <| h.of_pow hn, fun h ↦ (h.resolve_right hn).pow⟩

@[to_additive]
lemma not_isOfFinOrder_of_isMulTorsionFree [IsMulTorsionFree G] (ha : a ≠ 1) :
    ¬ IsOfFinOrder a := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, han⟩
  exact ha <| pow_left_injective hn.ne' <| by simpa using han

/-- Elements of finite order are of finite order in submonoids. -/
@[to_additive /-- Elements of finite order are of finite order in submonoids. -/]
theorem Submonoid.isOfFinOrder_coe {H : Submonoid G} {x : H} :
    IsOfFinOrder (x : G) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  norm_cast

theorem IsConj.isOfFinOrder (h : IsConj x y) : IsOfFinOrder x → IsOfFinOrder y := by
  simp_rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, n_gt_0, eq'⟩
  exact ⟨n, n_gt_0, by rw [← isConj_one_right, ← eq']; exact h.pow n⟩

/-- The image of an element of finite order has finite order. -/
@[to_additive /-- The image of an element of finite additive order has finite additive order. -/]
theorem MonoidHom.isOfFinOrder [Monoid H] (f : G →* H) {x : G} (h : IsOfFinOrder x) :
    IsOfFinOrder <| f x :=
  isOfFinOrder_iff_pow_eq_one.mpr <| by
    obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
    exact ⟨n, npos, by rw [← f.map_pow, hn, f.map_one]⟩

/-- If a direct product has finite order then so does each component. -/
@[to_additive /-- If a direct product has finite additive order then so does each component. -/]
theorem IsOfFinOrder.apply {η : Type*} {Gs : η → Type*} [∀ i, Monoid (Gs i)] {x : ∀ i, Gs i}
    (h : IsOfFinOrder x) : ∀ i, IsOfFinOrder (x i) := by
  obtain ⟨n, npos, hn⟩ := h.exists_pow_eq_one
  exact fun _ => isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, (congr_fun hn.symm _).symm⟩

/-- The submonoid generated by an element is a group if that element has finite order. -/
@[to_additive /-- The additive submonoid generated by an element is
an additive group if that element has finite order. -/]
noncomputable abbrev IsOfFinOrder.groupPowers (hx : IsOfFinOrder x) :
    Group (Submonoid.powers x) := by
  obtain ⟨hpos, hx⟩ := hx.exists_pow_eq_one.choose_spec
  exact Submonoid.groupPowers hpos hx

end IsOfFinOrder

/-- `orderOf x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `orderOf x` is `0` by convention. -/
@[to_additive
  /-- `addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it
  exists. Otherwise, i.e. if `a` is of infinite order, then `addOrderOf a` is `0` by convention. -/]
noncomputable def orderOf (x : G) : ℕ :=
  minimalPeriod (x * ·) 1

@[to_additive (attr := nontriviality)]
theorem Subsingleton.orderOf_eq [Subsingleton G] (x : G) : orderOf x = 1 := by
  simp [orderOf, nontriviality]

@[simp]
theorem addOrderOf_ofMul_eq_orderOf (x : G) : addOrderOf (Additive.ofMul x) = orderOf x :=
  rfl

@[simp]
lemma orderOf_ofAdd_eq_addOrderOf {α : Type*} [AddMonoid α] (a : α) :
    orderOf (Multiplicative.ofAdd a) = addOrderOf a := rfl

@[to_additive]
protected lemma IsOfFinOrder.orderOf_pos (h : IsOfFinOrder x) : 0 < orderOf x :=
  minimalPeriod_pos_of_mem_periodicPts h

@[to_additive (attr := simp) addOrderOf_nsmul_eq_zero]
theorem pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1 := by
  convert Eq.trans _ (isPeriodicPt_minimalPeriod (x * ·) 1)
  rw [orderOf, mul_left_iterate_apply_one]

@[to_additive]
theorem orderOf_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0 := by
  rwa [orderOf, minimalPeriod, dif_neg]

@[to_additive (attr := simp)]
theorem orderOf_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder x :=
  ⟨fun h H ↦ H.orderOf_pos.ne' h, orderOf_eq_zero⟩

@[to_additive]
theorem orderOf_eq_zero_iff' : orderOf x = 0 ↔ ∀ n : ℕ, 0 < n → x ^ n ≠ 1 := by
  simp_rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one, not_exists, not_and]

@[to_additive]
lemma orderOf_ne_zero_iff : orderOf x ≠ 0 ↔ IsOfFinOrder x := orderOf_eq_zero_iff.not_left

/-- In a nontrivial monoid with zero, the order of the zero element is zero. -/
@[simp]
lemma orderOf_zero (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀] : orderOf (0 : M₀) = 0 := by
  rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one]
  simp +contextual [ne_of_gt]

@[to_additive]
theorem orderOf_eq_iff {n} (h : 0 < n) :
    orderOf x = n ↔ x ^ n = 1 ∧ ∀ m, m < n → 0 < m → x ^ m ≠ 1 := by
  simp_rw [Ne, ← isPeriodicPt_mul_iff_pow_eq_one, orderOf, minimalPeriod]
  split_ifs with h1
  · classical
    rw [find_eq_iff]
    simp only [h, true_and]
    push_neg
    rfl
  · rw [iff_false_left h.ne]
    rintro ⟨h', -⟩
    exact h1 ⟨n, h, h'⟩

/-- A group element has finite order iff its order is positive. -/
@[to_additive (attr := simp)
/-- A group element has finite additive order iff its order is positive. -/]
theorem orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x := by
  rw [iff_not_comm.mp orderOf_eq_zero_iff, pos_iff_ne_zero]

@[to_additive]
theorem IsOfFinOrder.mono [Monoid β] {y : β} (hx : IsOfFinOrder x) (h : orderOf y ∣ orderOf x) :
    IsOfFinOrder y := by rw [← orderOf_pos_iff] at hx ⊢; exact Nat.pos_of_dvd_of_pos h hx

@[to_additive]
theorem pow_ne_one_of_lt_orderOf (n0 : n ≠ 0) (h : n < orderOf x) : x ^ n ≠ 1 := fun j =>
  not_isPeriodicPt_of_pos_of_lt_minimalPeriod n0 h ((isPeriodicPt_mul_iff_pow_eq_one x).mpr j)
@[to_additive]
theorem orderOf_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : orderOf x ≤ n :=
  IsPeriodicPt.minimalPeriod_le hn (by rwa [isPeriodicPt_mul_iff_pow_eq_one])

@[to_additive (attr := simp)]
theorem orderOf_one : orderOf (1 : G) = 1 := by
  rw [orderOf, ← minimalPeriod_id (x := (1 : G)), ← one_mul_eq_id]

@[to_additive (attr := simp) AddMonoid.addOrderOf_eq_one_iff]
theorem orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1 := by
  rw [orderOf, minimalPeriod_eq_one_iff_isFixedPt, IsFixedPt, mul_one]

@[to_additive (attr := simp) mod_addOrderOf_nsmul]
lemma pow_mod_orderOf (x : G) (n : ℕ) : x ^ (n % orderOf x) = x ^ n :=
  calc
    x ^ (n % orderOf x) = x ^ (n % orderOf x + orderOf x * (n / orderOf x)) := by
        simp [pow_add, pow_mul, pow_orderOf_eq_one]
    _ = x ^ n := by rw [Nat.mod_add_div]

@[to_additive]
theorem orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : orderOf x ∣ n :=
  IsPeriodicPt.minimalPeriod_dvd ((isPeriodicPt_mul_iff_pow_eq_one _).mpr h)

@[to_additive]
theorem orderOf_dvd_iff_pow_eq_one {n : ℕ} : orderOf x ∣ n ↔ x ^ n = 1 :=
  ⟨fun h => by rw [← pow_mod_orderOf, Nat.mod_eq_zero_of_dvd h, _root_.pow_zero],
    orderOf_dvd_of_pow_eq_one⟩

@[to_additive addOrderOf_smul_dvd]
theorem orderOf_pow_dvd (n : ℕ) : orderOf (x ^ n) ∣ orderOf x := by
  rw [orderOf_dvd_iff_pow_eq_one, pow_right_comm, pow_orderOf_eq_one, one_pow]

@[to_additive]
lemma pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).InjOn (x ^ ·) := by
  simpa only [mul_left_iterate_apply_one]
    using iterate_injOn_Iio_minimalPeriod (f := (x * ·)) (x := 1)

@[to_additive]
protected lemma IsOfFinOrder.mem_powers_iff_mem_range_orderOf [DecidableEq G]
    (hx : IsOfFinOrder x) :
    y ∈ Submonoid.powers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' hx.orderOf_pos <| pow_mod_orderOf _

@[to_additive]
protected lemma IsOfFinOrder.powers_eq_image_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) :
    (Submonoid.powers x : Set G) = (Finset.range (orderOf x)).image (x ^ ·) :=
  Set.ext fun _ ↦ hx.mem_powers_iff_mem_range_orderOf

@[to_additive]
theorem pow_eq_one_iff_modEq : x ^ n = 1 ↔ n ≡ 0 [MOD orderOf x] := by
  rw [modEq_zero_iff_dvd, orderOf_dvd_iff_pow_eq_one]

@[to_additive]
theorem orderOf_map_dvd {H : Type*} [Monoid H] (ψ : G →* H) (x : G) :
    orderOf (ψ x) ∣ orderOf x := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow, pow_orderOf_eq_one]
  apply map_one

@[to_additive]
theorem exists_pow_eq_self_of_coprime (h : n.Coprime (orderOf x)) : ∃ m : ℕ, (x ^ n) ^ m = x := by
  by_cases h0 : orderOf x = 0
  · rw [h0, coprime_zero_right] at h
    exact ⟨1, by rw [h, pow_one, pow_one]⟩
  by_cases h1 : orderOf x = 1
  · exact ⟨0, by rw [orderOf_eq_one_iff.mp h1, one_pow, one_pow]⟩
  obtain ⟨m, h⟩ := exists_mul_emod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩)
  exact ⟨m, by rw [← pow_mul, ← pow_mod_orderOf, h, pow_one]⟩

/-- If `x^n = 1`, but `x^(n/p) ≠ 1` for all prime factors `p` of `n`,
then `x` has order `n` in `G`. -/
@[to_additive addOrderOf_eq_of_nsmul_and_div_prime_nsmul /-- If `n * x = 0`, but `n/p * x ≠ 0` for
all prime factors `p` of `n`, then `x` has order `n` in `G`. -/]
theorem orderOf_eq_of_pow_and_pow_div_prime (hn : 0 < n) (hx : x ^ n = 1)
    (hd : ∀ p : ℕ, p.Prime → p ∣ n → x ^ (n / p) ≠ 1) : orderOf x = n := by
  -- Let `a` be `n/(orderOf x)`, and show `a = 1`
  obtain ⟨a, ha⟩ := exists_eq_mul_right_of_dvd (orderOf_dvd_of_pow_eq_one hx)
  suffices a = 1 by simp [this, ha]
  -- Assume `a` is not one...
  by_contra h
  have a_min_fac_dvd_p_sub_one : a.minFac ∣ n := by
    obtain ⟨b, hb⟩ : ∃ b : ℕ, a = b * a.minFac := exists_eq_mul_left_of_dvd a.minFac_dvd
    rw [hb, ← mul_assoc] at ha
    exact Dvd.intro_left (orderOf x * b) ha.symm
  -- Use the minimum prime factor of `a` as `p`.
  refine hd a.minFac (Nat.minFac_prime h) a_min_fac_dvd_p_sub_one ?_
  rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_div_iff_mul_dvd a_min_fac_dvd_p_sub_one, ha, mul_comm,
    Nat.mul_dvd_mul_iff_left (IsOfFinOrder.orderOf_pos _)]
  · exact Nat.minFac_dvd a
  · rw [isOfFinOrder_iff_pow_eq_one]
    exact Exists.intro n (id ⟨hn, hx⟩)

@[to_additive]
theorem orderOf_eq_orderOf_iff {H : Type*} [Monoid H] {y : H} :
    orderOf x = orderOf y ↔ ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1 := by
  simp_rw [← isPeriodicPt_mul_iff_pow_eq_one, ← minimalPeriod_eq_minimalPeriod_iff, orderOf]

/-- An injective homomorphism of monoids preserves orders of elements. -/
@[to_additive /-- An injective homomorphism of additive monoids preserves orders of elements. -/]
theorem orderOf_injective {H : Type*} [Monoid H] (f : G →* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  simp_rw [orderOf_eq_orderOf_iff, ← f.map_pow, ← f.map_one, hf.eq_iff, forall_const]

/-- A multiplicative equivalence preserves orders of elements. -/
@[to_additive (attr := simp) /-- An additive equivalence preserves orders of elements. -/]
lemma MulEquiv.orderOf_eq {H : Type*} [Monoid H] (e : G ≃* H) (x : G) :
    orderOf (e x) = orderOf x :=
  orderOf_injective e.toMonoidHom e.injective x

@[to_additive]
theorem Function.Injective.isOfFinOrder_iff [Monoid H] {f : G →* H} (hf : Injective f) :
    IsOfFinOrder (f x) ↔ IsOfFinOrder x := by
  rw [← orderOf_pos_iff, orderOf_injective f hf x, ← orderOf_pos_iff]

@[to_additive (attr := norm_cast, simp)]
theorem orderOf_submonoid {H : Submonoid G} (y : H) : orderOf (y : G) = orderOf y :=
  orderOf_injective H.subtype Subtype.coe_injective y

@[to_additive (attr := norm_cast)]
theorem orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y :=
  orderOf_injective (Units.coeHom G) Units.val_injective y

@[to_additive]
lemma IsUnit.orderOf_eq_one [Subsingleton Gˣ] {x : G} (h : IsUnit x) :
    orderOf x = 1 := by
  simp [isUnit_iff_eq_one.mp h]

@[to_additive (attr := norm_cast)]
theorem Units.isOfFinOrder_val {u : Gˣ} : IsOfFinOrder (u : G) ↔ IsOfFinOrder u :=
  Units.coeHom_injective.isOfFinOrder_iff

/-- If the order of `x` is finite, then `x` is a unit with inverse `x ^ (orderOf x - 1)`. -/
@[to_additive (attr := simps) /-- If the additive order of `x` is finite, then `x` is an additive
unit with inverse `(addOrderOf x - 1) • x`. -/]
noncomputable def IsOfFinOrder.unit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : Mˣ :=
  ⟨x, x ^ (orderOf x - 1),
    by rw [← _root_.pow_succ', tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one],
    by rw [← _root_.pow_succ, tsub_add_cancel_of_le (by exact hx.orderOf_pos), pow_orderOf_eq_one]⟩

@[to_additive]
lemma IsOfFinOrder.isUnit {M} [Monoid M] {x : M} (hx : IsOfFinOrder x) : IsUnit x := ⟨hx.unit, rfl⟩

variable (x)

@[to_additive]
theorem orderOf_pow' (h : n ≠ 0) : orderOf (x ^ n) = orderOf x / gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd h, mul_left_iterate]

@[to_additive]
lemma orderOf_pow_of_dvd {x : G} {n : ℕ} (hn : n ≠ 0) (dvd : n ∣ orderOf x) :
    orderOf (x ^ n) = orderOf x / n := by rw [orderOf_pow' _ hn, Nat.gcd_eq_right dvd]

@[to_additive]
lemma orderOf_pow_orderOf_div {x : G} {n : ℕ} (hx : orderOf x ≠ 0) (hn : n ∣ orderOf x) :
    orderOf (x ^ (orderOf x / n)) = n := by
  rw [orderOf_pow_of_dvd _ (Nat.div_dvd_of_dvd hn), Nat.div_div_self hn hx]
  rw [← Nat.div_mul_cancel hn] at hx; exact left_ne_zero_of_mul hx

variable (n)

@[to_additive]
protected lemma IsOfFinOrder.orderOf_pow (h : IsOfFinOrder x) :
    orderOf (x ^ n) = orderOf x / gcd (orderOf x) n := by
  unfold orderOf
  rw [← minimalPeriod_iterate_eq_div_gcd' h, mul_left_iterate]

@[to_additive]
lemma Nat.Coprime.orderOf_pow (h : (orderOf y).Coprime m) : orderOf (y ^ m) = orderOf y := by
  by_cases hg : IsOfFinOrder y
  · rw [hg.orderOf_pow y m, h.gcd_eq_one, Nat.div_one]
  · rw [m.coprime_zero_left.1 (orderOf_eq_zero hg ▸ h), pow_one]

@[to_additive]
lemma IsOfFinOrder.natCard_powers_le_orderOf (ha : IsOfFinOrder a) :
    Nat.card (powers a : Set G) ≤ orderOf a := by
  classical
  simpa [ha.powers_eq_image_range_orderOf, Finset.card_range, Nat.Iio_eq_range]
    using Finset.card_image_le (s := Finset.range (orderOf a))

@[to_additive]
lemma IsOfFinOrder.finite_powers (ha : IsOfFinOrder a) : (powers a : Set G).Finite := by
  classical rw [ha.powers_eq_image_range_orderOf]; exact Finset.finite_toSet _

namespace Commute

variable {x}

@[to_additive]
theorem orderOf_mul_dvd_lcm (h : Commute x y) :
    orderOf (x * y) ∣ Nat.lcm (orderOf x) (orderOf y) := by
  rw [orderOf, ← comp_mul_left]
  exact Function.Commute.minimalPeriod_of_comp_dvd_lcm h.function_commute_mul_left

@[to_additive]
theorem orderOf_dvd_lcm_mul (h : Commute x y) :
    orderOf y ∣ Nat.lcm (orderOf x) (orderOf (x * y)) := by
  by_cases h0 : orderOf x = 0
  · rw [h0, lcm_zero_left]
    apply dvd_zero
  conv_lhs =>
    rw [← one_mul y, ← pow_orderOf_eq_one x, ← succ_pred_eq_of_pos (Nat.pos_of_ne_zero h0),
      _root_.pow_succ, mul_assoc]
  exact
    (((Commute.refl x).mul_right h).pow_left _).orderOf_mul_dvd_lcm.trans
      (lcm_dvd_iff.2 ⟨(orderOf_pow_dvd _).trans (dvd_lcm_left _ _), dvd_lcm_right _ _⟩)

@[to_additive addOrderOf_add_dvd_mul_addOrderOf]
theorem orderOf_mul_dvd_mul_orderOf (h : Commute x y) :
    orderOf (x * y) ∣ orderOf x * orderOf y :=
  dvd_trans h.orderOf_mul_dvd_lcm (lcm_dvd_mul _ _)

@[to_additive addOrderOf_add_eq_mul_addOrderOf_of_coprime]
theorem orderOf_mul_eq_mul_orderOf_of_coprime (h : Commute x y)
    (hco : (orderOf x).Coprime (orderOf y)) : orderOf (x * y) = orderOf x * orderOf y := by
  rw [orderOf, ← comp_mul_left]
  exact h.function_commute_mul_left.minimalPeriod_of_comp_eq_mul_of_coprime hco

/-- Commuting elements of finite order are closed under multiplication. -/
@[to_additive /-- Commuting elements of finite additive order are closed under addition. -/]
theorem isOfFinOrder_mul (h : Commute x y) (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) :
    IsOfFinOrder (x * y) :=
  orderOf_pos_iff.mp <|
    pos_of_dvd_of_pos h.orderOf_mul_dvd_mul_orderOf <| mul_pos hx.orderOf_pos hy.orderOf_pos

/-- If each prime factor of `orderOf x` has higher multiplicity in `orderOf y`, and `x` commutes
  with `y`, then `x * y` has the same order as `y`. -/
@[to_additive addOrderOf_add_eq_right_of_forall_prime_mul_dvd
  /-- If each prime factor of
  `addOrderOf x` has higher multiplicity in `addOrderOf y`, and `x` commutes with `y`,
  then `x + y` has the same order as `y`. -/]
theorem orderOf_mul_eq_right_of_forall_prime_mul_dvd (h : Commute x y) (hy : IsOfFinOrder y)
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p * orderOf x ∣ orderOf y) :
    orderOf (x * y) = orderOf y := by
  have hoy := hy.orderOf_pos
  have hxy := dvd_of_forall_prime_mul_dvd hdvd
  apply orderOf_eq_of_pow_and_pow_div_prime hoy <;> simp only [Ne, ← orderOf_dvd_iff_pow_eq_one]
  · exact h.orderOf_mul_dvd_lcm.trans (lcm_dvd hxy dvd_rfl)
  refine fun p hp hpy hd => hp.ne_one ?_
  rw [← Nat.dvd_one, ← mul_dvd_mul_iff_right hoy.ne', one_mul, ← dvd_div_iff_mul_dvd hpy]
  refine (orderOf_dvd_lcm_mul h).trans (lcm_dvd ((dvd_div_iff_mul_dvd hpy).2 ?_) hd)
  by_cases h : p ∣ orderOf x
  exacts [hdvd p hp h, (hp.coprime_iff_not_dvd.2 h).mul_dvd_of_dvd_of_dvd hpy hxy]

end Commute

section PPrime
variable {x n} {p : ℕ} [hp : Fact p.Prime]

@[to_additive]
theorem orderOf_eq_prime_iff : orderOf x = p ↔ x ^ p = 1 ∧ x ≠ 1 := by
  rw [orderOf, minimalPeriod_eq_prime_iff, isPeriodicPt_mul_iff_pow_eq_one, IsFixedPt, mul_one]

/-- The backward direction of `orderOf_eq_prime_iff`. -/
@[to_additive /-- The backward direction of `addOrderOf_eq_prime_iff`. -/]
theorem orderOf_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : orderOf x = p :=
  orderOf_eq_prime_iff.mpr ⟨hg, hg1⟩

@[to_additive addOrderOf_eq_prime_pow]
theorem orderOf_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin : x ^ p ^ (n + 1) = 1) :
    orderOf x = p ^ (n + 1) := by
  apply minimalPeriod_eq_prime_pow <;> rwa [isPeriodicPt_mul_iff_pow_eq_one]

@[to_additive exists_addOrderOf_eq_prime_pow_iff]
theorem exists_orderOf_eq_prime_pow_iff :
    (∃ k : ℕ, orderOf x = p ^ k) ↔ ∃ m : ℕ, x ^ (p : ℕ) ^ m = 1 :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩, fun ⟨_, hm⟩ => by
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.elim).mp (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩⟩

end PPrime

/-- The equivalence between `Fin (orderOf x)` and `Submonoid.powers x`, sending `i` to `x ^ i` -/
@[to_additive /-- The equivalence between `Fin (addOrderOf a)` and
`AddSubmonoid.multiples a`, sending `i` to `i • a` -/]
noncomputable def finEquivPowers {x : G} (hx : IsOfFinOrder x) : Fin (orderOf x) ≃ powers x :=
  Equiv.ofBijective (fun n ↦ ⟨x ^ (n : ℕ), ⟨n, rfl⟩⟩) ⟨fun ⟨_, h₁⟩ ⟨_, h₂⟩ ij ↦
    Fin.ext (pow_injOn_Iio_orderOf h₁ h₂ (Subtype.mk_eq_mk.1 ij)), fun ⟨_, i, rfl⟩ ↦
      ⟨⟨i % orderOf x, mod_lt _ hx.orderOf_pos⟩, Subtype.eq <| pow_mod_orderOf _ _⟩⟩

@[to_additive (attr := simp)]
lemma finEquivPowers_apply {x : G} (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
    finEquivPowers hx n = ⟨x ^ (n : ℕ), n, rfl⟩ := rfl

@[to_additive (attr := simp)]
lemma finEquivPowers_symm_apply {x : G} (hx : IsOfFinOrder x) (n : ℕ) :
    (finEquivPowers hx).symm ⟨x ^ n, _, rfl⟩ = ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos⟩ := by
  rw [Equiv.symm_apply_eq, finEquivPowers_apply, Subtype.mk_eq_mk, ← pow_mod_orderOf, Fin.val_mk]

variable {x n} (hx : IsOfFinOrder x)
include hx

@[to_additive]
theorem IsOfFinOrder.pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m ≤ n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, (hx.isUnit.pow _).mul_eq_left, pow_eq_one_iff_modEq]
  exact ⟨fun h ↦ Nat.ModEq.add_left _ h, fun h ↦ Nat.ModEq.add_left_cancel' _ h⟩

@[to_additive]
lemma IsOfFinOrder.pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x :=
  hx.pow_eq_pow_iff_modEq

end Monoid

section CancelMonoid
variable [LeftCancelMonoid G] {x y : G} {a : G} {m n : ℕ}

@[to_additive]
theorem pow_eq_pow_iff_modEq : x ^ n = x ^ m ↔ n ≡ m [MOD orderOf x] := by
  wlog hmn : m ≤ n generalizing m n
  · rw [eq_comm, ModEq.comm, this (le_of_not_ge hmn)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [← mul_one (x ^ m), pow_add, mul_left_cancel_iff, pow_eq_one_iff_modEq]
  exact ⟨fun h => Nat.ModEq.add_left _ h, fun h => Nat.ModEq.add_left_cancel' _ h⟩

@[to_additive (attr := simp)]
lemma injective_pow_iff_not_isOfFinOrder : Injective (fun n : ℕ ↦ x ^ n) ↔ ¬IsOfFinOrder x := by
  refine ⟨fun h => not_isOfFinOrder_of_injective_pow h, fun h n m hnm => ?_⟩
  rwa [pow_eq_pow_iff_modEq, orderOf_eq_zero_iff.mpr h, modEq_zero_iff] at hnm

@[to_additive]
lemma pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x := pow_eq_pow_iff_modEq

@[to_additive]
theorem pow_inj_iff_of_orderOf_eq_zero (h : orderOf x = 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := by
  rw [pow_eq_pow_iff_modEq, h, modEq_zero_iff]

@[to_additive]
theorem infinite_not_isOfFinOrder {x : G} (h : ¬IsOfFinOrder x) :
    { y : G | ¬IsOfFinOrder y }.Infinite := by
  let s := { n | 0 < n }.image fun n : ℕ => x ^ n
  have hs : s ⊆ { y : G | ¬IsOfFinOrder y } := by
    rintro - ⟨n, hn : 0 < n, rfl⟩ (contra : IsOfFinOrder (x ^ n))
    apply h
    rw [isOfFinOrder_iff_pow_eq_one] at contra ⊢
    obtain ⟨m, hm, hm'⟩ := contra
    exact ⟨n * m, mul_pos hn hm, by rwa [pow_mul]⟩
  suffices s.Infinite by exact this.mono hs
  contrapose! h
  have : ¬Injective fun n : ℕ => x ^ n := by
    have := Set.not_injOn_infinite_finite_image (Set.Ioi_infinite 0) (Set.not_infinite.mp h)
    contrapose! this
    exact Set.injOn_of_injective this
  rwa [injective_pow_iff_not_isOfFinOrder, Classical.not_not] at this

@[to_additive (attr := simp)]
lemma finite_powers : (powers a : Set G).Finite ↔ IsOfFinOrder a := by
  refine ⟨fun h ↦ ?_, IsOfFinOrder.finite_powers⟩
  obtain ⟨m, n, hmn, ha⟩ := h.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ ↦ a ^ n)
    (fun n ↦ by simp [mem_powers_iff])
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨n - m, tsub_pos_iff_lt.2 hmn, ?_⟩
  rw [← mul_left_cancel_iff (a := a ^ m), ← pow_add, add_tsub_cancel_of_le hmn.le, ha, mul_one]

@[to_additive (attr := simp)]
lemma infinite_powers : (powers a : Set G).Infinite ↔ ¬ IsOfFinOrder a := finite_powers.not

/-- See also `orderOf_eq_card_powers`. -/
@[to_additive /-- See also `addOrder_eq_card_multiples`. -/]
lemma Nat.card_submonoidPowers : Nat.card (powers a) = orderOf a := by
  classical
  by_cases ha : IsOfFinOrder a
  · exact (Nat.card_congr (finEquivPowers ha).symm).trans <| by simp
  · have := (infinite_powers.2 ha).to_subtype
    rw [orderOf_eq_zero ha, Nat.card_eq_zero_of_infinite]

end CancelMonoid

section Group

variable [Group G] {x y : G} {i : ℤ}

/-- Inverses of elements of finite order have finite order. -/
@[to_additive (attr := simp) /-- Inverses of elements of finite additive order
have finite additive order. -/]
theorem isOfFinOrder_inv_iff {x : G} : IsOfFinOrder x⁻¹ ↔ IsOfFinOrder x := by
  simp [isOfFinOrder_iff_pow_eq_one]

@[to_additive] alias ⟨IsOfFinOrder.of_inv, IsOfFinOrder.inv⟩ := isOfFinOrder_inv_iff

@[to_additive]
theorem orderOf_dvd_iff_zpow_eq_one : (orderOf x : ℤ) ∣ i ↔ x ^ i = 1 := by
  rcases Int.eq_nat_or_neg i with ⟨i, rfl | rfl⟩
  · rw [Int.natCast_dvd_natCast, orderOf_dvd_iff_pow_eq_one, zpow_natCast]
  · rw [dvd_neg, Int.natCast_dvd_natCast, zpow_neg, inv_eq_one, zpow_natCast,
      orderOf_dvd_iff_pow_eq_one]

@[to_additive (attr := simp)]
theorem orderOf_inv (x : G) : orderOf x⁻¹ = orderOf x := by simp [orderOf_eq_orderOf_iff]

@[to_additive]
theorem orderOf_dvd_sub_iff_zpow_eq_zpow {a b : ℤ} : (orderOf x : ℤ) ∣ a - b ↔ x ^ a = x ^ b := by
  rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]

namespace Subgroup
variable {H : Subgroup G}

@[to_additive (attr := norm_cast)]
lemma orderOf_coe (a : H) : orderOf (a : G) = orderOf a :=
  orderOf_injective H.subtype Subtype.coe_injective _

@[to_additive (attr := simp)]
lemma orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = orderOf a := (orderOf_coe _).symm

end Subgroup

@[to_additive mod_addOrderOf_zsmul]
lemma zpow_mod_orderOf (x : G) (z : ℤ) : x ^ (z % (orderOf x : ℤ)) = x ^ z :=
  calc
    x ^ (z % (orderOf x : ℤ)) = x ^ (z % orderOf x + orderOf x * (z / orderOf x) : ℤ) := by
        simp [zpow_add, zpow_mul, pow_orderOf_eq_one]
    _ = x ^ z := by rw [Int.emod_add_mul_ediv]

@[to_additive (attr := simp) zsmul_smul_addOrderOf]
theorem zpow_pow_orderOf : (x ^ i) ^ orderOf x = 1 := by
  by_cases h : IsOfFinOrder x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · rw [orderOf_eq_zero h, _root_.pow_zero]

@[to_additive]
theorem IsOfFinOrder.zpow (h : IsOfFinOrder x) {i : ℤ} : IsOfFinOrder (x ^ i) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf x, h.orderOf_pos, zpow_pow_orderOf⟩

@[to_additive]
theorem IsOfFinOrder.of_mem_zpowers (h : IsOfFinOrder x) (h' : y ∈ Subgroup.zpowers x) :
    IsOfFinOrder y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h'
  exact h.zpow

@[to_additive]
theorem orderOf_dvd_of_mem_zpowers (h : y ∈ Subgroup.zpowers x) : orderOf y ∣ orderOf x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [orderOf_dvd_iff_pow_eq_one]
  exact zpow_pow_orderOf

theorem smul_eq_self_of_mem_zpowers {α : Type*} [MulAction G α] (hx : x ∈ Subgroup.zpowers y)
    {a : α} (hs : y • a = a) : x • a = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAction.toPerm_apply, ← MulAction.toPermHom_apply, MonoidHom.map_zpow _ y k,
    MulAction.toPermHom_apply]
  exact Function.IsFixedPt.perm_zpow (by exact hs) k -- Porting note: help elab'n with `by exact`

theorem vadd_eq_self_of_mem_zmultiples {G : Type*} [AddGroup G] {x y : G} {α : Type*}
    [AddAction G α] (hx : x ∈ AddSubgroup.zmultiples y) {a : α} (hs : y +ᵥ a = a) : x +ᵥ a = a :=
  @smul_eq_self_of_mem_zpowers (Multiplicative G) _ _ _ α _ hx a hs

attribute [to_additive existing] smul_eq_self_of_mem_zpowers

@[to_additive]
lemma IsOfFinOrder.mem_powers_iff_mem_zpowers (hx : IsOfFinOrder x) :
    y ∈ powers x ↔ y ∈ zpowers x :=
  ⟨fun ⟨n, hn⟩ ↦ ⟨n, by simp_all⟩, fun ⟨i, hi⟩ ↦ ⟨(i % orderOf x).natAbs, by
    dsimp only
    rwa [← zpow_natCast, Int.natAbs_of_nonneg <| Int.emod_nonneg _ <|
      Int.natCast_ne_zero_iff_pos.2 <| hx.orderOf_pos, zpow_mod_orderOf]⟩⟩

@[to_additive]
lemma IsOfFinOrder.powers_eq_zpowers (hx : IsOfFinOrder x) : (powers x : Set G) = zpowers x :=
  Set.ext fun _ ↦ hx.mem_powers_iff_mem_zpowers

@[to_additive]
lemma IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf [DecidableEq G] (hx : IsOfFinOrder x) :
    y ∈ zpowers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  hx.mem_powers_iff_mem_zpowers.symm.trans hx.mem_powers_iff_mem_range_orderOf

/-- See `Subgroup.closure_toSubmonoid_of_finite` for a version for finite groups. -/
@[to_additive
/-- See `AddSubgroup.closure_toAddSubmonoid_of_finite` for a version for finite additive groups. -/]
lemma Subgroup.closure_toSubmonoid_of_isOfFinOrder {s : Set G} (hs : ∀ x ∈ s, IsOfFinOrder x) :
    (closure s).toSubmonoid = Submonoid.closure s := by
  refine le_antisymm ?_ (le_closure_toSubmonoid s)
  rw [closure_toSubmonoid]
  refine Submonoid.closure_le.mpr <| Set.union_subset Submonoid.subset_closure
    fun x (hx : x⁻¹ ∈ s) ↦ ?_
  apply Submonoid.powers_le.mpr (Submonoid.subset_closure hx)
  simp [(hs _ hx).mem_powers_iff_mem_zpowers]

/-- The equivalence between `Fin (orderOf x)` and `Subgroup.zpowers x`, sending `i` to `x ^ i`. -/
@[to_additive /-- The equivalence between `Fin (addOrderOf a)` and
`Subgroup.zmultiples a`, sending `i` to `i • a`. -/]
noncomputable def finEquivZPowers (hx : IsOfFinOrder x) :
    Fin (orderOf x) ≃ zpowers x :=
  (finEquivPowers hx).trans <| Equiv.setCongr hx.powers_eq_zpowers

@[to_additive]
lemma finEquivZPowers_apply (hx : IsOfFinOrder x) {n : Fin (orderOf x)} :
    finEquivZPowers hx n = ⟨x ^ (n : ℕ), n, zpow_natCast x n⟩ := rfl

@[to_additive]
lemma finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (n : ℕ) :
    (finEquivZPowers hx).symm ⟨x ^ n, ⟨n, by simp⟩⟩ =
    ⟨n % orderOf x, Nat.mod_lt _ hx.orderOf_pos⟩ := by
  rw [finEquivZPowers, Equiv.symm_trans_apply]; exact finEquivPowers_symm_apply _ n

@[to_additive]
lemma pow_finEquivZPowers_symm_apply (hx : IsOfFinOrder x) (a : Subgroup.zpowers x) :
    x ^ ((finEquivZPowers hx).symm a : ℕ) = a := by
  simpa only [finEquivZPowers_apply] using
    congr_arg Subtype.val ((finEquivZPowers hx).apply_symm_apply a)

end Group

section CommMonoid

variable [CommMonoid G] {x y : G}

/-- Elements of finite order are closed under multiplication. -/
@[to_additive /-- Elements of finite additive order are closed under addition. -/]
theorem IsOfFinOrder.mul (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) : IsOfFinOrder (x * y) :=
  (Commute.all x y).isOfFinOrder_mul hx hy

end CommMonoid

section CommGroup
variable [CommGroup G]

@[to_additive]
lemma isMulTorsionFree_iff_not_isOfFinOrder :
    IsMulTorsionFree G ↔ ∀ ⦃a : G⦄, a ≠ 1 → ¬ IsOfFinOrder a where
  mp _ _ := not_isOfFinOrder_of_isMulTorsionFree
  mpr hG := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    rw [← div_eq_one] at hab ⊢
    simp only [← div_pow, isOfFinOrder_iff_pow_eq_one] at hab hG
    exact of_not_not fun hab' ↦ hG hab' ⟨n, hn.bot_lt, hab⟩

@[to_additive]
alias ⟨_, IsMulTorsionFree.of_not_isOfFinOrder⟩ := isMulTorsionFree_iff_not_isOfFinOrder

@[to_additive]
lemma not_isMulTorsionFree_iff_isOfFinOrder :
    ¬ IsMulTorsionFree G ↔ ∃ a ≠ (1 : G), IsOfFinOrder a := by
  simp [isMulTorsionFree_iff_not_isOfFinOrder]

@[to_additive (attr := simp)]
lemma zpowers_mabs [LinearOrder G] [IsOrderedMonoid G] (g : G) : zpowers |g|ₘ = zpowers g := by
  rcases mabs_cases g with h | h <;> simp only [h, zpowers_inv]

end CommGroup

section FiniteMonoid

variable [Monoid G] {x : G} {n : ℕ}

@[to_additive]
theorem sum_card_orderOf_eq_card_pow_eq_one [Fintype G] [DecidableEq G] (hn : n ≠ 0) :
    ∑ m ∈ divisors n, #{x : G | orderOf x = m} = #{x : G | x ^ n = 1} := by
  refine (Finset.card_biUnion ?_).symm.trans ?_
  · simp +contextual [Set.PairwiseDisjoint, Set.Pairwise, disjoint_iff, Finset.ext_iff]
  · congr; ext; simp [hn, orderOf_dvd_iff_pow_eq_one]

@[to_additive]
theorem orderOf_le_card_univ [Fintype G] : orderOf x ≤ Fintype.card G :=
  Finset.le_card_of_inj_on_range (x ^ ·) (fun _ _ ↦ Finset.mem_univ _) pow_injOn_Iio_orderOf

@[to_additive]
theorem orderOf_le_card [Finite G] : orderOf x ≤ Nat.card G := by
  obtain ⟨⟩ := nonempty_fintype G
  simpa using orderOf_le_card_univ

end FiniteMonoid

section FiniteCancelMonoid
variable [LeftCancelMonoid G]
-- TODO: Of course everything also works for `RightCancelMonoid`.

section Finite
variable [Finite G] {x y : G} {n : ℕ}

-- TODO: Use this to show that a finite left cancellative monoid is a group.
@[to_additive]
lemma isOfFinOrder_of_finite (x : G) : IsOfFinOrder x := by
  by_contra h; exact infinite_not_isOfFinOrder h <| Set.toFinite _

/-- This is the same as `IsOfFinOrder.orderOf_pos` but with one fewer explicit assumption since this
is automatic in case of a finite cancellative monoid. -/
@[to_additive /-- This is the same as `IsOfFinAddOrder.addOrderOf_pos` but with one fewer explicit
assumption since this is automatic in case of a finite cancellative additive monoid. -/]
lemma orderOf_pos (x : G) : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos

/-- This is the same as `orderOf_pow'` and `orderOf_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid. -/
@[to_additive /-- This is the same as `addOrderOf_nsmul'` and
`addOrderOf_nsmul` but with one assumption less which is automatic in the case of a
finite cancellative additive monoid. -/]
theorem orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / gcd (orderOf x) n :=
  (isOfFinOrder_of_finite _).orderOf_pow ..

@[to_additive]
theorem mem_powers_iff_mem_range_orderOf [DecidableEq G] :
    y ∈ powers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' (orderOf_pos x) <| pow_mod_orderOf _

/-- The equivalence between `Submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive
  /-- The equivalence between `Submonoid.multiples` of two elements `a, b` of the same additive
  order, mapping `i • a` to `i • b`. -/]
noncomputable def powersEquivPowers (h : orderOf x = orderOf y) : powers x ≃ powers y :=
  (finEquivPowers <| isOfFinOrder_of_finite _).symm.trans <|
    (finCongr h).trans <| finEquivPowers <| isOfFinOrder_of_finite _

@[to_additive (attr := simp)]
theorem powersEquivPowers_apply (h : orderOf x = orderOf y) (n : ℕ) :
    powersEquivPowers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ := by
  rw [powersEquivPowers, Equiv.trans_apply, Equiv.trans_apply, finEquivPowers_symm_apply, ←
    Equiv.eq_symm_apply, finEquivPowers_symm_apply]
  simp [h]

end Finite

variable [Fintype G] {x : G}

@[to_additive]
lemma orderOf_eq_card_powers : orderOf x = Fintype.card (powers x : Submonoid G) :=
  (Fintype.card_fin (orderOf x)).symm.trans <|
    Fintype.card_eq.2 ⟨finEquivPowers <| isOfFinOrder_of_finite _⟩

end FiniteCancelMonoid

lemma isOfFinOrder_iff_isUnit [Monoid G] [Finite Gˣ] {x : G} : IsOfFinOrder x ↔ IsUnit x := by
  use IsOfFinOrder.isUnit
  rintro ⟨u, rfl⟩
  rw [Units.isOfFinOrder_val]
  apply isOfFinOrder_of_finite

alias ⟨_, IsUnit.isOfFinOrder⟩ := isOfFinOrder_iff_isUnit

lemma orderOf_eq_zero_iff_eq_zero {G₀ : Type*} [GroupWithZero G₀] [Finite G₀] {a : G₀} :
    orderOf a = 0 ↔ a = 0 := by
  -- Prove an instance inline to avoid extra imports.
  -- TODO: move this instance elsewhere?
  have : Finite G₀ˣ := .of_injective _ Units.val_injective
  simp [isOfFinOrder_iff_isUnit]

section FiniteGroup
variable [Group G] {x y : G}

@[to_additive]
theorem zpow_eq_one_iff_modEq {n : ℤ} : x ^ n = 1 ↔ n ≡ 0 [ZMOD orderOf x] := by
  rw [Int.modEq_zero_iff_dvd, orderOf_dvd_iff_zpow_eq_one]


@[to_additive]
theorem zpow_eq_zpow_iff_modEq {m n : ℤ} : x ^ m = x ^ n ↔ m ≡ n [ZMOD orderOf x] := by
  rw [← mul_inv_eq_one, ← zpow_sub, zpow_eq_one_iff_modEq, Int.modEq_iff_dvd, Int.modEq_iff_dvd,
    zero_sub, neg_sub]

@[to_additive (attr := simp)]
theorem injective_zpow_iff_not_isOfFinOrder : (Injective fun n : ℤ => x ^ n) ↔ ¬IsOfFinOrder x := by
  refine ⟨?_, fun h n m hnm => ?_⟩
  · simp_rw [isOfFinOrder_iff_pow_eq_one]
    rintro h ⟨n, hn, hx⟩
    exact Nat.cast_ne_zero.2 hn.ne' (h <| by simpa using hx)
  rwa [zpow_eq_zpow_iff_modEq, orderOf_eq_zero_iff.2 h, Nat.cast_zero, Int.modEq_zero_iff] at hnm

@[to_additive]
lemma Subgroup.zpowers_eq_zpowers_iff {x y : G} (hx : ¬IsOfFinOrder x) :
    zpowers x = zpowers y ↔ x = y ∨ x⁻¹ = y := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  have hx_mem : x ∈ zpowers y := by simp [← h]
  have hy_mem : y ∈ zpowers x := by simp [h]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy_mem
  obtain ⟨l, hl⟩ := mem_zpowers_iff.mp hx_mem
  rw [← zpow_mul] at hl
  nth_rewrite 2 [← zpow_one x] at hl
  have h1 := (injective_zpow_iff_not_isOfFinOrder.mpr hx) hl
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one).mp h1 with (h | h) <;> simp [h.1]
section Finite
variable [Finite G]

@[to_additive]
theorem exists_zpow_eq_one (x : G) : ∃ (i : ℤ) (_ : i ≠ 0), x ^ (i : ℤ) = 1 := by
  obtain ⟨w, hw1, hw2⟩ := isOfFinOrder_of_finite x
  refine ⟨w, Int.natCast_ne_zero.mpr (_root_.ne_of_gt hw1), ?_⟩
  rw [zpow_natCast]
  exact (isPeriodicPt_mul_iff_pow_eq_one _).mp hw2

@[to_additive]
lemma mem_powers_iff_mem_zpowers : y ∈ powers x ↔ y ∈ zpowers x :=
  (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers

@[to_additive]
lemma powers_eq_zpowers (x : G) : (powers x : Set G) = zpowers x :=
  (isOfFinOrder_of_finite _).powers_eq_zpowers

@[to_additive]
lemma mem_zpowers_iff_mem_range_orderOf [DecidableEq G] :
    y ∈ zpowers x ↔ y ∈ (Finset.range (orderOf x)).image (x ^ ·) :=
  (isOfFinOrder_of_finite _).mem_zpowers_iff_mem_range_orderOf

/-- The equivalence between `Subgroup.zpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[to_additive
  /-- The equivalence between `Subgroup.zmultiples` of two elements `a, b` of the same additive
  order, mapping `i • a` to `i • b`. -/]
noncomputable def zpowersEquivZPowers (h : orderOf x = orderOf y) :
    Subgroup.zpowers x ≃ Subgroup.zpowers y :=
  (finEquivZPowers <| isOfFinOrder_of_finite _).symm.trans <| (finCongr h).trans <|
    finEquivZPowers <| isOfFinOrder_of_finite _

@[to_additive (attr := simp) zmultiples_equiv_zmultiples_apply]
theorem zpowersEquivZPowers_apply (h : orderOf x = orderOf y) (n : ℕ) :
    zpowersEquivZPowers h ⟨x ^ n, n, zpow_natCast x n⟩ = ⟨y ^ n, n, zpow_natCast y n⟩ := by
  rw [zpowersEquivZPowers, Equiv.trans_apply, Equiv.trans_apply, finEquivZPowers_symm_apply, ←
    Equiv.eq_symm_apply, finEquivZPowers_symm_apply]
  simp [h]

/-- See `Subgroup.closure_toSubmonoid_of_isOfFinOrder` for a version with weaker assumptions. -/
@[to_additive
/-- See `AddSubgroup.closure_toAddSubmonoid_of_isOfFinOrder` for a version with weaker
assumptions. -/]
lemma Subgroup.closure_toSubmonoid_of_finite {s : Set G} :
    (closure s).toSubmonoid = Submonoid.closure s :=
  closure_toSubmonoid_of_isOfFinOrder <| by simp [isOfFinOrder_of_finite]

end Finite

variable [Fintype G] {x : G} {n : ℕ}

/-- See also `Nat.card_zpowers`. -/
@[to_additive /-- See also `Nat.card_zmultiples`. -/]
theorem Fintype.card_zpowers : Fintype.card (zpowers x) = orderOf x :=
  (Fintype.card_eq.2 ⟨finEquivZPowers <| isOfFinOrder_of_finite _⟩).symm.trans <|
    Fintype.card_fin (orderOf x)

@[to_additive]
theorem card_zpowers_le (a : G) {k : ℕ} (k_pos : k ≠ 0)
    (ha : a ^ k = 1) : Fintype.card (Subgroup.zpowers a) ≤ k := by
  rw [Fintype.card_zpowers]
  apply orderOf_le_of_pow_eq_one k_pos.bot_lt ha

open QuotientGroup

@[to_additive]
theorem orderOf_dvd_card : orderOf x ∣ Fintype.card G := by
  use Fintype.card (G ⧸ zpowers x)
  rw [← card_zpowers, mul_comm, ← Fintype.card_prod,
    ← Fintype.card_congr groupEquivQuotientProdSubgroup]

@[to_additive]
theorem orderOf_dvd_natCard {G : Type*} [Group G] (x : G) : orderOf x ∣ Nat.card G := by
  obtain h | h := fintypeOrInfinite G
  · simp only [Nat.card_eq_fintype_card, orderOf_dvd_card]
  · simp only [card_eq_zero_of_infinite, dvd_zero]

@[to_additive]
nonrec lemma Subgroup.orderOf_dvd_natCard {G : Type*} [Group G] (s : Subgroup G) {x} (hx : x ∈ s) :
    orderOf x ∣ Nat.card s := by
  simpa using orderOf_dvd_natCard (⟨x, hx⟩ : s)

@[to_additive]
lemma Subgroup.orderOf_le_card {G : Type*} [Group G] (s : Subgroup G) (hs : (s : Set G).Finite)
    {x} (hx : x ∈ s) : orderOf x ≤ Nat.card s :=
  le_of_dvd (Nat.card_pos_iff.2 <| ⟨s.coe_nonempty.to_subtype, hs.to_subtype⟩) <|
    s.orderOf_dvd_natCard hx

@[to_additive]
lemma Submonoid.orderOf_le_card {G : Type*} [Group G] (s : Submonoid G) (hs : (s : Set G).Finite)
    {x} (hx : x ∈ s) : orderOf x ≤ Nat.card s := by
  rw [← Nat.card_submonoidPowers]; exact Nat.card_mono hs <| powers_le.2 hx

@[to_additive (attr := simp) card_nsmul_eq_zero']
theorem pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ Nat.card G = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp <| orderOf_dvd_natCard _

@[to_additive (attr := simp) card_nsmul_eq_zero]
theorem pow_card_eq_one : x ^ Fintype.card G = 1 := by
  rw [← Nat.card_eq_fintype_card, pow_card_eq_one']

@[to_additive]
theorem Subgroup.pow_index_mem {G : Type*} [Group G] (H : Subgroup G) [Normal H] (g : G) :
    g ^ index H ∈ H := by rw [← eq_one_iff, QuotientGroup.mk_pow H, index, pow_card_eq_one']


@[to_additive (attr := simp) mod_card_nsmul]
lemma pow_mod_card (a : G) (n : ℕ) : a ^ (n % card G) = a ^ n := by
  rw [eq_comm, ← pow_mod_orderOf, ← Nat.mod_mod_of_dvd n orderOf_dvd_card, pow_mod_orderOf]

@[to_additive (attr := simp) mod_card_zsmul]
theorem zpow_mod_card (a : G) (n : ℤ) : a ^ (n % Fintype.card G : ℤ) = a ^ n := by
  rw [eq_comm, ← zpow_mod_orderOf, ← Int.emod_emod_of_dvd n
    (Int.natCast_dvd_natCast.2 orderOf_dvd_card), zpow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_nsmul]
lemma pow_mod_natCard {G} [Group G] (a : G) (n : ℕ) : a ^ (n % Nat.card G) = a ^ n := by
  rw [eq_comm, ← pow_mod_orderOf, ← Nat.mod_mod_of_dvd n <| orderOf_dvd_natCard _, pow_mod_orderOf]

@[to_additive (attr := simp) mod_natCard_zsmul]
lemma zpow_mod_natCard {G} [Group G] (a : G) (n : ℤ) : a ^ (n % Nat.card G : ℤ) = a ^ n := by
  rw [eq_comm, ← zpow_mod_orderOf, ← Int.emod_emod_of_dvd n <|
    Int.natCast_dvd_natCast.2 <| orderOf_dvd_natCard _, zpow_mod_orderOf]

/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[to_additive (attr := simps) /-- If `gcd(|G|,n)=1` then the smul by `n` is a bijection -/]
noncomputable def powCoprime {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : G ≃ G where
  toFun g := g ^ n
  invFun g := g ^ (Nat.card G).gcdB n
  left_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    dsimp only at key
    rwa [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key
  right_inv g := by
    have key := congr_arg (g ^ ·) ((Nat.card G).gcd_eq_gcd_ab n)
    dsimp only at key
    rwa [zpow_add, zpow_mul, zpow_mul', zpow_natCast, zpow_natCast, zpow_natCast, h.gcd_eq_one,
      pow_one, pow_card_eq_one', one_zpow, one_mul, eq_comm] at key

@[to_additive]
theorem powCoprime_one {G : Type*} [Group G] (h : (Nat.card G).Coprime n) : powCoprime h 1 = 1 :=
  one_pow n

@[to_additive]
theorem powCoprime_inv {G : Type*} [Group G] (h : (Nat.card G).Coprime n) {g : G} :
    powCoprime h g⁻¹ = (powCoprime h g)⁻¹ :=
  inv_pow g n

@[to_additive Nat.Coprime.nsmul_right_bijective]
lemma Nat.Coprime.pow_left_bijective {G} [Group G] (hn : (Nat.card G).Coprime n) :
    Bijective (· ^ n : G → G) :=
  (powCoprime hn).bijective

/- TODO: Generalise to `Submonoid.powers`. -/
@[to_additive]
theorem image_range_orderOf [DecidableEq G] :
    letI : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
    Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset := by
  letI : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  ext x
  rw [Set.mem_toFinset, SetLike.mem_coe, mem_zpowers_iff_mem_range_orderOf]

/- TODO: Generalise to `Finite` + `CancelMonoid`. -/
@[to_additive gcd_nsmul_card_eq_zero_iff]
theorem pow_gcd_card_eq_one_iff : x ^ n = 1 ↔ x ^ gcd n (Fintype.card G) = 1 :=
  ⟨fun h => pow_gcd_eq_one _ h <| pow_card_eq_one, fun h => by
    let ⟨m, hm⟩ := gcd_dvd_left n (Fintype.card G)
    rw [hm, pow_mul, h, one_pow]⟩

lemma smul_eq_of_le_smul
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : a ≤ g • a) : g • a = a := by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul, ← _root_.pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm key h

lemma smul_eq_of_smul_le
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] (h : g • a ≤ a) : g • a = a := by
  have key := smul_mono_right g (pow_smul_le h (Nat.card G - 1))
  rw [smul_smul, ← _root_.pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm h key

end FiniteGroup

section PowIsSubgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
@[to_additive
/-- A nonempty idempotent subset of a finite cancellative additive monoid is a submonoid -/]
def submonoidOfIdempotent {M : Type*} [LeftCancelMonoid M] [Finite M] (S : Set M)
    (hS1 : S.Nonempty) (hS2 : S * S = S) : Submonoid M :=
  have pow_mem (a : M) (ha : a ∈ S) (n : ℕ) : a ^ (n + 1) ∈ S := by
    induction n with
    | zero => rwa [zero_add, pow_one]
    | succ n ih =>
      rw [← hS2, pow_succ]
      exact Set.mul_mem_mul ih ha
  { carrier := S
    one_mem' := by
      obtain ⟨a, ha⟩ := hS1
      rw [← pow_orderOf_eq_one a, ← tsub_add_cancel_of_le (succ_le_of_lt (orderOf_pos a))]
      exact pow_mem a ha (orderOf a - 1)
    mul_mem' := fun ha hb => (congr_arg₂ (· ∈ ·) rfl hS2).mp (Set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
@[to_additive /-- A nonempty idempotent subset of a finite additive group is a subgroup -/]
def subgroupOfIdempotent {G : Type*} [Group G] [Finite G] (S : Set G) (hS1 : S.Nonempty)
    (hS2 : S * S = S) : Subgroup G :=
  { submonoidOfIdempotent S hS1 hS2 with
    carrier := S
    inv_mem' := fun {a} ha => show a⁻¹ ∈ submonoidOfIdempotent S hS1 hS2 by
      rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a, ← pow_sub a (orderOf_pos a)]
      exact pow_mem ha (orderOf a - 1) }

/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
@[to_additive (attr := simps!) smulCardAddSubgroup
  /-- If `S` is a nonempty subset of a finite additive group `G`, then `|G| • S` is a subgroup -/]
def powCardSubgroup {G : Type*} [Group G] [Fintype G] (S : Set G) (hS : S.Nonempty) : Subgroup G :=
  have one_mem : (1 : G) ∈ S ^ Fintype.card G := by
    obtain ⟨a, ha⟩ := hS
    rw [← pow_card_eq_one]
    exact Set.pow_mem_pow ha
  subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩ <| by
    classical
    apply (Set.eq_of_subset_of_card_le (Set.subset_mul_left _ one_mem) (ge_of_eq _)).symm
    simp_rw [← pow_add,
        Group.card_pow_eq_card_pow_card_univ S (Fintype.card G + Fintype.card G) le_add_self]

end PowIsSubgroup

section LinearOrderedSemiring
variable [Semiring G] [LinearOrder G] [IsStrictOrderedRing G] {a : G}

protected lemma IsOfFinOrder.eq_one (ha₀ : 0 ≤ a) (ha : IsOfFinOrder a) : a = 1 := by
  obtain ⟨n, hn, ha⟩ := ha.exists_pow_eq_one
  exact (pow_eq_one_iff_of_nonneg ha₀ hn.ne').1 ha

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring G] [LinearOrder G] [IsStrictOrderedRing G] {a x : G}

protected lemma IsOfFinOrder.eq_neg_one (ha₀ : a ≤ 0) (ha : IsOfFinOrder a) : a = -1 :=
  (sq_eq_one_iff.1 <| ha.pow.eq_one <| sq_nonneg a).resolve_left <| by
    rintro rfl; exact one_pos.not_ge ha₀

theorem orderOf_abs_ne_one (h : |x| ≠ 1) : orderOf x = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hx
  replace hx : |x| ^ n = 1 := by simpa only [abs_one, abs_pow] using congr_arg abs hx
  rcases h.lt_or_gt with h | h
  · exact ((pow_lt_one₀ (abs_nonneg x) h hn.ne').ne hx).elim
  · exact ((one_lt_pow₀ h hn.ne').ne' hx).elim

theorem LinearOrderedRing.orderOf_le_two : orderOf x ≤ 2 := by
  rcases ne_or_eq |x| 1 with h | h
  · simp [orderOf_abs_ne_one h]
  rcases eq_or_eq_neg_of_abs_eq h with (rfl | rfl)
  · simp
  exact orderOf_le_of_pow_eq_one zero_lt_two (by simp)

end LinearOrderedRing

section Prod

variable [Monoid α] [Monoid β] {x : α × β} {a : α} {b : β}

@[to_additive]
protected theorem Prod.orderOf (x : α × β) : orderOf x = (orderOf x.1).lcm (orderOf x.2) :=
  minimalPeriod_prodMap _ _ _

@[to_additive]
theorem orderOf_fst_dvd_orderOf : orderOf x.1 ∣ orderOf x :=
  minimalPeriod_fst_dvd

@[to_additive]
theorem orderOf_snd_dvd_orderOf : orderOf x.2 ∣ orderOf x :=
  minimalPeriod_snd_dvd

@[to_additive]
theorem IsOfFinOrder.fst {x : α × β} (hx : IsOfFinOrder x) : IsOfFinOrder x.1 :=
  hx.mono orderOf_fst_dvd_orderOf

@[to_additive]
theorem IsOfFinOrder.snd {x : α × β} (hx : IsOfFinOrder x) : IsOfFinOrder x.2 :=
  hx.mono orderOf_snd_dvd_orderOf

@[to_additive IsOfFinAddOrder.prod_mk]
theorem IsOfFinOrder.prod_mk : IsOfFinOrder a → IsOfFinOrder b → IsOfFinOrder (a, b) := by
  simpa only [← orderOf_pos_iff, Prod.orderOf] using Nat.lcm_pos

@[to_additive]
lemma Prod.orderOf_mk : orderOf (a, b) = Nat.lcm (orderOf a) (orderOf b) :=
  (a, b).orderOf

end Prod

-- TODO: Corresponding `pi` lemmas. We cannot currently state them here because of import cycles

@[simp]
lemma Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fintype R] : (Fintype.card R : R) = 0 := by
  rw [← nsmul_one, card_nsmul_eq_zero]

section NonAssocRing
variable (R : Type*) [NonAssocRing R] (p : ℕ)

lemma CharP.addOrderOf_one : CharP R (addOrderOf (1 : R)) where
  cast_eq_zero_iff n := by rw [← Nat.smul_one_eq_cast, addOrderOf_dvd_iff_nsmul_eq_zero]

variable [Fintype R]

variable {R} in
lemma charP_of_ne_zero (hn : card R = p) (hR : ∀ i < p, (i : R) = 0 → i = 0) : CharP R p where
  cast_eq_zero_iff n := by
    have H : (p : R) = 0 := by rw [← hn, Nat.cast_card_eq_zero]
    constructor
    · intro h
      rw [← Nat.mod_add_div n p, Nat.cast_add, Nat.cast_mul, H, zero_mul, add_zero] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      apply hR _ (Nat.mod_lt _ _) h
      rw [← hn, Fintype.card_pos_iff]
      exact ⟨0⟩
    · rintro ⟨n, rfl⟩
      rw [Nat.cast_mul, H, zero_mul]

end NonAssocRing

lemma charP_of_prime_pow_injective (R) [Ring R] [Fintype R] (p n : ℕ) [hp : Fact p.Prime]
    (hn : card R = p ^ n) (hR : ∀ i ≤ n, (p : R) ^ i = 0 → i = n) : CharP R (p ^ n) := by
  obtain ⟨c, hc⟩ := CharP.exists R
  have hcpn : c ∣ p ^ n := by rw [← CharP.cast_eq_zero_iff R c, ← hn, Nat.cast_card_eq_zero]
  obtain ⟨i, hi, rfl⟩ : ∃ i ≤ n, c = p ^ i := by rwa [Nat.dvd_prime_pow hp.1] at hcpn
  obtain rfl : i = n := hR i hi <| by rw [← Nat.cast_pow, CharP.cast_eq_zero]
  assumption

namespace SemiconjBy

@[to_additive]
lemma orderOf_eq [Group G] (a : G) {x y : G} (h : SemiconjBy a x y) : orderOf x = orderOf y := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  exact (h.pow_right n).eq_one_iff

end SemiconjBy

section single

lemma orderOf_piMulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [(i : ι) → Monoid (M i)]
    (i : ι) (g : M i) :
    orderOf (Pi.mulSingle i g) = orderOf g :=
  orderOf_injective (MonoidHom.mulSingle M i) (Pi.mulSingle_injective i) g

end single
