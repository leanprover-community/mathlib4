/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Rat.Floor
import Mathlib.Data.NNRat.Defs

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

assert_not_exists Finset

open Int Set

variable {α : Type*}

/-- An ordered additive commutative monoid is called `Archimedean` if for any two elements `x`, `y`
such that `0 < y`, there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (α) [OrderedAddCommMonoid α] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : α) {y : α}, 0 < y → ∃ n : ℕ, x ≤ n • y

section MulArchimedean

/-- An ordered commutative monoid is called `MulArchimedean` if for any two elements `x`, `y`
such that `1 < y`, there exists a natural number `n` such that `x ≤ y ^ n`. -/
@[to_additive Archimedean]
class MulArchimedean (α) [OrderedCommMonoid α] : Prop where
  /-- For any two elements `x`, `y` such that `1 < y`, there exists a natural number `n`
  such that `x ≤ y ^ n`. -/
  arch : ∀ (x : α) {y : α}, 1 < y → ∃ n : ℕ, x ≤ y ^ n

end MulArchimedean

@[to_additive]
instance OrderDual.instMulArchimedean [OrderedCommGroup α] [MulArchimedean α] :
    MulArchimedean αᵒᵈ :=
  ⟨fun x y hy =>
    let ⟨n, hn⟩ := MulArchimedean.arch (ofDual x)⁻¹ (inv_lt_one_iff_one_lt.2 hy)
    ⟨n, by rwa [inv_pow, inv_le_inv_iff] at hn⟩⟩

instance Additive.instArchimedean [OrderedCommGroup α] [MulArchimedean α] :
    Archimedean (Additive α) :=
  ⟨fun x _ hy ↦ MulArchimedean.arch x.toMul hy⟩

instance Multiplicative.instMulArchimedean [OrderedAddCommGroup α] [Archimedean α] :
    MulArchimedean (Multiplicative α) :=
  ⟨fun x _ hy ↦ Archimedean.arch x.toAdd hy⟩

variable {M : Type*}

@[to_additive]
theorem exists_lt_pow [OrderedCommMonoid M] [MulArchimedean M]
    [MulLeftStrictMono M] {a : M} (ha : 1 < a) (b : M) :
    ∃ n : ℕ, b < a ^ n :=
  let ⟨k, hk⟩ := MulArchimedean.arch b ha
  ⟨k + 1, hk.trans_lt <| pow_lt_pow_right' ha k.lt_succ_self⟩

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] [MulArchimedean α]

/-- An archimedean decidable linearly ordered `CommGroup` has a version of the floor: for
`a > 1`, any `g` in the group lies between some two consecutive powers of `a`. -/
@[to_additive "An archimedean decidable linearly ordered `AddCommGroup` has a version of the floor:
for `a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/"]
theorem existsUnique_zpow_near_of_one_lt {a : α} (ha : 1 < a) (g : α) :
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
theorem existsUnique_zpow_near_of_one_lt' {a : α} (ha : 1 < a) (g : α) :
    ∃! k : ℤ, 1 ≤ g / a ^ k ∧ g / a ^ k < a := by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

@[to_additive]
theorem existsUnique_div_zpow_mem_Ico {a : α} (ha : 1 < a) (b c : α) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ico c (c * a) := by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
theorem existsUnique_mul_zpow_mem_Ico {a : α} (ha : 1 < a) (b c : α) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ico c (c * a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, mem_Ico, zpow_neg, ← div_eq_mul_inv, le_div_iff_mul_le, one_mul,
      mul_comm c, div_lt_iff_lt_mul, mul_assoc] using existsUnique_zpow_near_of_one_lt' ha (b / c)

@[to_additive]
theorem existsUnique_add_zpow_mem_Ioc {a : α} (ha : 1 < a) (b c : α) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ioc c (c * a) :=
  (Equiv.addRight (1 : ℤ)).bijective.existsUnique_iff.2 <| by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

@[to_additive]
theorem existsUnique_sub_zpow_mem_Ioc {a : α} (ha : 1 < a) (b c : α) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ioc c (c * a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

end LinearOrderedCommGroup

theorem exists_nat_ge [OrderedSemiring α] [Archimedean α] (x : α) : ∃ n : ℕ, x ≤ n := by
  nontriviality α
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

instance (priority := 100) [OrderedSemiring α] [Archimedean α] : IsDirected α (· ≤ ·) :=
  ⟨fun x y ↦
    let ⟨m, hm⟩ := exists_nat_ge x; let ⟨n, hn⟩ := exists_nat_ge y
    let ⟨k, hmk, hnk⟩ := exists_ge_ge m n
    ⟨k, hm.trans <| Nat.mono_cast hmk, hn.trans <| Nat.mono_cast hnk⟩⟩

section StrictOrderedSemiring
variable [StrictOrderedSemiring α] [Archimedean α] {y : α}

lemma exists_nat_gt (x : α) : ∃ n : ℕ, x < n :=
  (exists_lt_nsmul zero_lt_one x).imp fun n hn ↦ by rwa [← nsmul_one]

theorem add_one_pow_unbounded_of_pos (x : α) (hy : 0 < y) : ∃ n : ℕ, x < (y + 1) ^ n :=
  have : 0 ≤ 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h ↦
    calc
      x ≤ n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ ≤ (1 + y) ^ n :=
        one_add_mul_le_pow' (mul_nonneg hy.le hy.le) (mul_nonneg this this)
          (add_nonneg zero_le_two hy.le) _
      _ = (y + 1) ^ n := by rw [add_comm]

lemma pow_unbounded_of_one_lt [ExistsAddOfLE α] (x : α) (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n := by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

end StrictOrderedSemiring

section OrderedRing

variable {R : Type*} [OrderedRing R] [Archimedean R]

theorem exists_int_ge (x : R) : ∃ n : ℤ, x ≤ n := let ⟨n, h⟩ := exists_nat_ge x; ⟨n, mod_cast h⟩

theorem exists_int_le (x : R) : ∃ n : ℤ, n ≤ x :=
  let ⟨n, h⟩ := exists_int_ge (-x); ⟨-n, by simpa [neg_le] using h⟩

instance (priority := 100) : IsDirected R (· ≥ ·) where
  directed a b :=
    let ⟨m, hm⟩ := exists_int_le a; let ⟨n, hn⟩ := exists_int_le b
    ⟨(min m n : ℤ), le_trans (Int.cast_mono <| min_le_left _ _) hm,
      le_trans (Int.cast_mono <| min_le_right _ _) hn⟩

end OrderedRing

section StrictOrderedRing
variable [StrictOrderedRing α] [Archimedean α]

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_natCast]⟩

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
  let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩

theorem exists_floor (x : α) : ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : α) ≤ x := by
  haveI := Classical.propDecidable
  have : ∃ ub : ℤ, (ub : α) ≤ x ∧ ∀ z : ℤ, (z : α) ≤ x → z ≤ ub :=
    Int.exists_greatest_of_bdd
      (let ⟨n, hn⟩ := exists_int_gt x
      ⟨n, fun z h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
      (let ⟨n, hn⟩ := exists_int_lt x
      ⟨n, le_of_lt hn⟩)
  refine this.imp fun fl h z => ?_
  cases' h with h₁ h₂
  exact ⟨fun h => le_trans (Int.cast_le.2 h) h₁, h₂ z⟩

end StrictOrderedRing

section LinearOrderedSemiring
variable [LinearOrderedSemiring α] [Archimedean α] [ExistsAddOfLE α] {x y : α}

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
      ⟨Nat.pred n, le_of_not_lt (Nat.find_min h hltn), by rwa [hnsp]⟩

end LinearOrderedSemiring

section LinearOrderedSemifield
variable [LinearOrderedSemifield α] [Archimedean α] {x y ε : α}

lemma exists_nat_one_div_lt (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : α) < ε := by
  cases' exists_nat_gt (1 / ε) with n hn
  use n
  rw [div_lt_iff₀, ← div_lt_iff₀' hε]
  · apply hn.trans
    simp [zero_lt_one]
  · exact n.cast_add_one_pos

variable [ExistsAddOfLE α]

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ioc_zpow`,
but with ≤ and < the other way around. -/
theorem exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  classical exact
      let ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
      have he : ∃ m : ℤ, y ^ m ≤ x :=
        ⟨-N,
          le_of_lt
            (by
              rw [zpow_neg y ↑N, zpow_natCast]
              exact (inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN)⟩
      let ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy
      have hb : ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b :=
        ⟨M, fun m hm =>
          le_of_not_lt fun hlt =>
            not_lt_of_ge (zpow_le_zpow_right₀ hy.le hlt.le)
              (lt_of_le_of_lt hm (by rwa [← zpow_natCast] at hM))⟩
      let ⟨n, hn₁, hn₂⟩ := Int.exists_greatest_of_bdd hb he
      ⟨n, hn₁, lt_of_not_ge fun hge => not_le_of_gt (Int.lt_succ _) (hn₂ _ hge)⟩

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
  by_cases y_pos : y ≤ 0
  · use 1
    simp only [pow_one]
    exact y_pos.trans_lt hx
  rw [not_le] at y_pos
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

end LinearOrderedSemifield

section LinearOrderedField
variable [LinearOrderedField α] [Archimedean α] {x y ε : α}

theorem exists_rat_gt (x : α) : ∃ q : ℚ, x < q :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Rat.cast_natCast]⟩

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
  let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_intCast]⟩

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q : α) < y := by
  cases' exists_nat_gt (y - x)⁻¹ with n nh
  cases' exists_floor (x * n) with z zh
  refine ⟨(z + 1 : ℤ) / n, ?_⟩
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  have n0 := Nat.cast_pos.1 n0'
  rw [Rat.cast_div_of_ne_zero, Rat.cast_natCast, Rat.cast_intCast, div_lt_iff₀ n0']
  · refine ⟨(lt_div_iff₀ n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), ?_⟩
    rw [Int.cast_add, Int.cast_one]
    refine lt_of_le_of_lt (add_le_add_right ((zh _).1 le_rfl) _) ?_
    rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff₀' (sub_pos.2 h), one_div]
  · rw [Rat.den_intCast, Nat.cast_one]
    exact one_ne_zero
  · intro H
    rw [Rat.num_natCast, Int.cast_natCast, Nat.cast_eq_zero] at H
    subst H
    cases n0

theorem Rat.one_add_pow_le {r : ℚ} {n : ℕ} (hr : 0 ≤ r) :
    (1 + r) ^ n ≤ (2 ^ n - 1) * max 1 r ^ (n - 1) + r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set m := max 1 r with hm
    simp only [add_tsub_cancel_right] at ih ⊢
    calc (1 + r) ^ (n + 1)
        = (1 + r) ^ n * (1 + r) := by rw [pow_succ]
      _ ≤ ((2 ^ n - 1) * m ^ (n - 1) + r ^ n) * (1 + r) :=
          mul_le_mul_of_nonneg_right ih (add_nonneg zero_le_one hr)
      _ = ((2 ^ n - 1) * m ^ (n - 1)) * (1 + r) + r ^ n + r ^ (n + 1) := by ring
      _ ≤ _ := ?_
    apply add_le_add_right
    have h₁ : 1 + r ≤ 2 * m := by
      rw [two_mul, hm]
      apply add_le_add <;> simp only [le_sup_left, le_sup_right]
    have h₂ : r ^ n ≤ m ^ n := pow_le_pow_left₀ hr le_sup_right n
    calc (2 ^ n - 1) * m ^ (n - 1) * (1 + r) + r ^ n
        ≤ (2 ^ n - 1) * m ^ (n - 1) * (2 * m) + m ^ n := by
          apply add_le_add _ h₂
          apply mul_le_mul_of_nonneg_left h₁
          apply mul_nonneg _ (pow_nonneg (by simp [hm]) _)
          apply sub_nonneg.mpr (one_le_pow₀ rfl)
      _ = _ := ?_
    cases n with
    | zero => simp; ring
    | succ n => simp only [add_tsub_cancel_right]; ring

theorem exists_rat_pow_btwn_rat {n : ℕ} (hn : n ≠ 0) {x y : ℚ} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < q ^ n ∧ q ^ n < y := by
  wlog hx : 0 ≤ x generalizing x
  · have ⟨q, q_pos, qn_pos, lt_y⟩ := this hy le_rfl
    exact ⟨q, q_pos, (le_of_not_le hx).trans_lt qn_pos, lt_y⟩
  have yx_pos := sub_pos.mpr h
  obtain rfl | hn1 := (Nat.one_le_iff_ne_zero.mpr hn).eq_or_lt
  · exact ⟨(x + y) / 2, by positivity, by linarith, by linarith⟩
  let d := (2 ^ n * max 1 y) / (y - x)
  have h1d : 1 < d := (one_lt_div yx_pos).mpr <| ((sub_le_self _ hx).trans le_sup_right).trans_lt
    (lt_mul_of_one_lt_left (by positivity) <| one_lt_pow₀ one_lt_two hn)
  have d_pos : 0 < d := zero_lt_one.trans h1d
  have ex : ∃ m : ℕ, y ≤ (m / d) ^ n := by
    refine ⟨⌈y * d + d⌉₊, le_trans ?_ (le_self_pow₀ ?_ hn)⟩
    · rw [le_div_iff₀ d_pos]
      exact ((lt_add_of_pos_right _ d_pos).le.trans <| Nat.le_ceil _)
    · rw [le_div_iff₀ d_pos, one_mul]
      exact (le_add_of_nonneg_left <| by positivity).trans (Nat.le_ceil _)
  let num := Nat.find ex
  have num_pos : 0 < num := (Nat.find_pos _).mpr <| by simpa [zero_pow hn] using hy
  let q := num.pred / d
  have qny : q ^ n < y := lt_of_not_le (Nat.find_min ex <| Nat.pred_lt num_pos.ne')
  have key : max 1 ↑num.pred ^ (n - 1) / d ^ n < max 1 y / d := by
    conv in (d ^ _) => rw [← Nat.sub_one_add_one hn, pow_add, pow_one]
    rw [← div_div, ← div_pow, div_lt_div_iff_of_pos_right d_pos, lt_max_iff, or_iff_not_imp_left,
      not_lt, one_le_pow_iff_of_nonneg (by positivity) (Nat.sub_pos_of_lt hn1).ne']
    refine fun h ↦ (pow_le_pow_right₀ h <| n.sub_le 1).trans_lt ?_
    have : (1 : ℚ) ≤ num.pred := Nat.cast_le.mpr <| Nat.one_le_iff_ne_zero.mpr fun eq ↦ by
      rw [← max_div_div_right d_pos.le, le_max_iff, or_iff_not_imp_left, not_le, one_div,
        inv_lt_one₀ d_pos, eq, Nat.cast_zero, zero_div] at h
      exact zero_lt_one.not_le (h h1d)
    rwa [max_eq_right this]
  have aux : (1 + (num.pred : ℚ)) ^ n ≤ num.pred ^ n + 2 ^ n * (max 1 ↑num.pred) ^ (n - 1) := by
    apply (Rat.one_add_pow_le <| Nat.cast_nonneg' num.pred).trans
    rw [add_comm, sub_mul, one_mul]
    apply add_le_add_left <| sub_le_self _ <| pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have xqn : x < q ^ n :=
    calc x = y - (y - x) := (sub_sub_cancel _ _).symm
      _ ≤ (num / d) ^ n - 2 ^ n * max 1 y / d :=
        sub_le_sub (Nat.find_spec ex) (div_div_cancel₀ <| by positivity).le
      _ = (1 + num.pred) ^ n / d ^ n - _ := by rw [← Nat.cast_one, ← Nat.cast_add,
        Nat.cast_one, ← Nat.succ_eq_one_add, Nat.succ_pred num_pos.ne', div_pow]
      _ ≤ num.pred ^ n / d ^ n + 2 ^ n * (max 1 ↑num.pred ^ (n - 1) / d ^ n - max 1 y / d) :=
        (sub_le_sub_right (div_le_div_of_nonneg_right aux <| by positivity) _).trans <| by
          simp_rw [add_div, mul_sub, add_sub, mul_div, le_rfl]
      _ = q ^ n + _ := by rw [← div_pow]
      _ < q ^ n := add_lt_of_neg_right _ (mul_neg_of_pos_of_neg (by positivity) <| sub_neg.mpr key)
  refine ⟨q, lt_of_le_of_ne (by positivity) fun hq ↦ hx.not_lt ?_, xqn, qny⟩
  rwa [← hq, zero_pow hn] at xqn

/-- There is a rational power between any two positive elements of an archimedean ordered field. -/
theorem exists_rat_pow_btwn {n : ℕ} (hn : n ≠ 0) {x y : α} (h : x < y) (hy : 0 < y) :
    ∃ q : ℚ, 0 < q ∧ x < (q : α) ^ n ∧ (q : α) ^ n < y := by
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy)
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂
  norm_cast at hq₁₂ this
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_pow_btwn_rat hn hq₁₂ this
  refine ⟨q, hq, (le_max_left _ _).trans_lt <| hx₁.trans ?_, hy₂.trans' ?_⟩ <;> assumption_mod_cast

theorem le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : α) < x → (q : α) ≤ y) : x ≤ y :=
  le_of_not_lt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hy.not_le <| h _ hx

theorem le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
  le_of_not_lt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hx.not_le <| h _ hy

theorem le_iff_forall_rat_lt_imp_le : x ≤ y ↔ ∀ q : ℚ, (q : α) < x → (q : α) ≤ y :=
  ⟨fun hxy _ hqx ↦ hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

theorem le_iff_forall_lt_rat_imp_le : x ≤ y ↔ ∀ q : ℚ, y < q → x ≤ q :=
  ⟨fun hxy _ hqx ↦ hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

theorem eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : α) < x ↔ (q : α) < y) : x = y :=
  (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm <|
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le

theorem eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
  (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm <|
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0

theorem exists_rat_near (x : α) (ε0 : 0 < ε) : ∃ q : ℚ, |x - q| < ε :=
  let ⟨q, h₁, h₂⟩ :=
    exists_rat_btwn <| ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩

end LinearOrderedField

section LinearOrderedField

variable [LinearOrderedField α]

theorem archimedean_iff_nat_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
  ⟨@exists_nat_gt α _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff₀ y0, ← nsmul_eq_mul] at h⟩⟩

theorem archimedean_iff_nat_le : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩

theorem archimedean_iff_int_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℤ, x < n :=
  ⟨@exists_int_gt α _, by
    rw [archimedean_iff_nat_lt]
    intro h x
    obtain ⟨n, h⟩ := h x
    refine ⟨n.toNat, h.trans_le ?_⟩
    exact mod_cast Int.self_le_toNat _⟩

theorem archimedean_iff_int_le : Archimedean α ↔ ∀ x : α, ∃ n : ℤ, x ≤ n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

theorem archimedean_iff_rat_lt : Archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q where
  mp := @exists_rat_gt α _
  mpr H := archimedean_iff_nat_lt.2 fun x ↦
    let ⟨q, h⟩ := H x; ⟨⌈q⌉₊, lt_of_lt_of_le h <| mod_cast Nat.le_ceil _⟩

theorem archimedean_iff_rat_le : Archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩

end LinearOrderedField

instance : Archimedean ℕ :=
  ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n, smul_eq_mul, mul_assoc, one_mul m]
    exact Nat.mul_le_mul_left n (by omega)⟩⟩

instance : Archimedean ℤ :=
  ⟨fun n m m0 =>
    ⟨n.toNat,
      le_trans (Int.self_le_toNat _) <| by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.ofNat_zero_le n.toNat)⟩⟩

instance : Archimedean ℚ :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩

instance Nonneg.instArchimedean [OrderedAddCommMonoid α] [Archimedean α] :
    Archimedean { x : α // 0 ≤ x } :=
  ⟨fun x y hy =>
    let ⟨n, hr⟩ := Archimedean.arch (x : α) (hy : (0 : α) < y)
    ⟨n, show (x : α) ≤ (n • y : { x : α // 0 ≤ x }) by simp [*, -nsmul_eq_mul, nsmul_coe]⟩⟩

instance Nonneg.instMulArchimedean [StrictOrderedCommSemiring α] [Archimedean α] [ExistsAddOfLE α] :
    MulArchimedean { x : α // 0 ≤ x } :=
  ⟨fun x _ hy ↦ (pow_unbounded_of_one_lt x hy).imp fun _ h ↦ h.le⟩

instance : Archimedean NNRat := Nonneg.instArchimedean
instance : MulArchimedean NNRat := Nonneg.instMulArchimedean

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
noncomputable def Archimedean.floorRing (α) [LinearOrderedRing α] [Archimedean α] : FloorRing α :=
  FloorRing.ofFloor α (fun a => Classical.choose (exists_floor a)) fun z a =>
    (Classical.choose_spec (exists_floor a) z).symm

-- see Note [lower instance priority]
/-- A linear ordered field that is a floor ring is archimedean. -/
instance (priority := 100) FloorRing.archimedean (α) [LinearOrderedField α] [FloorRing α] :
    Archimedean α := by
  rw [archimedean_iff_int_le]
  exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩

@[to_additive]
instance Units.instMulArchimedean (α) [OrderedCommMonoid α] [MulArchimedean α] :
    MulArchimedean αˣ :=
  ⟨fun x {_} h ↦ MulArchimedean.arch x.val h⟩
