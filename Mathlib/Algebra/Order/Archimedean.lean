/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Field.Power

#align_import algebra.order.archimedean from "leanprover-community/mathlib"@"6f413f3f7330b94c92a5a27488fdc74e6d483a78"

/-!
# Archimedean groups and fields.

This file defines the archimedean property for ordered groups and proves several results connected
to this notion. Being archimedean means that for all elements `x` and `y>0` there exists a natural
number `n` such that `x ≤ n • y`.

## Main definitions

* `Archimedean` is a typeclass for an ordered additive commutative monoid to have the archimedean
  property.
* `Archimedean.floorRing` defines a floor function on an archimedean linearly ordered ring making
  it into a `floorRing`.

## Main statements

* `ℕ`, `ℤ`, and `ℚ` are archimedean.
-/

set_option autoImplicit true

open Int Set

variable {α : Type*}

/-- An ordered additive commutative monoid is called `Archimedean` if for any two elements `x`, `y`
such that `0 < y`, there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (α) [OrderedAddCommMonoid α] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : α) {y : α}, 0 < y → ∃ n : ℕ, x ≤ n • y
#align archimedean Archimedean

instance OrderDual.archimedean [OrderedAddCommGroup α] [Archimedean α] : Archimedean αᵒᵈ :=
  ⟨fun x y hy =>
    let ⟨n, hn⟩ := Archimedean.arch (-ofDual x) (neg_pos.2 hy)
    ⟨n, by rwa [neg_nsmul, neg_le_neg_iff] at hn⟩⟩
           -- 🎉 no goals
#align order_dual.archimedean OrderDual.archimedean

theorem exists_lt_nsmul [OrderedAddCommMonoid M] [Archimedean M]
    [CovariantClass M M (· + ·) (· < ·)] {a : M} (ha : 0 < a) (b : M) :
    ∃ n : ℕ, b < n • a :=
  let ⟨k, hk⟩ := Archimedean.arch b ha; ⟨k + 1, hk.trans_lt <| nsmul_lt_nsmul ha k.lt_succ_self⟩

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] [Archimedean α]

/-- An archimedean decidable linearly ordered `AddCommGroup` has a version of the floor: for
`a > 0`, any `g` in the group lies between some two consecutive multiples of `a`. -/
theorem existsUnique_zsmul_near_of_pos {a : α} (ha : 0 < a) (g : α) :
    ∃! k : ℤ, k • a ≤ g ∧ g < (k + 1) • a := by
  let s : Set ℤ := { n : ℤ | n • a ≤ g }
  -- ⊢ ∃! k, k • a ≤ g ∧ g < (k + 1) • a
  obtain ⟨k, hk : -g ≤ k • a⟩ := Archimedean.arch (-g) ha
  -- ⊢ ∃! k, k • a ≤ g ∧ g < (k + 1) • a
  have h_ne : s.Nonempty := ⟨-k, by simpa using neg_le_neg hk⟩
  -- ⊢ ∃! k, k • a ≤ g ∧ g < (k + 1) • a
  obtain ⟨k, hk⟩ := Archimedean.arch g ha
  -- ⊢ ∃! k, k • a ≤ g ∧ g < (k + 1) • a
  have h_bdd : ∀ n ∈ s, n ≤ (k : ℤ) := by
    intro n hn
    apply (zsmul_le_zsmul_iff ha).mp
    rw [← coe_nat_zsmul] at hk
    exact le_trans hn hk
  obtain ⟨m, hm, hm'⟩ := Int.exists_greatest_of_bdd ⟨k, h_bdd⟩ h_ne
  -- ⊢ ∃! k, k • a ≤ g ∧ g < (k + 1) • a
  have hm'' : g < (m + 1) • a := by
    contrapose! hm'
    exact ⟨m + 1, hm', lt_add_one _⟩
  refine' ⟨m, ⟨hm, hm''⟩, fun n hn => (hm' n hn.1).antisymm <| Int.le_of_lt_add_one _⟩
  -- ⊢ m < n + 1
  rw [← zsmul_lt_zsmul_iff ha]
  -- ⊢ m • a < (n + 1) • a
  exact lt_of_le_of_lt hm hn.2
  -- 🎉 no goals
#align exists_unique_zsmul_near_of_pos existsUnique_zsmul_near_of_pos

theorem existsUnique_zsmul_near_of_pos' {a : α} (ha : 0 < a) (g : α) :
    ∃! k : ℤ, 0 ≤ g - k • a ∧ g - k • a < a := by
  simpa only [sub_nonneg, add_zsmul, one_zsmul, sub_lt_iff_lt_add'] using
    existsUnique_zsmul_near_of_pos ha g
#align exists_unique_zsmul_near_of_pos' existsUnique_zsmul_near_of_pos'

theorem existsUnique_sub_zsmul_mem_Ico {a : α} (ha : 0 < a) (b c : α) :
    ∃! m : ℤ, b - m • a ∈ Set.Ico c (c + a) := by
  simpa only [mem_Ico, le_sub_iff_add_le, zero_add, add_comm c, sub_lt_iff_lt_add', add_assoc] using
    existsUnique_zsmul_near_of_pos' ha (b - c)
#align exists_unique_sub_zsmul_mem_Ico existsUnique_sub_zsmul_mem_Ico

theorem existsUnique_add_zsmul_mem_Ico {a : α} (ha : 0 < a) (b c : α) :
    ∃! m : ℤ, b + m • a ∈ Set.Ico c (c + a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, mem_Ico, neg_zsmul, ← sub_eq_add_neg, le_sub_iff_add_le, zero_add,
      add_comm c, sub_lt_iff_lt_add', add_assoc] using existsUnique_zsmul_near_of_pos' ha (b - c)
#align exists_unique_add_zsmul_mem_Ico existsUnique_add_zsmul_mem_Ico

theorem existsUnique_add_zsmul_mem_Ioc {a : α} (ha : 0 < a) (b c : α) :
    ∃! m : ℤ, b + m • a ∈ Set.Ioc c (c + a) :=
  (Equiv.addRight (1 : ℤ)).bijective.existsUnique_iff.2 <| by
    simpa only [add_zsmul, sub_lt_iff_lt_add', le_sub_iff_add_le', ← add_assoc, and_comm, mem_Ioc,
      Equiv.coe_addRight, one_zsmul, add_le_add_iff_right] using
      existsUnique_zsmul_near_of_pos ha (c - b)
#align exists_unique_add_zsmul_mem_Ioc existsUnique_add_zsmul_mem_Ioc

theorem existsUnique_sub_zsmul_mem_Ioc {a : α} (ha : 0 < a) (b c : α) :
    ∃! m : ℤ, b - m • a ∈ Set.Ioc c (c + a) :=
  (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, neg_zsmul, sub_neg_eq_add] using
      existsUnique_add_zsmul_mem_Ioc ha b c
#align exists_unique_sub_zsmul_mem_Ioc existsUnique_sub_zsmul_mem_Ioc

end LinearOrderedAddCommGroup

theorem exists_nat_gt [StrictOrderedSemiring α] [Archimedean α] (x : α) : ∃ n : ℕ, x < n :=
  (exists_lt_nsmul zero_lt_one x).imp fun n hn ↦ by rwa [← nsmul_one]
                                                    -- 🎉 no goals
#align exists_nat_gt exists_nat_gt

theorem exists_nat_ge [OrderedSemiring α] [Archimedean α] (x : α) : ∃ n : ℕ, x ≤ n := by
  nontriviality α
  -- ⊢ ∃ n, x ≤ ↑n
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]
  -- 🎉 no goals
#align exists_nat_ge exists_nat_ge

theorem add_one_pow_unbounded_of_pos [StrictOrderedSemiring α] [Archimedean α] (x : α) {y : α}
    (hy : 0 < y) : ∃ n : ℕ, x < (y + 1) ^ n :=
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
                            -- 🎉 no goals
#align add_one_pow_unbounded_of_pos add_one_pow_unbounded_of_pos

section StrictOrderedRing

variable [StrictOrderedRing α] [Archimedean α]

theorem pow_unbounded_of_one_lt (x : α) {y : α} (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n :=
  sub_add_cancel y 1 ▸ add_one_pow_unbounded_of_pos _ (sub_pos.2 hy1)
#align pow_unbounded_of_one_lt pow_unbounded_of_one_lt

theorem exists_int_gt (x : α) : ∃ n : ℤ, x < n :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Int.cast_ofNat]⟩
         -- 🎉 no goals
#align exists_int_gt exists_int_gt

theorem exists_int_lt (x : α) : ∃ n : ℤ, (n : α) < x :=
  let ⟨n, h⟩ := exists_int_gt (-x)
  ⟨-n, by rw [Int.cast_neg]; exact neg_lt.1 h⟩
          -- ⊢ -↑n < x
                             -- 🎉 no goals
#align exists_int_lt exists_int_lt

theorem exists_floor (x : α) : ∃ fl : ℤ, ∀ z : ℤ, z ≤ fl ↔ (z : α) ≤ x := by
  haveI := Classical.propDecidable
  -- ⊢ ∃ fl, ∀ (z : ℤ), z ≤ fl ↔ ↑z ≤ x
  have : ∃ ub : ℤ, (ub : α) ≤ x ∧ ∀ z : ℤ, (z : α) ≤ x → z ≤ ub :=
    Int.exists_greatest_of_bdd
      (let ⟨n, hn⟩ := exists_int_gt x
      ⟨n, fun z h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
      (let ⟨n, hn⟩ := exists_int_lt x
      ⟨n, le_of_lt hn⟩)
  refine' this.imp fun fl h z => _
  -- ⊢ z ≤ fl ↔ ↑z ≤ x
  cases' h with h₁ h₂
  -- ⊢ z ≤ fl ↔ ↑z ≤ x
  exact ⟨fun h => le_trans (Int.cast_le.2 h) h₁, h₂ z⟩
  -- 🎉 no goals
#align exists_floor exists_floor

end StrictOrderedRing

section LinearOrderedRing

variable [LinearOrderedRing α] [Archimedean α]

/-- Every x greater than or equal to 1 is between two successive
natural-number powers of every y greater than one. -/
theorem exists_nat_pow_near {x : α} {y : α} (hx : 1 ≤ x) (hy : 1 < y) :
    ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt _ hy
  -- ⊢ ∃ n, y ^ n ≤ x ∧ x < y ^ (n + 1)
  classical exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
      have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
      ⟨Nat.pred n, le_of_not_lt (Nat.find_min h hltn), by rwa [hnsp]⟩
#align exists_nat_pow_near exists_nat_pow_near

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField α] [Archimedean α] {x y ε : α}

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
              rw [zpow_neg y ↑N, zpow_ofNat]
              exact (inv_lt hx (lt_trans (inv_pos.2 hx) hN)).1 hN)⟩
      let ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy
      have hb : ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b :=
        ⟨M, fun m hm =>
          le_of_not_lt fun hlt =>
            not_lt_of_ge (zpow_le_of_le hy.le hlt.le)
              (lt_of_le_of_lt hm (by rwa [← zpow_ofNat] at hM))⟩
      let ⟨n, hn₁, hn₂⟩ := Int.exists_greatest_of_bdd hb he
      ⟨n, hn₁, lt_of_not_ge fun hge => not_le_of_gt (Int.lt_succ _) (hn₂ _ hge)⟩
#align exists_mem_Ico_zpow exists_mem_Ico_zpow

/-- Every positive `x` is between two successive integer powers of
another `y` greater than one. This is the same as `exists_mem_Ico_zpow`,
but with ≤ and < the other way around. -/
theorem exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) :=
  let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt (zpow_pos_of_pos hyp _) hx], by
                -- 🎉 no goals
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv hx (zpow_pos_of_pos hyp _)]⟩
    -- 🎉 no goals
#align exists_mem_Ioc_zpow exists_mem_Ioc_zpow

/-- For any `y < 1` and any positive `x`, there exists `n : ℕ` with `y ^ n < x`. -/
theorem exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 1) : ∃ n : ℕ, y ^ n < x := by
  by_cases y_pos : y ≤ 0
  -- ⊢ ∃ n, y ^ n < x
  · use 1
    -- ⊢ y ^ 1 < x
    simp only [pow_one]
    -- ⊢ y < x
    linarith
    -- 🎉 no goals
  rw [not_le] at y_pos
  -- ⊢ ∃ n, y ^ n < x
  rcases pow_unbounded_of_one_lt x⁻¹ (one_lt_inv y_pos hy) with ⟨q, hq⟩
  -- ⊢ ∃ n, y ^ n < x
  exact ⟨q, by rwa [inv_pow, inv_lt_inv hx (pow_pos y_pos _)] at hq⟩
  -- 🎉 no goals
#align exists_pow_lt_of_lt_one exists_pow_lt_of_lt_one

/-- Given `x` and `y` between `0` and `1`, `x` is between two successive powers of `y`.
This is the same as `exists_nat_pow_near`, but for elements between `0` and `1` -/
theorem exists_nat_pow_near_of_lt_one (xpos : 0 < x) (hx : x ≤ 1) (ypos : 0 < y) (hy : y < 1) :
    ∃ n : ℕ, y ^ (n + 1) < x ∧ x ≤ y ^ n := by
  rcases exists_nat_pow_near (one_le_inv_iff.2 ⟨xpos, hx⟩) (one_lt_inv_iff.2 ⟨ypos, hy⟩) with
    ⟨n, hn, h'n⟩
  refine' ⟨n, _, _⟩
  -- ⊢ y ^ (n + 1) < x
  · rwa [inv_pow, inv_lt_inv xpos (pow_pos ypos _)] at h'n
    -- 🎉 no goals
  · rwa [inv_pow, inv_le_inv (pow_pos ypos _) xpos] at hn
    -- 🎉 no goals
#align exists_nat_pow_near_of_lt_one exists_nat_pow_near_of_lt_one

theorem exists_rat_gt (x : α) : ∃ q : ℚ, x < q :=
  let ⟨n, h⟩ := exists_nat_gt x
  ⟨n, by rwa [Rat.cast_coe_nat]⟩
         -- 🎉 no goals
#align exists_rat_gt exists_rat_gt

theorem exists_rat_lt (x : α) : ∃ q : ℚ, (q : α) < x :=
  let ⟨n, h⟩ := exists_int_lt x
  ⟨n, by rwa [Rat.cast_coe_int]⟩
         -- 🎉 no goals
#align exists_rat_lt exists_rat_lt

theorem exists_rat_btwn {x y : α} (h : x < y) : ∃ q : ℚ, x < q ∧ (q : α) < y := by
  cases' exists_nat_gt (y - x)⁻¹ with n nh
  -- ⊢ ∃ q, x < ↑q ∧ ↑q < y
  cases' exists_floor (x * n) with z zh
  -- ⊢ ∃ q, x < ↑q ∧ ↑q < y
  refine' ⟨(z + 1 : ℤ) / n, _⟩
  -- ⊢ x < ↑(↑(z + 1) / ↑n) ∧ ↑(↑(z + 1) / ↑n) < y
  have n0' := (inv_pos.2 (sub_pos.2 h)).trans nh
  -- ⊢ x < ↑(↑(z + 1) / ↑n) ∧ ↑(↑(z + 1) / ↑n) < y
  have n0 := Nat.cast_pos.1 n0'
  -- ⊢ x < ↑(↑(z + 1) / ↑n) ∧ ↑(↑(z + 1) / ↑n) < y
  rw [Rat.cast_div_of_ne_zero, Rat.cast_coe_nat, Rat.cast_coe_int, div_lt_iff n0']
  refine' ⟨(lt_div_iff n0').2 <| (lt_iff_lt_of_le_iff_le (zh _)).1 (lt_add_one _), _⟩
  rw [Int.cast_add, Int.cast_one]
  refine' lt_of_le_of_lt (add_le_add_right ((zh _).1 le_rfl) _) _
  rwa [← lt_sub_iff_add_lt', ← sub_mul, ← div_lt_iff' (sub_pos.2 h), one_div]
  · rw [Rat.coe_int_den, Nat.cast_one]
    -- ⊢ 1 ≠ 0
    exact one_ne_zero
    -- 🎉 no goals
  · intro H
    -- ⊢ False
    rw [Rat.coe_nat_num, Int.cast_ofNat, Nat.cast_eq_zero] at H
    -- ⊢ False
    subst H
    -- ⊢ False
    cases n0
    -- 🎉 no goals
  · rw [Rat.coe_nat_den, Nat.cast_one]
    -- ⊢ 1 ≠ 0
    exact one_ne_zero
    -- 🎉 no goals
#align exists_rat_btwn exists_rat_btwn

theorem le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : α) < x → (q : α) ≤ y) : x ≤ y :=
  le_of_not_lt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hy.not_le <| h _ hx
#align le_of_forall_rat_lt_imp_le le_of_forall_rat_lt_imp_le

theorem le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
  le_of_not_lt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hx.not_le <| h _ hy
#align le_of_forall_lt_rat_imp_le le_of_forall_lt_rat_imp_le

theorem le_iff_forall_rat_lt_imp_le : x ≤ y ↔ ∀ q : ℚ, (q : α) < x → (q : α) ≤ y :=
  ⟨fun hxy _ hqx ↦ hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

theorem le_iff_forall_lt_rat_imp_le : x ≤ y ↔ ∀ q : ℚ, y < q → x ≤ q :=
  ⟨fun hxy _ hqx ↦ hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

theorem eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : α) < x ↔ (q : α) < y) : x = y :=
  (le_of_forall_rat_lt_imp_le fun q hq => ((h q).1 hq).le).antisymm <|
    le_of_forall_rat_lt_imp_le fun q hq => ((h q).2 hq).le
#align eq_of_forall_rat_lt_iff_lt eq_of_forall_rat_lt_iff_lt

theorem eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
  (le_of_forall_lt_rat_imp_le fun q hq => ((h q).2 hq).le).antisymm <|
    le_of_forall_lt_rat_imp_le fun q hq => ((h q).1 hq).le
#align eq_of_forall_lt_rat_iff_lt eq_of_forall_lt_rat_iff_lt

theorem exists_nat_one_div_lt {ε : α} (hε : 0 < ε) : ∃ n : ℕ, 1 / (n + 1 : α) < ε := by
  cases' exists_nat_gt (1 / ε) with n hn
  -- ⊢ ∃ n, 1 / (↑n + 1) < ε
  use n
  -- ⊢ 1 / (↑n + 1) < ε
  rw [div_lt_iff, ← div_lt_iff' hε]
  -- ⊢ 1 / ε < ↑n + 1
  · apply hn.trans
    -- ⊢ ↑n < ↑n + 1
    simp [zero_lt_one]
    -- 🎉 no goals
  · exact n.cast_add_one_pos
    -- 🎉 no goals
#align exists_nat_one_div_lt exists_nat_one_div_lt

theorem exists_pos_rat_lt {x : α} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : α) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0
  -- 🎉 no goals
#align exists_pos_rat_lt exists_pos_rat_lt

theorem exists_rat_near (x : α) (ε0 : 0 < ε) : ∃ q : ℚ, |x - q| < ε :=
  let ⟨q, h₁, h₂⟩ :=
    exists_rat_btwn <| ((sub_lt_self_iff x).2 ε0).trans ((lt_add_iff_pos_left x).2 ε0)
  ⟨q, abs_sub_lt_iff.2 ⟨sub_lt_comm.1 h₁, sub_lt_iff_lt_add.2 h₂⟩⟩
#align exists_rat_near exists_rat_near

end LinearOrderedField

section LinearOrderedField

variable [LinearOrderedField α]

theorem archimedean_iff_nat_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n :=
  ⟨@exists_nat_gt α _, fun H =>
    ⟨fun x y y0 =>
      (H (x / y)).imp fun n h => le_of_lt <| by rwa [div_lt_iff y0, ← nsmul_eq_mul] at h⟩⟩
                                                -- 🎉 no goals
#align archimedean_iff_nat_lt archimedean_iff_nat_lt

theorem archimedean_iff_nat_le : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n :=
  archimedean_iff_nat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Nat.cast_lt.2 (lt_add_one _))⟩⟩
#align archimedean_iff_nat_le archimedean_iff_nat_le

theorem archimedean_iff_int_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℤ, x < n :=
  ⟨@exists_int_gt α _, by
    rw [archimedean_iff_nat_lt]
    -- ⊢ (∀ (x : α), ∃ n, x < ↑n) → ∀ (x : α), ∃ n, x < ↑n
    intro h x
    -- ⊢ ∃ n, x < ↑n
    obtain ⟨n, h⟩ := h x
    -- ⊢ ∃ n, x < ↑n
    refine' ⟨n.toNat, h.trans_le _⟩
    -- ⊢ ↑n ≤ ↑(toNat n)
    exact_mod_cast Int.self_le_toNat _⟩
    -- 🎉 no goals
#align archimedean_iff_int_lt archimedean_iff_int_lt

theorem archimedean_iff_int_le : Archimedean α ↔ ∀ x : α, ∃ n : ℤ, x ≤ n :=
  archimedean_iff_int_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩
#align archimedean_iff_int_le archimedean_iff_int_le

theorem archimedean_iff_rat_lt : Archimedean α ↔ ∀ x : α, ∃ q : ℚ, x < q :=
  ⟨@exists_rat_gt α _, fun H =>
    archimedean_iff_nat_lt.2 fun x =>
      let ⟨q, h⟩ := H x
      ⟨⌈q⌉₊,
        lt_of_lt_of_le h <| by
          simpa only [Rat.cast_coe_nat] using (@Rat.cast_le α _ _ _).2 (Nat.le_ceil _)⟩⟩
          -- 🎉 no goals
#align archimedean_iff_rat_lt archimedean_iff_rat_lt

theorem archimedean_iff_rat_le : Archimedean α ↔ ∀ x : α, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩
#align archimedean_iff_rat_le archimedean_iff_rat_le

end LinearOrderedField

instance : Archimedean ℕ :=
  ⟨fun n m m0 => ⟨n, by
    rw [← mul_one n, smul_eq_mul, mul_assoc, one_mul m]
    -- ⊢ n * 1 ≤ n * m
    exact Nat.mul_le_mul_left n (by linarith)⟩⟩
    -- 🎉 no goals

instance : Archimedean ℤ :=
  ⟨fun n m m0 =>
    ⟨n.toNat,
      le_trans (Int.self_le_toNat _) <| by
        simpa only [nsmul_eq_mul, zero_add, mul_one] using
          mul_le_mul_of_nonneg_left (Int.add_one_le_iff.2 m0) (Int.ofNat_zero_le n.toNat)⟩⟩

instance : Archimedean ℚ :=
  archimedean_iff_rat_le.2 fun q => ⟨q, by rw [Rat.cast_id]⟩
                                           -- 🎉 no goals

/-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
cases we have a computable `floor` function. -/
noncomputable def Archimedean.floorRing (α) [LinearOrderedRing α] [Archimedean α] : FloorRing α :=
  FloorRing.ofFloor α (fun a => Classical.choose (exists_floor a)) fun z a =>
    (Classical.choose_spec (exists_floor a) z).symm
#align archimedean.floor_ring Archimedean.floorRing

-- see Note [lower instance priority]
/-- A linear ordered field that is a floor ring is archimedean. -/
instance (priority := 100) FloorRing.archimedean (α) [LinearOrderedField α] [FloorRing α] :
    Archimedean α := by
  rw [archimedean_iff_int_le]
  -- ⊢ ∀ (x : α), ∃ n, x ≤ ↑n
  exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩
  -- 🎉 no goals
#align floor_ring.archimedean FloorRing.archimedean
