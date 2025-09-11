/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notations

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

open Function

variable {G : Type*}

section LinearOrderedCommGroup
variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

@[to_additive] lemma mabs_pow (n : ℕ) (a : G) : |a ^ n|ₘ = |a|ₘ ^ n := by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]

@[to_additive] private lemma mabs_mul_eq_mul_mabs_le (hab : a ≤ b) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ha | ha := le_or_gt 1 a <;> obtain hb | hb := le_or_gt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : G) <| ha.trans_lt <| hab.trans_lt hb).elim
  swap
  · simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b ≤ 1) ↔
    (|a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1) := by
    simp [ha.le, ha.not_ge, hb, mabs_of_le_one, mabs_of_one_le]
  refine this.mp ⟨fun h ↦ ?_, fun h ↦ by simp only [h.antisymm hb, mabs_of_lt_one ha, mul_one]⟩
  obtain ab | ab := le_or_gt (a * b) 1
  · refine (eq_one_of_inv_eq' ?_).le
    rwa [mabs_of_le_one ab, mul_inv_rev, mul_comm, mul_right_inj] at h
  · rw [mabs_of_one_lt ab, mul_left_inj] at h
    rw [eq_one_of_inv_eq' h.symm] at ha
    cases ha.false

@[to_additive] lemma mabs_mul_eq_mul_mabs_iff (a b : G) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab

@[to_additive]
theorem mabs_le : |a|ₘ ≤ b ↔ b⁻¹ ≤ a ∧ a ≤ b := by rw [mabs_le', and_comm, inv_le']

@[to_additive]
theorem le_mabs' : a ≤ |b|ₘ ↔ b ≤ a⁻¹ ∨ a ≤ b := by rw [le_mabs, or_comm, le_inv']

@[to_additive]
theorem inv_le_of_mabs_le (h : |a|ₘ ≤ b) : b⁻¹ ≤ a :=
  (mabs_le.mp h).1

@[to_additive]
theorem le_of_mabs_le (h : |a|ₘ ≤ b) : a ≤ b :=
  (mabs_le.mp h).2

/-- The **triangle inequality** in `LinearOrderedCommGroup`s. -/
@[to_additive /-- The **triangle inequality** in `LinearOrderedAddCommGroup`s. -/]
theorem mabs_mul (a b : G) : |a * b|ₘ ≤ |a|ₘ * |b|ₘ := by
  rw [mabs_le, mul_inv]
  constructor <;> gcongr <;> apply_rules [inv_mabs_le, le_mabs_self]

@[to_additive]
theorem mabs_mul' (a b : G) : |a|ₘ ≤ |b|ₘ * |b * a|ₘ := by simpa using mabs_mul b⁻¹ (b * a)

@[to_additive]
theorem mabs_div (a b : G) : |a / b|ₘ ≤ |a|ₘ * |b|ₘ := by
  rw [div_eq_mul_inv, ← mabs_inv b]
  exact mabs_mul a _

@[to_additive]
theorem mabs_div_le_iff : |a / b|ₘ ≤ c ↔ a / b ≤ c ∧ b / a ≤ c := by
  rw [mabs_le, inv_le_div_iff_le_mul, div_le_iff_le_mul', and_comm, div_le_iff_le_mul']

@[to_additive]
theorem mabs_div_lt_iff : |a / b|ₘ < c ↔ a / b < c ∧ b / a < c := by
  rw [mabs_lt, inv_lt_div_iff_lt_mul', div_lt_iff_lt_mul', and_comm, div_lt_iff_lt_mul']

@[to_additive]
theorem div_le_of_mabs_div_le_left (h : |a / b|ₘ ≤ c) : b / c ≤ a :=
  div_le_comm.1 <| (mabs_div_le_iff.1 h).2

@[to_additive]
theorem div_le_of_mabs_div_le_right (h : |a / b|ₘ ≤ c) : a / c ≤ b :=
  div_le_of_mabs_div_le_left (mabs_div_comm a b ▸ h)

@[to_additive]
theorem div_lt_of_mabs_div_lt_left (h : |a / b|ₘ < c) : b / c < a :=
  div_lt_comm.1 <| (mabs_div_lt_iff.1 h).2

@[to_additive]
theorem div_lt_of_mabs_div_lt_right (h : |a / b|ₘ < c) : a / c < b :=
  div_lt_of_mabs_div_lt_left (mabs_div_comm a b ▸ h)

@[to_additive]
theorem mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / |b|ₘ ≤ |a / b|ₘ :=
  div_le_iff_le_mul.2 <|
    calc
      |a|ₘ = |a / b * b|ₘ := by rw [div_mul_cancel]
      _ ≤ |a / b|ₘ * |b|ₘ := mabs_mul _ _

@[to_additive]
theorem mabs_mabs_div_mabs_le_mabs_div (a b : G) : |(|a|ₘ / |b|ₘ)|ₘ ≤ |a / b|ₘ :=
  mabs_div_le_iff.2
    ⟨mabs_div_mabs_le_mabs_div _ _, by rw [mabs_div_comm]; apply mabs_div_mabs_le_mabs_div⟩

/-- `|a / b|ₘ ≤ n` if `1 ≤ a ≤ n` and `1 ≤ b ≤ n`. -/
@[to_additive /-- `|a - b| ≤ n` if `0 ≤ a ≤ n` and `0 ≤ b ≤ n`. -/]
theorem mabs_div_le_of_one_le_of_le {a b n : G} (one_le_a : 1 ≤ a) (a_le_n : a ≤ n)
    (one_le_b : 1 ≤ b) (b_le_n : b ≤ n) : |a / b|ₘ ≤ n := by
  rw [mabs_div_le_iff, div_le_iff_le_mul, div_le_iff_le_mul]
  exact ⟨le_mul_of_le_of_one_le a_le_n one_le_b, le_mul_of_le_of_one_le b_le_n one_le_a⟩

/-- `|a / b|ₘ < n` if `1 ≤ a < n` and `1 ≤ b < n`. -/
@[to_additive /-- `|a - b| < n` if `0 ≤ a < n` and `0 ≤ b < n`. -/]
theorem mabs_div_lt_of_one_le_of_lt {a b n : G} (one_le_a : 1 ≤ a) (a_lt_n : a < n)
    (one_le_b : 1 ≤ b) (b_lt_n : b < n) : |a / b|ₘ < n := by
  rw [mabs_div_lt_iff, div_lt_iff_lt_mul, div_lt_iff_lt_mul]
  exact ⟨lt_mul_of_lt_of_one_le a_lt_n one_le_b, lt_mul_of_lt_of_one_le b_lt_n one_le_a⟩

@[to_additive]
theorem mabs_eq (hb : 1 ≤ b) : |a|ₘ = b ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨eq_or_eq_inv_of_mabs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [mabs_inv, mabs_of_one_le hb]

@[to_additive]
theorem mabs_le_max_mabs_mabs (hab : a ≤ b) (hbc : b ≤ c) : |b|ₘ ≤ max |a|ₘ |c|ₘ :=
  mabs_le'.2
    ⟨by simp [hbc.trans (le_mabs_self c)], by
      simp [(inv_le_inv_iff.mpr hab).trans (inv_le_mabs a)]⟩

omit [IsOrderedMonoid G] in
@[to_additive]
theorem min_mabs_mabs_le_mabs_max : min |a|ₘ |b|ₘ ≤ |max a b|ₘ :=
  (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
    fun h => (min_le_left _ _).trans_eq <| congr_arg _ (max_eq_left h).symm

omit [IsOrderedMonoid G] in
@[to_additive]
theorem min_mabs_mabs_le_mabs_min : min |a|ₘ |b|ₘ ≤ |min a b|ₘ :=
  (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
    fun h => (min_le_right _ _).trans_eq <| congr_arg _ (min_eq_right h).symm

omit [IsOrderedMonoid G] in
@[to_additive]
theorem mabs_max_le_max_mabs_mabs : |max a b|ₘ ≤ max |a|ₘ |b|ₘ :=
  (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
    fun h => (congr_arg _ <| max_eq_left h).trans_le <| le_max_left _ _

omit [IsOrderedMonoid G] in
@[to_additive]
theorem mabs_min_le_max_mabs_mabs : |min a b|ₘ ≤ max |a|ₘ |b|ₘ :=
  (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
    (congr_arg _ <| min_eq_right h).trans_le <| le_max_right _ _

@[to_additive]
theorem eq_of_mabs_div_eq_one {a b : G} (h : |a / b|ₘ = 1) : a = b :=
  div_eq_one.1 <| mabs_eq_one.1 h

@[to_additive]
theorem mabs_div_le (a b c : G) : |a / c|ₘ ≤ |a / b|ₘ * |b / c|ₘ :=
  calc
    |a / c|ₘ = |a / b * (b / c)|ₘ := by rw [div_mul_div_cancel]
    _ ≤ |a / b|ₘ * |b / c|ₘ := mabs_mul _ _

@[to_additive]
theorem mabs_div_le_max_div {a b c : G} (hac : a ≤ b) (hcd : b ≤ c) (d : G) :
    |b / d|ₘ ≤ max (c / d) (d / a) := by
  rcases le_total d b with h | h
  · rw [mabs_of_one_le <| one_le_div'.mpr h]
    exact le_max_of_le_left <| div_le_div_right' hcd _
  · rw [mabs_of_le_one <| div_le_one'.mpr h, inv_div]
    exact le_max_of_le_right <| div_le_div_left' hac _

@[to_additive]
theorem mabs_mul_three (a b c : G) : |a * b * c|ₘ ≤ |a|ₘ * |b|ₘ * |c|ₘ :=
  (mabs_mul _ _).trans (mul_le_mul_right' (mabs_mul _ _) _)

@[to_additive]
theorem mabs_div_le_of_le_of_le {a b lb ub : G} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b)
    (hbu : b ≤ ub) : |a / b|ₘ ≤ ub / lb :=
  mabs_div_le_iff.2 ⟨div_le_div'' hau hbl, div_le_div'' hbu hal⟩

@[deprecated (since := "2025-03-02")]
alias dist_bdd_within_interval := abs_sub_le_of_le_of_le

@[to_additive]
theorem eq_of_mabs_div_le_one (h : |a / b|ₘ ≤ 1) : a = b :=
  eq_of_mabs_div_eq_one (le_antisymm h (one_le_mabs (a / b)))

@[to_additive]
lemma eq_of_mabs_div_lt_all {x y : G} (h : ∀ ε > 1, |x / y|ₘ < ε) : x = y :=
  eq_of_mabs_div_le_one <| le_of_forall_gt h

@[to_additive]
lemma eq_of_mabs_div_le_all [DenselyOrdered G] {x y : G} (h : ∀ ε > 1, |x / y|ₘ ≤ ε) : x = y :=
  eq_of_mabs_div_le_one <| forall_gt_imp_ge_iff_le_of_dense.mp h

@[to_additive]
theorem mabs_div_le_one : |a / b|ₘ ≤ 1 ↔ a = b :=
  ⟨eq_of_mabs_div_le_one, by rintro rfl; rw [div_self', mabs_one]⟩

@[to_additive]
theorem mabs_div_pos : 1 < |a / b|ₘ ↔ a ≠ b :=
  not_le.symm.trans mabs_div_le_one.not

@[to_additive (attr := simp)]
theorem mabs_eq_self : |a|ₘ = a ↔ 1 ≤ a := by
  rw [mabs_eq_max_inv, max_eq_left_iff, inv_le_self_iff]

@[to_additive (attr := simp)]
theorem mabs_eq_inv_self : |a|ₘ = a⁻¹ ↔ a ≤ 1 := by
  rw [mabs_eq_max_inv, max_eq_right_iff, le_inv_self_iff]

/-- For an element `a` of a multiplicative linear ordered group,
either `|a|ₘ = a` and `1 ≤ a`, or `|a|ₘ = a⁻¹` and `a < 1`. -/
@[to_additive
  /-- For an element `a` of an additive linear ordered group,
  either `|a| = a` and `0 ≤ a`, or `|a| = -a` and `a < 0`.
  Use cases on this lemma to automate linarith in inequalities -/]
theorem mabs_cases (a : G) : |a|ₘ = a ∧ 1 ≤ a ∨ |a|ₘ = a⁻¹ ∧ a < 1 := by
  cases le_or_gt 1 a <;> simp [*, le_of_lt]

@[to_additive (attr := simp)]
theorem max_one_mul_max_inv_one_eq_mabs_self (a : G) : max a 1 * max a⁻¹ 1 = |a|ₘ := by
  symm
  rcases le_total 1 a with (ha | ha) <;> simp [ha]

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {a b c : G}

@[to_additive]
theorem apply_abs_le_mul_of_one_le' {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G → H}
    {a : G} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) : f |a| ≤ f a * f (-a) :=
  (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

@[to_additive]
theorem apply_abs_le_mul_of_one_le {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G → H}
    (h : ∀ x, 1 ≤ f x) (a : G) : f |a| ≤ f a * f (-a) :=
  apply_abs_le_mul_of_one_le' (h _) (h _)

end LinearOrderedAddCommGroup
