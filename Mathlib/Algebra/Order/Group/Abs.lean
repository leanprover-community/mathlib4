/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Order.Group.Lattice
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

#align_import algebra.order.group.abs from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notations

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section Group
variable [Group α] {a b : α}

#noalign has_inv.to_has_abs
#noalign has_neg.to_has_abs

/-- `mabs a` is the absolute value of `a`. -/
@[to_additive "`abs a` is the absolute value of `a`"] def mabs (a : α) : α := a ⊔ a⁻¹
#align has_abs.abs abs

#align abs_eq_sup_inv mabs
#align abs_eq_sup_neg abs

@[inherit_doc mabs]
macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(mabs $a)

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

/-- Unexpander for the notation `|a|ₘ` for `mabs a`.
Tries to add discretionary parentheses in unparseable cases. -/
@[app_unexpander abs]
def mabs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|ₘ) | `(-$_) => `(|($a)|ₘ)
    | _ => `(|$a|ₘ)
  | _ => throw ()

/-- Unexpander for the notation `|a|` for `abs a`.
Tries to add discretionary parentheses in unparseable cases. -/
@[app_unexpander abs]
def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[to_additive] lemma mabs_le' : |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b := sup_le_iff
#align abs_le' abs_le'

@[to_additive] lemma le_mabs_self (a : α) : a ≤ |a|ₘ := le_sup_left
#align le_abs_self le_abs_self
#align lattice_ordered_comm_group.le_mabs le_mabs_self
#align lattice_ordered_comm_group.le_abs le_abs_self

@[to_additive] lemma inv_le_mabs (a : α) : a⁻¹ ≤ |a|ₘ := le_sup_right
#align neg_le_abs_self neg_le_abs
#align lattice_ordered_comm_group.inv_le_abs inv_le_mabs
#align lattice_ordered_comm_group.neg_le_abs neg_le_abs

@[to_additive] lemma mabs_le_mabs (h₀ : a ≤ b) (h₁ : a⁻¹ ≤ b) : |a|ₘ ≤ |b|ₘ :=
  (mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)
#align abs_le_abs abs_le_abs

@[to_additive (attr := simp)] lemma mabs_inv (a : α) : |a⁻¹|ₘ = |a|ₘ := by simp [mabs, sup_comm]
#align abs_neg abs_neg

@[to_additive] lemma mabs_div_comm (a b : α) : |a / b|ₘ = |b / a|ₘ := by rw [← mabs_inv, inv_div]
#align abs_sub_comm abs_sub_comm

variable [CovariantClass α α (· * ·) (· ≤ ·)]

@[to_additive] lemma mabs_of_one_le (h : 1 ≤ a) : |a|ₘ = a :=
  sup_eq_left.2 <| (inv_le_one'.2 h).trans h
#align abs_of_nonneg abs_of_nonneg
#align lattice_ordered_comm_group.mabs_of_one_le mabs_of_one_le
#align lattice_ordered_comm_group.abs_of_nonneg abs_of_nonneg

@[to_additive] lemma mabs_of_one_lt (h : 1 < a) : |a|ₘ = a := mabs_of_one_le h.le
#align abs_of_pos abs_of_pos

@[to_additive] lemma mabs_of_le_one (h : a ≤ 1) : |a|ₘ = a⁻¹ :=
  sup_eq_right.2 <| h.trans (one_le_inv'.2 h)
#align abs_of_nonpos abs_of_nonpos

@[to_additive] lemma mabs_of_lt_one (h : a < 1) : |a|ₘ = a⁻¹ := mabs_of_le_one h.le
#align abs_of_neg abs_of_neg

@[to_additive] lemma mabs_le_mabs_of_one_le (ha : 1 ≤ a) (hab : a ≤ b) : |a|ₘ ≤ |b|ₘ := by
  rwa [mabs_of_one_le ha, mabs_of_one_le (ha.trans hab)]
#align abs_le_abs_of_nonneg abs_le_abs_of_nonneg

attribute [gcongr] abs_le_abs_of_nonneg

@[to_additive (attr := simp)] lemma mabs_one : |(1 : α)|ₘ = 1 := mabs_of_one_le le_rfl
#align abs_zero abs_zero

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)]

@[to_additive (attr := simp) abs_nonneg] lemma one_le_mabs (a : α) : 1 ≤ |a|ₘ := by
  apply pow_two_semiclosed _
  rw [mabs, pow_two, mul_sup,  sup_mul, ← pow_two, mul_left_inv, sup_comm, ← sup_assoc]
  apply le_sup_right
#align abs_nonneg abs_nonneg

@[to_additive (attr := simp)] lemma mabs_mabs (a : α) : |(|a|ₘ)|ₘ = |a|ₘ :=
  mabs_of_one_le <| one_le_mabs a
#align abs_abs abs_abs
#align lattice_ordered_comm_group.mabs_mabs mabs_mabs
#align lattice_ordered_comm_group.abs_abs abs_abs

end Group

section CommGroup
variable [CommGroup α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/-- The absolute value satisfies the triangle inequality. -/
@[to_additive "The absolute value satisfies the triangle inequality."]
lemma mabs_mul_le (a b : α) : |a * b|ₘ ≤ |a|ₘ * |b|ₘ := by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)
#align lattice_ordered_comm_group.mabs_mul_le mabs_mul_le
#align lattice_ordered_comm_group.abs_add_le abs_add_le

@[to_additive]
lemma mabs_mabs_div_mabs_le (a b : α) : |(|a|ₘ / |b|ₘ)|ₘ ≤ |a / b|ₘ := by
  rw [mabs, sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert mabs_mul_le (a / b) b
    rw [div_mul_cancel]
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, mabs_div_comm]
    convert mabs_mul_le (b / a) a
    · rw [div_mul_cancel]
#align lattice_ordered_comm_group.abs_abs_div_abs_le mabs_mabs_div_mabs_le
#align lattice_ordered_comm_group.abs_abs_sub_abs_le abs_abs_sub_abs_le

@[to_additive] lemma sup_div_inf_eq_mabs_div (a b : α) : (a ⊔ b) / (a ⊓ b) = |b / a|ₘ := by
  simp_rw [sup_div, div_inf, div_self', sup_comm, sup_sup_sup_comm, sup_idem]
  rw [← inv_div, sup_comm (b := _ / _), ← mabs, sup_eq_left]
  exact one_le_mabs _
#align lattice_ordered_comm_group.sup_div_inf_eq_abs_div sup_div_inf_eq_mabs_div
#align lattice_ordered_comm_group.sup_sub_inf_eq_abs_sub sup_sub_inf_eq_abs_sub

@[to_additive two_nsmul_sup_eq_add_add_abs_sub]
lemma sup_sq_eq_mul_mul_mabs_div (a b : α) : (a ⊔ b) ^ 2 = a * b * |b / a|ₘ := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_mabs_div, div_eq_mul_inv, ← mul_assoc, mul_comm,
     mul_assoc, ← pow_two, inv_mul_cancel_left]
#align lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div sup_sq_eq_mul_mul_mabs_div
#align lattice_ordered_comm_group.two_sup_eq_add_add_abs_sub two_nsmul_sup_eq_add_add_abs_sub

@[to_additive two_nsmul_inf_eq_add_sub_abs_sub]
lemma inf_sq_eq_mul_div_mabs_div (a b : α) : (a ⊓ b) ^ 2 = a * b / |b / a|ₘ := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_mabs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev,
    inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]
#align lattice_ordered_comm_group.inf_sq_eq_mul_div_abs_div inf_sq_eq_mul_div_mabs_div
#align lattice_ordered_comm_group.two_inf_eq_add_sub_abs_sub two_nsmul_inf_eq_add_sub_abs_sub

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
@[to_additive]
lemma mabs_div_sup_mul_mabs_div_inf (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ = |a / b|ₘ := by
  letI : DistribLattice α := CommGroup.toDistribLattice α
  calc
    |(a ⊔ c) / (b ⊔ c)|ₘ * |(a ⊓ c) / (b ⊓ c)|ₘ =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)|ₘ := by
        rw [sup_div_inf_eq_mabs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / (b ⊓ c ⊓ (a ⊓ c))) := by
        rw [sup_div_inf_eq_mabs_div (b ⊓ c) (a ⊓ c)]
    _ = (b ⊔ a ⊔ c) / (b ⊓ a ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) := by
        rw [← sup_inf_right, ← inf_sup_right, sup_assoc, sup_comm c (a ⊔ c), sup_right_idem,
          sup_assoc, inf_assoc, inf_comm c (a ⊓ c), inf_right_idem, inf_assoc]
    _ = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) / ((b ⊓ a ⊔ c) * (b ⊓ a ⊓ c)) := by rw [div_mul_div_comm]
    _ = (b ⊔ a) * c / ((b ⊓ a) * c) := by
        rw [mul_comm, inf_mul_sup, mul_comm (b ⊓ a ⊔ c), inf_mul_sup]
    _ = (b ⊔ a) / (b ⊓ a) := by
        rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← div_eq_mul_inv]
    _ = |a / b|ₘ := by rw [sup_div_inf_eq_mabs_div]
#align lattice_ordered_comm_group.abs_div_sup_mul_abs_div_inf mabs_div_sup_mul_mabs_div_inf
#align lattice_ordered_comm_group.abs_sub_sup_add_abs_sub_inf abs_sub_sup_add_abs_sub_inf

@[to_additive] lemma mabs_sup_div_sup_le_mabs (a b c : α) : |(a ⊔ c) / (b ⊔ c)|ₘ ≤ |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_left _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]
#align lattice_ordered_comm_group.mabs_sup_div_sup_le_mabs mabs_sup_div_sup_le_mabs
#align lattice_ordered_comm_group.abs_sup_sub_sup_le_abs abs_sup_sub_sup_le_abs

@[to_additive] lemma mabs_inf_div_inf_le_mabs (a b c : α) : |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_right _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]
#align lattice_ordered_comm_group.mabs_inf_div_inf_le_mabs mabs_inf_div_inf_le_mabs
#align lattice_ordered_comm_group.abs_inf_sub_inf_le_abs abs_inf_sub_inf_le_abs

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
@[to_additive Birkhoff_inequalities]
lemma m_Birkhoff_inequalities (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ ⊔ |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)
set_option linter.uppercaseLean3 false in
#align lattice_ordered_comm_group.m_Birkhoff_inequalities m_Birkhoff_inequalities
set_option linter.uppercaseLean3 false in
#align lattice_ordered_comm_group.Birkhoff_inequalities Birkhoff_inequalities

end CommGroup
end Lattice

section LinearOrder
variable [Group α] [LinearOrder α] {a b : α}

@[to_additive] lemma mabs_choice (x : α) : |x|ₘ = x ∨ |x|ₘ = x⁻¹ := max_choice _ _
#align abs_choice abs_choice

@[to_additive] lemma le_mabs : a ≤ |b|ₘ ↔ a ≤ b ∨ a ≤ b⁻¹ := le_max_iff
#align le_abs le_abs

@[to_additive] lemma mabs_eq_max_inv : |a|ₘ = max a a⁻¹ := rfl
#align abs_eq_max_neg abs_eq_max_neg

@[to_additive] lemma lt_mabs : a < |b|ₘ ↔ a < b ∨ a < b⁻¹ := lt_max_iff
#align lt_abs lt_abs

@[to_additive] lemma mabs_by_cases (P : α → Prop) (h1 : P a) (h2 : P a⁻¹) : P |a|ₘ :=
  sup_ind _ _ h1 h2
#align abs_by_cases abs_by_cases

@[to_additive] lemma eq_or_eq_inv_of_mabs_eq (h : |a|ₘ = b) : a = b ∨ a = b⁻¹ := by
  simpa only [← h, eq_comm (a := |a|ₘ), inv_eq_iff_eq_inv] using mabs_choice a
#align eq_or_eq_neg_of_abs_eq eq_or_eq_neg_of_abs_eq

@[to_additive] lemma mabs_eq_mabs : |a|ₘ = |b|ₘ ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨fun h ↦ ?_, by rintro (h | h) <;> simp [h, abs_neg]⟩
  obtain rfl | rfl := eq_or_eq_inv_of_mabs_eq h <;>
    simpa only [inv_eq_iff_eq_inv (a := |b|ₘ), inv_inv, inv_inj, or_comm] using mabs_choice b
#align abs_eq_abs abs_eq_abs

@[to_additive] lemma isSquare_mabs : IsSquare |a|ₘ ↔ IsSquare a :=
  mabs_by_cases (IsSquare · ↔ _) Iff.rfl isSquare_inv
#align even_abs even_abs

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α}

@[to_additive (attr := simp) abs_pos] lemma one_lt_mabs : 1 < |a|ₘ ↔ a ≠ 1 := by
  obtain ha | rfl | ha := lt_trichotomy a 1
  · simp [mabs_of_lt_one ha, neg_pos, ha.ne, ha]
  · simp
  · simp [mabs_of_one_lt ha, ha, ha.ne']
#align abs_pos abs_pos

@[to_additive abs_pos_of_pos] lemma one_lt_mabs_pos_of_one_lt (h : 1 < a) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne'
#align abs_pos_of_pos abs_pos_of_pos

@[to_additive abs_pos_of_neg] lemma one_lt_mabs_of_lt_one (h : a < 1) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne
#align abs_pos_of_neg abs_pos_of_neg

@[to_additive] lemma inv_mabs_le (a : α) : |a|ₘ⁻¹ ≤ a := by
  obtain h | h := le_total 1 a
  · simpa [mabs_of_one_le h] using (inv_le_one'.2 h).trans h
  · simp [mabs_of_le_one h]
#align neg_abs_le_self neg_abs_le

@[to_additive add_abs_nonneg] lemma one_le_mul_mabs (a : α) : 1 ≤ a * |a|ₘ := by
  rw [← mul_right_inv a]; exact mul_le_mul_left' (inv_le_mabs a) _
#align add_abs_nonneg add_abs_nonneg

@[to_additive] lemma inv_mabs_le_inv (a : α) : |a|ₘ⁻¹ ≤ a⁻¹ := by simpa using inv_mabs_le a⁻¹
#align neg_abs_le_neg neg_abs_le_neg

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)]

@[to_additive] lemma mabs_ne_one : |a|ₘ ≠ 1 ↔ a ≠ 1 :=
  (one_le_mabs a).gt_iff_ne.symm.trans one_lt_mabs

@[to_additive (attr := simp)] lemma mabs_eq_one : |a|ₘ = 1 ↔ a = 1 := not_iff_not.1 mabs_ne_one
#align abs_eq_zero abs_eq_zero

@[to_additive (attr := simp) abs_nonpos_iff] lemma mabs_le_one : |a|ₘ ≤ 1 ↔ a = 1 :=
  (one_le_mabs a).le_iff_eq.trans mabs_eq_one
#align abs_nonpos_iff abs_nonpos_iff

@[to_additive] lemma mabs_le_mabs_of_le_one (ha : a ≤ 1) (hab : b ≤ a) : |a|ₘ ≤ |b|ₘ := by
  rw [mabs_of_le_one ha, mabs_of_le_one (hab.trans ha)]; exact inv_le_inv_iff.mpr hab
#align abs_le_abs_of_nonpos abs_le_abs_of_nonpos

@[to_additive] lemma mabs_lt : |a|ₘ < b ↔ b⁻¹ < a ∧ a < b :=
  max_lt_iff.trans <| and_comm.trans <| by rw [inv_lt']
#align abs_lt abs_lt

@[to_additive] lemma inv_lt_of_mabs_lt (h : |a|ₘ < b) : b⁻¹ < a := (mabs_lt.mp h).1
#align neg_lt_of_abs_lt neg_lt_of_abs_lt

@[to_additive] lemma lt_of_mabs_lt : |a|ₘ < b → a < b := (le_mabs_self _).trans_lt
#align lt_of_abs_lt lt_of_abs_lt

@[to_additive] lemma max_div_min_eq_mabs' (a b : α) : max a b / min a b = |a / b|ₘ := by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, mabs_of_le_one, inv_div]
    rwa [div_le_one']
  · rw [max_eq_left ba, min_eq_right ba, mabs_of_one_le]
    rwa [one_le_div']
#align max_sub_min_eq_abs' max_sub_min_eq_abs'

@[to_additive] lemma max_div_min_eq_mabs (a b : α) : max a b / min a b = |b / a|ₘ := by
  rw [mabs_div_comm, max_div_min_eq_mabs']
#align max_sub_min_eq_abs max_sub_min_eq_abs

end LinearOrder

section LinearOrderedCommGroup
variable [LinearOrderedCommGroup α] {a b : α}

@[to_additive] lemma mabs_pow (n : ℕ) (a : α) : |a ^ n|ₘ = |a|ₘ ^ n := by
  obtain ha | ha := le_total a 1
  · rw [mabs_of_le_one ha, ← mabs_inv, ← inv_pow, mabs_of_one_le]
    exact one_le_pow_of_one_le' (one_le_inv'.2 ha) n
  · rw [mabs_of_one_le ha, mabs_of_one_le (one_le_pow_of_one_le' ha n)]
#align abs_nsmul abs_nsmul

@[to_additive] private lemma mabs_mul_eq_mul_mabs_le (hab : a ≤ b) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ha | ha := le_or_lt 1 a <;> obtain hb | hb := le_or_lt 1 b
  · simp [ha, hb, mabs_of_one_le, one_le_mul ha hb]
  · exact (lt_irrefl (1 : α) <| ha.trans_lt <| hab.trans_lt hb).elim
  any_goals simp [ha.le, hb.le, mabs_of_le_one, mul_le_one', mul_comm]
  have : (|a * b|ₘ = a⁻¹ * b ↔ b ≤ 1) ↔
    (|a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1) := by
    simp [ha.le, ha.not_le, hb, mabs_of_le_one, mabs_of_one_le]
  refine this.mp ⟨fun h ↦ ?_, fun h ↦ by simp only [h.antisymm hb, mabs_of_lt_one ha, mul_one]⟩
  obtain ab | ab := le_or_lt (a * b) 1
  · refine (eq_one_of_inv_eq' ?_).le
    rwa [mabs_of_le_one ab, mul_inv_rev, mul_comm, mul_right_inj] at h
  · rw [mabs_of_one_lt ab, mul_left_inj] at h
    rw [eq_one_of_inv_eq' h.symm] at ha
    cases ha.false
#noalign abs_add_eq_add_abs_le

@[to_additive] lemma mabs_mul_eq_mul_mabs_iff (a b : α) :
    |a * b|ₘ = |a|ₘ * |b|ₘ ↔ 1 ≤ a ∧ 1 ≤ b ∨ a ≤ 1 ∧ b ≤ 1 := by
  obtain ab | ab := le_total a b
  · exact mabs_mul_eq_mul_mabs_le ab
  · simpa only [mul_comm, and_comm] using mabs_mul_eq_mul_mabs_le ab
#align abs_add_eq_add_abs_iff abs_add_eq_add_abs_iff

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

-- Porting note:
-- Lean can perfectly well find this instance,
-- but in the rewrites below it is going looking for it without having fixed `α`.
example : CovariantClass α α (swap fun x y ↦ x + y) fun x y ↦ x ≤ y := inferInstance

theorem abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b := by rw [abs_le', and_comm, @neg_le α]
#align abs_le abs_le

theorem le_abs' : a ≤ |b| ↔ b ≤ -a ∨ a ≤ b := by rw [le_abs, or_comm, @le_neg α]
#align le_abs' le_abs'

theorem neg_le_of_abs_le (h : |a| ≤ b) : -b ≤ a :=
  (abs_le.mp h).1
#align neg_le_of_abs_le neg_le_of_abs_le

theorem le_of_abs_le (h : |a| ≤ b) : a ≤ b :=
  (abs_le.mp h).2
#align le_of_abs_le le_of_abs_le

@[to_additive]
theorem apply_abs_le_mul_of_one_le' {β : Type*} [MulOneClass β] [Preorder β]
    [CovariantClass β β (· * ·) (· ≤ ·)] [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {f : α → β}
    {a : α} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) : f |a| ≤ f a * f (-a) :=
  (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂
#align apply_abs_le_mul_of_one_le' apply_abs_le_mul_of_one_le'
#align apply_abs_le_add_of_nonneg' apply_abs_le_add_of_nonneg'

@[to_additive]
theorem apply_abs_le_mul_of_one_le {β : Type*} [MulOneClass β] [Preorder β]
    [CovariantClass β β (· * ·) (· ≤ ·)] [CovariantClass β β (swap (· * ·)) (· ≤ ·)] {f : α → β}
    (h : ∀ x, 1 ≤ f x) (a : α) : f |a| ≤ f a * f (-a) :=
  apply_abs_le_mul_of_one_le' (h _) (h _)
#align apply_abs_le_mul_of_one_le apply_abs_le_mul_of_one_le
#align apply_abs_le_add_of_nonneg apply_abs_le_add_of_nonneg

/-- The **triangle inequality** in `LinearOrderedAddCommGroup`s. -/
theorem abs_add (a b : α) : |a + b| ≤ |a| + |b| :=
  abs_le.2
    ⟨(neg_add |a| |b|).symm ▸
        add_le_add ((@neg_le α ..).2 <| neg_le_abs _) ((@neg_le α ..).2 <| neg_le_abs _),
      add_le_add (le_abs_self _) (le_abs_self _)⟩
#align abs_add abs_add

theorem abs_add' (a b : α) : |a| ≤ |b| + |b + a| := by simpa using abs_add (-b) (b + a)
#align abs_add' abs_add'

theorem abs_sub (a b : α) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add a _
#align abs_sub abs_sub

theorem abs_sub_le_iff : |a - b| ≤ c ↔ a - b ≤ c ∧ b - a ≤ c := by
  rw [abs_le, neg_le_sub_iff_le_add, sub_le_iff_le_add', and_comm, sub_le_iff_le_add']
#align abs_sub_le_iff abs_sub_le_iff

theorem abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c := by
  rw [@abs_lt α, neg_lt_sub_iff_lt_add', sub_lt_iff_lt_add', and_comm, sub_lt_iff_lt_add']
#align abs_sub_lt_iff abs_sub_lt_iff

theorem sub_le_of_abs_sub_le_left (h : |a - b| ≤ c) : b - c ≤ a :=
  sub_le_comm.1 <| (abs_sub_le_iff.1 h).2
#align sub_le_of_abs_sub_le_left sub_le_of_abs_sub_le_left

theorem sub_le_of_abs_sub_le_right (h : |a - b| ≤ c) : a - c ≤ b :=
  sub_le_of_abs_sub_le_left (abs_sub_comm a b ▸ h)
#align sub_le_of_abs_sub_le_right sub_le_of_abs_sub_le_right

theorem sub_lt_of_abs_sub_lt_left (h : |a - b| < c) : b - c < a :=
  sub_lt_comm.1 <| (abs_sub_lt_iff.1 h).2
#align sub_lt_of_abs_sub_lt_left sub_lt_of_abs_sub_lt_left

theorem sub_lt_of_abs_sub_lt_right (h : |a - b| < c) : a - c < b :=
  sub_lt_of_abs_sub_lt_left (abs_sub_comm a b ▸ h)
#align sub_lt_of_abs_sub_lt_right sub_lt_of_abs_sub_lt_right

theorem abs_sub_abs_le_abs_sub (a b : α) : |a| - |b| ≤ |a - b| :=
  (@sub_le_iff_le_add α ..).2 <|
    calc
      |a| = |a - b + b| := by rw [sub_add_cancel]
      _ ≤ |a - b| + |b| := abs_add _ _
#align abs_sub_abs_le_abs_sub abs_sub_abs_le_abs_sub

theorem abs_abs_sub_abs_le_abs_sub (a b : α) : |(|a| - |b|)| ≤ |a - b| :=
  abs_sub_le_iff.2
    ⟨abs_sub_abs_le_abs_sub _ _, by rw [abs_sub_comm]; apply abs_sub_abs_le_abs_sub⟩
#align abs_abs_sub_abs_le_abs_sub abs_abs_sub_abs_le_abs_sub

/-- `|a - b| ≤ n` if `0 ≤ a ≤ n` and `0 ≤ b ≤ n`. -/
theorem abs_sub_le_of_nonneg_of_le {a b n : α} (a_nonneg : 0 ≤ a) (a_le_n : a ≤ n)
    (b_nonneg : 0 ≤ b) (b_le_n : b ≤ n) : |a - b| ≤ n := by
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
  exact ⟨le_add_of_le_of_nonneg a_le_n b_nonneg, le_add_of_le_of_nonneg b_le_n a_nonneg⟩

/-- `|a - b| < n` if `0 ≤ a < n` and `0 ≤ b < n`. -/
theorem abs_sub_lt_of_nonneg_of_lt {a b n : α} (a_nonneg : 0 ≤ a) (a_lt_n : a < n)
    (b_nonneg : 0 ≤ b) (b_lt_n : b < n) : |a - b| < n := by
  rw [abs_sub_lt_iff, sub_lt_iff_lt_add, sub_lt_iff_lt_add]
  exact ⟨lt_add_of_lt_of_nonneg a_lt_n b_nonneg, lt_add_of_lt_of_nonneg b_lt_n a_nonneg⟩

theorem abs_eq (hb : 0 ≤ b) : |a| = b ↔ a = b ∨ a = -b := by
  refine ⟨eq_or_eq_neg_of_abs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [abs_neg, abs_of_nonneg hb]
#align abs_eq abs_eq

theorem abs_le_max_abs_abs (hab : a ≤ b) (hbc : b ≤ c) : |b| ≤ max |a| |c| :=
  abs_le'.2
    ⟨by simp [hbc.trans (le_abs_self c)], by
      simp [((@neg_le_neg_iff α ..).mpr hab).trans (neg_le_abs a)]⟩
#align abs_le_max_abs_abs abs_le_max_abs_abs

theorem min_abs_abs_le_abs_max : min |a| |b| ≤ |max a b| :=
  (le_total a b).elim (fun h => (min_le_right _ _).trans_eq <| congr_arg _ (max_eq_right h).symm)
    fun h => (min_le_left _ _).trans_eq <| congr_arg _ (max_eq_left h).symm
#align min_abs_abs_le_abs_max min_abs_abs_le_abs_max

theorem min_abs_abs_le_abs_min : min |a| |b| ≤ |min a b| :=
  (le_total a b).elim (fun h => (min_le_left _ _).trans_eq <| congr_arg _ (min_eq_left h).symm)
    fun h => (min_le_right _ _).trans_eq <| congr_arg _ (min_eq_right h).symm
#align min_abs_abs_le_abs_min min_abs_abs_le_abs_min

theorem abs_max_le_max_abs_abs : |max a b| ≤ max |a| |b| :=
  (le_total a b).elim (fun h => (congr_arg _ <| max_eq_right h).trans_le <| le_max_right _ _)
    fun h => (congr_arg _ <| max_eq_left h).trans_le <| le_max_left _ _
#align abs_max_le_max_abs_abs abs_max_le_max_abs_abs

theorem abs_min_le_max_abs_abs : |min a b| ≤ max |a| |b| :=
  (le_total a b).elim (fun h => (congr_arg _ <| min_eq_left h).trans_le <| le_max_left _ _) fun h =>
    (congr_arg _ <| min_eq_right h).trans_le <| le_max_right _ _
#align abs_min_le_max_abs_abs abs_min_le_max_abs_abs

theorem eq_of_abs_sub_eq_zero {a b : α} (h : |a - b| = 0) : a = b :=
  sub_eq_zero.1 <| (abs_eq_zero (α := α)).1 h
#align eq_of_abs_sub_eq_zero eq_of_abs_sub_eq_zero

theorem abs_sub_le (a b c : α) : |a - c| ≤ |a - b| + |b - c| :=
  calc
    |a - c| = |a - b + (b - c)| := by rw [sub_add_sub_cancel]
    _ ≤ |a - b| + |b - c| := abs_add _ _
#align abs_sub_le abs_sub_le

theorem abs_add_three (a b c : α) : |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
#align abs_add_three abs_add_three

theorem dist_bdd_within_interval {a b lb ub : α} (hal : lb ≤ a) (hau : a ≤ ub) (hbl : lb ≤ b)
    (hbu : b ≤ ub) : |a - b| ≤ ub - lb :=
  abs_sub_le_iff.2 ⟨sub_le_sub hau hbl, sub_le_sub hbu hal⟩
#align dist_bdd_within_interval dist_bdd_within_interval

theorem eq_of_abs_sub_nonpos (h : |a - b| ≤ 0) : a = b :=
  eq_of_abs_sub_eq_zero (le_antisymm h (abs_nonneg (a - b)))
#align eq_of_abs_sub_nonpos eq_of_abs_sub_nonpos

theorem abs_sub_nonpos : |a - b| ≤ 0 ↔ a = b :=
  ⟨eq_of_abs_sub_nonpos, by rintro rfl; rw [sub_self, abs_zero]⟩

theorem abs_sub_pos : 0 < |a - b| ↔ a ≠ b :=
  not_le.symm.trans abs_sub_nonpos.not

@[simp]
theorem abs_eq_self : |a| = a ↔ 0 ≤ a := by
  rw [abs_eq_max_neg, max_eq_left_iff, neg_le_self_iff]
#align abs_eq_self abs_eq_self

@[simp]
theorem abs_eq_neg_self : |a| = -a ↔ a ≤ 0 := by
  rw [abs_eq_max_neg, max_eq_right_iff, le_neg_self_iff]
#align abs_eq_neg_self abs_eq_neg_self

/-- For an element `a` of a linear ordered ring, either `abs a = a` and `0 ≤ a`,
    or `abs a = -a` and `a < 0`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem abs_cases (a : α) : |a| = a ∧ 0 ≤ a ∨ |a| = -a ∧ a < 0 := by
  by_cases h : 0 ≤ a
  · left
    exact ⟨abs_eq_self.mpr h, h⟩
  · right
    push_neg at h
    exact ⟨abs_eq_neg_self.mpr (le_of_lt h), h⟩
#align abs_cases abs_cases

@[simp]
theorem max_zero_add_max_neg_zero_eq_abs_self (a : α) : max a 0 + max (-a) 0 = |a| := by
  symm
  rcases le_total 0 a with (ha | ha) <;> simp [ha]
#align max_zero_add_max_neg_zero_eq_abs_self max_zero_add_max_neg_zero_eq_abs_self

end LinearOrderedAddCommGroup

namespace LatticeOrderedAddCommGroup
variable [Lattice α] [AddCommGroup α] {s t : Set α}

/-- A set `s` in a lattice ordered group is *solid* if for all `x ∈ s` and all `y ∈ α` such that
`|y| ≤ |x|`, then `y ∈ s`. -/
def IsSolid (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s
#align lattice_ordered_add_comm_group.is_solid LatticeOrderedAddCommGroup.IsSolid

/-- The solid closure of a subset `s` is the smallest superset of `s` that is solid. -/
def solidClosure (s : Set α) : Set α := {y | ∃ x ∈ s, |y| ≤ |x|}
#align lattice_ordered_add_comm_group.solid_closure LatticeOrderedAddCommGroup.solidClosure

lemma isSolid_solidClosure (s : Set α) : IsSolid (solidClosure s) :=
  fun _ ⟨y, hy, hxy⟩ _ hzx ↦ ⟨y, hy, hzx.trans hxy⟩
#align lattice_ordered_add_comm_group.is_solid_solid_closure LatticeOrderedAddCommGroup.isSolid_solidClosure

lemma solidClosure_min (hst : s ⊆ t) (ht : IsSolid t) : solidClosure s ⊆ t :=
  fun _ ⟨_, hy, hxy⟩ ↦ ht (hst hy) hxy
#align lattice_ordered_add_comm_group.solid_closure_min LatticeOrderedAddCommGroup.solidClosure_min

end LatticeOrderedAddCommGroup

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, AddGroup (α i)] [∀ i, Lattice (α i)]

@[simp] lemma abs_apply (f : ∀ i, α i) (i : ι) : |f| i = |f i| := rfl

lemma abs_def (f : ∀ i, α i) : |f| = fun i ↦ |f i| := rfl

end Pi

@[deprecated (since := "2024-01-13")] alias neg_le_abs_self := neg_le_abs
@[deprecated (since := "2024-01-13")] alias neg_abs_le_self := neg_abs_le
