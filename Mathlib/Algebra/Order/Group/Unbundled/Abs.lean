/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.Group.Lattice

/-!
# Absolute values in ordered groups

The absolute value of an element in a group which is also a lattice is its supremum with its
negation. This generalizes the usual absolute value on real numbers (`|x| = max x (-x)`).

## Notation

- `|a|`: The *absolute value* of an element `a` of an additive lattice ordered group
- `|a|ₘ`: The *absolute value* of an element `a` of a multiplicative lattice ordered group
-/

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section Group
variable [Group α] {a b : α}

/-- `mabs a`, denoted `|a|ₘ`, is the absolute value of `a`. -/
@[to_additive /-- `abs a`, denoted `|a|`, is the absolute value of `a` -/]
def mabs (a : α) : α := a ⊔ a⁻¹

@[inherit_doc mabs]
macro:max atomic("|" noWs) a:term noWs "|ₘ" : term => `(mabs $a)

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(abs $a)

/-- Unexpander for the notation `|a|ₘ` for `mabs a`.
Tries to add discretionary parentheses in unparsable cases. -/
@[app_unexpander mabs]
def mabs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|ₘ)
    | _ => `(|$a|ₘ)
  | _ => throw ()

/-- Unexpander for the notation `|a|` for `abs a`.
Tries to add discretionary parentheses in unparsable cases. -/
@[app_unexpander abs]
def abs.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) =>
    match a with
    | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|)
    | _ => `(|$a|)
  | _ => throw ()

@[to_additive] lemma mabs_le' : |a|ₘ ≤ b ↔ a ≤ b ∧ a⁻¹ ≤ b := sup_le_iff

@[to_additive] lemma le_mabs_self (a : α) : a ≤ |a|ₘ := le_sup_left

@[to_additive] lemma inv_le_mabs (a : α) : a⁻¹ ≤ |a|ₘ := le_sup_right

@[to_additive] lemma mabs_le_mabs (h₀ : a ≤ b) (h₁ : a⁻¹ ≤ b) : |a|ₘ ≤ |b|ₘ :=
  (mabs_le'.2 ⟨h₀, h₁⟩).trans (le_mabs_self b)

@[to_additive (attr := simp)] lemma mabs_inv (a : α) : |a⁻¹|ₘ = |a|ₘ := by simp [mabs, sup_comm]

@[to_additive] lemma mabs_div_comm (a b : α) : |a / b|ₘ = |b / a|ₘ := by rw [← mabs_inv, inv_div]

@[to_additive] lemma mabs_ite (p : Prop) [Decidable p] :
    |if p then a else b|ₘ = if p then |a|ₘ else |b|ₘ :=
  apply_ite _ _ _ _

@[to_additive] lemma mabs_dite (p : Prop) [Decidable p] (a : p → α) (b : ¬p → α) :
    |if h : p then a h else b h|ₘ = if h : p then |a h|ₘ else |b h|ₘ :=
  apply_dite _ _ _ _

variable [MulLeftMono α]

@[to_additive] lemma mabs_of_one_le (h : 1 ≤ a) : |a|ₘ = a :=
  sup_eq_left.2 <| (inv_le_one'.2 h).trans h

@[to_additive] lemma mabs_of_one_lt (h : 1 < a) : |a|ₘ = a := mabs_of_one_le h.le

@[to_additive] lemma mabs_of_le_one (h : a ≤ 1) : |a|ₘ = a⁻¹ :=
  sup_eq_right.2 <| h.trans (one_le_inv'.2 h)

@[to_additive] lemma mabs_of_lt_one (h : a < 1) : |a|ₘ = a⁻¹ := mabs_of_le_one h.le

@[to_additive] lemma mabs_le_mabs_of_one_le (ha : 1 ≤ a) (hab : a ≤ b) : |a|ₘ ≤ |b|ₘ := by
  rwa [mabs_of_one_le ha, mabs_of_one_le (ha.trans hab)]

attribute [gcongr] abs_le_abs_of_nonneg

@[to_additive (attr := simp)] lemma mabs_one : |(1 : α)|ₘ = 1 := mabs_of_one_le le_rfl

variable [MulRightMono α]

@[to_additive (attr := simp) abs_nonneg] lemma one_le_mabs (a : α) : 1 ≤ |a|ₘ := by
  apply pow_two_semiclosed _
  rw [mabs, pow_two, mul_sup, sup_mul, ← pow_two, inv_mul_cancel, sup_comm, ← sup_assoc]
  apply le_sup_right

@[to_additive (attr := simp)] lemma mabs_mabs (a : α) : |(|a|ₘ)|ₘ = |a|ₘ :=
  mabs_of_one_le <| one_le_mabs a

end Group

section CommGroup
variable [CommGroup α] [MulLeftMono α]

-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/-- The absolute value satisfies the triangle inequality. -/
@[to_additive /-- The absolute value satisfies the triangle inequality. -/]
lemma mabs_mul_le (a b : α) : |a * b|ₘ ≤ |a|ₘ * |b|ₘ := by
  apply sup_le
  · exact mul_le_mul' (le_mabs_self a) (le_mabs_self b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_mabs _) (inv_le_mabs _)

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

@[to_additive] lemma sup_div_inf_eq_mabs_div (a b : α) : (a ⊔ b) / (a ⊓ b) = |b / a|ₘ := by
  simp_rw [sup_div, div_inf, div_self', sup_comm, sup_sup_sup_comm, sup_idem]
  rw [← inv_div, sup_comm (b := _ / _), ← mabs, sup_eq_left]
  exact one_le_mabs _

@[to_additive two_nsmul_sup_eq_add_add_abs_sub]
lemma sup_sq_eq_mul_mul_mabs_div (a b : α) : (a ⊔ b) ^ 2 = a * b * |b / a|ₘ := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_mabs_div, div_eq_mul_inv, ← mul_assoc, mul_comm,
     mul_assoc, ← pow_two, inv_mul_cancel_left]

@[to_additive two_nsmul_inf_eq_add_sub_abs_sub]
lemma inf_sq_eq_mul_div_mabs_div (a b : α) : (a ⊓ b) ^ 2 = a * b / |b / a|ₘ := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_mabs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev,
    inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]

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

@[to_additive] lemma mabs_sup_div_sup_le_mabs (a b c : α) : |(a ⊔ c) / (b ⊔ c)|ₘ ≤ |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_left _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

@[to_additive] lemma mabs_inf_div_inf_le_mabs (a b c : α) : |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ := by
  apply le_of_mul_le_of_one_le_right _ (one_le_mabs _); rw [mabs_div_sup_mul_mabs_div_inf]

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
@[to_additive Birkhoff_inequalities]
lemma m_Birkhoff_inequalities (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)|ₘ ⊔ |(a ⊓ c) / (b ⊓ c)|ₘ ≤ |a / b|ₘ :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

end CommGroup
end Lattice

section LinearOrder
variable [Group α] [LinearOrder α] {a b : α}

@[to_additive] lemma mabs_choice (x : α) : |x|ₘ = x ∨ |x|ₘ = x⁻¹ := max_choice _ _

@[to_additive] lemma le_mabs : a ≤ |b|ₘ ↔ a ≤ b ∨ a ≤ b⁻¹ := le_max_iff

@[to_additive] lemma mabs_eq_max_inv : |a|ₘ = max a a⁻¹ := rfl

@[to_additive] lemma lt_mabs : a < |b|ₘ ↔ a < b ∨ a < b⁻¹ := lt_max_iff

@[to_additive] lemma mabs_by_cases (P : α → Prop) (h1 : P a) (h2 : P a⁻¹) : P |a|ₘ :=
  sup_ind _ _ h1 h2

@[to_additive] lemma eq_or_eq_inv_of_mabs_eq (h : |a|ₘ = b) : a = b ∨ a = b⁻¹ := by
  simpa only [← h, eq_comm (a := |a|ₘ), inv_eq_iff_eq_inv] using mabs_choice a

@[to_additive] lemma mabs_eq_mabs : |a|ₘ = |b|ₘ ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨fun h ↦ ?_, by rintro (h | h) <;> simp [h]⟩
  obtain rfl | rfl := eq_or_eq_inv_of_mabs_eq h <;>
    simpa only [inv_eq_iff_eq_inv (a := |b|ₘ), inv_inv, inv_inj, or_comm] using mabs_choice b

@[to_additive] lemma isSquare_mabs : IsSquare |a|ₘ ↔ IsSquare a :=
  mabs_by_cases (IsSquare · ↔ _) Iff.rfl isSquare_inv

@[to_additive] lemma lt_of_mabs_lt : |a|ₘ < b → a < b := (le_mabs_self _).trans_lt

@[to_additive (attr := simp)] lemma map_mabs {β F : Type*} [Group β] [LinearOrder β] [FunLike F α β]
    [OrderHomClass F α β] [MonoidHomClass F α β] (f : F) (a : α) :
    f |a|ₘ = |f a|ₘ := by
  rw [mabs, mabs, (OrderHomClass.mono f).map_max, map_inv]

variable [MulLeftMono α] {a b : α}

@[to_additive (attr := simp) abs_pos] lemma one_lt_mabs : 1 < |a|ₘ ↔ a ≠ 1 := by
  obtain ha | rfl | ha := lt_trichotomy a 1
  · simp [mabs_of_lt_one ha, ha.ne, ha]
  · simp
  · simp [mabs_of_one_lt ha, ha, ha.ne']

@[to_additive abs_pos_of_pos] lemma one_lt_mabs_pos_of_one_lt (h : 1 < a) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne'

@[to_additive abs_pos_of_neg] lemma one_lt_mabs_of_lt_one (h : a < 1) : 1 < |a|ₘ :=
  one_lt_mabs.2 h.ne

@[to_additive] lemma inv_mabs_le (a : α) : |a|ₘ⁻¹ ≤ a := by
  obtain h | h := le_total 1 a
  · simpa [mabs_of_one_le h] using (inv_le_one'.2 h).trans h
  · simp [mabs_of_le_one h]

@[to_additive add_abs_nonneg] lemma one_le_mul_mabs (a : α) : 1 ≤ a * |a|ₘ := by
  grw [← mul_inv_cancel a, inv_le_mabs a]

@[to_additive] lemma inv_mabs_le_inv (a : α) : |a|ₘ⁻¹ ≤ a⁻¹ := by simpa using inv_mabs_le a⁻¹

variable [MulRightMono α]

@[to_additive] lemma mabs_ne_one : |a|ₘ ≠ 1 ↔ a ≠ 1 :=
  (one_le_mabs a).lt_iff_ne'.symm.trans one_lt_mabs

@[to_additive (attr := simp)] lemma mabs_eq_one : |a|ₘ = 1 ↔ a = 1 := not_iff_not.1 mabs_ne_one

@[to_additive (attr := simp) abs_nonpos_iff] lemma mabs_le_one : |a|ₘ ≤ 1 ↔ a = 1 :=
  (one_le_mabs a).ge_iff_eq'.trans mabs_eq_one

@[to_additive] lemma mabs_le_mabs_of_le_one (ha : a ≤ 1) (hab : b ≤ a) : |a|ₘ ≤ |b|ₘ := by
  rw [mabs_of_le_one ha, mabs_of_le_one (hab.trans ha)]; exact inv_le_inv_iff.mpr hab

@[to_additive] lemma mabs_lt : |a|ₘ < b ↔ b⁻¹ < a ∧ a < b :=
  max_lt_iff.trans <| and_comm.trans <| by rw [inv_lt']

@[to_additive] lemma inv_lt_of_mabs_lt (h : |a|ₘ < b) : b⁻¹ < a := (mabs_lt.mp h).1

@[to_additive] lemma max_div_min_eq_mabs' (a b : α) : max a b / min a b = |a / b|ₘ := by
  rcases le_total a b with ab | ba
  · rw [max_eq_right ab, min_eq_left ab, mabs_of_le_one, inv_div]
    rwa [div_le_one']
  · rw [max_eq_left ba, min_eq_right ba, mabs_of_one_le]
    rwa [one_le_div']

@[to_additive] lemma max_div_min_eq_mabs (a b : α) : max a b / min a b = |b / a|ₘ := by
  rw [mabs_div_comm, max_div_min_eq_mabs']

end LinearOrder

namespace LatticeOrderedAddCommGroup
variable [Lattice α] [AddCommGroup α] {s t : Set α}

/-- A set `s` in a lattice ordered group is *solid* if for all `x ∈ s` and all `y ∈ α` such that
`|y| ≤ |x|`, then `y ∈ s`. -/
def IsSolid (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s

/-- The solid closure of a subset `s` is the smallest superset of `s` that is solid. -/
def solidClosure (s : Set α) : Set α := {y | ∃ x ∈ s, |y| ≤ |x|}

lemma isSolid_solidClosure (s : Set α) : IsSolid (solidClosure s) :=
  fun _ ⟨y, hy, hxy⟩ _ hzx ↦ ⟨y, hy, hzx.trans hxy⟩

lemma solidClosure_min (hst : s ⊆ t) (ht : IsSolid t) : solidClosure s ⊆ t :=
  fun _ ⟨_, hy, hxy⟩ ↦ ht (hst hy) hxy

end LatticeOrderedAddCommGroup

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, AddGroup (α i)] [∀ i, Lattice (α i)]

@[simp] lemma abs_apply (f : ∀ i, α i) (i : ι) : |f| i = |f i| := rfl

@[push ←]
lemma abs_def (f : ∀ i, α i) : |f| = fun i ↦ |f i| := rfl

end Pi
