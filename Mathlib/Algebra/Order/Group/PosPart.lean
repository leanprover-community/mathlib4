/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Notation

/-!
# Positive & negative parts

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure).

This file provides instances of `PosPart` and `NegPart`, the positive and negative parts of an
element in a lattice ordered group.

## Main statements

* `posPart_sub_negPart`: Every element `a` can be decomposed into `a⁺ - a⁻`, the difference of its
  positive and negative parts.
* `posPart_inf_negPart_eq_zero`: The positive and negative parts are coprime.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

positive part, negative part
-/

open Function

variable {α : Type*}

section Lattice
variable [Lattice α]

section Group
variable [Group α] {a b : α}

/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 1`, denoted `a⁺ᵐ`. -/
@[to_additive
/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 0`, denoted `a⁺`. -/]
instance instOneLePart : OneLePart α where
  oneLePart a := a ⊔ 1

/-- The *negative part* of an element `a` in a lattice ordered group is `a⁻¹ ⊔ 1`, denoted `a⁻ᵐ `.
-/
@[to_additive
/-- The *negative part* of an element `a` in a lattice ordered group is `(-a) ⊔ 0`, denoted `a⁻`.
-/]
instance instLeOnePart : LeOnePart α where
  leOnePart a := a⁻¹ ⊔ 1

@[to_additive] lemma leOnePart_def (a : α) : a⁻ᵐ = a⁻¹ ⊔ 1 := rfl

@[to_additive] lemma oneLePart_def (a : α) : a⁺ᵐ = a ⊔ 1 := rfl

@[to_additive] lemma oneLePart_mono : Monotone (·⁺ᵐ : α → α) :=
  fun _a _b hab ↦ sup_le_sup_right hab _

@[to_additive (attr := simp high)] lemma oneLePart_one : (1 : α)⁺ᵐ = 1 := sup_idem _

@[to_additive (attr := simp)] lemma leOnePart_one : (1 : α)⁻ᵐ = 1 := by simp [leOnePart]

@[to_additive posPart_nonneg] lemma one_le_oneLePart (a : α) : 1 ≤ a⁺ᵐ := le_sup_right

@[to_additive negPart_nonneg] lemma one_le_leOnePart (a : α) : 1 ≤ a⁻ᵐ := le_sup_right

-- TODO: `to_additive` guesses `nonposPart`
@[to_additive le_posPart] lemma le_oneLePart (a : α) : a ≤ a⁺ᵐ := le_sup_left

@[to_additive] lemma inv_le_leOnePart (a : α) : a⁻¹ ≤ a⁻ᵐ := le_sup_left

@[to_additive (attr := simp)] lemma oneLePart_eq_self : a⁺ᵐ = a ↔ 1 ≤ a := sup_eq_left
@[to_additive (attr := simp)] lemma oneLePart_eq_one : a⁺ᵐ = 1 ↔ a ≤ 1 := sup_eq_right

@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_one_le⟩ := oneLePart_eq_self
@[to_additive (attr := simp)] alias ⟨_, oneLePart_of_le_one⟩ := oneLePart_eq_one

/-- See also `leOnePart_eq_inv`. -/
@[to_additive /-- See also `negPart_eq_neg`. -/]
lemma leOnePart_eq_inv' : a⁻ᵐ = a⁻¹ ↔ 1 ≤ a⁻¹ := sup_eq_left

/-- See also `leOnePart_eq_one`. -/
@[to_additive /-- See also `negPart_eq_zero`. -/]
lemma leOnePart_eq_one' : a⁻ᵐ = 1 ↔ a⁻¹ ≤ 1 := sup_eq_right

@[to_additive] lemma oneLePart_le_one : a⁺ᵐ ≤ 1 ↔ a ≤ 1 := by simp [oneLePart]

/-- See also `leOnePart_le_one`. -/
@[to_additive /-- See also `negPart_nonpos`. -/]
lemma leOnePart_le_one' : a⁻ᵐ ≤ 1 ↔ a⁻¹ ≤ 1 := by simp [leOnePart]

@[to_additive] lemma leOnePart_le_one : a⁻ᵐ ≤ 1 ↔ a⁻¹ ≤ 1 := by simp [leOnePart]

@[to_additive (attr := simp) posPart_pos] lemma one_lt_oneLePart (ha : 1 < a) : 1 < a⁺ᵐ := by
  rwa [oneLePart_eq_self.2 ha.le]

@[to_additive (attr := simp)] lemma oneLePart_inv (a : α) : a⁻¹⁺ᵐ = a⁻ᵐ := rfl

@[to_additive (attr := simp)] lemma leOnePart_inv (a : α) : a⁻¹⁻ᵐ = a⁺ᵐ := by
  simp [oneLePart, leOnePart]

section MulLeftMono
variable [MulLeftMono α]

@[to_additive (attr := simp)] lemma leOnePart_eq_inv : a⁻ᵐ = a⁻¹ ↔ a ≤ 1 := by simp [leOnePart]

@[to_additive (attr := simp)]
lemma leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 ≤ a := by simp [leOnePart_eq_one']

@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_le_one⟩ := leOnePart_eq_inv
@[to_additive (attr := simp)] alias ⟨_, leOnePart_of_one_le⟩ := leOnePart_eq_one

@[to_additive (attr := simp) negPart_pos] lemma one_lt_ltOnePart (ha : a < 1) : 1 < a⁻ᵐ := by
  rwa [leOnePart_eq_inv.2 ha.le, one_lt_inv']

-- Bourbaki A.VI.12 Prop 9 a)
@[to_additive (attr := simp)] lemma oneLePart_div_leOnePart (a : α) : a⁺ᵐ / a⁻ᵐ = a := by
  rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul, leOnePart_def, mul_sup, mul_one, mul_inv_cancel,
    sup_comm, oneLePart_def]

@[to_additive (attr := simp)] lemma leOnePart_div_oneLePart (a : α) : a⁻ᵐ / a⁺ᵐ = a⁻¹ := by
  rw [← inv_div, oneLePart_div_leOnePart]

@[to_additive]
lemma oneLePart_leOnePart_injective : Injective fun a : α ↦ (a⁺ᵐ, a⁻ᵐ) := by
  simp only [Injective, Prod.mk.injEq, and_imp]
  rintro a b hpos hneg
  rw [← oneLePart_div_leOnePart a, ← oneLePart_div_leOnePart b, hpos, hneg]

@[to_additive]
lemma oneLePart_leOnePart_inj : a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b :=
  Prod.mk_inj.symm.trans oneLePart_leOnePart_injective.eq_iff

section MulRightMono
variable [MulRightMono α]

@[to_additive] lemma leOnePart_anti : Antitone (leOnePart : α → α) :=
  fun _a _b hab ↦ sup_le_sup_right (inv_le_inv_iff.2 hab) _

@[to_additive]
lemma leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 1)⁻¹ := by
  rw [leOnePart_def, ← inv_inj, inv_sup, inv_inv, inv_inv, inv_one]

-- Bourbaki A.VI.12 Prop 9 d)
@[to_additive] lemma oneLePart_mul_leOnePart (a : α) : a⁺ᵐ * a⁻ᵐ = |a|ₘ := by
  rw [oneLePart_def, sup_mul, one_mul, leOnePart_def, mul_sup, mul_one, mul_inv_cancel, sup_assoc,
    ← sup_assoc a, sup_eq_right.2 le_sup_right]
  exact sup_eq_left.2 <| one_le_mabs a

@[to_additive] lemma leOnePart_mul_oneLePart (a : α) : a⁻ᵐ * a⁺ᵐ = |a|ₘ := by
  rw [oneLePart_def, mul_sup, mul_one, leOnePart_def, sup_mul, one_mul, inv_mul_cancel, sup_assoc,
    ← @sup_assoc _ _ a, sup_eq_right.2 le_sup_right]
  exact sup_eq_left.2 <| one_le_mabs a

-- Bourbaki A.VI.12 Prop 9 a)
-- a⁺ᵐ ⊓ a⁻ᵐ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive] lemma oneLePart_inf_leOnePart_eq_one (a : α) : a⁺ᵐ ⊓ a⁻ᵐ = 1 := by
  rw [← mul_left_inj a⁻ᵐ⁻¹, inf_mul, one_mul, mul_inv_cancel, ← div_eq_mul_inv,
    oneLePart_div_leOnePart, leOnePart_eq_inv_inf_one, inv_inv]

end MulRightMono

end MulLeftMono

end Group

section CommGroup
variable [CommGroup α] [MulLeftMono α]

-- Bourbaki A.VI.12 (with a and b swapped)
@[to_additive] lemma sup_eq_mul_oneLePart_div (a b : α) : a ⊔ b = b * (a / b)⁺ᵐ := by
  simp [oneLePart, mul_sup]

-- Bourbaki A.VI.12 (with a and b swapped)
@[to_additive] lemma inf_eq_div_oneLePart_div (a b : α) : a ⊓ b = a / (a / b)⁺ᵐ := by
  simp [oneLePart, div_sup, inf_comm]

-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive] lemma le_iff_oneLePart_leOnePart (a b : α) : a ≤ b ↔ a⁺ᵐ ≤ b⁺ᵐ ∧ b⁻ᵐ ≤ a⁻ᵐ := by
  refine ⟨fun h ↦ ⟨oneLePart_mono h, leOnePart_anti h⟩, fun h ↦ ?_⟩
  rw [← oneLePart_div_leOnePart a, ← oneLePart_div_leOnePart b]
  exact div_le_div'' h.1 h.2

@[to_additive abs_add_eq_two_nsmul_posPart]
lemma mabs_mul_eq_oneLePart_sq (a : α) : |a|ₘ * a = a⁺ᵐ ^ 2 := by
  rw [sq, ← mul_mul_div_cancel a⁺ᵐ, oneLePart_mul_leOnePart, oneLePart_div_leOnePart]

@[to_additive add_abs_eq_two_nsmul_posPart]
lemma mul_mabs_eq_oneLePart_sq (a : α) : a * |a|ₘ = a⁺ᵐ ^ 2 := by
  rw [mul_comm, mabs_mul_eq_oneLePart_sq]

@[to_additive abs_sub_eq_two_nsmul_negPart]
lemma mabs_div_eq_leOnePart_sq (a : α) : |a|ₘ / a = a⁻ᵐ ^ 2 := by
  rw [sq, ← mul_div_div_cancel, oneLePart_mul_leOnePart, oneLePart_div_leOnePart]

@[to_additive sub_abs_eq_neg_two_nsmul_negPart]
lemma div_mabs_eq_inv_leOnePart_sq (a : α) : a / |a|ₘ = (a⁻ᵐ ^ 2)⁻¹ := by
  rw [← mabs_div_eq_leOnePart_sq, inv_div]

end CommGroup
end Lattice

section LinearOrder
variable [LinearOrder α] [Group α] {a b : α}

@[to_additive] lemma oneLePart_eq_ite : a⁺ᵐ = if 1 ≤ a then a else 1 := by
  rw [oneLePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]

@[to_additive (attr := simp) posPart_pos_iff] lemma one_lt_oneLePart_iff : 1 < a⁺ᵐ ↔ 1 < a :=
  lt_iff_lt_of_le_iff_le <| (one_le_oneLePart _).ge_iff_eq'.trans oneLePart_eq_one

@[to_additive posPart_eq_of_posPart_pos]
lemma oneLePart_of_one_lt_oneLePart (ha : 1 < a⁺ᵐ) : a⁺ᵐ = a := by
  rw [oneLePart_def, right_lt_sup, not_le] at ha; exact oneLePart_eq_self.2 ha.le

@[to_additive (attr := simp)] lemma oneLePart_lt : a⁺ᵐ < b ↔ a < b ∧ 1 < b := sup_lt_iff

section covariantmul
variable [MulLeftMono α]

@[to_additive] lemma leOnePart_eq_ite : a⁻ᵐ = if a ≤ 1 then a⁻¹ else 1 := by
  simp_rw [← one_le_inv']; rw [leOnePart_def, ← maxDefault, ← sup_eq_maxDefault]; simp_rw [sup_comm]

@[to_additive (attr := simp) negPart_pos_iff] lemma one_lt_ltOnePart_iff : 1 < a⁻ᵐ ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le <| (one_le_leOnePart _).ge_iff_eq'.trans leOnePart_eq_one

variable [MulRightMono α]

@[to_additive (attr := simp)] lemma leOnePart_lt : a⁻ᵐ < b ↔ b⁻¹ < a ∧ 1 < b :=
  sup_lt_iff.trans <| by rw [inv_lt']

end covariantmul
end LinearOrder

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)] [∀ i, Group (α i)]

@[to_additive (attr := simp)] lemma oneLePart_apply (f : ∀ i, α i) (i : ι) : f⁺ᵐ i = (f i)⁺ᵐ := rfl
@[to_additive (attr := simp)] lemma leOnePart_apply (f : ∀ i, α i) (i : ι) : f⁻ᵐ i = (f i)⁻ᵐ := rfl

@[to_additive (attr := push ←)] lemma oneLePart_def (f : ∀ i, α i) : f⁺ᵐ = fun i ↦ (f i)⁺ᵐ := rfl
@[to_additive (attr := push ←)] lemma leOnePart_def (f : ∀ i, α i) : f⁻ᵐ = fun i ↦ (f i)⁻ᵐ := rfl

end Pi
