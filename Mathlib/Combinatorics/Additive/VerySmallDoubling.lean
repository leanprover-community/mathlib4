/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.Finite.Set
import Mathlib.Data.Real.Archimedean
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sets with very small doubling

For a finset `A` in a group, its *doubling* is `#(A * A) / #A`. This file characterises sets with
* no doubling as the sets which are either empty or translates of a subgroup.
  For the converse, use the existing facts from the pointwise API: `∅ ^ 2 = ∅` (`Finset.empty_pow`),
  `(a • H) ^ 2 = a ^ 2 • H ^ 2 = a ^ 2 • H` (`smul_pow`, `coe_set_pow`).
* doubling strictly less than `3 / 2` as the sets that are contained in a coset of a subgroup of
  size strictly less than `3 / 2 * #A`.

## TODO

* Do we need versions stated using the doubling constant (`Finset.mulConst`)?
* Add characterisation of sets with doubling < φ. See
  https://terrytao.wordpress.com/2009/11/10/an-elementary-non-commutative-freiman-theorem.
* Add characterisation of sets with doubling ≤ 2 - ε. See
  https://terrytao.wordpress.com/2011/03/12/hamidounes-freiman-kneser-theorem-for-nonabelian-groups.

## References

* [*An elementary non-commutative Freiman theorem*, Terence Tao](https://terrytao.wordpress.com/2009/11/10/an-elementary-non-commutative-freiman-theorem)
* [*Introduction to approximate groups*, Matthew Tointon][tointon2020]
-/

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A : Finset G} {a : G}

/-! ### Doubling exactly `1` -/

@[to_additive]
private lemma smul_stabilizer_of_no_doubling_aux (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A ∧ (stabilizer G A : Set G) <• a = A := by
  have smul_A {a} (ha : a ∈ A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have A_smul {a} (ha : a ∈ A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_A_smul {a} (ha : a ∈ A) : a •> A = A <• a := by rw [smul_A ha, A_smul ha]
  have mul_mem_A_comm {x a} (ha : a ∈ A) : x * a ∈ A ↔ a * x ∈ A := by
    rw [← smul_mem_smul_finset_iff a, smul_A_eq_A_smul ha, ← op_smul_eq_mul, smul_comm,
      smul_mem_smul_finset_iff, smul_eq_mul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a ∈ A) : a⁻¹ • (A : Set G) = H := by
    ext x
    rw [Set.mem_inv_smul_set_iff, smul_eq_mul]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · simpa [← smul_A ha, mul_smul] using smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha, inv_smul_smul]

/-- A non-empty set with no doubling is the left translate of its stabilizer. -/
@[to_additive "A non-empty set with no doubling is the left-translate of its stabilizer."]
lemma smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A := (smul_stabilizer_of_no_doubling_aux hA ha).1

/-- A non-empty set with no doubling is the right translate of its stabilizer. -/
@[to_additive "A non-empty set with no doubling is the right translate of its stabilizer."]
lemma op_smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    (stabilizer G A : Set G) <• a = A := (smul_stabilizer_of_no_doubling_aux hA ha).2

/-! ### Doubling strictly less than `3 / 2` -/

private lemma big_intersection {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    2 * #A ≤ #((x • A) ∩ (y • A)) + #(A * A) := by
  have : #((x • A) ∪ (y • A)) ≤ #(A * A) := by
    refine card_le_card ?_
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul hx, smul_finset_subset_mul hy⟩
  refine (add_le_add_left this _).trans_eq' ?_
  rw [card_inter_add_card_union]
  simp only [card_smul_finset, two_mul]

private lemma mul_inv_eq_inv_mul_of_doubling_lt_two_aux (h : #(A * A) < 2 * #A) :
    A⁻¹ * A ⊆ A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A ∩ y • A).Nonempty := by
    rw [← card_pos]
    linarith [big_intersection hx hy]
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hzxwy, inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_inv_eq_inv_mul_of_doubling_lt_two_aux` a goal?
-- ie wlog in the target rather than hypothesis
-- (BM: third time seeing this pattern)
-- I'm thinking something like wlog_suffices, where I could write
-- wlog_suffices : A⁻¹ * A ⊆ A * A⁻¹
-- which reverts *everything* (just like wlog does) and makes the side goal A⁻¹ * A = A * A⁻¹
-- under the assumption A⁻¹ * A ⊆ A * A⁻¹
-- and changes the main goal to A⁻¹ * A ⊆ A * A⁻¹
/-- If `A` has doubling strictly less than `2`, then `A * A⁻¹ = A⁻¹ * A`. -/
lemma mul_inv_eq_inv_mul_of_doubling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = A⁻¹ * A := by
  refine Subset.antisymm ?_ (mul_inv_eq_inv_mul_of_doubling_lt_two_aux h)
  simpa using
    mul_inv_eq_inv_mul_of_doubling_lt_two_aux (A := A⁻¹) (by simpa [← mul_inv_rev] using h)

private lemma weaken_doubling (h : #(A * A) < (3 / 2 : ℚ) * #A) : #(A * A) < 2 * #A := by
  rw [← Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  linarith only [h]

private lemma nonempty_of_doubling (h : #(A * A) < (3 / 2 : ℚ) * #A) : A.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp at h

/-- If `A` has doubling strictly less than `3 / 2`, then `A⁻¹ * A` is a subgroup.

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and `A⁻¹ * A` isn't a subgroup. -/
def invMulSubgroup (A : Finset G) (h : #(A * A) < (3 / 2 : ℚ) * #A) : Subgroup G where
  carrier := A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ : ∀ x ∈ A, ∀ y ∈ A, (1 / 2 : ℚ) * #A < #(x • A ∩ y • A) := by
      intro x hx y hy
      have := big_intersection hx hy
      rw [← Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
      linarith
    intro a c ha hc
    simp only [mem_mul, mem_inv'] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : ℚ) * #A < #(A ∩ (a * b)⁻¹ • A) := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [← card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : ℚ) * #A < #(A ∩ (c * d) • A) := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [← card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A ∩ (c * d) • A) ∩ (A ∩ (a * b)⁻¹ • A)).Nonempty := by
      rw [← card_pos, ← Nat.cast_pos (α := ℚ)]
      have := card_inter_add_card_union (A ∩ (c * d) • A) (A ∩ (a * b)⁻¹ • A)
      rw [← Nat.cast_inj (R := ℚ), Nat.cast_add, Nat.cast_add] at this
      have : (#((A ∩ (c * d) • A) ∪ (A ∩ (a * b)⁻¹ • A)) : ℚ) ≤ #A := by
        rw [Nat.cast_le, ← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), mem_mul]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩

lemma invMulSubgroup_eq_inv_mul (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A := rfl

lemma invMulSubgroup_eq_mul_inv (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A * A⁻¹ := by
  rw [invMulSubgroup_eq_inv_mul, eq_comm]
  norm_cast
  exact mul_inv_eq_inv_mul_of_doubling_lt_two (by qify at h ⊢; linarith)

instance (A : Finset G) (h) : Fintype (invMulSubgroup A h) := by
  simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, mem_coe]; infer_instance

private lemma weak_invMulSubgroup_bound (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) < 2 * #A := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ : ∀ x ∈ A, ∀ y ∈ A, (1 / 2 : ℚ) * #A < #((x • A) ∩ (y • A)) := by
    intro x hx y hy
    have := big_intersection hx hy
    rw [← Nat.cast_le (α := ℚ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
    linarith
  have h₂ : ∀ a ∈ A⁻¹ * A, (1 / 2 : ℚ) * #A < #{xy ∈ A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    simp only [mem_mul, and_imp, mem_inv, exists_exists_and_eq_and,
      forall_exists_index]
    rintro _ a ha b hb rfl
    refine (h₁ a ha b hb).trans_le ?_
    rw [Nat.cast_le]
    refine card_le_card_of_injOn (fun t => (a⁻¹ * t, b⁻¹ * t)) ?_ (by simp [Set.InjOn])
    simp only [mem_inter, mem_product, and_imp, mem_filter, mul_inv_rev, inv_inv,
      forall_exists_index, smul_eq_mul,
      forall_apply_eq_imp_iff₂, inv_mul_cancel_left, mem_smul_finset]
    rintro c hc d hd h
    rw [mul_assoc, mul_inv_cancel_left, ← h, inv_mul_cancel_left]
    simp [hd, hc]
  have h₃ : ∀ x ∈ A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x ∈ A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : ℚ) * #A) * #(A⁻¹ * A) < (#A : ℚ) ^ 2 := by
    rw [← Nat.cast_pow, sq, ← card_product, card_eq_sum_card_fiberwise h₃, Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₂).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  have : (0 : ℚ) < #A := by simpa [card_pos]
  rw [← Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith

private lemma A_subset_aH (a : G) (ha : a ∈ A) : A ⊆ a • (A⁻¹ * A) := by
  rw [← smul_mul_assoc]
  exact subset_mul_right _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

private lemma subgroup_strong_bound_left (h : #(A * A) < (3 / 2 : ℚ) * #A) (a : G) (ha : a ∈ A) :
    A * A ⊆ a • op a • (A⁻¹ * A) := by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj, coe_mul, coe_mul, ← invMulSubgroup_eq_inv_mul _ h, coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm, smul_mul_assoc, h₁, smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), ← mul_smul_comm]
  exact subset_mul_left _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

private lemma subgroup_strong_bound_right (h : #(A * A) < (3 / 2 : ℚ) * #A) (a : G) (ha : a ∈ A) :
    a • op a • (A⁻¹ * A) ⊆ A * A := by
  intro z hz
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A ∩ ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) ∩ (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj, coe_mul, coe_mul, ← invMulSubgroup_eq_inv_mul _ h, coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left, ← this, subset_smul_finset_iff]
    simp only [← hz, mul_inv_rev, inv_inv, ← mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right, ← this, mul_assoc _ A,
      ← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), subset_smul_finset_iff]
    simp only [← mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [← hz, mul_mem_mul, ha, hb, hc]
  have lr : l ∪ r ⊆ a • (A⁻¹ * A) := by
    rw [union_subset_iff, hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : #l = #A := by rw [hl]
  have : #r = #A := by rw [hr, card_smul_finset, card_inv]
  have : #(l ∪ r) < 2 * #A := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_invMulSubgroup_bound h
  have ⟨t, ht⟩ : (l ∩ r).Nonempty := by
    rw [← card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ← inv_smul_mem_iff, smul_eq_mul, mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩

open scoped RightActions in
lemma smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A)
    (ha : a ∈ A) : a •> ((A⁻¹ * A) <• a) = A * A :=
  (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

lemma card_inv_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) = #(A * A) := by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  simp_rw [← smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves h ha, card_smul_finset]

lemma smul_inv_mul_eq_inv_mul_opSMul (h : #(A * A) < (3 / 2 : ℚ) * #A) (ha : a ∈ A) :
    a •> (A⁻¹ * A) = (A⁻¹ * A) <• a := by
  refine subset_antisymm ?_ ?_
  · rw [subset_smul_finset_iff, ← op_inv]
    calc
      a •> (A⁻¹ * A) <• a⁻¹ ⊆ a •> (A⁻¹ * A) * A⁻¹ := op_smul_finset_subset_mul (by simpa)
      _ ⊆ A * (A⁻¹ * A) * A⁻¹ := by gcongr; exact smul_finset_subset_mul (by simpa)
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc, ← invMulSubgroup_eq_mul_inv _ h, mul_assoc,
          ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe, invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) ⊆ A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ ⊆ A⁻¹ * ((A⁻¹ * A) * A) := by gcongr; exact op_smul_finset_subset_mul (by simpa)
      _ = A⁻¹ * A := by
        rw [← mul_inv_eq_inv_mul_of_doubling_lt_two <| weaken_doubling h]
        simp_rw [← coe_inj, coe_mul]
        rw [mul_assoc, ← invMulSubgroup_eq_inv_mul _ h, ← mul_assoc,
          ← invMulSubgroup_eq_inv_mul _ h, ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe]

open scoped RightActions in
/-- If `A` has doubling strictly less than `3 / 2`, then there exists a subgroup `H` of the
normaliser of `A` of size strictly less than `3 / 2 * #A` such that `A` is a subset of a coset of
`H` (in fact a subset of `a • H` for every `a ∈ A`).

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and can't be covered by a subgroup
of size at most `2`.

This is Theorem 2.2.1 in [tointon2020]. -/
theorem doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H), Fintype.card H < (3 / 2 : ℚ) * #A ∧ ∀ a ∈ A,
      (A : Set G) ⊆ a • H ∧ a •> (H : Set G) = H <• a := by
  let H := invMulSubgroup A h
  refine ⟨H, inferInstance, ?_, fun a ha ↦ ⟨?_, ?_⟩⟩
  · simp [← Nat.card_eq_fintype_card, invMulSubgroup, ← coe_mul, - coe_inv, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

/-! ### Doubling less than `2-ε` -/

variable (ε : ℝ)

omit [DecidableEq G] in
private lemma rightCoset_eq_of_mem {H : Subgroup G} {c : Set G} {x : G}
    (hc: c ∈ orbit Gᵐᵒᵖ (H : Set G)) (hx : x ∈ c) : c = H <• x := by
  rw [mem_orbit_iff] at hc
  obtain ⟨a', ha⟩ := hc
  let a := a'.unop
  have ha : c = H <• a := by exact id (Eq.symm ha)
  rw [ha, mem_rightCoset_iff] at hx
  rw [← rightCoset_mem_rightCoset H hx, smul_smul] at ha
  simp_all only [op_mul, op_inv, mul_inv_cancel_left, SetLike.mem_coe]

/-- Underlying structure for the set of representatives of a finite set of right cosets -/
private structure RCosRepFin (G : Type*) [Group G] [DecidableEq G] where
  H : Subgroup G
  A : Finset G
  preZ : Set (Set G)
  fin_preZ : preZ.Finite
  preZ' : Finset (Set G)
  chooseZ' : Set G → G
  chooseZ'_spec : ∀ cH ∈ preZ', chooseZ' cH ∈ cH ∩ (↑H * ↑A)
  Z' : Finset G
  toH : G → G
  toH_mem_H : ∀ z ∈ Z', toH z ∈ ↑H
  toA : G → G
  toA_mem_A : ∀ z ∈ Z', toA z ∈ A
  toH_mul_toA : ∀ z ∈ Z', toH z * toA z = z
  toZ : G → G
  toZ_comp_chooseZ'_mem_self {c : Set G} (hc : c ∈ preZ') : toZ (chooseZ' c) ∈ c
  Z : Finset G

private noncomputable def rCosRepFin (H : Subgroup G) [Fintype H] {A : Finset G}
    (hA : A.Nonempty) : RCosRepFin G := by
  -- we first take all right cosets that intersect `A`, show that there is finitely many
  -- of them and take for `Z'` a set of representatives of all these cosets; then we
  -- multiply every element of `Z'` with an appropriate element of `H` to make `Z ⊆ A`
  classical
  let preZ := {cH ∈ orbit Gᵐᵒᵖ (H : Set G) | (cH ∩ (H * A)).Nonempty}
  have fin_preZ : preZ.Finite := by
    obtain ⟨a, ha⟩ := hA
    let f_preZ : Set G → (H : Set G) * (A : Set G) := fun cH =>
      if h : cH ∈ preZ
      then ⟨Classical.choose h.2, by
        apply And.right at h
        apply Classical.choose_spec at h
        apply Set.mem_of_mem_inter_right at h
        exact h⟩
      else ⟨1 * a, Set.mul_mem_mul (H.one_mem) ha⟩

    have inj_f_preZ : Set.InjOn f_preZ preZ := by
      unfold Set.InjOn
      intro c₁ hc₁ c₂ hc₂ hc₁c₂
      unfold f_preZ at hc₁c₂
      simp_all only [↓reduceDIte, Subtype.mk.injEq]
      let s := Classical.choose hc₁.2
      have s_mem_c₁ : s ∈ c₁ := by
        apply And.right at hc₁
        apply Classical.choose_spec at hc₁
        exact Set.mem_of_mem_inter_left hc₁
      have s_mem_c₂ : s ∈ c₂ := by
        apply And.right at hc₂
        apply Classical.choose_spec at hc₂
        rw [← hc₁c₂] at hc₂
        exact Set.mem_of_mem_inter_left hc₂
      rw [rightCoset_eq_of_mem hc₁.1 s_mem_c₁, rightCoset_eq_of_mem hc₂.1 s_mem_c₂]

    exact Finite.Set.finite_of_finite_image preZ inj_f_preZ

  let preZ' := fin_preZ.toFinset
  have elts_preZ'_nonempty (cH : Set G) (hcH : cH ∈ preZ') : (cH ∩ (H * A)).Nonempty := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf] at hcH
    exact hcH.2

  choose! chooseZ' chooseZ'_spec using elts_preZ'_nonempty
  let Z' := image chooseZ' preZ'

  have Z'_subset_HA : (Z' : Set G) ⊆ H * A := by
    simpa only [coe_image, Set.image_subset_iff, Z'] using fun x hx ↦ (chooseZ'_spec _ hx).2

  change ∀ (z : G), z ∈ (Z' : Set G) → z ∈ (H : Set G) * A at Z'_subset_HA
  simp only [mem_coe, Set.mem_mul] at Z'_subset_HA
  choose! toH toH_mem_H toA toA_mem_A toH_mul_toA using Z'_subset_HA
  let toZ := fun z' => (toH z')⁻¹ * z'

  have toZ_comp_chooseZ'_mem_self {c : Set G} (hc : c ∈ preZ')
      : toZ (chooseZ' c) ∈ c := by
    unfold toZ
    nth_rw 1 [rightCoset_eq_of_mem ((Set.Finite.mem_toFinset _).mp hc).1 (chooseZ'_spec _ hc).1]
    apply mem_rightCoset
    apply H.inv_mem
    exact toH_mem_H _ (mem_image_of_mem chooseZ' hc)

  let Z := image toZ Z'
  exact ⟨H, A, preZ, fin_preZ, preZ', chooseZ', chooseZ'_spec, Z', toH, toH_mem_H, toA,
          toA_mem_A, toH_mul_toA, toZ, toZ_comp_chooseZ'_mem_self, Z⟩

-- TODO: Here `Z` is defined by extracting a representative from each coset and the definitional
-- property is actually not (explicitely) proved as it is not needed here; as far as I could check,
-- no such coset representing set is available in the library at this point, although it might be
-- useful independently of this section
/-- Given a finite subset `A` of group `G` and a subgroup `H ≤ G`, right coset representing set of
`H * A` is a subset `Z` of `A` such that `H * Z = H * A` and `∀ z₁ z₂ ∈ Z → Hz₁ ≠ Hz₂` -/
private noncomputable def rightCosetRepresentingFinset (H : Subgroup G) [Fintype H] {A : Finset G}
    (hA : A.Nonempty) : Finset G :=
  (rCosRepFin H hA).Z

private lemma rightCosetRepresentingFinset_subset_finset (H : Subgroup G) [Fintype H] {A : Finset G}
    (hA : A.Nonempty) : rightCosetRepresentingFinset H hA ⊆ A := by
  intro z hz
  obtain ⟨z', hz'₁, (hz'₂ : ((rCosRepFin H hA).toH z')⁻¹ * z' = z)⟩ := mem_image.mp hz
  rw [← hz'₂, inv_mul_eq_of_eq_mul (Eq.symm ((rCosRepFin H hA).toH_mul_toA z' hz'₁))]
  exact (rCosRepFin H hA).toA_mem_A z' hz'₁

private lemma mul_rightCosetRepresentingFinset_eq_mul_set (H : Subgroup G) [Fintype H]
    {A : Finset G} (hA : A.Nonempty) : (H : Set G) * (rightCosetRepresentingFinset H hA) = H * A
    := by
  have H_eq_HH : (H : Set G) = H * H := by simp only [coe_mul_coe]
  let rcrf := rCosRepFin H hA
  apply Set.Subset.antisymm (Set.mul_subset_mul_left
          (coe_subset.mpr (rightCosetRepresentingFinset_subset_finset H hA)))
  intro x hx
  obtain ⟨h, hh, a, ha, hha⟩ := Set.mem_mul.mp hx
  rw [← hha, H_eq_HH, mul_assoc]
  apply Set.mul_mem_mul hh
  let ca := (H : Set G) <• a
  have ca_mem_preZ' : ca ∈ rcrf.preZ' := by
    change ca ∈ rcrf.fin_preZ.toFinset
    rw [Set.Finite.mem_toFinset]
    change ca ∈ {cH ∈ orbit Gᵐᵒᵖ (H : Set G) | (cH ∩ (H * A)).Nonempty}
    rw [Set.mem_setOf]
    constructor
    · simp_all only [coe_mul_coe, SetLike.mem_coe, mem_coe, mem_orbit, ca]
    · use a
      constructor
      · rw [← one_mul a]
        exact mem_rightCoset a (one_mem H)
      · rw [← one_mul a]
        exact Set.mul_mem_mul H.one_mem ha
  let z := rcrf.toZ (rcrf.chooseZ' ca)
  have z_mem_ca : z ∈ ca := rcrf.toZ_comp_chooseZ'_mem_self (ca_mem_preZ')
  have z_mem_Z : z ∈ rightCosetRepresentingFinset H hA :=
    mem_image_of_mem _ (mem_image_of_mem _ ca_mem_preZ')
  have a_mem_Hz : a ∈ (H: Set G) <• z := by
    rw [mem_rightCoset_iff, SetLike.mem_coe]
    rw [mem_rightCoset_iff, SetLike.mem_coe] at z_mem_ca
    apply inv_mem at z_mem_ca
    simp_all only [coe_mul_coe, SetLike.mem_coe, mem_coe, mul_inv_rev, inv_inv]
  exact Set.op_smul_set_subset_mul z_mem_Z a_mem_Hz

private lemma mul_rightCosetRepresentingFinset_eq_mul_finset (H : Subgroup G) [Fintype H]
    {A : Finset G} (hA : A.Nonempty)
    : Set.toFinset H * (rightCosetRepresentingFinset H hA) = Set.toFinset H * A := by
  simpa only [← coe_inj, coe_mul, Set.coe_toFinset]
    using mul_rightCosetRepresentingFinset_eq_mul_set H hA

private lemma card_mul_rightCosetRepresentingFinset_eq_mul_card (H : Subgroup G) [Fintype H]
    {A : Finset G} (hA : A.Nonempty) : #(Set.toFinset H * (rightCosetRepresentingFinset H hA))
    = Fintype.card H * #(rightCosetRepresentingFinset H hA) := by
  let rcrf := rCosRepFin H hA
  simp only [← SetLike.coe_sort_coe, ← Set.toFinset_card, card_mul_iff, Set.coe_toFinset]
  unfold Set.InjOn
  simp only [Set.mem_prod, SetLike.mem_coe, mem_coe, and_imp, Prod.forall, Prod.mk.injEq]
  intro h z hh (hz : z ∈ image rcrf.toZ rcrf.Z')
        g t hg (ht : t ∈ image rcrf.toZ rcrf.Z') hyp
  rw [mem_image] at hz ht

  obtain ⟨z', (hz'₁ : z' ∈ image rcrf.chooseZ' rcrf.preZ'), hz'₂⟩ := hz
  obtain ⟨t', (ht'₁ : t' ∈ image rcrf.chooseZ' rcrf.preZ'), ht'₂⟩ := ht
  rw [mem_image] at hz'₁ ht'₁

  obtain ⟨cz, hcz₁, hcz₂⟩ := hz'₁
  have hcz₃ : z ∈ cz := by simp only [← hz'₂, ← hcz₂, rcrf.toZ_comp_chooseZ'_mem_self hcz₁]
  change cz ∈ rcrf.fin_preZ.toFinset at hcz₁
  rw [Set.Finite.mem_toFinset rcrf.fin_preZ] at hcz₁
  have hcz₄ := rightCoset_eq_of_mem hcz₁.1 hcz₃

  obtain ⟨ct, hct₁, hct₂⟩ := ht'₁
  have hct₃ : t ∈ ct := by simp only [← ht'₂, ← hct₂, rcrf.toZ_comp_chooseZ'_mem_self hct₁]
  change ct ∈ rcrf.fin_preZ.toFinset at hct₁
  rw [Set.Finite.mem_toFinset rcrf.fin_preZ] at hct₁
  have hct₄ := rightCoset_eq_of_mem hct₁.1 hct₃

  rw [← inv_mul_eq_iff_eq_mul, ← mul_assoc] at hyp
  rw [← hyp, op_mul, ← smul_smul, rightCoset_mem_rightCoset H (H.mul_mem (H.inv_mem hg) hh),
      ← hcz₄] at hct₄
  rw [hct₄, hcz₂] at hct₂
  apply congr_arg rcrf.toZ at hct₂
  rw [hz'₂, ht'₂] at hct₂
  rw [hct₂, mul_eq_right, inv_mul_eq_one] at hyp
  exact ⟨Eq.symm hyp, hct₂⟩

private structure ExpansionMeasure (G : Type*) [Group G] [DecidableEq G] where
  K : ℝ
  hK : K < 1
  A : Finset G
  hA : A.Nonempty
  toFun : Finset G → ℝ
  toFun_def : ∀ (S : Finset G), toFun S = #(S * A) - K * #S
  left_invariant : ∀ (S : Finset G) (x : G), toFun (x •> S) = toFun S
  submodularity : ∀ (S : Finset G) (T : Finset G),
      toFun (S ∩ T) + toFun (S ∪ T) ≤ toFun S + toFun T
  lower_bound : ∀ (S : Finset G), (1 - K) * #S ≤ toFun S

private def expansionMeasure {K : ℝ} (hK : K < 1) {A : Finset G} (hA : A.Nonempty)
    : ExpansionMeasure G := {
  K := K
  hK := hK
  A := A
  hA := hA
  toFun := fun S => #(S * A) - K * #S
  toFun_def := fun S => rfl
  left_invariant := fun _ _ => by simp_all only [card_smul_finset, smul_mul_assoc]
  submodularity := by
    intro S T
    have eq1 : K * #(S ∩ T) + K * #(S ∪ T) = K * #S + K * #T := by
      simpa only [← mul_add, ← Nat.cast_add, mul_eq_mul_left_iff, Nat.cast_inj]
        using Or.inl (card_inter_add_card_union S T)
    have eq2 : (#((S ∩ T) * A) : ℝ) + #((S ∪ T) * A) ≤ #(S * A) + #(T * A) := by
      calc
        (#((S ∩ T) * A) : ℝ) + #((S ∪ T) * A) ≤ #((S * A) ∩ (T * A)) + #((S * A) ∪ (T * A))
                                        := by gcongr; exact inter_mul_subset; exact union_mul.le
                                            _ = #(S * A) + #(T * A)
                                        := ?_
      · norm_cast
        exact card_inter_add_card_union (S * A) (T * A)
    have eq3 : #((S ∩ T) * A) - K * #(S ∩ T) + (#((S ∪ T) * A) - K * #(S ∪ T))
        = #((S ∩ T) * A) + #((S ∪ T) * A) - (K * #(S ∩ T) + K * #(S ∪ T)) := by ring1
    have eq4 : #(S * A) - K * #S + (#(T * A) - K * #T)
        = #(S * A) + #(T * A) - (K * #S + K * #T) := by ring1
    rw [eq3, eq4, eq1]
    exact sub_le_sub_right eq2 _
  lower_bound := by
    intro S
    obtain ⟨a, ha⟩ := hA
    calc
          (1 - K) * #S
      _ = #S - K * #S           := by ring1
      _ = #S - K * #S           := by rfl
      _ = #(S * {a}) - K * #S   := by norm_num
      _ ≤ #(S * A)  - K * #S    := ?_
    apply sub_le_sub_right
    norm_cast
    apply card_le_card
    exact mul_subset_mul_left (singleton_subset_iff.mpr ha)
}

private lemma expansionMeasure_pos (em : ExpansionMeasure G)
    : ∀ {S : Finset G} (_ : S.Nonempty), 0 < em.toFun S := by
  intro S hS
  calc
          0
      _ < (1 - em.K) * #S   := ?_
      _ ≤ em.toFun S        := em.lower_bound S
  simp_all only [em.hK, sub_pos, mul_pos_iff_of_pos_left, Nat.cast_pos, card_pos]

private def expansionMeasure_image (em : ExpansionMeasure G) : Set ℝ :=
  em.toFun '' {S : Finset G | S.Nonempty}

private lemma expansionMeasure_image_nonempty (em : ExpansionMeasure G)
    : (expansionMeasure_image em).Nonempty :=
  ⟨em.toFun {1}, Set.mem_image_of_mem em.toFun (by exact ⟨1, mem_singleton.mpr (rfl)⟩)⟩

private lemma expansionMeasure_image_bddBelow (em : ExpansionMeasure G)
    : BddBelow (expansionMeasure_image em) := ⟨0, fun c hc => by
  obtain ⟨S, (hS₁ : S.Nonempty), hS₂⟩ := hc
  simpa only [hS₂] using le_of_lt (expansionMeasure_pos em hS₁)
⟩

private noncomputable def connectivity (em : ExpansionMeasure G) : ℝ :=
  sInf (expansionMeasure_image em)

private lemma connectivity_le (em : ExpansionMeasure G) : ∀ {S : Finset G} (_ : S.Nonempty),
    connectivity em ≤ em.toFun S := fun hS =>
  csInf_le (expansionMeasure_image_bddBelow em) (Set.mem_image_of_mem em.toFun hS)

private lemma connectivity_nonneg (em : ExpansionMeasure G) : 0 ≤ connectivity em := by
  apply le_csInf (expansionMeasure_image_nonempty em)
  intro k hk
  obtain ⟨S, (hS₁ : S.Nonempty), hS₂⟩ := (Set.mem_image _ _ _).mp hk
  rw [← hS₂]
  exact le_of_lt (expansionMeasure_pos em hS₁)

/-- The value of connectivity is attained by an element of the image of the expansion measure
function. -/
private lemma connectivity_mem_expansionMeasure_image (em : ExpansionMeasure G)
    : connectivity em ∈ expansionMeasure_image em := by
  apply by_contradiction

  let κ := connectivity em
  have κ_add_one_pos : 0 < κ + 1 := by linarith [connectivity_nonneg em]
  have one_sub_K_pos : 0 < 1 - em.K := by linarith [em.hK]

  unfold expansionMeasure_image
  rw [Set.mem_image]
  push_neg
  intro h

  let t := Nat.floor ((κ + 1) / (1 - em.K))
  have largeT {T : Finset G} (hT : t < #T) : κ + 1 < em.toFun T := by
    rw [Nat.lt_iff_add_one_le] at hT
    calc
          κ + 1
      _ = (κ + 1) / ((κ + 1) / (1 - em.K)) * ((κ + 1) / (1 - em.K))
            := Eq.symm (div_mul_cancel₀ _ (div_ne_zero (by linarith) (by linarith)))
      _ < (κ + 1) / ((κ + 1) / (1 - em.K)) * (t + 1)
            := by gcongr; exact Nat.lt_floor_add_one ((κ + 1) / (1 - em.K))
      _ = (1 - em.K) * (t + 1)    := by field_simp
      _ ≤ (1 - em.K) * #T         := by gcongr; rw [← Nat.cast_add_one, Nat.cast_le]; exact hT
      _ ≤ em.toFun T              := em.lower_bound T

  let im_smallT := (((Icc #em.A (t * #em.A)).map Nat.castEmbedding : Finset ℝ)
                    - em.K • ((Icc 1 t).map Nat.castEmbedding)).filter (fun x => κ < x)
  have smallT {T : Finset G} (hT₁ : T.Nonempty) (hT₂ : #T ≤ t) : em.toFun T ∈ im_smallT := by
    rw [mem_filter]
    constructor
    · rw [em.toFun_def]
      apply sub_mem_sub
      · apply mem_map_of_mem
        rw [mem_Icc]
        constructor
        obtain ⟨x, hx⟩ := hT₁
        · calc
                #em.A
            _ = #(x •> em.A)    := Eq.symm (card_smul_finset x em.A)
            _ ≤ #(T •> em.A)    := card_le_card (smul_finset_subset_smul hx)
            _ ≤ #(T * em.A)     := by simp only [smul_eq_mul, le_refl]
        · calc
                #(T * em.A)
            _ ≤ #T * #em.A      := card_mul_le
            _ ≤ t * #em.A       := Nat.mul_le_mul_right (#em.A) hT₂
      · rw [← smul_eq_mul]
        apply smul_mem_smul_finset
        apply mem_map_of_mem
        rw [mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (card_pos.mpr hT₁)), hT₂⟩
    · exact lt_of_le_of_ne (connectivity_le em hT₁) (Ne.symm (h T hT₁))
  have : (im_smallT ∪ {κ + 1}).Nonempty := by simp
  let k := (im_smallT ∪ {κ + 1}).min' this
  have : κ < k := by
    rw [lt_min'_iff _ this]
    intro x hx
    rw [mem_union] at hx
    cases hx with
    | inl hx =>
      exact (Finset.mem_filter.mp hx).2
    | inr hx =>
      rw [mem_singleton] at hx
      linarith
  obtain ⟨s, hs₁, hs₂⟩ := (csInf_lt_iff (expansionMeasure_image_bddBelow em)
                                        (expansionMeasure_image_nonempty em)).mp this
  obtain ⟨S, (hS₁ : S.Nonempty), hS₂⟩ := (Set.mem_image _ _ _).mp hs₁
  have : em.toFun S ≤ κ + 1 := by
    calc
          em.toFun S
      _ = s           := hS₂
      _ ≤ k           := le_of_lt hs₂
      _ ≤ κ + 1       := min'_le _ _ (by simp only [mem_union, mem_singleton, or_true])
  have := not_lt.mp (mt largeT (not_lt.mpr this))
  apply smallT hS₁ at this
  rw [hS₂] at this
  exact (and_not_self_iff (s ∈ im_smallT)).mp ⟨this,
    (notMem_union.mp (mt (min'_le (im_smallT ∪ {κ + 1}) _) (not_le.mpr hs₂))).1⟩

private lemma connectivity_pos (em : ExpansionMeasure G) : 0 < connectivity em := by
  obtain ⟨S, hS₁, hS₂⟩ := (Set.mem_image _ _ _).mp
    (connectivity_mem_expansionMeasure_image em)
  exact lt_of_lt_of_eq (expansionMeasure_pos em hS₁) hS₂

private def isFragment (em : ExpansionMeasure G) : Finset G → Prop :=
  fun S => em.toFun S = connectivity em

private lemma fragment_inter_of_inter_nonempty {em : ExpansionMeasure G} {S T : Finset G}
    (hS : isFragment em S) (hT : isFragment em T) (hST : (S ∩ T).Nonempty)
    : isFragment em (S ∩ T) := by
  unfold isFragment at *
  let κ := connectivity em
  have ub := em.submodularity S T
  rw [hS, hT, ← two_mul] at ub
  have lb₁ : κ ≤ em.toFun (S ∩ T) := connectivity_le em hST
  have lb₂ : κ ≤ em.toFun (S ∪ T) := connectivity_le em
    (Set.Nonempty.mono inter_subset_union hST)
  linarith

private lemma fragment_left_invariant {em : ExpansionMeasure G} {S : Finset G}
    (hS : isFragment em S) (x : G) : isFragment em (x •> S) :=
  Eq.trans (em.left_invariant S x) hS

private lemma fragment_nonempty {em : ExpansionMeasure G} {S : Finset G} (hS : isFragment em S)
    : S.Nonempty := by
  apply by_contradiction
  let κ := connectivity em
  rw [not_nonempty_iff_eq_empty]
  intro hS_empty
  have : κ = 0 := by
    unfold κ
    rw [← hS, hS_empty, em.toFun_def]
    rw [empty_mul, card_empty]
    ring1
  have : κ ≠ 0 := ne_of_gt (connectivity_pos em)
  contradiction

private def isAtom (em : ExpansionMeasure G) : Finset G → Prop :=
  fun S => isFragment em S ∧ ∀ (T : Finset G), isFragment em T → #S ≤ #T

private lemma atom_partition {em : ExpansionMeasure G} {S T : Finset G} (hS : isAtom em S)
    (hT : isAtom em T) : (S ∩ T).Nonempty → S = T := by
  intro hST₁
  obtain ⟨hS₁, hS₂⟩ := hS
  obtain ⟨hT₁, hT₂⟩ := hT
  have hST₂ := fragment_inter_of_inter_nonempty hS₁ hT₁ hST₁
  have hS₃ := eq_of_subset_of_card_le inter_subset_left (hS₂ _ hST₂)
  have hT₃ := eq_of_subset_of_card_le inter_subset_right (hT₂ _ hST₂)
  exact Eq.trans (Eq.symm hS₃) hT₃

private lemma atom_left_invariant {em : ExpansionMeasure G} {S : Finset G} (hS : isAtom em S)
    (x : G) : isAtom em (x •> S) :=
  ⟨fragment_left_invariant hS.1 x, by simpa only [card_smul_finset] using hS.2⟩

private lemma atom_nonempty {em : ExpansionMeasure G} {S : Finset G} (hS : isAtom em S)
    : S.Nonempty :=
  fragment_nonempty hS.1

private lemma atom_exists (em : ExpansionMeasure G) : ∃ N, isAtom em N := by
  have : {S : Finset G | isFragment em S}.Nonempty := by
    obtain ⟨S, _, (hS : isFragment em S)⟩ := (Set.mem_image _ _ _).mp
      (connectivity_mem_expansionMeasure_image em)
    exact ⟨S, hS⟩
  exact ⟨ Function.argminOn card {S : Finset G | isFragment em S} this,
    ⟨Function.argminOn_mem card _ this, fun T hT => Function.argminOn_le card _ hT⟩ ⟩

private def atomicSubgroup {em : ExpansionMeasure G} {N : Finset G} (hN : isAtom em N) {n : G}
    (hn : n ∈ N) : Subgroup G := by
  have one_mem_carrier : 1 ∈ n⁻¹ •> N := by
    apply smul_mem_smul_finset (a := n⁻¹) at hn
    simpa only [smul_eq_mul, inv_mul_cancel] using hn

  exact {
    carrier := n⁻¹ •> N

    one_mem' := by
      simpa only [← coe_smul_finset, mem_coe] using one_mem_carrier

    mul_mem' := by
      intro a b ha hb
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have ha' : a ∈ a • n⁻¹ • N := by
        apply smul_mem_smul_finset (a := a) at one_mem_carrier
        simpa only [smul_eq_mul, mul_one] using one_mem_carrier
      have : (n⁻¹ •> N ∩ a •> n⁻¹ •> N).Nonempty := by
        use a
        rw [mem_inter]
        exact ⟨ha, ha'⟩
      simpa only [← atom_partition (atom_left_invariant hN n⁻¹)
                  (atom_left_invariant (atom_left_invariant hN n⁻¹) a) this] using hb

    inv_mem' := by
      intro a ha
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul, inv_mul_cancel] at ha
      have ha' : a⁻¹ ∈ a⁻¹ •> n⁻¹ •> N := by
        apply smul_mem_smul_finset (a := a⁻¹) at one_mem_carrier
        simpa only [smul_eq_mul, mul_one] using one_mem_carrier
      have : (n⁻¹ •> N ∩ a⁻¹ •> n⁻¹ •> N).Nonempty := by
        use 1
        rw [mem_inter]
        exact ⟨one_mem_carrier, ha⟩
      simpa only [← atom_partition (atom_left_invariant hN n⁻¹)
                  (atom_left_invariant (atom_left_invariant hN n⁻¹) a⁻¹) this] using ha'
  }

private def atomicSubgroup_fintype {em : ExpansionMeasure G} {N : Finset G} (hN : isAtom em N)
    {n : G} (hn : n ∈ N) : Fintype (atomicSubgroup hN hn) := Fintype.ofFinset (n⁻¹ •> N) (by
  intro a
  let H := atomicSubgroup hN hn
  rw [← mem_coe, coe_smul_finset]
  change a ∈ H.carrier ↔ a ∈ H
  exact H.mem_carrier
)

/-- If `A` is such that there is `S` with `|A| ≤ |S|` such that `|S * A| ≤ (2 - ε) * |A|` for some
`0 < ε ≤ 1`, then there is a finite subgroup `H` of `G` of size `|H| ≤ (2 / ε - 1) * |A|` such that
`A` is covered by at most `2 / ε - 1` right cosets of `H`.
In particular, for `S = A`, we get a characterisation of sets of doubling less than `2 - ε`. -/
theorem doubling_lt_two {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hA : A.Nonempty)
    (hS : ∃ (S : Finset G) (_ : #S ≥ #A), #(S * A) ≤ (2 - ε) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H) (_ : Fintype.card H ≤ (2 / ε - 1) * #A) (Z : Finset G)
      (_ : #Z ≤ 2 / ε - 1), (A : Set G) ⊆ (H : Set G) * Z := by
  classical

  let K := 1 - ε / 2
  have hK : K < 1 := by unfold K; linarith [hε₀]

  let em := expansionMeasure hK hA
  let κ := connectivity em

  obtain ⟨N, hN⟩ := atom_exists em
  obtain ⟨n, hn⟩ := atom_nonempty hN

  let H := atomicSubgroup hN hn
  let fintypeH := atomicSubgroup_fintype hN hn
  have _ : Fintype ((n⁻¹ •> N : Set G)) := fintypeH

  obtain ⟨S, hS₁, hS₂⟩ := hS
  have calc₁ : em.toFun (Set.toFinset H) ≤ (1 - ε / 2) * #A := by
    calc
          em.toFun (Set.toFinset H)
      _ = em.toFun (n⁻¹ •> N : Set G).toFinset  := congr_arg _ (Set.toFinset_inj.mpr rfl)
      _ = em.toFun (n⁻¹ •> N) := by simp only [Set.toFinset_smul_set, toFinset_coe]
      _ = em.toFun N                            := em.left_invariant _ _
      _ = κ                                     := hN.1
      _ ≤ em.toFun S := connectivity_le em (card_pos.mp (lt_of_lt_of_le (card_pos.mpr hA) hS₁))
      _ = #(S * A) - K * #S                     := by rfl
      _ ≤ (2 - ε) * #A - (1 - ε / 2) * #A       := by gcongr; linarith
      _ = (1 - ε / 2) * #A                      := by linarith

  let Z := rightCosetRepresentingFinset H hA
  refine ⟨H, fintypeH, ?cardH, Z, ?cardZ, ?A_subset_HZ⟩

  case cardH =>
    have : ε / 2 * (Fintype.card H) ≤ (1 - ε / 2) * #A := by
      calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset := by simp only [Set.toFinset_card, SetLike.coe_sort_coe]
        _ = (1 - K) * #(H : Set G).toFinset := by ring1
        _ ≤ em.toFun (Set.toFinset H)     := em.lower_bound (Set.toFinset H)
        _ ≤ (1 - ε / 2) * #A              := calc₁
    rw [← mul_le_mul_left (by positivity)]
    have : ε / 2 * ((2 / ε - 1) * #A) = (1 - ε / 2) * #A := by field_simp; ring1
    linarith

  case cardZ =>
    have card_HA_bound : #(Set.toFinset H * A) ≤ (2 / ε - 1) * #(H : Set G).toFinset := by
      rw [← mul_le_mul_left (by change 0 < 1 - K; linarith [hK])]
      suffices (1 - K) * #(Set.toFinset H * A) ≤ (1 - ε / 2) * #(H : Set G).toFinset by
        apply le_of_eq_of_le' _ this; field_simp; ring1
      rw [sub_mul, one_mul, sub_le_iff_le_add]
      calc
            (#(Set.toFinset H * A) : ℝ)
        _ = K * #(H : Set G).toFinset + (#(Set.toFinset H * A) - K * #(H : Set G).toFinset)
              := by ring1
        _ = K * #(H : Set G).toFinset + em.toFun (Set.toFinset H)   := by rfl
        _ ≤ K * #(H : Set G).toFinset + (1 - ε / 2) * #A            := by linarith [calc₁]
        _ ≤ K *  #(H : Set G).toFinset + (1 - ε / 2) * #(Set.toFinset H * A)
              := by gcongr; linarith; simp only [Set.mem_toFinset, SetLike.mem_coe,
                                                  H.one_mem, subset_mul_right]
    calc
          (#Z : ℝ)
      _ = #(H : Set G).toFinset * #Z / #(H : Set G).toFinset          := by field_simp
      _ = #(Set.toFinset H * Z) / #(H : Set G).toFinset               := ?_
      _ = #(Set.toFinset H * A) / #(H : Set G).toFinset
            := by rw [mul_rightCosetRepresentingFinset_eq_mul_finset H hA]
      _ ≤ (2 / ε - 1) * #(H : Set G).toFinset / #(H : Set G).toFinset := by gcongr
      _ = 2 / ε - 1                                                   := by field_simp; ring1

    · nth_rw 1 [Set.toFinset_card]
      simp only [SetLike.coe_sort_coe]
      rw [← Nat.cast_mul, ← card_mul_rightCosetRepresentingFinset_eq_mul_card H hA]

  case A_subset_HZ =>
    rw [mul_rightCosetRepresentingFinset_eq_mul_set H hA]
    exact Set.subset_mul_right _ H.one_mem

end Finset
