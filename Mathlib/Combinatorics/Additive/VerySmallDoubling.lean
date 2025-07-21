/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify
import Mathlib.Data.Real.Basic
--import Mathlib.Data.Real.Archimedean
--import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Instances.Real.Lemmas

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

private structure ExpansionMeasure (G : Type*) [Group G] [DecidableEq G] where
  K : ℝ
  A : Finset G
  toFun : Finset G → ℝ
  left_invariant : ∀ (S : Finset G) (x : G), toFun (x •> S) = toFun S
  submodularity : ∀ (S : Finset G) (T : Finset G),
      toFun (S ∩ T) + toFun (S ∪ T) ≤ toFun S + toFun T

private def expansionMeasure {G : Type*} [Group G] [DecidableEq G] (K : ℝ)
    (A : Finset G) : ExpansionMeasure G := {
  K := K
  A := A
  toFun := fun S => #(S * A) - K * #S
  left_invariant := fun _ _ => by simp_all only [card_smul_finset, smul_mul_assoc]
  submodularity := by
    intro S T
    have eq1 : K * #(S ∩ T) + K * #(S ∪ T) = K * #S + K * #T := by
      simpa [← mul_add, ← Nat.cast_add] using Or.inl (card_inter_add_card_union S T)
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
}


-- def expansionMeasure (K : ℝ) (B : Finset G) : Finset G → ℝ := fun S => #(S * B) - K * #S

-- lemma expansionMeasure_left_invariant (K : ℝ) (B : Finset G) (S : Finset G) (x : G) :
--     expansionMeasure K B (x •> S) = expansionMeasure K B S := sorry

theorem doubling_lt_two {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hA : A.Nonempty)
    (hS : ∃ (S : Finset G) (_ : #S ≥ #A), #(S * A) ≤ (2 - ε) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H) (_ : Fintype.card H ≤ (2 / ε - 1) * #A) (Z : Finset G)
      (_ : #Z ≤ 2 / ε - 1), (A : Set G) ⊆ (H : Set G) * Z := by
  let K := 1 - ε / 2
  let em := expansionMeasure K A
  have min_em (S : Finset G) : ε / 2 * #S ≤ em.toFun S := by
    change ε / 2 * #S ≤ #(S * A) - K * #S
    obtain ⟨a, ha⟩ := hA
    calc
      ε / 2 * #S  = #S - (1 - ε / 2) * #S := by ring1
                _ = #S - K * #S           := by rfl
                _ = #(S * {a}) - K * #S   := by norm_num
                _ ≤ #(S * A)  - K * #S    := ?_
    · apply sub_le_sub_right
      norm_cast
      apply card_le_card
      exact mul_subset_mul_left (singleton_subset_iff.mpr ha)
  have em_pos {S : Finset G} (hS : S.Nonempty) : 0 < em.toFun S := by
    calc
      0 < ε / 2 * #S := ?_
      _ ≤ em.toFun S := min_em S
    · simp_all only [ge_iff_le, exists_prop, div_pos_iff_of_pos_left, Nat.ofNat_pos,
        mul_pos_iff_of_pos_left, Nat.cast_pos, card_pos]

  let im_em := em.toFun '' {S : Finset G | S.Nonempty}
  have nonempty_im_em : im_em.Nonempty := by
    use em.toFun {1}
    aesop
  have bddBelow_im_em : BddBelow im_em := by
    use 0
    intro c hc
    obtain ⟨S, (hS₁ : S.Nonempty), hS₂⟩ := hc
    simpa only [hS₂] using le_of_lt (em_pos hS₁)

  let κ := sInf im_em
  have κ_min {S : Finset G} (hS : S.Nonempty) : κ ≤ em.toFun S := by
    apply csInf_le bddBelow_im_em
    exact Set.mem_image_of_mem em.toFun hS
  have κ_nonneg : 0 ≤ κ := by
    apply le_csInf ⟨em.toFun {1}, Set.mem_image_of_mem em.toFun (by show {1} ∈ {S : Finset G | S.Nonempty}; sorry)⟩

    sorry
  have κ_mem_im_em : κ ∈ im_em := by
    apply by_contradiction
    rw [Set.mem_image]
    push_neg
    intro h
    let t := Nat.floor (2 * (κ + 1) / ε)
    have largeT {T : Finset G} (hT : t < #T) : κ + 1 < em.toFun T := by
      rw [Nat.lt_iff_add_one_le] at hT
      calc
            κ + 1
        _ = (κ + 1) / (2 * (κ + 1) / ε) * (2 * (κ + 1) / ε)
              := Eq.symm (div_mul_cancel₀ _ (by positivity))
        _ < (κ + 1) / (2 * (κ + 1) / ε) * (t + 1)
              := by gcongr; exact Nat.lt_floor_add_one (2 * (κ + 1) / ε)
        _ = ε / 2 * (t + 1)   := by field_simp; ring1
        _ ≤ ε / 2 * #T        := by gcongr; rw [← Nat.cast_add_one, Nat.cast_le]; exact hT
        _ ≤ em.toFun T        := min_em T
    let im_smallT := (((Icc #A (t * #A)).map Nat.castEmbedding : Finset ℝ)
                      - K • ((Icc 1 t).map Nat.castEmbedding)).filter (fun x => κ < x)
    have smallT {T : Finset G} (hT₁ : T.Nonempty) (hT₂ : #T ≤ t) : em.toFun T ∈ im_smallT := by
      rw [mem_filter]
      constructor
      · apply sub_mem_sub
        · apply mem_map_of_mem
          rw [mem_Icc]
          constructor
          obtain ⟨x, hx⟩ := hT₁
          · calc
                  #A
              _ = #(x •> A)   := Eq.symm (card_smul_finset x A)
              _ ≤ #(T •> A)   := card_le_card (smul_finset_subset_smul hx)
              _ ≤ #(T * A)    := by simp
          · calc
                  #(T * A)
              _ ≤ #T * #A     := card_mul_le
              _ ≤ t * #A      := Nat.mul_le_mul_right (#A) hT₂
        · rw [← smul_eq_mul]
          apply smul_mem_smul_finset
          apply mem_map_of_mem
          rw [mem_Icc]
          exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (card_pos.mpr hT₁)), hT₂⟩
      · exact lt_of_le_of_ne (κ_min hT₁) (Ne.symm (h T hT₁))
    let k := (im_smallT ∪ {κ + 1}).min' (by finiteness)
    have : κ < k := by
      rw [lt_min'_iff _ (by finiteness)]
      intro x hx
      rw [mem_union] at hx
      cases hx with
      | inl hx =>
        exact (Finset.mem_filter.mp hx).2
      | inr hx =>
        rw [mem_singleton] at hx
        linarith
    obtain ⟨s, hs₁, hs₂⟩ := (csInf_lt_iff bddBelow_im_em nonempty_im_em).mp this
    obtain ⟨S, (hS₁ : S.Nonempty), hS₂⟩ := (Set.mem_image _ _ _).mp hs₁
    have : em.toFun S ≤ κ + 1 := by
      calc
            em.toFun S
        _ = s           := hS₂
        _ ≤ k           := le_of_lt hs₂
        _ ≤ κ + 1       := min'_le _ _ (by simp)
    have := not_lt.mp (mt largeT (not_lt.mpr this))
    apply smallT hS₁ at this
    rw [hS₂] at this
    exact (and_not_self_iff (s ∈ im_smallT)).mp ⟨this,
      (notMem_union.mp (mt (min'_le (im_smallT ∪ {κ + 1}) _) (not_le.mpr hs₂))).1⟩
  have κ_pos : 0 < κ := by
    obtain ⟨S, (hS₁ : S.Nonempty), hS₂⟩ := (Set.mem_image _ _ _).mp κ_mem_im_em
    exact lt_of_lt_of_eq (em_pos hS₁) hS₂

  let isFragment (S : Finset G) : Prop := em.toFun S = κ
  have fragment_inter {S T : Finset G} (hS : isFragment S) (hT : isFragment T)
      (hST : (S ∩ T).Nonempty) : isFragment (S ∩ T) := by
    unfold isFragment at *
    have ub := em.submodularity S T
    rw [hS, hT, ← two_mul] at ub
    have lb₁ : κ ≤ em.toFun (S ∩ T) := κ_min hST
    have lb₂ : κ ≤ em.toFun (S ∪ T) := κ_min (Set.Nonempty.mono inter_subset_union hST)
    linarith
  have fragment_left_invariance {S : Finset G} (hS : isFragment S)
      (x : G) : isFragment (x •> S) := Eq.trans (em.left_invariant S x) hS
  have fragment_nonempty {S : Finset G} (hS : isFragment S) : S.Nonempty := by
    apply by_contradiction
    rw [not_nonempty_iff_eq_empty]
    intro hS_empty
    have : κ = 0 := by
      rw [← hS, hS_empty]
      change #(∅ * A) - K * #∅ = 0
      rw [empty_mul, card_empty]
      ring1
    rw [this, lt_self_iff_false] at κ_pos
    assumption

  let isAtom (S : Finset G) : Prop := isFragment S ∧ ∀ (T : Finset G), isFragment T → #S ≤ #T
  have atom_partition {S T : Finset G} (hS : isAtom S) (hT : isAtom T) :
      (S ∩ T).Nonempty → S = T := by
    intro hST₁
    obtain ⟨hS₁, hS₂⟩ := hS
    obtain ⟨hT₁, hT₂⟩ := hT
    have hST₂ := fragment_inter hS₁ hT₁ hST₁
    have hS₃ := eq_of_subset_of_card_le inter_subset_left (hS₂ _ hST₂)
    have hT₃ := eq_of_subset_of_card_le inter_subset_right (hT₂ _ hST₂)
    exact Eq.trans (Eq.symm hS₃) hT₃
  have atom_left_invariance {S : Finset G} (hS : isAtom S) (x : G) : isAtom (x •> S) := by
    unfold isAtom
    constructor
    · exact fragment_left_invariance hS.1 x
    · simpa only [card_smul_finset] using hS.2
  have atom_nonempty {S : Finset G} (hS : isAtom S) : S.Nonempty := fragment_nonempty hS.1

  let fragments := {S : Finset G | isFragment S}
  have fragments_nonempty : fragments.Nonempty := by
    obtain ⟨S, _, (hS : isFragment S)⟩ := (Set.mem_image _ _ _).mp κ_mem_im_em
    exact ⟨S, hS⟩
  let N := Function.argminOn card fragments fragments_nonempty
  have N_atom : isAtom N := ⟨Function.argminOn_mem card _ fragments_nonempty,
    fun T hT => Function.argminOn_le card _ hT⟩

  obtain ⟨n, hn⟩ := atom_nonempty N_atom

  have one_mem_n1N : 1 ∈ n⁻¹ •> N := by
    apply smul_mem_smul_finset (a := n⁻¹) at hn
    simpa [smul_eq_mul, inv_mul_cancel] using hn
  let H : Subgroup G := {
    carrier := n⁻¹ •> N
    one_mem' := by
      simpa only [← coe_smul_finset, mem_coe] using one_mem_n1N
    mul_mem' := by
      intro a b ha hb
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have ha' : a ∈ a • n⁻¹ • N := by
        apply smul_mem_smul_finset (a := a) at one_mem_n1N
        simpa only [smul_eq_mul, mul_one] using one_mem_n1N
      have : (n⁻¹ •> N ∩ a •> n⁻¹ •> N).Nonempty := by
        use a
        rw [mem_inter]
        exact ⟨ha, ha'⟩
      simpa only [← atom_partition (atom_left_invariance N_atom n⁻¹)
                  (atom_left_invariance (atom_left_invariance N_atom n⁻¹) a) this] using hb
    inv_mem' := by
      intro a ha
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul, inv_mul_cancel] at ha
      have ha' : a⁻¹ ∈ a⁻¹ •> n⁻¹ •> N := by
        apply smul_mem_smul_finset (a := a⁻¹) at one_mem_n1N
        simpa only [smul_eq_mul, mul_one] using one_mem_n1N
      have : (n⁻¹ •> N ∩ a⁻¹ •> n⁻¹ •> N).Nonempty := by
        use 1
        rw [mem_inter]
        exact ⟨one_mem_n1N, ha⟩
      simpa only [← atom_partition (atom_left_invariance N_atom n⁻¹)
                  (atom_left_invariance (atom_left_invariance N_atom n⁻¹) a⁻¹) this] using ha'
  }
  have fintypeH : Fintype H := Fintype.ofFinset (n⁻¹ •> N) (by
    intro a
    constructor
    · intro ha
      rw [SetLike.mem_coe, ← Subgroup.mem_carrier]
      change a ∈ n⁻¹ •> (N : Set G)
      simpa only [← coe_smul_finset, mem_coe] using ha
    · intro ha
      rw [SetLike.mem_coe, ← Subgroup.mem_carrier] at ha
      change a ∈ n⁻¹ •> (N : Set G) at ha
      simpa only [← coe_smul_finset, mem_coe] using ha
  )

  obtain ⟨S, hS₁, hS₂⟩ := hS

  refine ⟨H, fintypeH, ?cardH, S, ?cardS, ?A_subset_HS⟩

  case cardH =>
    have : ε / 2 * (Fintype.card H) ≤ (1 - ε / 2) * #A := by
      calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset         := by simp [Set.toFinset_card]
        _ = ε / 2 * #(n⁻¹ •> N : Set G).toFinset  := by abel
        _ = ε / 2 * #(n⁻¹ •> N)                   := by simp
        _ ≤ em.toFun (n⁻¹ •> N)                   := min_em (n⁻¹ •> N)
        _ = em.toFun N                            := em.left_invariant N n⁻¹
        _ = κ                                     := N_atom.1
        _ ≤ em.toFun S := κ_min (card_pos.mp (lt_of_lt_of_le (card_pos.mpr hA) hS₁))
        _ = #(S * A) - K * #S                     := by rfl
        _ ≤ (2 - ε) * #A - (1 - ε / 2) * #A       := by gcongr; linarith
        _ = (1 - ε / 2) * #A                      := by linarith
    rw [← mul_le_mul_left (by change 0 < ε / 2; positivity)]
    have : ε / 2 * ((2 / ε - 1) * #A) = (1 - ε / 2) * #A := by field_simp; ring1
    linarith

  · sorry
  · sorry



end Finset
