/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify

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

/-! ### Doubling strictly less than `φ` -/

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


private lemma big_intersection_inv {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    2 * #A ≤ #((x⁻¹ • A) ∩ (y⁻¹ • A)) + #(A⁻¹ * A) := by
  have : #((x⁻¹ • A) ∪ (y⁻¹ • A)) ≤ #(A⁻¹ * A) := by
    apply card_le_card
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul (inv_mem_inv hx),
            smul_finset_subset_mul (inv_mem_inv hy)⟩
  apply (add_le_add_left this _).trans_eq'
  rw [card_inter_add_card_union]
  simp only [card_smul_finset, two_mul]


private lemma card_pairs_eq_card_smul_inter_smul {x y : G} :
    #{xy ∈ A ×ˢ A | xy.1 * (xy.2 : G)⁻¹ = x * y⁻¹} = #(x⁻¹ •> A ∩ y⁻¹ •> A) :=
  card_bij (s := {xy ∈ A ×ˢ A | xy.1 * (xy.2 : G)⁻¹ = x * y⁻¹})
    (t := (x⁻¹ •> A ∩ y⁻¹ •> A))
    (fun xy hxy => x⁻¹ * xy.1) (by
      intro xy hxy
      change x⁻¹ * xy.1 ∈ x⁻¹ •> A ∩ y⁻¹ •> A
      rw [mem_inter]
      rw [mem_filter, mem_product] at hxy
      constructor
      · exact smul_mem_smul_finset hxy.1.1
      · rw [mul_inv_eq_iff_eq_mul, mul_assoc,
            ← inv_mul_eq_iff_eq_mul] at hxy
        rw [hxy.2]
        exact smul_mem_smul_finset hxy.1.2
    ) (by
      intro xy hxy xy' hxy' h
      change x⁻¹ * xy.1 = x⁻¹ * xy'.1 at h
      apply mul_left_cancel at h
      rw [mem_filter] at hxy hxy'
      rw [← hxy.2, h] at hxy'
      apply And.right at hxy'
      apply mul_left_cancel at hxy'
      rw [inv_inj] at hxy'
      exact Prod.ext h (Eq.symm hxy')
    ) (by
      intro z hz
      rw [mem_inter, mem_smul_finset, mem_smul_finset] at hz
      obtain ⟨⟨a, ha, hxa⟩, b, hb, hyb⟩ := hz
      use (a, b)
      rw [smul_eq_mul] at hxa hyb
      use (by
        rw [mem_filter, mem_product]
        change (a ∈ A ∧ b ∈ A) ∧ a * b⁻¹ = x * y⁻¹
        constructor
        · exact ⟨ha, hb⟩
        · rw [← hyb] at hxa
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc,
              ← mul_inv_eq_iff_eq_mul] at hxa
          exact hxa
      )
    )

open goldenRatio in
/-- If `A` has doubling strictly less than `φ`, then `A * A⁻¹` is covered by
at most constant number of cosets of a finite subgroup of `G`. -/
theorem doubling_lt_golden_ratio {K : ℝ} (hK₁ : 1 < K) (hKφ : K < φ)
    (hA₁ : #(A⁻¹ * A) ≤ K * #A) (hA₂ : #(A * A⁻¹) ≤ K * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G) (_: #Z ≤ K * (2 - K) / (1- K * (K - 1))),
    A * A⁻¹ = (H : Set G) * Z := by
  classical

  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [goldConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [gold_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity

  have calc1 : (1 - K * (K - 1)) = (φ - K) * (K - ψ) := by
    rw [mul_sub, ← sub_add, mul_sub, sub_mul, sub_mul,
          ← sub_add, gold_mul_goldConj, sub_neg_eq_add]
    ring_nf
  rw [calc1]

  obtain rfl | emptyA := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp [const_pos.le]⟩

  let S := A * A⁻¹
  have id_in_S : 1 ∈ S := by obtain ⟨a, ha⟩ := emptyA; simpa using mul_mem_mul ha (inv_mem_inv ha)

  let H := stabilizer G S
  have HS_eq_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  have finH : Finite H := by
    simpa [H, ← stabilizer_coe_finset] using stabilizer_finite (by simpa [S]) S.finite_toSet
  cases nonempty_fintype H

  let preZ := {cH ∈ orbit Gᵐᵒᵖ (H : Set G) | (cH ∩ S : Set G).Nonempty}

  have fin_preZ : preZ.Finite := by
    let f_preZ : Set G → S := fun cH =>
      if h: cH ∈ preZ
      then ⟨Classical.choose h.2, by
        let s:= Classical.choose h.2
        apply And.right at h
        apply Classical.choose_spec at h
        apply Set.mem_of_mem_inter_right at h
        exact mem_coe.mp h
      ⟩ else ⟨(1 : G), id_in_S⟩

    have inj_f_preZ : Set.InjOn f_preZ preZ := by
      unfold Set.InjOn
      intro c₁ hc₁ c₂ hc₂ hc₁c₂
      unfold f_preZ at hc₁c₂
      simp_all
      let s := Classical.choose hc₁.2
      have s_in_c₁ : s ∈ c₁ := by
        apply And.right at hc₁
        apply Classical.choose_spec at hc₁
        exact Set.mem_of_mem_inter_left hc₁
      have s_in_c₂ : s ∈ c₂ := by
        apply And.right at hc₂
        apply Classical.choose_spec at hc₂
        rw [← hc₁c₂] at hc₂
        exact Set.mem_of_mem_inter_left hc₂
      rw [rightCoset_eq_of_mem hc₁.1 s_in_c₁, rightCoset_eq_of_mem hc₂.1 s_in_c₂]

    exact Finite.Set.finite_of_finite_image preZ inj_f_preZ

  let preZ' := fin_preZ.toFinset
  have elts_preZ'_nonempty (cH : Set G) (hcH : cH ∈ preZ') : (cH ∩ S).Nonempty := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf] at hcH
    exact hcH.2

  choose! chooseZ chooseZ_spec using elts_preZ'_nonempty
  let Z := Finset.image chooseZ preZ'

  have Z_subset_S : Z ⊆ S := by
    simpa [Z, Finset.image_subset_iff] using fun x hx ↦ (chooseZ_spec _ hx).2

  have S_eq_HZ : (S: Set G) = H * Z := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [mem_coe] at hx
      let cx := (H: Set G) <• x
      have cx_in_preZ' : cx ∈ preZ' := by
        rw [Set.Finite.mem_toFinset, Set.mem_setOf]
        constructor
        · simp_all [cx]
        · unfold Set.Nonempty
          use x
          constructor
          · rw [← one_mul x]
            exact mem_rightCoset x (one_mem H)
          · exact hx
      let z := chooseZ cx
      have z_in_cx : z ∈ cx := (chooseZ_spec _ cx_in_preZ').1
      have z_in_Z : z ∈ Z := by
        apply Finset.mem_image_of_mem
        exact cx_in_preZ'
      have x_in_Hz : x ∈ (H: Set G) <• z := by
        rw [mem_rightCoset_iff, SetLike.mem_coe]
        rw [mem_rightCoset_iff, SetLike.mem_coe] at z_in_cx
        apply inv_mem at z_in_cx
        simp_all
      exact Set.op_smul_set_subset_mul z_in_Z x_in_Hz
    · calc
        (H: Set G) * Z  ⊆ H * S   := by gcongr
                      _ ⊆ S       := by exact Eq.subset HS_eq_S

  have S_eq_HZ_finsets : S = Set.toFinset H * Z := by
    apply Subset.antisymm
    · intro s hs
      rw [← mem_coe, S_eq_HZ, Set.mem_mul] at hs
      obtain ⟨x, hx, y, hy, hxy⟩ := hs
      rw [← Set.mem_toFinset] at hx
      rw [mem_coe] at hy
      rw [← hxy]
      exact mul_mem_mul hx hy
    · intro xz hxz
      rw [mem_mul] at hxz
      obtain ⟨y, hy, z, hz, hyz⟩ := hxz
      rw [← mem_coe, S_eq_HZ, ← hyz]
      exact Set.mul_mem_mul (Set.mem_toFinset.mp hy) (mem_coe.mpr hz)

  refine ⟨H, inferInstance, Z, ?_, mod_cast S_eq_HZ⟩
  let r : G → ℕ := fun z => #{xy ∈ A ×ˢ A | xy.1 * (xy.2 : G)⁻¹ = z}

  have many_big_z : #{z ∈ S | (K - 1) * #A < r z} ≥ (φ - K) * (K - ψ) / (2 - K) * #A := by
    let k := #{z ∈ S | (K - 1) * #A < r z}

    have ineq1 : #A * #A ≤ ((2 - K) * k + K * (K - 1) * #A) * #A := by
      calc
        (#A : ℝ) * #A = #(A ×ˢ A) := by simp only [card_product, Nat.cast_mul]
                    _ = ∑ z ∈ S, r z                                            := ?eq1
                    _ = ∑ z ∈ {z ∈ S | (K - 1) * #A < r z}, r z
                          + ∑ z ∈ {z ∈ S | ¬ (K - 1) * #A < r z}, r z           := ?eq2
                    _ ≤ ∑ z ∈ {z ∈ S | (K - 1) * #A < r z}, r z
                          + ∑ z ∈ {z ∈ S | ¬ (K - 1) * #A < r z}, (K - 1) * #A  := ?eq3
                    _ ≤ ∑ z ∈ {z ∈ S | (K - 1) * #A < r z}, r z
                          + (K - 1) * #A * #{z ∈ S | ¬ (K - 1) * #A < r z}      := ?eq4
                    _ ≤ ∑ z ∈ {z ∈ S | (K - 1) * #A < r z}, r z
                          + (K - 1) * #A * (K * #A - k)                         := ?eq5
                    _ = ∑ z ∈ {z ∈ S | (K - 1) * #A < r z}, r z
                          + (K * (K - 1) * #A - (K - 1) * k) * #A               := by ring
                    _ ≤ ∑ z ∈ {z ∈ S | (K - 1) * #A < r z}, #A
                          + (K * (K - 1) * #A - (K - 1) * k) * #A               := ?eq6
                    _ = k * #A + (K * (K - 1) * #A - (K - 1) * k) * #A          := ?eq7
                    _ = ((2 - K) * k + K * (K - 1) * #A) * #A                   := by ring
      case eq1 =>
        unfold r
        rw [Nat.cast_inj]
        let f : G × G → G := fun xy => xy.1 * xy.2⁻¹
        exact card_eq_sum_card_fiberwise (by
          change Set.MapsTo f ((A ×ˢ A) : Finset (G × G)) (S : Finset G)
          intro xy hxy
          unfold f S
          rw [mem_coe] at hxy
          rw [mem_coe]
          exact mul_mem_mul (mem_product.mp hxy).1 (inv_mem_inv (mem_product.mp hxy).2)
        )
      case eq2 =>
        rw [← Nat.cast_add, Nat.cast_inj]
        exact Eq.symm (sum_filter_add_sum_filter_not S (fun z => (K - 1) * #A < r z) r)
      case eq3 =>
        push_cast
        gcongr with z hz
        exact not_lt.mp (mem_filter.mp hz).2
      case eq4 =>
        gcongr
        rw [card_eq_sum_ones {z ∈ S | ¬ (K - 1) * #A < r z}, Nat.cast_sum,
            mul_sum, mul_assoc, ← Nat.cast_mul, mul_one]
      case eq5 =>
        have : 0 ≤ K - 1 := by linarith
        gcongr
        simp only [le_sub_iff_add_le', k, ← Nat.cast_add, filter_card_add_filter_neg_card_eq_card]
        exact hA₂
      case eq6 =>
        gcongr with z hz
        apply card_le_card_of_injOn (fun xy => xy.1)
        · intro a ha
          rw [mem_filter, mem_product] at ha
          exact ha.1.1
        · unfold Set.InjOn
          intro xy hxy xy' hxy' h
          change xy.1 = xy'.1 at h
          rw [mem_coe, mem_filter] at hxy hxy'
          apply And.right at hxy
          rw [← hxy'.2, h] at hxy
          apply mul_left_cancel at hxy
          rw [inv_inj] at hxy
          exact Prod.ext h hxy
      case eq7 =>
        rw [add_right_cancel_iff, ← Nat.cast_mul, Nat.cast_inj]
        unfold k
        rw [card_eq_sum_ones {z ∈ S | (K - 1) * #A < r z}, sum_mul, one_mul]

    have ineq2 := le_of_mul_le_mul_right ineq1 <| by simpa

    have ineq3 : (φ - K) * (K - ψ) * #A ≤ (2 - K) * k := by
      rw [← calc1]
      linarith only [ineq2]

    apply le_of_mul_le_mul_of_pos_left ?_ hK₂'
    have : (2 - K) * ((φ - K) * (K - ψ) / (2 - K) * (#A: ℝ)) = (φ - K) * (K - ψ) * #A := by
      field_simp [hK₂'.ne']
      ring

    rw [this]
    exact ineq3


  have mem_H_of_big_z {z : G} : z ∈ S ∧ (r z) > (K - 1) * #A → (z : G) ∈ H := by
    intro hz
    obtain ⟨hz, hrz⟩ := hz
    rw [mem_stabilizer_iff]
    rw [← subset_iff_eq_of_card_le (card_smul_finset z S).ge]
    intro zw hzw
    rw [mem_smul_finset] at hzw
    obtain ⟨w, hw, hzw⟩ := hzw
    rw [smul_eq_mul] at hzw
    rw [← hzw]
    unfold S at hz hw
    simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hz hw
    obtain ⟨x, hx, y, hy, hxy⟩ := hz
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    rw [← hxy, ← hab]
    unfold r at hrz
    rw [← hxy, card_pairs_eq_card_smul_inter_smul] at hrz

    have big_w : #(a⁻¹ •> A ∩ b⁻¹ •> A) ≥ (2 - K) * #A := by
      have := big_intersection_inv ha hb
      rw [← Nat.cast_le (α := ℝ), Nat.cast_mul, Nat.cast_add, Nat.cast_two] at this
      linarith

    have big_w' : (2 - K) * #A ≤ #(A ∩ (b * a⁻¹)⁻¹ • A) := by
      apply big_w.trans
      rw [← card_smul_finset a]
      simp [smul_smul, smul_finset_inter]

    have big_z' : (K - 1) * #A < #(A ∩ (x * y⁻¹)⁻¹ • A) := by
      apply hrz.trans_le
      rw [← card_smul_finset y]
      simp [smul_smul, smul_finset_inter, inter_comm]

    have ⟨t, ht⟩ : ((A ∩ (x * y⁻¹)⁻¹ •> A) ∩ (A ∩ (b * a⁻¹)⁻¹ •> A)).Nonempty := by
      rw [← card_pos, ← Nat.cast_pos (α := ℝ)]
      have := card_inter_add_card_union (A ∩ (x * y⁻¹)⁻¹ • A) (A ∩ (b * a⁻¹)⁻¹ • A)
      rw [← Nat.cast_inj (R := ℝ), Nat.cast_add, Nat.cast_add] at this
      have : (#((A ∩ (x * y⁻¹)⁻¹ • A) ∪ (A ∩ (b * a⁻¹)⁻¹ • A)) : ℝ) ≤ #A := by
        rw [Nat.cast_le, ← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith

    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
        smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [mem_mul]
    exact ⟨x * y⁻¹ * t, by simp [ht, mul_assoc], ((a * b⁻¹)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩


  have big_H : Fintype.card H ≥ (φ - K) * (K - ψ) / (2 - K) * #A := by
    change Fintype.card (H: Set G) ≥ (φ - K) * (K - ψ) / (2 - K) * #A
    rw [← Set.toFinset_card]
    exact le_trans many_big_z (by
      change #(H : Set G).toFinset ≥ (#{z ∈ S | r z > (K - 1) * #A} : ℝ)
      simp only [Nat.cast_le]
      apply card_le_card
      intro z hz
      rw [Set.mem_toFinset]
      exact mem_H_of_big_z (mem_filter.mp hz)
    )

  have card_mul_eq_mul_card : #S = (Fintype.card H) * #Z := by
    change #S = (Fintype.card (H : Set G)) * #Z
    rw [← Set.toFinset_card]
    apply le_antisymm
    · calc
        #S = #((H : Set G).toFinset * Z)  := by exact congrArg card S_eq_HZ_finsets
          _≤ #(H: Set G).toFinset * #Z    := by exact card_mul_le

    rw [← card_product (Set.toFinset (H: Set G)) Z]
    apply card_le_card_of_injOn (fun xy => xy.1 * xy.2)
    · intro xz hxz
      rw [← mem_coe, S_eq_HZ]
      rw [mem_product] at hxz
      apply Set.mul_mem_mul
      · simp_all only [Set.mem_toFinset]
      · exact mem_coe.mpr hxz.2

    simp only [Set.InjOn, coe_product, Set.coe_toFinset, coe_image,
      Set.mem_prod, SetLike.mem_coe, and_imp, Prod.forall, Prod.mk.injEq, Z]
    rintro x y hx hy w t hw ht hxywt
    rw [Set.mem_image] at hy ht

    obtain ⟨cx, hcx1, hcx2⟩ := hy
    change (cx : Set G) ∈ preZ' at hcx1
    have hcx3 : y ∈ (cx : Set G) := by simpa [hcx2] using (chooseZ_spec _ hcx1).1
    rw [Set.Finite.mem_toFinset fin_preZ] at hcx1
    have hcx4 := rightCoset_eq_of_mem hcx1.1 hcx3

    obtain ⟨cw, hcw1, hcw2⟩ := ht
    change (cw : Set G) ∈ preZ' at hcw1
    have hcw3 : t ∈ (cw : Set G) := by simpa [hcw2] using (chooseZ_spec _ hcw1).1
    rw [Set.Finite.mem_toFinset fin_preZ] at hcw1
    have hcw4 := rightCoset_eq_of_mem hcw1.1 hcw3

    rw [← inv_mul_eq_iff_eq_mul, ← mul_assoc] at hxywt
    rw [← hxywt, op_mul, ← smul_smul,
        rightCoset_mem_rightCoset H (H.mul_mem (H.inv_mem hw) hx),
        ← hcx4] at hcw4

    rw [hcw4, hcx2] at hcw2
    rw [hcw2, mul_eq_right, inv_mul_eq_one] at hxywt
    exact ⟨(Eq.symm hxywt), hcw2⟩


  apply le_of_mul_le_mul_of_pos_left ?_ (by
    change (0 : ℝ) < Fintype.card H
    rw [← Nat.cast_zero, Nat.cast_lt]
    exact Finset.Nonempty.card_pos ⟨(1 : H), mem_univ 1⟩
  )

  rw [← Nat.cast_mul, ← card_mul_eq_mul_card]

  have K_ineq1 : 0 < (1 + √5) - 2 * K := by
    have _ : 0 < (1 + √5) / 2 - K := by simp [hKφ]
    linarith
  have K_ineq2 : 0 < K * 2 - (1 - √5) := by
    have _ : 0 < K - (1 - √5) / 2 := by simp [lt_trans goldConj_neg K_pos]
    linarith

  calc
    #S  ≤ K * #A                                                                  := by assumption
      _ = (φ - K) * (K - ψ) / (2 - K) * #A * (K * (2 - K) / ((φ - K) * (K - ψ)))  := ?_
      _ ≤ ↑(Fintype.card ↥H) * (K * (2 - K) / ((φ - K) * (K - ψ)))                := by gcongr

  · field_simp [ne_of_gt K_pos, ne_of_gt (sub_pos.mpr hKφ),
                ne_of_gt (sub_pos.mpr (lt_trans hKφ gold_lt_two)),
                ne_of_gt (sub_pos.mpr (lt_trans goldConj_neg K_pos))]
    ring

end Finset
