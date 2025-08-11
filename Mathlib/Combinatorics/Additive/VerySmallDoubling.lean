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
  --  of them and take for `Z'` a set of representatives of all these cosets; then we
  --  multiply every element of `Z'` with an appropriate element of `H` to make `Z ⊆ A`
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
--  property is actually not (explicitely) proved as it is not needed here; as far as I could check,
--  no such coset representing set is available in the library at this point, although it might be
--  useful independently of this section
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

  -- some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [goldConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [gold_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity

  have calc₁ : (1 - K * (K - 1)) = (φ - K) * (K - ψ) := by
    rw [mul_sub, ← sub_add, mul_sub, sub_mul, sub_mul,
        ← sub_add, gold_mul_goldConj, sub_neg_eq_add]
    ring_nf
  rw [calc₁]

  -- we need to consider the trivial case A = ∅ separately
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp only [coe_empty, inv_empty, Set.mul_empty,
      Subgroup.coe_bot, card_empty, CharP.cast_eq_zero, const_pos.le, exists_const]⟩

  -- the main case A ≠ ∅
  let S := A * A⁻¹
  have S_nonempty : S.Nonempty := ⟨1, by
    obtain ⟨a, ha⟩ := A_nonempty
    simpa only [mul_inv_cancel] using mul_mem_mul ha (inv_mem_inv ha)⟩

  let H := stabilizer G S
  have finH : Finite H := by
    simpa only [H, mem_stabilizer_iff, ← stabilizer_coe_finset]
      using stabilizer_finite (by simpa only [coe_mul, coe_inv, Set.mul_nonempty, coe_nonempty,
        Set.nonempty_inv, and_self, S]) S.finite_toSet
  cases nonempty_fintype H

  let Z := rightCosetRepresentingFinset H S_nonempty

  have S_eq_HZ : S = (H : Set G) * Z := Eq.symm <| Eq.trans
    (mul_rightCosetRepresentingFinset_eq_mul_set H S_nonempty)
    (by simp only [← stabilizer_coe_finset, stabilizer_mul_self, H])
  have S_eq_HZ_finset : S = Set.toFinset H * Z := by
    simpa only [← coe_inj, coe_mul, Set.coe_toFinset]
      using S_eq_HZ

  -- it remains to prove that Z is not "too big"
  refine ⟨H, inferInstance, Z, ?_, mod_cast S_eq_HZ⟩

  -- function r counts the number of representations of z ∈ S as xy⁻¹ for x, y ∈ A
  let r : G → ℕ := fun z => #{xy ∈ A ×ˢ A | xy.1 * (xy.2 : G)⁻¹ = z}

  -- first we show that "a lot of" z ∈ S have many representations as given by r
  have many_big_z : #{z ∈ S | (K - 1) * #A < r z} ≥ (φ - K) * (K - ψ) / (2 - K) * #A := by
    let k := #{z ∈ S | (K - 1) * #A < r z}

    have ineq₁ : #A * #A ≤ ((2 - K) * k + K * (K - 1) * #A) * #A := by
      calc
            (#A : ℝ) * #A
        _ = #(A ×ˢ A) := by simp only [card_product, Nat.cast_mul]
        _ = ∑ z ∈ S, r z                                            := ?eq₁
        _ = ∑ z ∈ S with (K - 1) * #A < r z, r z + ∑ z ∈ S with ¬ (K - 1) * #A < r z, r z := ?eq₂
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, r z
              + ∑ z ∈ S with ¬ (K - 1) * #A < r z, (K - 1) * #A     := ?eq₃
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, r z
              + (K - 1) * #A * #{z ∈ S | ¬ (K - 1) * #A < r z}      := ?eq₄
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, r z + (K - 1) * #A * (K * #A - k)  := ?eq₅
        _ = ∑ z ∈ S with (K - 1) * #A < r z, r z + (K * (K - 1) * #A - (K - 1) * k) * #A := by ring
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, #A + (K * (K - 1) * #A - (K - 1) * k) * #A := ?eq₆
        _ = k * #A + (K * (K - 1) * #A - (K - 1) * k) * #A          := ?eq₇
        _ = ((2 - K) * k + K * (K - 1) * #A) * #A                   := by ring
      case eq₁ =>
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
      case eq₂ =>
        rw [← Nat.cast_add, Nat.cast_inj]
        exact Eq.symm (sum_filter_add_sum_filter_not S (fun z => (K - 1) * #A < r z) r)
      case eq₃ =>
        push_cast
        gcongr with z hz
        exact not_lt.mp (mem_filter.mp hz).2
      case eq₄ =>
        gcongr
        rw [card_eq_sum_ones {z ∈ S | ¬ (K - 1) * #A < r z}, Nat.cast_sum,
            mul_sum, mul_assoc, ← Nat.cast_mul, mul_one]
      case eq₅ =>
        have : 0 ≤ K - 1 := by linarith
        gcongr
        simp only [le_sub_iff_add_le', k, ← Nat.cast_add, filter_card_add_filter_neg_card_eq_card]
        exact hA₂
      case eq₆ =>
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
      case eq₇ =>
        rw [add_right_cancel_iff, ← Nat.cast_mul, Nat.cast_inj]
        unfold k
        rw [card_eq_sum_ones {z ∈ S | (K - 1) * #A < r z}, sum_mul, one_mul]

    have ineq₂ := le_of_mul_le_mul_right ineq₁ <| by simpa only [Nat.cast_pos, card_pos]

    have ineq₃ : (φ - K) * (K - ψ) * #A ≤ (2 - K) * k := by
      rw [← calc₁]
      linarith only [ineq₂]

    apply le_of_mul_le_mul_of_pos_left ?_ hK₂'
    have : (2 - K) * ((φ - K) * (K - ψ) / (2 - K) * (#A: ℝ)) = (φ - K) * (K - ψ) * #A := by
      field_simp [hK₂'.ne']
      ring

    rw [this]
    exact ineq₃

  -- here we show that those z ∈ S that have "a lot of" representations
  --  are actually in H
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
      simp only [smul_finset_inter, smul_smul, mul_inv_cancel, one_smul,
                  mul_inv_rev, inv_inv, le_refl]

    have big_z' : (K - 1) * #A < #(A ∩ (x * y⁻¹)⁻¹ • A) := by
      apply hrz.trans_le
      rw [← card_smul_finset y]
      simp only [smul_finset_inter, smul_smul, mul_inv_cancel, one_smul,
                  inter_comm, mul_inv_rev, inv_inv, le_refl]

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
    exact ⟨x * y⁻¹ * t, by simp only [mul_assoc, ht], ((a * b⁻¹)⁻¹ * t)⁻¹,
      by simp only [mul_inv_rev, inv_inv, mul_assoc, mem_inv', ht, mul_inv_cancel_left, and_self]⟩

  -- now we show that H is relatively big, which will then
  --  make Z relatively small once we show that #S = #H * #Z
  --  (which is already clear because Hz for z ∈ Z are all different
  --  and hence disjoint cosets)
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

  have card_S_eq_card_H_mul_card_Z : #S = (Fintype.card H) * #Z := by
    rw [← card_mul_rightCosetRepresentingFinset_eq_mul_card H S_nonempty]
    exact congr_arg _ S_eq_HZ_finset

  -- we have all the claims that we need in order to prove that
  --  Z is not too large, we will just multiply both sides with #H
  --  and use the claims
  apply le_of_mul_le_mul_of_pos_left ?_ (by
    change (0 : ℝ) < Fintype.card H
    rw [← Nat.cast_zero, Nat.cast_lt]
    exact Finset.Nonempty.card_pos ⟨(1 : H), mem_univ 1⟩
  )

  rw [← Nat.cast_mul, ← card_S_eq_card_H_mul_card_Z]

  have K_ineq₁ : 0 < (1 + √5) - 2 * K := by
    have _ : 0 < (1 + √5) / 2 - K := by simp only [sub_pos, hKφ]
    linarith
  have K_ineq₂ : 0 < K * 2 - (1 - √5) := by
    have _ : 0 < K - (1 - √5) / 2 := by simp only [sub_pos, lt_trans goldConj_neg K_pos]
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
