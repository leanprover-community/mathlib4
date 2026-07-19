/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Combinatorics.Additive.Convolution
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Qify

/-!
# Sets with very small doubling

For a finset `A` in a group, its *doubling* is `#(A * A) / #A`. This file characterises sets with
* no doubling as the sets which are either empty or translates of a subgroup.
  For the converse, use the existing facts from the pointwise API: `∅ ^ 2 = ∅` (`Finset.empty_pow`),
  `(a • H) ^ 2 = a ^ 2 • H ^ 2 = a ^ 2 • H` (`smul_pow`, `coe_set_pow`).
* doubling strictly less than `3 / 2` as the sets that are contained in a coset of a subgroup of
  size strictly less than `3 / 2 * #A`.
* doubling strictly less than `φ` as the set `A` such that `A * A⁻¹` is covered by at most some
  constant (depending only on the doubling) number of cosets of a finite subgroup of `G`.

## TODO

* Do we need versions stated using the doubling constant (`Finset.mulConst`)?
* Add characterisation of sets with doubling ≤ 2 - ε. See
  https://terrytao.wordpress.com/2011/03/12/hamidounes-freiman-kneser-theorem-for-nonabelian-groups.

## References

* [*An elementary non-commutative Freiman theorem*, Terence Tao](https://terrytao.wordpress.com/2009/11/10/an-elementary-non-commutative-freiman-theorem)
* [*Introduction to approximate groups*, Matthew Tointon][tointon2020]
-/

@[expose] public section

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {K : ℝ} {A B S : Finset G} {a b c d x y : G}

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
    · simpa [← smul_A ha, mul_smul] using! smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha, inv_smul_smul]

/-- A non-empty set with no doubling is the left translate of its stabilizer. -/
@[to_additive /-- A non-empty set with no doubling is the left-translate of its stabilizer. -/]
lemma smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A := (smul_stabilizer_of_no_doubling_aux hA ha).1

/-- A non-empty set with no doubling is the right translate of its stabilizer. -/
@[to_additive /-- A non-empty set with no doubling is the right translate of its stabilizer. -/]
lemma op_smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    (stabilizer G A : Set G) <• a = A := (smul_stabilizer_of_no_doubling_aux hA ha).2

/-! ### Doubling strictly less than `3 / 2` -/

private lemma big_intersection (ha : a ∈ B) (hb : b ∈ B) :
    2 * #A ≤ #((a • A) ∩ (b • A)) + #(B * A) := by
  have : #((a • A) ∪ (b • A)) ≤ #(B * A) := by
    gcongr
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul ha, smul_finset_subset_mul hb⟩
  grw [← this, card_inter_add_card_union]
  simp [card_smul_finset, two_mul]

private lemma le_card_smul_inter_smul (hA : #(B * A) ≤ K * #A) (ha : a ∈ B) (hb : b ∈ B) :
    (2 - K) * #A ≤ #((a • A) ∩ (b • A)) := by
  have : 2 * (#A : ℝ) ≤ #(a •> A ∩ b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

private lemma lt_card_smul_inter_smul (hA : #(B * A) < K * #A) (ha : a ∈ B) (hb : b ∈ B) :
    (2 - K) * #A < #((a • A) ∩ (b • A)) := by
  have : 2 * (#A : ℝ) ≤ #(a •> A ∩ b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

private lemma le_card_mul_inv_eq (hA : #(B * A) ≤ K * #A) (hx : x ∈ B⁻¹ * B) :
    (2 - K) * #A ≤ #{ab ∈ A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using le_card_smul_inter_smul hA ha hb

private lemma lt_card_mul_inv_eq (hA : #(B * A) < K * #A) (hx : x ∈ B⁻¹ * B) :
    (2 - K) * #A < #{ab ∈ A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using lt_card_smul_inter_smul hA ha hb

private lemma mul_inv_eq_inv_mul_of_doubling_lt_two_aux (h : #(A * A) < 2 * #A) :
    A⁻¹ * A ⊆ A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv, exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A ∩ y • A).Nonempty := by
    simpa using lt_card_smul_inter_smul (K := 2) (mod_cast h) hx hy
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hzxwy, inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_inv_eq_inv_mul_of_doubling_lt_two_aux` a goal?
-- i.e. wlog in the target rather than hypothesis
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
  by_contra! rfl
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
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe, and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ x (hx : x ∈ A) y (hy : y ∈ A) : (1 / 2 : ℚ) * #A < #(x • A ∩ y • A) := by
      convert! lt_card_smul_inter_smul (by simpa using Rat.cast_strictMono (K := ℝ) h) hx hy
      norm_num
      simp [← Rat.cast_lt (K := ℝ)]
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
  simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    mem_coe]
  infer_instance

private lemma weak_invMulSubgroup_bound (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) < 2 * #A := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ a (ha : a ∈ A⁻¹ * A) : (1 / 2 : ℚ) * #A < #{xy ∈ A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    convert! lt_card_mul_inv_eq (by simpa using Rat.cast_strictMono (K := ℝ) h) ha
    norm_num
    simp [← Rat.cast_lt (K := ℝ)]
  have h₂ : ∀ x ∈ A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x ∈ A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : ℚ) * #A) * #(A⁻¹ * A) < (#A : ℚ) ^ 2 := by
    rw [← Nat.cast_pow, sq, ← card_product, card_eq_sum_card_fiberwise h₂, Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₁).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
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
      _ ⊆ A * (A⁻¹ * A) * A⁻¹ := by grw [smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc, ← invMulSubgroup_eq_mul_inv _ h, mul_assoc,
          ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe, invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) ⊆ A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ ⊆ A⁻¹ * ((A⁻¹ * A) * A) := by grw [op_smul_finset_subset_mul (by simpa)]
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
  · simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_coe, ← Nat.card_eq_fintype_card, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

/-! ### Doubling strictly less than `φ` -/

omit [DecidableEq G] in
private lemma op_smul_eq_iff_mem {H : Subgroup G} {c : Set G} {x : G}
    (hc : c ∈ orbit Gᵐᵒᵖ (H : Set G)) : x ∈ c ↔ H <• x = c := by
  refine ⟨fun hx => ?_, fun hx =>
    by simp only [← hx, mem_rightCoset_iff, mul_inv_cancel, SetLike.mem_coe, one_mem]⟩
  obtain ⟨⟨a⟩, rfl⟩ := hc
  change _ = _ <• _
  rw [eq_comm, smul_eq_iff_eq_inv_smul, ← op_inv, op_smul_op_smul, rightCoset_mem_rightCoset]
  rwa [← op_smul_eq_mul, op_inv, ← SetLike.mem_coe, ← Set.mem_smul_set_iff_inv_smul_mem]

omit [DecidableEq G] in
private lemma op_smul_eq_op_smul_iff_mem {H : Subgroup G} {x y : G} :
    x ∈ (H : Set G) <• y ↔ (H : Set G) <• x = H <• y := op_smul_eq_iff_mem (mem_orbit _ _)

omit [DecidableEq G] in
/-- Given a finite subset `A` of a group `G` and a subgroup `H ≤ G`, there exists a subset `Z ⊆ A`
such that `H * Z = H * A` and the cosets `Hz` are disjoint as `z` runs over `Z`. -/
private lemma exists_subset_mul_eq_mul_injOn (H : Subgroup G) (A : Finset G) :
    ∃ Z ⊆ A, (H : Set G) * Z = H * A ∧ (Z : Set G).InjOn ((H : Set G) <• ·) := by
  obtain ⟨Z, hZA, hZinj, hHZA⟩ :=
    ((A : Set G).surjOn_image ((H : Set G) <• ·)).exists_subset_injOn_image_eq
  lift Z to Finset G using A.finite_toSet.subset hZA
  refine ⟨Z, mod_cast hZA, ?_, hZinj⟩
  simpa [-SetLike.mem_coe, Set.iUnion_op_smul_set] using congr(Set.sUnion $hHZA)

private lemma card_mul_eq_mul_card_of_injOn_opSMul {H : Subgroup G} [Fintype H]
    {Z : Finset G} (hZ : (Z : Set G).InjOn ((H : Set G) <• ·)) :
    Fintype.card H * #Z = #(Set.toFinset H * Z) := by
  rw [card_mul_iff.2]
  · simp
  rintro ⟨h₁, z₁⟩ ⟨hh₁, hz₁⟩ ⟨h₂, z₂⟩ ⟨hh₂, hz₂⟩ h
  simp only [Set.coe_toFinset, SetLike.mem_coe] at *
  obtain rfl := hZ hz₁ hz₂ <| (rightCoset_eq_iff _).2 <| by
    simpa [eq_inv_mul_iff_mul_eq.2 h, mul_assoc] using mul_mem (inv_mem hh₂) hh₁
  simp_all

set_option linter.flexible false in -- simp followed by positivity
open goldenRatio in
/-- If `A` has doubling `K` strictly less than `φ`, then `A * A⁻¹` is covered by
at most a constant number of cosets of a finite subgroup of `G`. -/
theorem doubling_lt_golden_ratio (hK₁ : 1 < K) (hKφ : K < φ)
    (hA₁ : #(A⁻¹ * A) ≤ K * #A) (hA₂ : #(A * A⁻¹) ≤ K * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      #Z ≤ (2 - K) * K / ((φ - K) * (K - ψ)) ∧ (H : Set G) * Z = A * A⁻¹ := by
  -- Some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [Real.goldenConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [Real.goldenRatio_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity
  -- We dispatch the trivial case `A = ∅` separately.
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp; positivity⟩
  -- In the case where `A` is non-empty, we consider the set `S := A * A⁻¹` and its stabilizer `H`.
  let S := A * A⁻¹
  let H := stabilizer G S
  -- `S` is finite and non-empty (because `A` is), and therefore `H` is finite too.
  have S_nonempty : S.Nonempty := by simpa [S]
  have : Finite H := by simpa [H] using! stabilizer_finite (by simpa) S.finite_toSet
  cases nonempty_fintype H
  -- By definition, `H * S = S`.
  have H_mul_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  -- Since `H` is a subgroup, find a finite set `Z ⊆ S` such that `H * Z = S` and `|H| * |Z| = |S|`.
  obtain ⟨Z, hZ⟩ := exists_subset_mul_eq_mul_injOn H S
  have H_mul_Z : (H : Set G) * Z = S := by simp [hZ.2.1, H_mul_S]
  have H_toFinset_mul_Z : Set.toFinset H * Z = S := by simpa [← Finset.coe_inj]
  have card_H_mul_card_Z : Fintype.card H * #Z = #S := by
    simpa [card_mul_eq_mul_card_of_injOn_opSMul hZ.2.2] using! congr_arg _ H_toFinset_mul_Z
  -- It remains to show that `|Z| ≤ C(K)` for some `C(K)` depending only on `K`.
  refine ⟨H, inferInstance, Z, ?_, mod_cast H_mul_Z⟩
  -- This is equivalent to showing that `|H| ≥ c(K)|S|` for some `c(K)` depending only on `K`.
  suffices ((φ - K) * (K - ψ)) / ((2 - K) * K) * #S ≤ Fintype.card H by
    calc
          (#Z : ℝ)
      _ = (Fintype.card H / #S : ℝ)⁻¹ := by simp [← card_H_mul_card_Z]
      _ ≤ (((φ - K) * (K - ψ) / ((2 - K) * K) * #S) / #S)⁻¹ := by gcongr
      _ = (2 - K) * K / ((φ - K) * (K - ψ)) := by
        have : (#S : ℝ) ≠ 0 := by positivity
        simp [this]
  -- Write `r(z)` the number of representations of `z ∈ S` as `x * y⁻¹` for `x, y ∈ A`.
  let r z : ℕ := A.convolution A⁻¹ z
  -- `r` is invariant under inverses.
  have r_inv z : r z⁻¹ = r z := by simp [r, inv_inv]
  -- We show that every `z ∈ S` with at least `(K - 1)|A|` representations lies in `H`,
  -- and that such `z` make up a proportion of at least `(2 - K) / ((φ - K) * (K - ψ))` of `S`.
  calc
        (φ - K) * (K - ψ) / ((2 - K) * K) * #S
    _ ≤ #{z ∈ S | (K - 1) * #A < r z} := ?_
    _ ≤ #(H : Set G).toFinset := ?_
    _ = Fintype.card H := by simp
  -- First, let's show that a large proportion of all `z ∈ S` have many representations.
  · -- Let `l` be that number.
    set l : ℕ := #{z ∈ S | (K - 1) * #A < r z} with hk
    -- By upper-bounding `r(z)` by `(K - 1)|A|` for the `z` with few representations,
    -- and by `|A|` for the `z` with many representations,
    -- we get `|A|² ≤ l|A| + (|S| - l)(K - 1)|A| = ((2 - K)l + (K - 1)|S|)|A|`.
    have ineq : #A * #A ≤ ((2 - K) * l + (K - 1) * #S) * #A := by
      calc
            (#A : ℝ) * #A
        _ = #A * #A⁻¹ := by simp
        _ = #(A ×ˢ A⁻¹) := by simp
        _ = ∑ z ∈ S, ↑(r z) := by
          norm_cast
          exact card_eq_sum_card_fiberwise fun xy hxy ↦
            mul_mem_mul (mem_product.mp hxy).1 (mem_product.mp hxy).2
        _ = ∑ z ∈ S with (K - 1) * #A < r z, ↑(r z) + ∑ z ∈ S with r z ≤ (K - 1) * #A, ↑(r z) := by
          norm_cast; simp_rw [← not_lt, sum_filter_add_sum_filter_not]
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, ↑(#A)
          + ∑ z ∈ S with r z ≤ (K - 1) * #A, (K - 1) * #A := by
          gcongr with z hz z hz
          · exact convolution_le_card_left
          · simp_all
        _ = l * #A + (#S - l) * (K - 1) * #A := by
          simp [hk, ← not_lt, mul_assoc,
            ← S.card_filter_add_card_filter_not fun z ↦ (K - 1) * #A < r z]
        _ = ((2 - K) * l + (K - 1) * #S) * #A := by ring
    -- By cancelling `|A|` on both sides, we get `|A| ≤ (2 - K)l + (K - 1)|S|`.
    -- By composing with `|S| ≤ K|A|`, we get `|S| ≤ (2 - K)Kl + (K - 1)K|S|`.
    have : 0 < #A := by positivity
    replace ineq := calc
          (#S : ℝ)
      _ ≤ K * #A := ‹_›
      _ ≤ K * ((2 - K) * l + (K - 1) * #S) := by
        gcongr; exact le_of_mul_le_mul_right ineq <| by positivity
      _ = (2 - K) * K * l + (K - 1) * K * #S := by ring
    -- Now, we are done.
    calc
          (φ - K) * (K - ψ) / ((2 - K) * K) * #S
      _ = (φ - K) * (K - ψ) * #S / ((2 - K) * K) := div_mul_eq_mul_div ..
      _ ≤ (2 - K) * K * l / ((2 - K) * K) := by
        have := Real.goldenRatio_mul_goldenConj
        have := Real.goldenRatio_add_goldenConj
        rw [show (φ - K) * (K - ψ) = 1 - (K - 1) * K by grind]
        gcongr ?_ / _
        linarith [ineq]
      _ = l := by field
  -- Second, let's show that the `z ∈ S` with many representations are in `H`.
  · gcongr
    simp only [subset_iff, mem_filter, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    rintro z hz hrz
    -- It's enough to show that `z * w ∈ S` for all `w ∈ S`.
    rw [mem_stabilizer_finset']
    rintro w hw
    -- Since `w ∈ S` and `|A⁻¹ * A| ≤ K|A|`, we know that `r(w) ≥ (2 - K)|A|`.
    have hrw : (2 - K) * #A ≤ r w := by
      simpa [card_mul_inv_eq_convolution_inv] using! le_card_mul_inv_eq hA₁ (by simpa)
    -- But also `r(z⁻¹) = r(z) > (K - 1)|A|`.
    rw [← r_inv] at hrz
    simp only [r, ← card_inter_smul] at hrz hrw
    -- By inclusion-exclusion, we get that `(z⁻¹ •> A) ∩ (w •> A)` is non-empty.
    have : (0 : ℝ) < #((z⁻¹ •> A) ∩ (w •> A)) := by
      have : (#((A ∩ z⁻¹ •> A) ∩ (A ∩ w •> A)) : ℝ) ≤ #(z⁻¹ •> A ∩ w •> A) := by
        gcongr <;> exact inter_subset_right
      have : (#((A ∩ z⁻¹ •> A) ∪ (A ∩ w •> A)) : ℝ) ≤ #A := by
        gcongr; exact union_subset inter_subset_left inter_subset_left
      have :
          (#((A ∩ z⁻¹ •> A) ∩ (A ∩ w •> A)) + #((A ∩ z⁻¹ •> A) ∪ (A ∩ w •> A)) : ℝ) =
            #(A ∩ z⁻¹ •> A) + #(A ∩ w •> A) := mod_cast card_inter_add_card_union ..
      linarith
    -- This is exactly what we set out to prove.
    simpa [S, card_smul_inter_smul, Finset.Nonempty, mem_mul, mem_inv, -mem_inv', and_assoc]
      using! this

/-! ### Doubling less than `2-ε` -/

variable (ε : ℝ)

/-- Given a constant `K ∈ ℝ` (usually `0 < K ≤ 1`) and a finite subset `S ⊆ G`,
`expansion K S : Finset G → ℝ` measures the extent to which `S` extends the argument, compared
against the reference constant `K`. That is, given a finite `A ⊆ G` (possibly empty),
`expansion K S A` is defined as the value of `#(SA) - K#S`. -/
private def expansion (K : ℝ) (S A : Finset G) : ℝ := #(A * S) - K * #A

@[simp] private lemma expansion_empty (K : ℝ) (S : Finset G) : expansion K S ∅ = 0 := by
  simp [expansion]

private lemma mul_card_le_expansion (hS : S.Nonempty) : (1 - K) * #A ≤ expansion K S A := by
  rw [one_sub_mul, expansion]; have := card_le_card_mul_right hS (s := A); gcongr

@[simp] private lemma expansion_nonneg (hK : K ≤ 1) (hS : S.Nonempty) : 0 ≤ expansion K S A := by
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]

@[simp] private lemma expansion_pos (hK : K < 1) (hS : S.Nonempty) (hA : A.Nonempty) :
    0 < expansion K S A := by
  have : (0 : ℝ) < #A := by simp [hA]
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]

@[simp] private lemma expansion_pos_iff (hK : K < 1) (hS : S.Nonempty) :
    0 < expansion K S A ↔ A.Nonempty where
  mp hA := by by_contra! rfl; simp at hA
  mpr := expansion_pos hK hS

@[simp] private lemma expansion_smul_finset (K : ℝ) (S A : Finset G) (a : G) :
    expansion K S (a • A) = expansion K S A := by simp [expansion, smul_mul_assoc]

private lemma expansion_submodularity :
    expansion K S (A ∩ B) + expansion K S (A ∪ B) ≤ expansion K S A + expansion K S B := by
  have : (#(A ∩ B) + #(A ∪ B) : ℝ) = #A + #B := mod_cast card_inter_add_card_union A B
  have : K * #(A ∩ B) + K * #(A ∪ B) = K * #A + K * #B := by simp only [← mul_add, this]
  have : (#(A * S ∩ (B * S)) + #(A * S ∪ B * S) : ℝ) = #(A * S) + #(B * S) :=
    mod_cast card_inter_add_card_union (A * S) (B * S)
  have : (#((A ∩ B) * S) : ℝ) ≤ #(A * S ∩ (B * S)) := by grw [inter_mul_subset]
  simp_rw [expansion, union_mul]
  nlinarith

private lemma bddBelow_expansion (hK : K ≤ 1) (hS : S.Nonempty) :
    BddBelow (Set.range fun A : {A : Finset G // A.Nonempty} ↦ expansion K S A) :=
  ⟨0, by simp [lowerBounds, *]⟩

/-- Given `K ∈ ℝ` and a finite `S ⊆ G`, the connectivity `κ` of `G` with respect to `K` and `S` is
the infimum of `expansion K S A` over all finite nonempty `A ⊆ G`. Note that when `K ≤ 1`,
`expansion K S A` is nonnegative for all `A`, so the infimum exists. -/
private noncomputable def connectivity (K : ℝ) (S : Finset G) : ℝ :=
  ⨅ A : {A : Finset G // A.Nonempty}, expansion K S A

@[simp] private lemma le_connectivity_iff (hK : K ≤ 1) (hS : S.Nonempty) {r : ℝ} :
    r ≤ connectivity K S ↔ ∀ ⦃A : Finset G⦄, A.Nonempty → r ≤ expansion K S A := by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, le_ciInf_iff, bddBelow_expansion, *]

@[simp] private lemma connectivity_lt_iff (hK : K ≤ 1) (hS : S.Nonempty) {r : ℝ} :
    connectivity K S < r ↔ ∃ A : Finset G, A.Nonempty ∧ expansion K S A < r := by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, ciInf_lt_iff, bddBelow_expansion, *]

@[simp] private lemma connectivity_le_expansion (hK : K ≤ 1) (hS : S.Nonempty) (hA : A.Nonempty) :
    connectivity K S ≤ expansion K S A := (le_connectivity_iff hK hS).1 le_rfl hA

private lemma connectivity_nonneg (hK : K ≤ 1) (hS : S.Nonempty) :
    0 ≤ connectivity K S := by simp [*]

/-- Given `K ∈ ℝ` and a finite `S ⊆ G`, a fragment of `G` with respect to `K` and `S` is a finite
nonempty `A ⊆ G` whose expansion attains the value of the connectivity, that is,
`expansion K S A = κ`. -/
private def IsFragment (K : ℝ) (S A : Finset G) : Prop := expansion K S A = connectivity K S

/-- Given `K ∈ ℝ` and a finite `S ⊆ G`, an atom of `G` with respect to `K` and `S` is a (finite
and nonempty) fragment `A` of minimal cardinality. -/
private def IsAtom (K : ℝ) (S A : Finset G) : Prop := MinimalFor (IsFragment K S) card A

private lemma IsAtom.isFragment (hA : IsAtom K S A) : IsFragment K S A := hA.1

@[simp] private lemma isFragment_smul_finset : IsFragment K S (a • A) ↔ IsFragment K S A := by
  simp [IsFragment]

@[simp] private lemma isAtom_smul_finset : IsAtom K S (a • A) ↔ IsAtom K S A := by
  simp [IsAtom, MinimalFor]

private lemma IsFragment.smul_finset (a : G) (hA : IsFragment K S A) : IsFragment K S (a • A) :=
  isFragment_smul_finset.2 hA

private lemma IsAtom.smul_finset (a : G) (hA : IsAtom K S A) : IsAtom K S (a • A) :=
  isAtom_smul_finset.2 hA

private lemma IsFragment.inter (hK : K ≤ 1) (hS : S.Nonempty) (hA : IsFragment K S A)
    (hB : IsFragment K S B) (hAB : (A ∩ B).Nonempty) : IsFragment K S (A ∩ B) := by
  unfold IsFragment at *
  have := expansion_submodularity (S := S) (A := A) (B := B) (K := K)
  have := connectivity_le_expansion hK hS hAB
  have := connectivity_le_expansion hK hS <| hAB.mono inter_subset_union
  linarith

private lemma IsAtom.eq_of_inter_nonempty (hK : K ≤ 1) (hS : S.Nonempty)
    (hA : IsAtom K S A) (hB : IsAtom K S B) (hAB : (A ∩ B).Nonempty) : A = B := by
  replace hAB := hA.isFragment.inter hK hS hB.isFragment hAB
  replace hA := hA.2 hAB <| by grw [inter_subset_left]
  replace hB := hB.2 hAB <| by grw [inter_subset_right]
  replace hA := eq_of_subset_of_card_le inter_subset_left hA
  replace hB := eq_of_subset_of_card_le inter_subset_right hB
  exact hA.symm.trans hB

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- For `K < 1` and `S ⊆ G` finite and nonempty, the value of connectivity is attained by a
nonempty finite subset of `G`. That is, a fragment for given `K` and `S` exists. -/
private lemma exists_nonempty_isFragment (hK : K < 1) (hS : S.Nonempty) :
    ∃ A, A.Nonempty ∧ IsFragment K S A := by
  -- We will show this lemma by contradiction. So we suppose that the infimum in the definition of
  -- connectivity is not attained by a nonempty finite subset of `G`, or, equivalently, that for
  -- every `κ < k` where `κ` is the connectivity, there is nonempty `A` such that `κ < ex A < k`.
  by_contra! H
  let ex := expansion K S
  let κ := connectivity K S
  -- Some useful calculations
  have κ_add_one_pos : 0 < κ + 1 := by linarith [connectivity_nonneg hK.le hS]
  have one_sub_K_pos : 0 < 1 - K := by linarith
  -- First we show that for large enough `A`, `κ + 1 < ex A`. Calculations show that
  -- `#A > ⌊(κ + 1) / (1 - K)⌋` suffices. We will actually use the contrapositive of this result: if
  -- `ex A` is near `κ`, then `A` will need to be small.
  let t := Nat.floor ((κ + 1) / (1 - K))
  have largeA {A : Finset G} (hA : t < #A) : κ + 1 < ex A := by
    rw [Nat.lt_iff_add_one_le] at hA
    calc
          κ + 1
      _ = (κ + 1) / ((κ + 1) / (1 - K)) * ((κ + 1) / (1 - K)) := by field
      _ < (κ + 1) / ((κ + 1) / (1 - K)) * (t + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = (1 - K) * (t + 1) := by field
      _ ≤ (1 - K) * #A      := by norm_cast; gcongr
      _ ≤ ex A              := mul_card_le_expansion hS
  -- On the other hand, we essentially show that there are only finitely many possible values for
  -- `A` with `#A ≤ t`, and these values are found in the set `M = (⟦#S, t#S⟧ - K⟦1, t⟧) ∩ (κ, ∞)`.
  let M := {x ∈ ((Icc #S (t * #S)).map Nat.castEmbedding -
    K • (Icc 1 t).map Nat.castEmbedding : Finset ℝ) | κ < x}
  have smallA {A : Finset G} (hA : A.Nonempty) (hAt : #A ≤ t) : ex A ∈ M := by
    rw [mem_filter]
    refine ⟨sub_mem_sub ?_ ?_, (connectivity_le_expansion hK.le hS hA).lt_of_ne' <| H _ hA⟩
    · apply mem_map_of_mem
      exact mem_Icc.2 ⟨card_le_card_mul_left hA, by grw [card_mul_le, hAt]⟩
    · apply smul_mem_smul_finset
      apply mem_map_of_mem
      exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero, hAt⟩
  -- Now we take the minimum value of `M` (union `{κ + 1}` to handle the eventual emptiness of `M`
  -- and get better bounds). This will be strictly larger than `κ` by definition.
  have : (M ∪ {κ + 1}).Nonempty := by simp
  let k := (M ∪ {κ + 1}).min' this
  have : κ < k := by simp [k, M]
  -- By the property of infimum and the previous claim, there is `A` with `κ < ex A < k ≤ κ + 1`.
  -- But then the claim about large `A` implies that `#A ≤ t` and thus `ex A ∈ M` and `k ≤ ex A`,
  -- a contradiction.
  obtain ⟨A, hA, hAk⟩ := (connectivity_lt_iff hK.le hS).mp this
  have : ex A ≤ κ + 1 := hAk.le.trans <| min'_le _ _ (by simp)
  have := not_lt.mp (mt largeA this.not_gt)
  exact hAk.not_ge <| min'_le (M ∪ {κ + 1}) _ <| subset_union_left <| smallA hA this

private lemma exists_isFragment (hK : K < 1) (hS : S.Nonempty) :
    ∃ A, IsFragment K S A := let ⟨A, _, hA⟩ := exists_nonempty_isFragment hK hS; ⟨A, hA⟩

private lemma exists_isAtom (hK : K < 1) (hS : S.Nonempty) : ∃ A, IsAtom K S A :=
  exists_minimalFor_of_wellFoundedLT _ _ <| exists_isFragment hK hS

private lemma connectivity_pos (hK : K < 1) (hS : S.Nonempty) : 0 < connectivity K S := by
  obtain ⟨A, hA, hSA⟩ := exists_nonempty_isFragment hK hS
  exact (expansion_pos hK hS hA).trans_eq hSA

private lemma not_isFragment_empty (hK : K < 1) (hS : S.Nonempty) : ¬ IsFragment K S ∅ := by
  simp [IsFragment, (connectivity_pos hK hS).ne]

private lemma IsFragment.nonempty (hK : K < 1) (hS : S.Nonempty) (hA : IsFragment K S A) :
    A.Nonempty := by
  by_contra! rfl
  simp [*, not_isFragment_empty hK hS] at hA

private lemma IsAtom.nonempty (hK : K < 1) (hS : S.Nonempty) (hA : IsAtom K S A) : A.Nonempty :=
  hA.isFragment.nonempty hK hS

/-- For `K < 1` and finite nonempty `S ⊆ G`, there exists a finite subgroup `H ≤ G` that is also
an atom for `K` and `S`. -/
private lemma exists_subgroup_isAtom (hK : K < 1) (hS : S.Nonempty) :
    ∃ (H : Subgroup G) (_ : Fintype H), IsAtom K S (Set.toFinset H) := by
  -- We take any atom `N` of `G` with respect to `K` and `S`. Since left multiples of `N` (which
  -- are atoms as well) partition `G` by `IsAtom.eq_of_inter_nonempty`, we will deduce that a left
  -- multiple that contains `1` is a (finite) subgroup of `G`.
  obtain ⟨N, hN⟩ := exists_isAtom hK hS
  obtain ⟨n, hn⟩ := IsAtom.nonempty hK hS hN
  have one_mem_carrier : 1 ∈ n⁻¹ •> N := by simpa [mem_inv_smul_finset_iff]
  have self_mem_smul_carrier (x : G) : x ∈ x • n⁻¹ • N := by
    apply smul_mem_smul_finset (a := x) at one_mem_carrier
    simpa only [smul_eq_mul, mul_one] using! one_mem_carrier
  let H : Subgroup G := {
    carrier := n⁻¹ •> N
    one_mem' := mod_cast one_mem_carrier
    mul_mem' {a b} ha hb := by
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have : (n⁻¹ •> N ∩ a •> n⁻¹ •> N).Nonempty := ⟨a, by
        simpa only [mem_inter] using! ⟨ha, self_mem_smul_carrier a⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a) this] using! hb
    inv_mem' {a} ha := by
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul, inv_mul_cancel] at ha
      have : (n⁻¹ •> N ∩ a⁻¹ •> n⁻¹ •> N).Nonempty := ⟨1, by simpa using! ⟨one_mem_carrier, ha⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a⁻¹) this] using! self_mem_smul_carrier a⁻¹
  }
  refine ⟨H, Fintype.ofFinset (n⁻¹ •> N) fun a => ?_, ?_⟩
  · simpa only [← mem_coe, coe_smul_finset] using! H.mem_carrier
  · simpa [Set.toFinset_smul_set, toFinset_coe, H] using! IsAtom.smul_finset n⁻¹ hN

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `S` is nonempty such that there is `A` with `|S| ≤ |A|` such that `|A * S| ≤ (2 - ε) * |S|`
for some `0 < ε ≤ 1`, then there is a finite subgroup `H` of `G` of size `|H| ≤ (2 / ε - 1) * |S|`
such that `S` is covered by at most `2 / ε - 1` right cosets of `H`. -/
theorem card_mul_finset_lt_two {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hS : S.Nonempty)
    (hA : ∃ A : Finset G, #S ≤ #A ∧ #(A * S) ≤ (2 - ε) * #S) :
    ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      Fintype.card H ≤ (2 / ε - 1) * #S ∧ #Z ≤ 2 / ε - 1 ∧ (S : Set G) ⊆ H * Z := by
  let K := 1 - ε / 2
  have hK : K < 1 := by unfold K; linarith [hε₀]
  let ex := expansion K S
  let κ := connectivity K S
  -- We will show that an atomic subgroup `H ≤ G` with respect to `K` and `S` and the right coset
  -- representing finset of `S` acting on `H` are adequate choices for the theorem
  obtain ⟨H, _, hH⟩ := exists_subgroup_isAtom hK hS
  obtain ⟨Z, hZS, hHZS, hZinj⟩ := exists_subset_mul_eq_mul_injOn H S
  -- We only use the existence of `A` given by assumption to get a good bound on `ex H` solely
  -- in terms of `#S` and `ε`.
  obtain ⟨A, hA₁, hA₂⟩ := hA
  have calc₁ : ex (Set.toFinset H) ≤ (1 - ε / 2) * #S := by
    calc
          ex (Set.toFinset H)
      _ = κ                               := hH.isFragment
      _ ≤ #(A * S) - K * #A :=
        connectivity_le_expansion hK.le hS <| card_pos.mp <| hS.card_pos.trans_le hA₁
      _ ≤ (2 - ε) * #S - (1 - ε / 2) * #S := by gcongr; linarith
      _ = (1 - ε / 2) * #S                := by linarith
  refine ⟨H, inferInstance, Z, ?cardH, ?cardZ, by
    simpa only [hHZS] using Set.subset_mul_right _ H.one_mem⟩
  -- Bound on `#H` follows easily from the previous calculation.
  case cardH =>
    rw [← mul_le_mul_iff_right₀ (a := ε / 2) (by positivity)]
    calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset   := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
        _ = (1 - K) * #(H : Set G).toFinset := by ring
        _ ≤ ex (Set.toFinset H)             := mul_card_le_expansion hS
        _ ≤ (1 - ε / 2) * #S                := calc₁
        _ = ε / 2 * ((2 / ε - 1) * #S)      := by field
  -- To show the bound on `#Z`, we note that `#Z = #(HS) / #H` and show `#(HS) ≤ (2 / ε - 1) * #H`.
  case cardZ =>
    calc
          (#Z : ℝ)
      _ = #(H : Set G).toFinset * #Z / #(H : Set G).toFinset          := by field
      _ = #(Set.toFinset H * Z) / #(H : Set G).toFinset               := by
        simp [← card_mul_eq_mul_card_of_injOn_opSMul hZinj, Nat.cast_mul]
      _ = #(Set.toFinset H * S) / #(H : Set G).toFinset               := by
        congr 3; simpa using congr(($hHZS).toFinset)
      _ ≤ (2 / ε - 1) * #(H : Set G).toFinset / #(H : Set G).toFinset := ?_
      _ = 2 / ε - 1                                                   := by field
    gcongr
    -- Finally, to show `#(HS) ≤ (2 / ε - 1) * #H`, we multiply both sides by `1 - K = ε / 2` and
    -- show `#(HS) = K * #H + ex H ≤ K * #H + (1 - ε / 2) * #S ≤ K * #H + (1 - ε / 2) * #(HS)`,
    -- where we used `calc₁` again.
    rw [← mul_le_mul_iff_right₀ (show 0 < 1 - K by linarith [hK])]
    suffices (1 - K) * #(Set.toFinset H * S) ≤ (1 - ε / 2) * #(H : Set G).toFinset by
      apply le_of_le_of_eq this; simp [K]; field
    rw [sub_mul, one_mul, sub_le_iff_le_add]
    calc
          (#(Set.toFinset H * S) : ℝ)
      _ = K * #(H : Set G).toFinset + (#(Set.toFinset H * S) - K * #(H : Set G).toFinset) := by ring
      _ = K * #(H : Set G).toFinset + ex (Set.toFinset H)                 := rfl
      _ ≤ K * #(H : Set G).toFinset + (1 - ε / 2) * #(Set.toFinset H * S) := by
        grw [calc₁]
        gcongr
        · linarith
        · simp only [Set.mem_toFinset, SetLike.mem_coe, H.one_mem, subset_mul_right]

/-- Corollary of `card_mul_finset_lt_two` in the case `A = S`, giving characterisation of sets of
doubling less than `2 - ε`. -/
theorem doubling_lt_two {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hA₀ : A.Nonempty)
    (hA₁ : #(A * A) ≤ (2 - ε) * #A) : ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      Fintype.card H ≤ (2 / ε - 1) * #A ∧ #Z ≤ 2 / ε - 1 ∧ (A : Set G) ⊆ H * Z :=
  card_mul_finset_lt_two hε₀ hε₁ hA₀ ⟨A, by rfl, hA₁⟩

end Finset
