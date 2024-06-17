/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in ordered rings

This file contains the results concerning the interaction of finset big operators with ordered
rings.
-/

variable {ι R : Type*}

namespace Finset

section CommMonoidWithZero
variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]

section PosMulMono
variable [PosMulMono R] {f g : ι → R} {s t : Finset ι}

lemma prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0
#align finset.prod_nonneg Finset.prod_nonneg

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction' s using Finset.cons_induction with a s has ih h
  · simp
  · simp only [prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · exact h1 a (mem_cons_self a s)
    · refine ih (fun x H ↦ h0 _ ?_) (fun x H ↦ h1 _ ?_) <;> exact subset_cons _ H
    · apply prod_nonneg fun x H ↦ h0 x (subset_cons _ H)
    · apply le_trans (h0 a (mem_cons_self a s)) (h1 a (mem_cons_self a s))
#align finset.prod_le_prod Finset.prod_le_prod

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`.

This is a variant (beta-reduced) version of the standard lemma `Finset.prod_le_prod`, convenient
for the `gcongr` tactic. -/
@[gcongr]
lemma _root_.GCongr.prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    s.prod f ≤ s.prod g :=
  s.prod_le_prod h0 h1

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `Finset.prod_le_one'` for the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  convert ← prod_le_prod h0 h1
  exact Finset.prod_const_one
#align finset.prod_le_one Finset.prod_le_one

end PosMulMono

section PosMulStrictMono
variable [PosMulStrictMono R] [Nontrivial R] {f g : ι → R} {s t : Finset ι}

lemma prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i :=
  prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0
#align finset.prod_pos Finset.prod_pos

lemma prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_le_of_lt' hilt ?_ ?_ ?_
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)

lemma prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end PosMulStrictMono
end CommMonoidWithZero

section OrderedCommSemiring
variable [OrderedCommSemiring R] {f g : ι → R} {s t : Finset ι}

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `OrderedCommSemiring`. -/
lemma prod_add_prod_le {i : ι} {f g h : ι → R} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
    (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_diff_singleton hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    refine add_le_add ?_ ?_ <;>
    · refine mul_le_mul_of_nonneg_left ?_ ?_
      · refine prod_le_prod ?_ ?_ <;> simp (config := { contextual := true }) [*]
      · try apply_assumption
        try assumption
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji ↦ le_trans (hg j hj) (hgf j hj hji)
#align finset.prod_add_prod_le Finset.prod_add_prod_le

end OrderedCommSemiring

section LinearOrderedCommSemiring
variable [LinearOrderedCommSemiring R] [ExistsAddOfLE R]

/-- **Cauchy-Schwarz inequality** for finsets. -/
lemma sum_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 := by
  nontriviality R
  obtain h' | h' := (sum_nonneg fun _ _ ↦ sq_nonneg <| g _).eq_or_lt
  · have h'' : ∀ i ∈ s, g i = 0 := fun i hi ↦ by
      simpa using (sum_eq_zero_iff_of_nonneg fun i _ ↦ sq_nonneg (g i)).1 h'.symm i hi
    rw [← h', sum_congr rfl (show ∀ i ∈ s, f i * g i = 0 from fun i hi ↦ by simp [h'' i hi])]
    simp
  refine le_of_mul_le_mul_of_pos_left
    (le_of_add_le_add_left (a := (∑ i ∈ s, g i ^ 2) * (∑ j ∈ s, f j * g j) ^ 2) ?_) h'
  calc
    _ = ∑ i ∈ s, 2 * (f i * ∑ j ∈ s, g j ^ 2) * (g i * ∑ j ∈ s, f j * g j) := by
        simp_rw [mul_assoc (2 : R), mul_mul_mul_comm, ← mul_sum, ← sum_mul]; ring
    _ ≤ ∑ i ∈ s, ((f i * ∑ j ∈ s, g j ^ 2) ^ 2 + (g i * ∑ j ∈ s, f j * g j) ^ 2) :=
        sum_le_sum fun i _ ↦ two_mul_le_add_sq (f i * ∑ j ∈ s, g j ^ 2) (g i * ∑ j ∈ s, f j * g j)
    _ = _ := by simp_rw [sum_add_distrib, mul_pow, ← sum_mul]; ring

end LinearOrderedCommSemiring

lemma abs_prod [LinearOrderedCommRing R] (s : Finset ι) (f : ι → R) :
    |∏ x ∈ s, f x| = ∏ x ∈ s, |f x| :=
  map_prod absHom _ _
#align finset.abs_prod Finset.abs_prod

section CanonicallyOrderedCommSemiring
variable [CanonicallyOrderedCommSemiring R] {f g h : ι → R} {s : Finset ι} {i : ι}

/-- Note that the name is to match `CanonicallyOrderedCommSemiring.mul_pos`. -/
@[simp] lemma _root_.CanonicallyOrderedCommSemiring.prod_pos [Nontrivial R] :
    0 < ∏ i ∈ s, f i ↔ (∀ i ∈ s, (0 : R) < f i) :=
  CanonicallyOrderedCommSemiring.multiset_prod_pos.trans Multiset.forall_mem_map_iff
#align canonically_ordered_comm_semiring.prod_pos CanonicallyOrderedCommSemiring.prod_pos

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `CanonicallyOrderedCommSemiring`.
-/
lemma prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
    (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi]
    refine le_trans ?_ (mul_le_mul_right' h2i _)
    rw [right_distrib]
    apply add_le_add <;> apply mul_le_mul_left' <;> apply prod_le_prod' <;>
            simp only [and_imp, mem_sdiff, mem_singleton] <;>
          intros <;>
        apply_assumption <;>
      assumption
#align finset.prod_add_prod_le' Finset.prod_add_prod_le'

end CanonicallyOrderedCommSemiring
end Finset

section AbsoluteValue

variable {S : Type*}

lemma AbsoluteValue.sum_le [Semiring R] [OrderedSemiring S] (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι → R) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) :=
  Finset.le_sum_of_subadditive abv (map_zero _) abv.add_le _ _
#align absolute_value.sum_le AbsoluteValue.sum_le

lemma IsAbsoluteValue.abv_sum [Semiring R] [OrderedSemiring S] (abv : R → S) [IsAbsoluteValue abv]
    (f : ι → R) (s : Finset ι) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _
#align is_absolute_value.abv_sum IsAbsoluteValue.abv_sum

@[deprecated (since := "2024-02-14")] alias abv_sum_le_sum_abv := IsAbsoluteValue.abv_sum

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [LinearOrderedCommRing S]
    (abv : AbsoluteValue R S) (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  map_prod abv f s
#align absolute_value.map_prod AbsoluteValue.map_prod

lemma IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [LinearOrderedCommRing S]
    (abv : R → S) [IsAbsoluteValue abv] (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _
#align is_absolute_value.map_prod IsAbsoluteValue.map_prod

end AbsoluteValue

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

private alias ⟨_, prod_ne_zero⟩ := prod_ne_zero_iff

/-- The `positivity` extension which proves that `∏ i ∈ s, f i` is nonnegative if `f` is, and
positive if each `f i` is.

TODO: The following example does not work
```
example (s : Finset ℕ) (f : ℕ → ℤ) (hf : ∀ n, 0 ≤ f n) : 0 ≤ s.prod f := by positivity
```
because `compareHyp` can't look for assumptions behind binders.
-/
@[positivity Finset.prod _ _]
def evalFinsetProd : PositivityExt where eval {u α} zα pα e := do
  match e with
  | ~q(@Finset.prod $ι _ $instα $s $f) =>
    let i : Q($ι) ← mkFreshExprMVarQ q($ι) .syntheticOpaque
    have body : Q($α) := Expr.betaRev f #[i]
    let rbody ← core zα pα body
    let _instαmon ← synthInstanceQ q(CommMonoidWithZero $α)

    -- Try to show that the product is positive
    let p_pos : Option Q(0 < $e) := ← do
      let .positive pbody := rbody | pure none -- Fail if the body is not provably positive
      -- TODO(quote4#38): We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulStrictMono $α) | pure none
      let .some _instαnontriv ← trySynthInstanceQ q(Nontrivial $α) | pure none
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      return some q(prod_pos fun i _ ↦ $pr i)
    if let some p_pos := p_pos then return .positive p_pos

    -- Try to show that the product is nonnegative
    let p_nonneg : Option Q(0 ≤ $e) := ← do
      let .some pbody := rbody.toNonneg
        | return none -- Fail if the body is not provably nonnegative
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      -- TODO(quote4#38): We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulMono $α) | pure none
      assertInstancesCommute
      return some q(prod_nonneg fun i _ ↦ $pr i)
    if let some p_nonneg := p_nonneg then return .nonnegative p_nonneg

    -- Fall back to showing that the product is nonzero
    let pbody ← rbody.toNonzero
    let pr : Q(∀ i, $f i ≠ 0) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
    -- TODO(quote4#38): We must name the following, else `assertInstancesCommute` loops.
    let _instαnontriv ← synthInstanceQ q(Nontrivial $α)
    let _instαnozerodiv ← synthInstanceQ q(NoZeroDivisors $α)
    assertInstancesCommute
    return .nonzero q(prod_ne_zero fun i _ ↦ $pr i)

end Mathlib.Meta.Positivity
