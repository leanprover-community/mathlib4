/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Tactic.Ring

/-!
# Big operators on a finset in ordered rings

This file contains the results concerning the interaction of finset big operators with ordered
rings.

In particular, this file contains the standard form of the Cauchy-Schwarz inequality, as well as
some of its immediate consequences.
-/

variable {ι R S : Type*}

namespace Finset

section CommMonoidWithZero
variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]

section PosMulMono
variable [PosMulMono R] {f g : ι → R} {s t : Finset ι}

lemma prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  prod_induction f (fun i ↦ 0 ≤ i) (fun _ _ ha hb ↦ mul_nonneg ha hb) zero_le_one h0

/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `Finset.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid. -/
@[gcongr]
lemma prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `Finset.prod_le_one'` for the case of an ordered commutative multiplicative monoid. -/
lemma prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  convert ← prod_le_prod h0 h1
  exact Finset.prod_const_one

end PosMulMono

section PosMulStrictMono
variable [PosMulStrictMono R] [Nontrivial R] {f g : ι → R} {s t : Finset ι}

lemma prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i :=
  prod_induction f (fun x ↦ 0 < x) (fun _ _ ha hb ↦ mul_pos ha hb) zero_lt_one h0

lemma prod_lt_prod (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i ≤ g i)
    (hlt : ∃ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  classical
  obtain ⟨i, hi, hilt⟩ := hlt
  rw [← insert_erase hi, prod_insert (notMem_erase _ _), prod_insert (notMem_erase _ _)]
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹PosMulStrictMono R›
  refine mul_lt_mul_of_pos_of_nonneg' hilt ?_ ?_ ?_
  · exact prod_le_prod (fun j hj => le_of_lt (hf j (mem_of_mem_erase hj)))
      (fun _ hj ↦ hfg _ <| mem_of_mem_erase hj)
  · exact prod_pos fun j hj => hf j (mem_of_mem_erase hj)
  · exact (hf i hi).le.trans hilt.le

lemma prod_lt_prod_of_nonempty (hf : ∀ i ∈ s, 0 < f i) (hfg : ∀ i ∈ s, f i < g i)
    (h_ne : s.Nonempty) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  apply prod_lt_prod hf fun i hi => le_of_lt (hfg i hi)
  obtain ⟨i, hi⟩ := h_ne
  exact ⟨i, hi, hfg i hi⟩

end PosMulStrictMono
end CommMonoidWithZero

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {f : ι → R} {s : Finset ι}

lemma sum_sq_le_sq_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi ↦ ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

end OrderedSemiring

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : ι → R} {s t : Finset ι}

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `OrderedCommSemiring`. -/
lemma prod_add_prod_le {i : ι} {f g h : ι → R} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
    (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_diff_singleton hi]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right h2i ?_)
  · rw [right_distrib]
    gcongr with j hj <;> aesop
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    exact fun j hj hji ↦ le_trans (hg j hj) (hgf j hj hji)

theorem le_prod_of_submultiplicative_on_pred_of_nonneg {M : Type*} [CommMonoid M] (f : M → R)
    (p : M → Prop) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Finset ι) (g : ι → M) (hps : ∀ a, a ∈ s → p (g a)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  apply le_trans (Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg f p h_nonneg h_one
    h_mul hp_mul _ ?_) (by simp [Multiset.map_map])
  intro _ ha
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
  exact hps i hi

theorem le_prod_of_submultiplicative_of_nonneg {M : Type*} [CommMonoid M]
    (f : M → R) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ x y : M, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) :=
  le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

end OrderedCommSemiring

theorem sum_mul_self_eq_zero_iff [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) : ∑ i ∈ s, f i * f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _]
  simp

lemma abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι) (f : ι → R) :
    |∏ x ∈ s, f x| = ∏ x ∈ s, |f x| :=
  map_prod absHom _ _

@[simp, norm_cast]
theorem PNat.coe_prod {ι : Type*} (f : ι → ℕ+) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : ℕ) :=
  map_prod PNat.coeMonoidHom _ _

section CanonicallyOrderedAdd
variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  {f g h : ι → R} {s : Finset ι} {i : ι}

/-- Note that the name is to match `CanonicallyOrderedAdd.mul_pos`. -/
@[simp] lemma _root_.CanonicallyOrderedAdd.prod_pos [NoZeroDivisors R] [Nontrivial R] :
    0 < ∏ i ∈ s, f i ↔ (∀ i ∈ s, (0 : R) < f i) :=
  CanonicallyOrderedAdd.multiset_prod_pos.trans Multiset.forall_mem_map_iff

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `CanonicallyOrderedAdd`.
-/
lemma prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
    (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_diff_singleton hi]
  refine le_trans ?_ (mul_le_mul_right' h2i _)
  rw [right_distrib]
  gcongr with j hj j hj <;> simp_all

end CanonicallyOrderedAdd

/-! ### Named inequalities -/

/-- **Cauchy-Schwarz inequality** for finsets.

This is written in terms of sequences `f`, `g`, and `r`, where `r` is a stand-in for
`√(f i * g i)`. See `sum_mul_sq_le_sq_mul_sq` for the more usual form in terms of squared
sequences. -/
lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R]
    (s : Finset ι) {r f g : ι → R} (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) : (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i := by
  obtain h | h := (sum_nonneg hg).eq_or_lt'
  · have ht' : ∑ i ∈ s, r i = 0 := sum_eq_zero fun i hi ↦ by
      simpa [(sum_eq_zero_iff_of_nonneg hg).1 h i hi] using ht i hi
    rw [h, ht']
    simp
  · refine le_of_mul_le_mul_of_pos_left
      (le_of_add_le_add_left (a := (∑ i ∈ s, g i) * (∑ i ∈ s, r i) ^ 2) ?_) h
    calc
      _ = ∑ i ∈ s, 2 * r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j) := by
          simp_rw [mul_assoc, ← mul_sum, ← sum_mul]; ring
      _ ≤ ∑ i ∈ s, (f i * (∑ j ∈ s, g j) ^ 2 + g i * (∑ j ∈ s, r j) ^ 2) := by
          gcongr with i hi
          have ht : (r i * (∑ j ∈ s, g j) * (∑ j ∈ s, r j)) ^ 2 =
              (f i * (∑ j ∈ s, g j) ^ 2) * (g i * (∑ j ∈ s, r j) ^ 2) := by grind
          refine le_of_eq_of_le ?_ (two_mul_le_add_of_sq_eq_mul
            (mul_nonneg (hf i hi) (sq_nonneg _)) (mul_nonneg (hg i hi) (sq_nonneg _)) ht)
          repeat rw [mul_assoc]
      _ = _ := by simp_rw [sum_add_distrib, ← sum_mul]; ring

/-- **Cauchy-Schwarz inequality** for finsets, squared version. -/
lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ mul_pow ..)

/-- **Sedrakyan's lemma**, aka **Titu's lemma** or **Engel's form**.

This is a specialization of the Cauchy-Schwarz inequality with the sequences `f n / √(g n)` and
`√(g n)`, though here it is proven without relying on square roots. -/
theorem sq_sum_div_le_sum_sq_div [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) {g : ι → R} (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i := by
  have hg' : ∀ i ∈ s, 0 ≤ g i := fun i hi ↦ (hg i hi).le
  have H : ∀ i ∈ s, 0 ≤ f i ^ 2 / g i := fun i hi ↦ div_nonneg (sq_nonneg _) (hg' i hi)
  refine div_le_of_le_mul₀ (sum_nonneg hg') (sum_nonneg H)
    (sum_sq_le_sum_mul_sum_of_sq_eq_mul _ H hg' fun i hi ↦ ?_)
  rw [div_mul_cancel₀]
  exact (hg i hi).ne'

end Finset

/-! ### Absolute values -/

section AbsoluteValue

lemma AbsoluteValue.sum_le [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι → R) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) :=
  Finset.le_sum_of_subadditive abv (map_zero _) abv.add_le _ _

lemma IsAbsoluteValue.abv_sum [Semiring R] [Semiring S] [PartialOrder S] [IsOrderedRing S]
    (abv : R → S) [IsAbsoluteValue abv]
    (f : ι → R) (s : Finset ι) : abv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _

nonrec lemma AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : AbsoluteValue R S) (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  map_prod abv f s

lemma IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R]
    [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (abv : R → S) [IsAbsoluteValue abv] (f : ι → R) (s : Finset ι) :
    abv (∏ i ∈ s, f i) = ∏ i ∈ s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _

end AbsoluteValue

/-! ### Positivity extension -/

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

private alias ⟨_, prod_ne_zero⟩ := prod_ne_zero_iff

attribute [local instance] monadLiftOptionMetaM in
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
      -- TODO(https://github.com/leanprover-community/quote4/issues/38):
      -- We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulStrictMono $α) | pure none
      let .some _instαnontriv ← trySynthInstanceQ q(Nontrivial $α) | pure none
      assertInstancesCommute
      let pr : Q(∀ i, 0 < $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      return some q(prod_pos fun i _ ↦ $pr i)
    if let some p_pos := p_pos then return .positive p_pos
    -- Try to show that the product is nonnegative
    let p_nonneg : Option Q(0 ≤ $e) := ← do
      let some pbody := rbody.toNonneg
        | return none -- Fail if the body is not provably nonnegative
      let pr : Q(∀ i, 0 ≤ $f i) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
      -- TODO(https://github.com/leanprover-community/quote4/issues/38):
      -- We must name the following, else `assertInstancesCommute` loops.
      let .some _instαzeroone ← trySynthInstanceQ q(ZeroLEOneClass $α) | pure none
      let .some _instαposmul ← trySynthInstanceQ q(PosMulMono $α) | pure none
      assertInstancesCommute
      return some q(prod_nonneg fun i _ ↦ $pr i)
    if let some p_nonneg := p_nonneg then return .nonnegative p_nonneg
    -- Fall back to showing that the product is nonzero
    let pbody ← rbody.toNonzero
    let pr : Q(∀ i, $f i ≠ 0) ← mkLambdaFVars #[i] pbody (binderInfoForMVars := .default)
    -- TODO(https://github.com/leanprover-community/quote4/issues/38):
    -- We must name the following, else `assertInstancesCommute` loops.
    let _instαnontriv ← synthInstanceQ q(Nontrivial $α)
    let _instαnozerodiv ← synthInstanceQ q(NoZeroDivisors $α)
    assertInstancesCommute
    return .nonzero q(prod_ne_zero fun i _ ↦ $pr i)

end Mathlib.Meta.Positivity
