/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Logic.Function.Basic

/-!
# Very basic algebraic operations on pi types

This file provides very basic algebraic operations on functions.
-/

assert_not_exists Monoid Preorder

open Function

variable {ι ι' α β : Type*} {G M N O : ι → Type*}

namespace Pi
variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive /-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]
def mulSingle (i : ι) (x : M i) : ∀ j, M j := Function.update 1 i x

@[to_additive (attr := simp)]
lemma mulSingle_eq_same (i : ι) (x : M i) : mulSingle i x i = x := Function.update_self i x _

@[to_additive (attr := simp)]
lemma mulSingle_eq_of_ne {i i' : ι} (h : i' ≠ i) (x : M i) : mulSingle i x i' = 1 :=
  Function.update_of_ne h x _

/-- Abbreviation for `mulSingle_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[to_additive (attr := simp)
  /-- Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`. -/]
lemma mulSingle_eq_of_ne' {i i' : ι} (h : i ≠ i') (x : M i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]
lemma mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1 := Function.update_eq_self _ _

@[to_additive (attr := simp)]
lemma mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ mulSingle_one i⟩
  rw [← mulSingle_eq_same i x, h, one_apply]

@[to_additive]
lemma mulSingle_ne_one_iff : mulSingle i x ≠ 1 ↔ x ≠ 1 :=
  mulSingle_eq_one_iff.ne

@[to_additive]
lemma apply_mulSingle (f' : ∀ i, M i → N i) (hf' : ∀ i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using Function.apply_update f' 1 i x j

@[to_additive apply_single₂]
lemma apply_mulSingle₂ (f' : ∀ i, M i → N i → O i) (hf' : ∀ i, f' i 1 1 = 1) (i : ι)
    (x : M i) (y : N i) (j : ι) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]
lemma mulSingle_op (op : ∀ i, M i → N i) (h : ∀ i, op i 1 = 1) (i : ι) (x : M i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  .symm <| funext <| apply_mulSingle op h i x

@[to_additive]
lemma mulSingle_op₂ (op : ∀ i, M i → N i → O i) (h : ∀ i, op i 1 1 = 1) (i : ι) (x : M i)
    (y : N i) : mulSingle i (op i x y) = fun j ↦ op j (mulSingle i x j) (mulSingle i y j) :=
  .symm <| funext <| apply_mulSingle₂ op h i x y

@[to_additive]
lemma mulSingle_injective (i : ι) : Function.Injective (mulSingle i : M i → ∀ i, M i) :=
  Function.update_injective _ i

@[to_additive (attr := simp)]
lemma mulSingle_inj (i : ι) {x y : M i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (mulSingle_injective _).eq_iff

variable {M : Type*} [One M]

/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive /-- On non-dependent functions, `Pi.single` can be expressed as an `ite` -/]
lemma mulSingle_apply (i : ι) (x : M) (i' : ι) :
    (mulSingle i x : ι → M) i' = if i' = i then x else 1 :=
  Function.update_apply (1 : ι → M) i x i'

-- Porting note: added type ascription (_ : ι → M)
/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive /-- On non-dependent functions, `Pi.single` is symmetric in the two indices. -/]
lemma mulSingle_comm (i : ι) (x : M) (j : ι) :
    (mulSingle i x : ι → M) j = (mulSingle j x : ι → M) i := by simp [mulSingle_apply, eq_comm]

variable [DecidableEq ι']

@[to_additive (attr := simp)]
theorem curry_mulSingle (i : ι × ι') (b : M) :
    curry (Pi.mulSingle i b) = Pi.mulSingle i.1 (Pi.mulSingle i.2 b) :=
  curry_update _ _ _

@[to_additive (attr := simp)]
theorem uncurry_mulSingle_mulSingle (i : ι) (i' : ι') (b : M) :
    uncurry (Pi.mulSingle i (Pi.mulSingle i' b)) = Pi.mulSingle (i, i') b :=
  uncurry_update_update _ _ _ _

end Pi
