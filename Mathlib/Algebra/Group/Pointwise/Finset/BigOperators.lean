/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Pointwise big operators on finsets

This file contains basic results on applying big operators (product and sum) on finsets.

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open scoped Pointwise

variable {α ι : Type*}

namespace Finset

section CommMonoid

variable [CommMonoid α]

variable [DecidableEq α]

@[to_additive (attr := simp, norm_cast)]
theorem coe_prod (s : Finset ι) (f : ι → Finset α) :
    ↑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : Set α) :=
  map_prod ((coeMonoidHom) : Finset α →* Set α) _ _

omit [DecidableEq α]
variable [DecidableEq ι]

@[to_additive (attr := simp)] lemma prod_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s⁻¹, f i = ∏ i ∈ s, f i⁻¹ := prod_image inv_injective.injOn

@[to_additive existing, simp] lemma prod_neg_index [InvolutiveNeg ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ -s, f i = ∏ i ∈ s, f (-i) := prod_image neg_injective.injOn

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α] [DecidableEq ι]

@[to_additive existing, simp] lemma sum_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s⁻¹, f i = ∑ i ∈ s, f i⁻¹ := sum_image inv_injective.injOn

end AddCommMonoid

end Finset
