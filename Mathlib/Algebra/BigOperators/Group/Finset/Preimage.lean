/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Finset.Preimage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums and products over preimages of finite sets.
-/

assert_not_exists MonoidWithZero MulAction OrderedCommMonoid

variable {ι κ β : Type*}

open Fin Function

namespace Finset

variable [CommMonoid β]

@[to_additive]
lemma prod_preimage' (f : ι → κ) [DecidablePred (· ∈ Set.range f)] (s : Finset κ) (hf) (g : κ → β) :
    ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s with x ∈ Set.range f, g x := by
  classical
  calc
    ∏ x ∈ preimage s f hf, g (f x) = ∏ x ∈ image f (preimage s f hf), g x :=
      Eq.symm <| prod_image <| by simpa [mem_preimage, Set.InjOn] using hf
    _ = ∏ x ∈ s with x ∈ Set.range f, g x := by rw [image_preimage]

@[to_additive]
lemma prod_preimage (f : ι → κ) (s : Finset κ) (hf) (g : κ → β)
    (hg : ∀ x ∈ s, x ∉ Set.range f → g x = 1) :
    ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s, g x := by
  classical rw [prod_preimage', prod_filter_of_ne]; exact fun x hx ↦ Not.imp_symm (hg x hx)

@[to_additive]
lemma prod_preimage_of_bij (f : ι → κ) (s : Finset κ) (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) (g : κ → β) :
    ∏ x ∈ s.preimage f hf.injOn, g (f x) = ∏ x ∈ s, g x :=
  prod_preimage _ _ hf.injOn g fun _ hs h_f ↦ (h_f <| hf.subset_range hs).elim

end Finset
