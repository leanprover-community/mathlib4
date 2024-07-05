/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Congruence.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Interactions between `∑, ∏` and Two-Sided-Ideals

-/

namespace TwoSidedIdeal

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

lemma listSum_mem {ι : Type*} (l : List ι) (f : ι → R) (hl : ∀ x ∈ l, f x ∈ I) :
    (l.map f).sum ∈ I := by
  rw [mem_iff]
  convert I.ringCon.listSum l (f := f) (g := 0) hl
  exact List.sum_map_zero |>.symm

lemma multisetSum_mem {ι : Type*} (s : Multiset ι) (f : ι → R) (hs : ∀ x ∈ s, f x ∈ I) :
    (s.map f).sum ∈ I := by
  rw [mem_iff]
  convert I.ringCon.multisetSum s (f := f) (g := 0) hs
  exact Multiset.sum_map_zero |>.symm

lemma finsetSum_mem {ι : Type*} (s : Finset ι) (f : ι → R) (hs : ∀ x ∈ s, f x ∈ I) :
    s.sum f ∈ I := by
  rw [mem_iff]
  convert I.ringCon.finsetSum s (f := f) (g := 0) hs
  simp

end TwoSidedIdeal
