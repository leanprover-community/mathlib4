/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.Congruence.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Interactions between `∑, ∏` and two sided ideals

-/

namespace TwoSidedIdeal

section sum

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

end sum

section prod

section ring

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R)

lemma listProd_mem {ι : Type*} (l : List ι) (f : ι → R) (hl : ∃ x ∈ l, f x ∈ I) :
    (l.map f).prod ∈ I := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hl
  | cons x l ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at hl
    rcases hl with h|⟨y, ⟨hy₁, hy₂⟩⟩
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_right _ _ h
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_left _ _ $ ih ⟨y, hy₁, hy₂⟩

end ring

section commRing

variable {R : Type*} [CommRing R] (I : TwoSidedIdeal R)

lemma multiSetProd_mem {ι : Type*} (s : Multiset ι) (f : ι → R) (hs : ∃ x ∈ s, f x ∈ I) :
    (s.map f).prod ∈ I := by
  rcases s
  simpa using listProd_mem (hl := hs)

lemma finsetProd_mem {ι : Type*} (s : Finset ι) (f : ι → R) (hs : ∃ x ∈ s, f x ∈ I) :
    s.prod f ∈ I := by
  rcases s
  simpa using multiSetProd_mem (hs := hs)

end commRing

end prod

end TwoSidedIdeal
