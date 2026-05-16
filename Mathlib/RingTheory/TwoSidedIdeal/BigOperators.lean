/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.Congruence.BigOperators
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Interactions between `∑, ∏` and two-sided ideals

-/

public section

namespace TwoSidedIdeal

section sum

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

lemma listSum_mem {ι : Type*} (l : List ι) (f : ι → R) (hl : ∀ x ∈ l, f x ∈ I) :
    (l.map f).sum ∈ I := by
  rw [mem_iff, ← List.sum_map_zero]
  exact I.ringCon.listSum l hl

lemma multisetSum_mem {ι : Type*} (s : Multiset ι) (f : ι → R) (hs : ∀ x ∈ s, f x ∈ I) :
    (s.map f).sum ∈ I := by
  rw [mem_iff, ← Multiset.sum_map_zero]
  exact I.ringCon.multisetSum s hs

lemma finsetSum_mem {ι : Type*} (s : Finset ι) (f : ι → R) (hs : ∀ x ∈ s, f x ∈ I) :
    s.sum f ∈ I := by
  rw [mem_iff, ← Finset.sum_const_zero]
  exact I.ringCon.finsetSum s hs

lemma finsuppSum_mem {ι : Type*} {β : Type*} [Zero β]
    {f : ι →₀ β} (g : ι → β → R) (h : ∀ i ∈ f.support, g i (f i) ∈ I) :
    f.sum g ∈ I :=
  finsetSum_mem _ _ _ h

lemma dfinsuppSum_mem {ι : Type*} {β : ι → Type*}
    [DecidableEq ι] [∀ i, Zero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)]
    {f : Π₀ i, β i} (g : (i : ι) → β i → R) (h : ∀ i ∈ f.support, g i (f i) ∈ I) :
    f.sum g ∈ I :=
  finsetSum_mem _ _ _ h

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
    rcases hl with h | hal
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_right _ _ h
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_left _ _ <| ih hal

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

lemma finsuppProd_mem {ι : Type*} {β : Type*} {M : Type*}
    [Add M] [CommMonoid M] [Zero β]
    (h : ι → β → R) {f : ι →₀ β} (H : ∃ i ∈ f.support, h i (f i) ∈ I) :
    f.prod h ∈ I :=
  finsetProd_mem _ _ _ H

lemma dfinsuppProd_mem {ι : Type*} {β : ι → Type*}
    [DecidableEq ι] [∀ i, Zero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)]
    {f : Π₀ i, β i} (g : (i : ι) → β i → R) (h : ∃ i ∈ f.support, g i (f i) ∈ I) :
    f.prod g ∈ I :=
  finsetProd_mem _ _ _ h

end commRing

end prod

end TwoSidedIdeal
