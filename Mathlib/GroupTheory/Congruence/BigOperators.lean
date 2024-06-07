/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Multiset
import Mathlib.Algebra.BigOperators.Group.List

/-!
# Interactions between `∑, ∏` and `(Add)Con`

-/

open BigOperators

namespace Con

/-- Multiplicative congruence relations preserve product indexed by a list. -/
@[to_additive "Additive congruence relations preserve sum indexed by a list."]
protected theorem list_prod {ι M : Type*} [CommMonoid M] (c : Con M) {l : List ι} {f g : ι → M}
    (h : ∀ x ∈ l, c (f x) (g x)) :
    c (l.map f).prod (l.map g).prod := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using c.refl 1
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    refine c.mul (h _ (by simp)) <| ih fun k hk => h _ ?_
    simp only [List.mem_cons]
    tauto

/-- Multiplicative congruence relations preserve product indexed by a multiset. -/
@[to_additive "Additive congruence relations preserve sum indexed by a multiset."]
protected theorem multiset_prod {ι M : Type*} [CommMonoid M] (c : Con M) {s : Multiset ι}
    {f g : ι → M} (h : ∀ x ∈ s, c (f x) (g x)) :
    c (s.map f).prod (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    simpa only [Multiset.map_zero, Multiset.prod_zero] using c.refl 1
  | cons x xs ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    refine c.mul (h _ (by simp)) <| ih fun k hk => h _ ?_
    simp only [Multiset.mem_cons]
    tauto

/-- Multiplicative congruence relations preserve finite product. -/
@[to_additive "Additive congruence relations preserve finite sum."]
protected theorem finset_prod {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    {f g : ι → M} (h : ∀ i ∈ s, c (f i) (g i)) :
    c (s.prod f) (s.prod g) := by
  classical
  induction s using Finset.cons_induction_on with
  | h₁ => simpa using c.refl 1
  | @h₂ i s hi ih =>
    rw [Finset.prod_cons hi, Finset.prod_cons hi]
    exact c.mul (h _ (by simp)) <| ih fun i hi ↦ h _ (by aesop)

end Con
