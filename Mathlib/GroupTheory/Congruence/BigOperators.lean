/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.GroupTheory.Congruence.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Interactions between `∑, ∏` and `(Add)Con`

-/

public section

namespace Con

/-- Multiplicative congruence relations preserve product indexed by a list. -/
@[to_additive /-- Additive congruence relations preserve sum indexed by a list. -/]
protected theorem list_prod {ι M : Type*} [MulOneClass M] (c : Con M) {l : List ι} {f g : ι → M}
    (h : ∀ x ∈ l, c (f x) (g x)) :
    c (l.map f).prod (l.map g).prod := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.prod_nil] using c.refl 1
  | cons x xs ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    exact c.mul (h _ <| .head _) <| ih fun k hk ↦ h _ (.tail _ hk)

/-- Multiplicative congruence relations preserve product indexed by a multiset. -/
@[to_additive /-- Additive congruence relations preserve sum indexed by a multiset. -/]
protected theorem multiset_prod {ι M : Type*} [CommMonoid M] (c : Con M) {s : Multiset ι}
    {f g : ι → M} (h : ∀ x ∈ s, c (f x) (g x)) :
    c (s.map f).prod (s.map g).prod := by
  rcases s; simpa using c.list_prod h

/-- Multiplicative congruence relations preserve finite product. -/
@[to_additive /-- Additive congruence relations preserve finite sum. -/]
protected theorem finsetProd {ι M : Type*} [CommMonoid M] (c : Con M) (s : Finset ι)
    {f g : ι → M} (h : ∀ i ∈ s, c (f i) (g i)) :
    c (s.prod f) (s.prod g) :=
  c.multiset_prod h

@[to_additive]
protected theorem finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [CommMonoid M] [Zero β]
    (c : Con M) (h : ι → β → M) (h' : ι → β → M)
    {f g : ι →₀ β} (hf : ∀ i, h i 0 = 1) (hf' : ∀ i, h' i 0 = 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') := by
  classical
  rw [Finsupp.prod_of_support_subset f
      (Finset.subset_union_left (s₁ := f.support) (s₂ := g.support)) _ (fun i _ ↦ hf i),
    Finsupp.prod_of_support_subset g
      (Finset.subset_union_right (s₁ := f.support) (s₂ := g.support)) _ (fun i _ ↦ hf' i)]
  exact c.finsetProd (f.support ∪ g.support) fun i _ ↦ H i

@[to_additive]
protected theorem dfinsuppProd {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [CommMonoid M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : Con M) (h : (i : ι) → β i → M) (h' : (i : ι) → β i → M)
    {f g : Π₀ i, β i} (hf : ∀ i, h i 0 = 1) (hf' : ∀ i, h' i 0 = 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') := by
  rw [DFinsupp.prod_of_support_subset (fun i _ ↦ hf i)
      (Finset.subset_union_left (s₁ := f.support) (s₂ := g.support)),
    DFinsupp.prod_of_support_subset (fun i _ ↦ hf' i)
      (Finset.subset_union_right (s₁ := f.support) (s₂ := g.support))]
  exact c.finsetProd (f.support ∪ g.support) fun i _ ↦ H i

protected theorem _root_.AddCon.dfinsuppSumAddHom {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [∀ i, AddCommMonoid (β i)]
    (c : AddCon M) (h : (i : ι) → β i →+ M) (h' : (i : ι) → β i →+ M) {f g : Π₀ i, β i}
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sumAddHom h) (g.sumAddHom h') := by
  classical
  simp_rw [DFinsupp.sumAddHom_apply]
  exact c.dfinsuppSum _ _ (map_zero <| h ·) (map_zero <| h' ·) H

@[deprecated (since := "2026-04-08")]
protected alias _root_.AddCon.finset_sum := AddCon.finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
protected alias finset_prod := Con.finsetProd


end Con
