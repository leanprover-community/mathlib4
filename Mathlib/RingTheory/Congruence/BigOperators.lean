/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.GroupTheory.Congruence.BigOperators
public import Mathlib.RingTheory.Congruence.Defs

/-!
# Interactions between `∑, ∏` and `RingCon`

-/

public section

namespace RingCon

/-- Congruence relation of a ring preserves finite product indexed by a list. -/
protected lemma listProd {ι S : Type*} [Add S] [Monoid S]
    (t : RingCon S) (l : List ι) {f g : ι → S} (h : ∀ i ∈ l, t (f i) (g i)) :
    t (l.map f).prod (l.map g).prod :=
  t.toCon.list_prod h

/-- Congruence relation of a ring preserves finite sum indexed by a list. -/
protected lemma listSum {ι S : Type*} [AddMonoid S] [Mul S]
    (t : RingCon S) (l : List ι) {f g : ι → S} (h : ∀ i ∈ l, t (f i) (g i)) :
    t (l.map f).sum (l.map g).sum :=
  t.toAddCon.list_sum h

/-- Congruence relation of a ring preserves finite product indexed by a multiset. -/
protected lemma multisetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S)
    (s : Multiset ι) {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.map f).prod (s.map g).prod :=
  t.toCon.multiset_prod h

/-- Congruence relation of a ring preserves finite sum indexed by a multiset. -/
protected lemma multisetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
    (s : Multiset ι) {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.map f).sum (s.map g).sum :=
  t.toAddCon.multiset_sum h

/-- Congruence relation of a ring preserves finite product. -/
protected lemma finsetProd {ι S : Type*} [Add S] [CommMonoid S] (t : RingCon S) (s : Finset ι)
    {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.prod f) (s.prod g) :=
  t.toCon.finsetProd s h

/-- Congruence relation of a ring preserves finite sum. -/
protected lemma finsetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
    {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.sum f) (s.sum g) :=
  t.toAddCon.finsetSum s h

protected lemma finsuppProd {ι : Type*} {β : Type*} {M : Type*}
    [Add M] [CommMonoid M] [Zero β]
    (c : RingCon M) (h : ι → β → M) (h' : ι → β → M)
    {f g : ι →₀ β} (hf : ∀ i, h i 0 = 1) (hf' : ∀ i, h' i 0 = 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') :=
  c.toCon.finsuppProd h h' hf hf' H

protected lemma finsuppSum {ι : Type*} {β : Type*} {M : Type*}
    [AddCommMonoid M] [Mul M] [Zero β]
    (c : RingCon M) (h : ι → β → M) (h' : ι → β → M)
    {f g : ι →₀ β} (hf : ∀ i, h i 0 = 0) (hf' : ∀ i, h' i 0 = 0)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sum h) (g.sum h') :=
  c.toAddCon.finsuppSum h h' hf hf' H

protected lemma dfinsuppProd {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [Add M] [CommMonoid M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : RingCon M) (h : (i : ι) → β i → M) (h' : (i : ι) → β i → M)
    {f g : Π₀ i, β i} (hf : ∀ i, h i 0 = 1) (hf' : ∀ i, h' i 0 = 1)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.prod h) (g.prod h') :=
  c.toCon.dfinsuppProd h h' hf hf' H

protected lemma dfinsuppSum {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [∀ i, Zero (β i)] [∀ i (y : β i), Decidable (y ≠ 0)]
    (c : RingCon M) (h : (i : ι) → β i → M) (h' : (i : ι) → β i → M)
    {f g : Π₀ i, β i} (hf : ∀ i, h i 0 = 0) (hf' : ∀ i, h' i 0 = 0)
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sum h) (g.sum h') :=
  c.toAddCon.dfinsuppSum h h' hf hf' H

protected lemma dfinsuppSumAddHom {ι : Type*} {β : ι → Type*} {M : Type*}
    [DecidableEq ι] [AddCommMonoid M] [Mul M] [∀ i, AddCommMonoid (β i)]
    (c : RingCon M) (h : (i : ι) → β i →+ M) (h' : (i : ι) → β i →+ M) {f g : Π₀ i, β i}
    (H : ∀ i, c (h i (f i)) (h' i (g i))) :
    c (f.sumAddHom h) (g.sumAddHom h') :=
  c.toAddCon.dfinsuppSumAddHom h h' H

end RingCon
