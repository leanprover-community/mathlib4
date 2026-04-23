/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.RingTheory.Congruence.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.GroupTheory.Congruence.BigOperators
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Interactions between `∑, ∏` and `RingCon`

-/

public section

namespace RingCon

/-- Congruence relation of a ring preserves finite sum indexed by a list. -/
protected lemma listSum {ι S : Type*} [AddMonoid S] [Mul S]
    (t : RingCon S) (l : List ι) {f g : ι → S} (h : ∀ i ∈ l, t (f i) (g i)) :
    t (l.map f).sum (l.map g).sum :=
  t.toAddCon.list_sum h

/-- Congruence relation of a ring preserves finite sum indexed by a multiset. -/
protected lemma multisetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S)
    (s : Multiset ι) {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.map f).sum (s.map g).sum :=
  t.toAddCon.multiset_sum h

/-- Congruence relation of a ring preserves finite sum. -/
protected lemma finsetSum {ι S : Type*} [AddCommMonoid S] [Mul S] (t : RingCon S) (s : Finset ι)
    {f g : ι → S} (h : ∀ i ∈ s, t (f i) (g i)) :
    t (s.sum f) (s.sum g) :=
  t.toAddCon.finset_sum s h

end RingCon
