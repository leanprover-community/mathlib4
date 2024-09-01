/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Topology.Separation
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local maxima from monotonicity and antitonicityOrder-closed topologies

In this file we prove a lemma that is useful for the First Derivative Test in calculus.

## Main statement

* `isLocalMax_of_mono_anti` : if a function `f` is monotone to the left of `x`
  and antitone to the right of `x` then `f` has a local maximum at `x`.

-/

open Set Topology

/-- If `f` is monotone on `(a,b]` and antitone on `[b,c)` then `f` has
a local maximum at `b`. -/
lemma isLocalMax_of_mono_anti.{u, v}
    {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {β : Type v} [Preorder β]
    {a b c : α} (g₀ : a < b) (g₁ : b < c) {f : α → β}
    (h₀ : MonotoneOn f (Ioc a b))
    (h₁ : AntitoneOn f (Ico b c)) : IsLocalMax f b := by
  unfold IsLocalMax IsMaxFilter Filter.Eventually
  rw [nhds_def, Filter.mem_iInf]
  use {Ioo a c}, (toFinite _), (fun _ ↦ Ioo a c ∪ {x | f x ≤ f b})
  simp only [mem_setOf_eq, Subtype.forall, mem_singleton_iff, forall_eq, mem_Ioo,
    iInter_coe_set, iInter_iInter_eq_left]
  constructor
  · exact Filter.mem_iInf_of_mem
      (by simp_all only [and_self, true_and]; apply isOpen_Ioo)
      (by simp_all)
  · ext u
    simp only [mem_setOf_eq, mem_union, mem_Ioo, iff_or_self, and_imp]
    intros
    exact (em (u < b)).elim
      (fun H => h₀ (by simp_all only [mem_Ioc, true_and]; exact le_of_lt H)
        (by simp_all) (le_of_lt H))
      (fun H => h₁ (by simp_all) (by simp_all) (le_of_not_lt H))
