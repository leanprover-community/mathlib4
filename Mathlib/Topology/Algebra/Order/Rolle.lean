/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.T5

#align_import analysis.calculus.local_extr from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Rolle's Theorem (topological part)

In this file we prove the purely topological part of Rolle's Theorem:
a function that is continuous on an interval $[a, b]$, $a < b$,
has a local extremum at a point $x ∈ (a, b)$ provided that $f(a)=f(b)$.
We also prove several variations of this statement.

In `Mathlib/Analysis/Calculus/LocalExtr/Rolle` we use these lemmas
to prove several versions of Rolle's Theorem from calculus.

## Keywords
local minimum, local maximum, extremum, Rolle's Theorem
-/

open Filter Set Topology

variable {X Y : Type*}
  [ConditionallyCompleteLinearOrder X] [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X]
  [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
  {f : X → Y} {a b : X} {l : Y}

/-- A continuous function on a closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the interval. -/
theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x :=
    isCompact_Icc.exists_isMinOn ne hfc
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C :=
    isCompact_Icc.exists_isMaxOn ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : ∀ x ∈ Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx ↦ ?_⟩
      simp only [mem_setOf_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
    · refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 <| mt ?_ hC, lt_of_le_of_ne Cmem.2 <| mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
  · refine ⟨c, ⟨lt_of_le_of_ne cmem.1 <| mt ?_ hc, lt_of_le_of_ne cmem.2 <| mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
#align exists_Ioo_extr_on_Icc exists_Ioo_extr_on_Icc

/-- A continuous function on a closed interval with `f a = f b`
has a local extremum at some point of the corresponding open interval. -/
theorem exists_isLocalExtr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
  ⟨c, cmem, hc.isLocalExtr <| Icc_mem_nhds cmem.1 cmem.2⟩
#align exists_local_extr_Ioo exists_isLocalExtr_Ioo

/-- If a function `f` is continuous on an open interval
and tends to the same value at its endpoints, then it has an extremum on this open interval. -/
lemma exists_isExtrOn_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Ioo a b) c := by
  have h : EqOn (extendFrom (Ioo a b) f) f (Ioo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : ∃ c ∈ Ioo a b, IsExtrOn (extendFrom (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuousOn_Icc_extendFrom_Ioo hab.ne hfc ha hb)
      ((eq_lim_at_left_extendFrom_Ioo hab ha).trans (eq_lim_at_right_extendFrom_Ioo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩

/-- If a function `f` is continuous on an open interval
and tends to the same value at its endpoints,
then it has a local extremum on this open interval. -/
lemma exists_isLocalExtr_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioo_of_tendsto hab hfc ha hb
  ⟨c, cmem, hc.isLocalExtr <| Ioo_mem_nhds cmem.1 cmem.2⟩
