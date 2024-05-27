/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Algebra.Algebra.Pi

#align_import order.filter.zero_and_bounded_at_filter from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `ZeroAtFilter` as well as being
`BoundedAtFilter`. Alongside this we construct the `Submodule`, `AddSubmonoid` of functions
that are `ZeroAtFilter`. Similarly, we construct the `Submodule` and `Subalgebra` of functions
that are `BoundedAtFilter`.

-/


namespace Filter

variable {𝕜 α β : Type*}

open Topology

/-- If `l` is a filter on `α`, then a function `f : α → β` is `ZeroAtFilter l`
  if it tends to zero along `l`. -/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)
#align filter.zero_at_filter Filter.ZeroAtFilter

theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds
#align filter.zero_zero_at_filter Filter.zero_zeroAtFilter

nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α → β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using hf.add hg
#align filter.zero_at_filter.add Filter.ZeroAtFilter.add

nonrec theorem ZeroAtFilter.neg [TopologicalSpace β] [AddGroup β] [ContinuousNeg β] {l : Filter α}
    {f : α → β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by simpa using hf.neg
#align filter.zero_at_filter.neg Filter.ZeroAtFilter.neg

theorem ZeroAtFilter.smul [TopologicalSpace β] [Zero 𝕜] [Zero β]
    [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using hf.const_smul c
#align filter.zero_at_filter.smul Filter.ZeroAtFilter.smul

variable (𝕜) in
/-- `zeroAtFilterSubmodule l` is the submodule of `f : α → β` which
tend to zero along `l`. -/
def zeroAtFilterSubmodule
    [TopologicalSpace β] [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β]
    [ContinuousAdd β] [ContinuousConstSMul 𝕜 β]
    (l : Filter α) : Submodule 𝕜 (α → β) where
  carrier := ZeroAtFilter l
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c
#align filter.zero_at_filter_submodule Filter.zeroAtFilterSubmodule

/-- `zeroAtFilterAddSubmonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β) where
  carrier := ZeroAtFilter l
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l
#align filter.zero_at_filter_add_submonoid Filter.zeroAtFilterAddSubmonoid

/-- If `l` is a filter on `α`, then a function `f: α → β` is `BoundedAtFilter l`
if `f =O[l] 1`. -/
def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)
#align filter.bounded_at_filter Filter.BoundedAtFilter

theorem ZeroAtFilter.boundedAtFilter [NormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f := by
  rw [ZeroAtFilter, ← Asymptotics.isLittleO_const_iff (one_ne_zero' ℝ)] at hf
  exact hf.isBigO
#align filter.zero_at_filter.bounded_at_filter Filter.ZeroAtFilter.boundedAtFilter

theorem const_boundedAtFilter [Norm β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α → β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l
#align filter.const_bounded_at_filter Filter.const_boundedAtFilter

nonrec theorem BoundedAtFilter.add [SeminormedAddCommGroup β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using hf.add hg
#align filter.bounded_at_filter.add Filter.BoundedAtFilter.add

theorem BoundedAtFilter.neg [SeminormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left
#align filter.bounded_at_filter.neg Filter.BoundedAtFilter.neg

theorem BoundedAtFilter.smul
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [BoundedSMul 𝕜 β]
    {l : Filter α} {f : α → β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c
#align filter.bounded_at_filter.smul Filter.BoundedAtFilter.smul

nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert Asymptotics.isBigO_refl (E := ℝ) _ l
  simp
#align filter.bounded_at_filter.mul Filter.BoundedAtFilter.mul

variable (𝕜) in
/-- The submodule of functions that are bounded along a filter `l`. -/
def boundedFilterSubmodule
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [BoundedSMul 𝕜 β] (l : Filter α) :
    Submodule 𝕜 (α → β) where
  carrier := BoundedAtFilter l
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c
#align filter.bounded_filter_submodule Filter.boundedFilterSubmodule

variable (𝕜) in
/-- The subalgebra of functions that are bounded along a filter `l`. -/
def boundedFilterSubalgebra
    [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra 𝕜 β] [BoundedSMul 𝕜 β] (l : Filter α) :
    Subalgebra 𝕜 (α → β) :=
  Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg ↦ by simpa only [Pi.one_apply, mul_one, norm_mul] using hf.mul hg)
#align filter.bounded_filter_subalgebra Filter.boundedFilterSubalgebra

end Filter
