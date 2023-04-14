/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler

! This file was ported from Lean 3 source module order.filter.zero_and_bounded_at_filter
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Submodule.Basic
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `zero_at_filter` as well as being
`bounded_at_filter`. Alongside this we construct the `submodule`, `add_submonoid` of functions
that are `zero_at_filter`. Similarly, we construct the `submodule` and `subalgebra` of functions
that are `bounded_at_filter`.

-/


namespace Filter

variable {α β : Type _}

open Topology

/-- If `l` is a filter on `α`, then a function `f : α → β` is `zero_at_filter l`
  if it tends to zero along `l`. -/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)
#align filter.zero_at_filter Filter.ZeroAtFilter

theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds
#align filter.zero_zero_at_filter Filter.zero_zeroAtFilter

theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β] {l : Filter α}
    {f g : α → β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) : ZeroAtFilter l (f + g) := by
  simpa using hf.add hg
#align filter.zero_at_filter.add Filter.ZeroAtFilter.add

theorem ZeroAtFilter.neg [TopologicalSpace β] [AddGroup β] [ContinuousNeg β] {l : Filter α}
    {f : α → β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by simpa using hf.neg
#align filter.zero_at_filter.neg Filter.ZeroAtFilter.neg

theorem ZeroAtFilter.smul {𝕜 : Type _} [TopologicalSpace 𝕜] [TopologicalSpace β] [Zero 𝕜] [Zero β]
    [SMulWithZero 𝕜 β] [ContinuousSMul 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using hf.const_smul c
#align filter.zero_at_filter.smul Filter.ZeroAtFilter.smul

/-- `zero_at_filter_submodule l` is the submodule of `f : α → β` which
tend to zero along `l`. -/
def zeroAtFilterSubmodule [TopologicalSpace β] [Semiring β] [ContinuousAdd β] [ContinuousMul β]
    (l : Filter α) : Submodule β (α → β)
    where
  carrier := ZeroAtFilter l
  zero_mem' := zero_zeroAtFilter l
  add_mem' a b ha hb := ha.add hb
  smul_mem' c f hf := hf.smul c
#align filter.zero_at_filter_submodule Filter.zeroAtFilterSubmodule

/-- `zero_at_filter_add_submonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β)
    where
  carrier := ZeroAtFilter l
  add_mem' a b ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l
#align filter.zero_at_filter_add_submonoid Filter.zeroAtFilterAddSubmonoid

/-- If `l` is a filter on `α`, then a function `f: α → β` is `bounded_at_filter l`
if `f =O[l] 1`. -/
def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)
#align filter.bounded_at_filter Filter.BoundedAtFilter

theorem ZeroAtFilter.boundedAtFilter [NormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f :=
  by
  rw [zero_at_filter, ← Asymptotics.isLittleO_const_iff (one_ne_zero' ℝ)] at hf
  exact hf.is_O
#align filter.zero_at_filter.bounded_at_filter Filter.ZeroAtFilter.boundedAtFilter

theorem const_boundedAtFilter [NormedField β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α → β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l
#align filter.const_bounded_at_filter Filter.const_boundedAtFilter

theorem BoundedAtFilter.add [NormedAddCommGroup β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using hf.add hg
#align filter.bounded_at_filter.add Filter.BoundedAtFilter.add

theorem BoundedAtFilter.neg [NormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left
#align filter.bounded_at_filter.neg Filter.BoundedAtFilter.neg

theorem BoundedAtFilter.smul {𝕜 : Type _} [NormedField 𝕜] [NormedAddCommGroup β] [NormedSpace 𝕜 β]
    {l : Filter α} {f : α → β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c
#align filter.bounded_at_filter.smul Filter.BoundedAtFilter.smul

theorem BoundedAtFilter.mul [NormedField β] {l : Filter α} {f g : α → β} (hf : BoundedAtFilter l f)
    (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) :=
  by
  refine' (hf.mul hg).trans _
  convert Asymptotics.isBigO_refl _ l
  ext x
  simp
#align filter.bounded_at_filter.mul Filter.BoundedAtFilter.mul

/-- The submodule of functions that are bounded along a filter `l`. -/
def boundedFilterSubmodule [NormedField β] (l : Filter α) : Submodule β (α → β)
    where
  carrier := BoundedAtFilter l
  zero_mem' := const_boundedAtFilter l 0
  add_mem' f g hf hg := hf.add hg
  smul_mem' c f hf := hf.smul c
#align filter.bounded_filter_submodule Filter.boundedFilterSubmodule

/-- The subalgebra of functions that are bounded along a filter `l`. -/
def boundedFilterSubalgebra [NormedField β] (l : Filter α) : Subalgebra β (α → β) :=
  by
  refine' Submodule.toSubalgebra (bounded_filter_submodule l) _ fun f g hf hg => _
  · exact const_bounded_at_filter l (1 : β)
  · simpa only [Pi.one_apply, mul_one, norm_mul] using hf.mul hg
#align filter.bounded_filter_subalgebra Filter.boundedFilterSubalgebra

end Filter

