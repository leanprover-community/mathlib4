/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Algebra.Algebra.Pi

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `ZeroAtFilter` as well as being
`BoundedAtFilter`. Alongside this we construct the `Submodule`, `AddSubmonoid` of functions
that are `ZeroAtFilter`. Similarly, we construct the `Submodule` and `Subalgebra` of functions
that are `BoundedAtFilter`.

-/

@[expose] public section


namespace Filter

variable {𝕜 α β : Type*}

open Topology

/-- If `l` is a filter on `α`, then a function `f : α → β` is `ZeroAtFilter l`
  if it tends to zero along `l`. -/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)

theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds

nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α → β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using hf.add hg

nonrec theorem ZeroAtFilter.neg [TopologicalSpace β] [SubtractionMonoid β] [ContinuousNeg β]
    {l : Filter α} {f : α → β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by
  simpa using hf.neg

theorem ZeroAtFilter.smul [TopologicalSpace β] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousConstSMul 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using hf.const_smul c

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

/-- `zeroAtFilterAddSubmonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β) where
  carrier := ZeroAtFilter l
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l

/-- If `l` is a filter on `α`, then a function `f: α → β` is `BoundedAtFilter l`
if `f =O[l] 1`. -/
def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)

theorem ZeroAtFilter.boundedAtFilter [SeminormedAddGroup β] {l : Filter α} {f : α → β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f :=
  ((Asymptotics.isLittleO_one_iff _).mpr hf).isBigO

theorem const_boundedAtFilter [Norm β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α → β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l

-- TODO(https://github.com/leanprover-community/mathlib4/issues/19288): Remove all Comm in the next
-- three lemmas. This would require modifying the corresponding general asymptotics lemma.
nonrec theorem BoundedAtFilter.add [SeminormedAddCommGroup β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using hf.add hg

theorem BoundedAtFilter.neg [SeminormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left

theorem BoundedAtFilter.smul
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
    {l : Filter α} {f : α → β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c

nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert Asymptotics.isBigO_refl (E := ℝ) _ l
  simp

nonrec theorem ZeroAtFilter.mul_boundedAtFilter [SeminormedRing β] {l : Filter α}
    {f g : α → β} (hf : ZeroAtFilter l f) (hg : BoundedAtFilter l g) : ZeroAtFilter l (f * g) := by
  rw [ZeroAtFilter, ← Asymptotics.isLittleO_one_iff (F := ℝ)] at hf ⊢
  simpa using hf.mul_isBigO hg

nonrec theorem BoundedAtFilter.mul_zeroAtFilter [SeminormedRing β] {l : Filter α}
    {f g : α → β} (hf : BoundedAtFilter l f) (hg : ZeroAtFilter l g) : ZeroAtFilter l (f * g) := by
  rw [ZeroAtFilter, ← Asymptotics.isLittleO_one_iff (F := ℝ)] at hg ⊢
  simpa using hf.mul_isLittleO hg

variable (𝕜) in
/-- The submodule of functions that are bounded along a filter `l`. -/
def boundedFilterSubmodule
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) :
    Submodule 𝕜 (α → β) where
  carrier := BoundedAtFilter l
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c

variable (𝕜) in
/-- The subalgebra of functions that are bounded along a filter `l`. -/
def boundedFilterSubalgebra
    [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) :
    Subalgebra 𝕜 (α → β) :=
  Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg ↦ by simpa only [Pi.one_apply, mul_one, norm_mul] using hf.mul hg)

theorem BoundedAtFilter.prod {ι : Type} (s : Finset ι) [SeminormedCommRing β]
    {l : Filter α} {f : ι → α → β} (h : ∀ i ∈ s, BoundedAtFilter l (f i)) :
    BoundedAtFilter l (∏ i ∈ s, f i) :=
  (boundedFilterSubalgebra β l).prod_mem (f := f) h

end Filter
