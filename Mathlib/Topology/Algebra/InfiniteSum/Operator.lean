/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! # Infinite sums with operator norm  -/

public section

namespace ContinuousLinearMap

variable {ι R M M₂ : Type*} [NontriviallyNormedField R] [SeminormedAddCommGroup M] [NormedSpace R M]
  [SeminormedAddCommGroup M₂] [NormedSpace R M₂] {L : SummationFilter ι}

theorem hasSum_apply {f : ι → M →L[R] M₂} {g : M →L[R] M₂} (hf : HasSum f g L) (x : M) :
    HasSum (f · x) (g x) L :=
  (ContinuousLinearMap.apply R M₂ x).hasSum hf

theorem summable_apply {f : ι → M →L[R] M₂} (hf : Summable f L) (x : M) :
    Summable (f · x) L :=
  (ContinuousLinearMap.apply R M₂ x).summable hf

theorem tsum_apply [T2Space M₂] [L.NeBot] {f : ι → M →L[R] M₂} (hf : Summable f L) (x : M) :
    (∑'[L] n, f n) x = ∑'[L] n, f n x :=
  (ContinuousLinearMap.apply R M₂ x).map_tsum hf

end ContinuousLinearMap
