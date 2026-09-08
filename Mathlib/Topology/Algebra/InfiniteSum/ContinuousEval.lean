/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Hom.ContinuousEval

import Mathlib.Data.FunLike.Group

/-! # Applying an infinite sum of functions

This file provides lemmas for `(∏'[L] n, f n) x` and `(∑'[L] n, f n) x` where `f` is a family of
functions. We state this for `FunLike` objects that are `ContinuousEvalConst`. This is applicable
to e.g. `ContinuousLinearMap`.
-/

public section

variable {α β γ F : Type*} [TopologicalSpace β] [CommMonoid β]
  [FunLike F α β] [TopologicalSpace F] [CommMonoid F] [ContinuousEvalConst F α β]
  [IsMulApply F α β] [IsOneApply F α β] {f : γ → F} {g : F} {L : SummationFilter γ}

/-- See also `Pi.hasProd` for bare pi type. -/
@[to_additive /-- See also `Pi.hasSum` for bare pi type. -/]
theorem hasProd_apply (hf : HasProd f g L) (x : α) : HasProd (f · x) (g x) L :=
  hf.map ((Pi.evalMonoidHom _ x).comp (FunLike.coeMonoidHom F α β)) (continuous_eval_const x)

/-- See also `Pi.multipliable` for bare pi type. -/
@[to_additive /-- See also `Pi.summable` for bare pi type. -/]
theorem multipliable_apply (hf : Multipliable f L) (x : α) : Multipliable (f · x) L :=
  hf.map ((Pi.evalMonoidHom _ x).comp (FunLike.coeMonoidHom F α β)) (continuous_eval_const x)

/-- See also `Pi.tprod_apply` for bare pi type. -/
@[to_additive /-- See also `Pi.tsum_apply` for bare pi type. -/]
theorem tprod_apply [T2Space β] [L.NeBot] (hf : Multipliable f L) (x : α) :
    (∏'[L] n, f n) x = ∏'[L] n, f n x :=
  hf.map_tprod ((Pi.evalMonoidHom _ x).comp (FunLike.coeMonoidHom F α β)) (continuous_eval_const x)
