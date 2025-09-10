/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# The Logarithmic derivative of an infinite product

We show that if we have an infinite product of functions `f` that is locally uniformly convergent,
then the logarithmic derivative of the product is the sum of the logarithmic derivatives of the
individual functions.

-/

open Complex

theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set ℂ} (hs : IsOpen s) {x : s} {f : ι → ℂ → ℂ}
    (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) s)
    (hm : Summable fun i ↦ logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f s)
    (hnez : ∏' i, f i x ≠ 0) :
    logDeriv (∏' i, f i ·) x = ∑' i, logDeriv (f i) x := by
  rw [Eq.comm, ← hm.hasSum_iff]
  refine logDeriv_tendsto hs x htend.hasProdLocallyUniformlyOn (.of_forall <| by fun_prop) hnez
    |>.congr fun b ↦ ?_
  rw [logDeriv_prod _ _ _ (fun i _ ↦ hf i)
    (fun i _ ↦ (hd i x x.2).differentiableAt (hs.mem_nhds x.2))]
