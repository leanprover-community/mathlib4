/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# The Logarithmic derivative of an infinite product

We show that if we have an infinite product of functions `f` that is locally uniformly convergent,
then the logarithmic derivative of the product is the sum of the logarithmic derivatives of the
individual functions.

-/

open  TopologicalSpace Filter  Complex Set Function

theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set ℂ} (hs : IsOpen s) {x : s} {f : ι → ℂ → ℂ}
    (hf : ∀ i, f i x ≠ 0) (hd : ∀ i : ι, DifferentiableOn ℂ (f i) s)
    (hm : Summable fun i ↦ logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f s)
    (hnez : ∏' (i : ι), f i x ≠ 0) : logDeriv (∏' i : ι, f i ·) x = ∑' i : ι, logDeriv (f i) x := by
    apply symm
    rw [← Summable.hasSum_iff hm, HasSum]
    have := logDeriv_tendsto (f := fun (n : Finset ι) ↦ ∏ i ∈ n, (f i))
      (g := (∏' i : ι, f i ·)) (s := s) hs (p := atTop)
    simp only [eventually_atTop, ge_iff_le, ne_eq, forall_exists_index, Subtype.forall] at this
    conv =>
      enter [1]
      ext n
      rw [← logDeriv_prod _ _ _ (by intro i hi; apply hf i)
        (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
    apply (this x x.2 ?_ ⊥ ?_ hnez).congr
    · intro m
      congr
      aesop
    · convert hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
        htend.hasProdLocallyUniformlyOn
      simp
    · intro b hb z hz
      apply DifferentiableAt.differentiableWithinAt
      have hp : ∀ (i : ι), i ∈ b → DifferentiableAt ℂ (f i) z := by
        exact fun i hi ↦ (hd i z hz).differentiableAt (IsOpen.mem_nhds hs hz)
      simpa using  DifferentiableAt.finset_prod hp
