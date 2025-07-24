/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!
# Rank and torsion

## Main statements

- `rank_quotient_eq_of_le_torsion` : `rank M/N = rank M` if `N ≤ torsion M`.
-/

open Submodule

theorem rank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hN : M' ≤ torsion R M) : Module.rank R (M ⧸ M') = Module.rank R M :=
  (rank_quotient_le M').antisymm <| by
    nontriviality R
    rw [Module.rank]
    refine ciSup_le fun ⟨s, hs⟩ ↦ LinearIndependent.cardinal_le_rank (v := (M'.mkQ ·)) ?_
    rw [LinearIndepOn, linearIndependent_iff'] at hs
    simp_rw [linearIndependent_iff', ← map_smul, ← map_sum, mkQ_apply, Quotient.mk_eq_zero]
    intro t g hg i hi
    obtain ⟨r, hg⟩ := hN hg
    simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at hg
    exact r.prop _ (mul_comm (g i) r ▸ hs t _ hg i hi)
