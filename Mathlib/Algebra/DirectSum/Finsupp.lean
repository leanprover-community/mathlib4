/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.direct_sum.finsupp
! leanprover-community/mathlib commit aca0874a9ce95510752f4075f80f273172e9b177
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.
-/


universe u v w

noncomputable section

open DirectSum

open LinearMap Submodule

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

section finsuppLequivDirectSum

variable (R M) (ι : Type _) [DecidableEq ι]

/-- The finitely supported functions `ι →₀ M` are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsuppLEquivDirectSum : (ι →₀ M) ≃ₗ[R] ⨁ _ : ι, M :=
  haveI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  finsuppLequivDFinsupp R
#align finsupp_lequiv_direct_sum finsuppLEquivDirectSum

@[simp]
theorem finsuppLEquivDirectSum_single (i : ι) (m : M) :
    finsuppLEquivDirectSum R M ι (Finsupp.single i m) = DirectSum.lof R ι _ i m :=
  Finsupp.toDFinsupp_single i m
#align finsupp_lequiv_direct_sum_single finsuppLEquivDirectSum_single

@[simp]
theorem finsuppLEquivDirectSum_symm_lof (i : ι) (m : M) :
    (finsuppLEquivDirectSum R M ι).symm (DirectSum.lof R ι _ i m) = Finsupp.single i m :=
  letI : ∀ m : M, Decidable (m ≠ 0) := Classical.decPred _
  DFinsupp.toFinsupp_single i m
#align finsupp_lequiv_direct_sum_symm_lof finsuppLEquivDirectSum_symm_lof

end finsuppLequivDirectSum
