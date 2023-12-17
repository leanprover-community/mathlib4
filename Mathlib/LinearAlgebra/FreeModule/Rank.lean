/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Dimension
import Mathlib.SetTheory.Cardinal.Algebraic

#align_import linear_algebra.free_module.rank from "leanprover-community/mathlib"@"465d4301d8da5945ef1dc1b29fb34c2f2b315ac4"

/-!

# Extra results about `Module.rank`

This file contains some extra results not in `LinearAlgebra.Dimension`.

-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal

section Ring

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

open Module.Free

@[simp]
theorem rank_finsupp (ι : Type w) :
    Module.rank R (ι →₀ M) = Cardinal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M) := by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← bs.mk_eq_rank'', ← (Finsupp.basis fun _ : ι => bs).mk_eq_rank'', Cardinal.mk_sigma,
    Cardinal.sum_const]
#align rank_finsupp rank_finsupp

theorem rank_finsupp' (ι : Type v) : Module.rank R (ι →₀ M) = #ι * Module.rank R M := by
  simp [rank_finsupp]
#align rank_finsupp' rank_finsupp'

/-- The rank of `(ι →₀ R)` is `(#ι).lift`. -/
-- Porting note, this should not be `@[simp]`, as simp can prove it.
-- @[simp]
theorem rank_finsupp_self (ι : Type w) : Module.rank R (ι →₀ R) = Cardinal.lift.{u} #ι := by
  simp [rank_finsupp]
#align rank_finsupp_self rank_finsupp_self

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp_self' {ι : Type u} : Module.rank R (ι →₀ R) = #ι := by simp
#align rank_finsupp_self' rank_finsupp_self'

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_directSum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) := by
  let B i := chooseBasis R (M i)
  let b : Basis _ R (⨁ i, M i) := DFinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']
#align rank_direct_sum rank_directSum

/-- If `m` and `n` are `Fintype`, the rank of `m × n` matrices is `(#m).lift * (#n).lift`. -/
@[simp]
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) =
      Cardinal.lift.{max v w u, v} #m * Cardinal.lift.{max v w u, w} #n := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  have h := (Matrix.stdBasis R m n).mk_eq_rank
  rw [← lift_lift.{max v w u, max v w}, lift_inj] at h
  simpa using h.symm
#align rank_matrix rank_matrix

/-- If `m` and `n` are `Fintype` that lie in the same universe, the rank of `m × n` matrices is
  `(#n * #m).lift`. -/
@[simp high]
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = Cardinal.lift.{u} (#m * #n) := by
  rw [rank_matrix, lift_mul, lift_umax.{v, u}]
#align rank_matrix' rank_matrix'

/-- If `m` and `n` are `Fintype` that lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
-- @[simp] -- Porting note: simp can prove this
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = #m * #n := by simp
#align rank_matrix'' rank_matrix''

end Ring

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

open Module.Free

/-- The rank of `M ⊗[R] N` is `(Module.rank R M).lift * (Module.rank R N).lift`. -/
@[simp]
theorem rank_tensorProduct :
    Module.rank R (M ⊗[R] N) =
      Cardinal.lift.{w, v} (Module.rank R M) * Cardinal.lift.{v, w} (Module.rank R N) := by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := R) (M := N)
  rw [← bM.mk_eq_rank'', ← bN.mk_eq_rank'', ← (bM.tensorProduct bN).mk_eq_rank'', Cardinal.mk_prod]
#align rank_tensor_product rank_tensorProduct

/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(Module.rank R M) * (Module.rank R N)`. -/
theorem rank_tensorProduct' (N : Type v) [AddCommGroup N] [Module R N] [Module.Free R N] :
    Module.rank R (M ⊗[R] N) = Module.rank R M * Module.rank R N := by simp
#align rank_tensor_product' rank_tensorProduct'

end CommRing

section DivisionRing

variable (K : Type*) [DivisionRing K]

/-- The **Erdős-Kaplansky Theorem**. https://mathoverflow.net/a/168624/3332 -/
theorem rank_pi_nat : max ℵ₀ #K ≤ Module.rank K (ℕ → K) := by
  have aleph0_le : ℵ₀ ≤ Module.rank K (ℕ → K) := (rank_finsupp_self K ℕ).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact FunLike.coe_injective)
  have card_basis := Module.Free.rank_eq_card_chooseBasisIndex
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_lt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  let b := Module.Free.chooseBasis K (ℕ → K)
  let L := Subfield.closure (Set.range (fun i : _ × ℕ ↦ b i.1 i.2))
  have : #L < #K
  · refine (Subfield.cardinal_mk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, ← card_basis, mul_aleph0_eq aleph0_le]
  have : ℵ₀ ≤ Module.rank L K
  · sorry


end DivisionRing
