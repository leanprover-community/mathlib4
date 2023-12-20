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

variable {R M}
theorem rank_eq_cardinal_basis {ι : Type w} (b : Basis ι R M) :
    Cardinal.lift.{w} (Module.rank R M) = Cardinal.lift.{v} #ι := by
  apply Cardinal.lift_injective.{u}
  simp_rw [Cardinal.lift_lift]
  have := b.repr.lift_rank_eq
  rwa [rank_finsupp_self, Cardinal.lift_lift] at this

theorem rank_eq_cardinal_basis' {ι : Type v} (b : Basis ι R M) : Module.rank R M = #ι :=
  Cardinal.lift_injective.{v} (rank_eq_cardinal_basis b)

variable (R M)

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

variable (K : Type u) [DivisionRing K]

/-- Preliminary lemma for the Erdős-Kaplansky Theorem from https://mathoverflow.net/a/168624 -/
theorem rank_pi_nat : max ℵ₀ #K ≤ Module.rank K (ℕ → K) := by
  have aleph0_le : ℵ₀ ≤ Module.rank K (ℕ → K) := (rank_finsupp_self K ℕ).symm.trans_le
    (Finsupp.lcoeFun.rank_le_of_injective <| by exact FunLike.coe_injective)
  refine max_le aleph0_le ?_
  obtain card_K | card_K := le_or_lt #K ℵ₀
  · exact card_K.trans aleph0_le
  by_contra!
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ℕ → K)
  let L := Subfield.closure (Set.range (fun i : ιK × ℕ ↦ bK i.1 i.2))
  have hLK : #L < #K
  · refine (Subfield.cardinal_mk_closure_le_max _).trans_lt
      (max_lt_iff.mpr ⟨mk_range_le.trans_lt ?_, card_K⟩)
    rwa [mk_prod, ← aleph0, lift_uzero, ← rank_eq_cardinal_basis' bK, mul_aleph0_eq aleph0_le]
  letI := Module.compHom K (RingHom.op L.subtype)
  obtain ⟨⟨ιL, bL⟩⟩ := Module.Free.exists_basis (R := Lᵐᵒᵖ) (M := K)
  have card_ιL : ℵ₀ ≤ #ιL
  · contrapose! hLK
    haveI := @Fintype.ofFinite _ (lt_aleph0_iff_finite.mp hLK)
    rw [bL.repr.toEquiv.cardinal_eq, mk_finsupp_of_fintype,
        ← MulOpposite.opEquiv.cardinal_eq] at card_K ⊢
    apply power_nat_le
    contrapose! card_K
    exact (power_lt_aleph0 card_K <| nat_lt_aleph0 _).le
  obtain ⟨e⟩ := lift_mk_le'.mp (card_ιL.trans_eq (lift_uzero #ιL).symm)
  have rep_e := bK.total_repr (bL ∘ e)
  rw [Finsupp.total_apply, Finsupp.sum] at rep_e
  set c := bK.repr (bL ∘ e)
  set s := c.support
  set N := s.card + 1
  let f (i : Fin N) (j : s) : L :=
    ⟨bK j i, Subfield.subset_closure ⟨(j, i), rfl⟩⟩
  have : ¬LinearIndependent Lᵐᵒᵖ f := fun h ↦ by
    have := cardinal_lift_le_rank_of_linearIndependent' h
    rw [lift_uzero, (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Lᵐᵒᵖ).rank_eq,
        rank_fun', Fintype.card_coe, mk_fin, lift_natCast, natCast_le] at this
    exact (Nat.lt_succ_self _).not_le this
  obtain ⟨g, eq0, i, hi⟩ := Fintype.not_linearIndependent_iff.mp this
  refine hi <| Fintype.linearIndependent_iff.mp (bL.linearIndependent.comp _ <|
    e.injective.comp Fin.val_injective) g (?_ : ∑ i : Fin N, g i • (bL ∘ e) i = 0) i
  clear_value c s N
  simp_rw [← rep_e, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  replace eq0 := congr_arg L.subtype (congr_fun eq0 ⟨i, hi⟩)
  rw [Finset.sum_apply, map_sum] at eq0
  have : SMulCommClass Lᵐᵒᵖ K K := ⟨fun _ _ _ ↦ mul_assoc _ _ _⟩
  simp_rw [smul_comm _ (c i), ← Finset.smul_sum]
  erw [eq0, smul_zero]

variable {K}

open Function in
theorem rank_pi_infinite {ι : Type v} [hι : Infinite ι] : Module.rank K (ι → K) = #(ι → K) := by
  obtain ⟨⟨ιK, bK⟩⟩ := Module.Free.exists_basis (R := K) (M := ι → K)
  obtain ⟨e⟩ := lift_mk_le'.mp ((aleph0_le_mk_iff.mpr hι).trans_eq (lift_uzero #ι).symm)
  have := LinearMap.lift_rank_le_of_injective _ <|
    LinearMap.funLeft_injective_of_surjective K K _ (invFun_surjective e.injective)
  rw [lift_umax.{u,v}, lift_id'.{u,v}] at this
  have key := (lift_le.{v}.mpr <| rank_pi_nat K).trans this
  rw [lift_max, lift_aleph0, max_le_iff] at key
  haveI : Infinite ιK := by
    rw [← aleph0_le_mk_iff, ← rank_eq_cardinal_basis' bK]; exact key.1
  rw [bK.repr.toEquiv.cardinal_eq, mk_finsupp_lift_of_infinite,
      lift_umax.{u,v}, lift_id'.{u,v}, ← rank_eq_cardinal_basis' bK, eq_comm, max_eq_left]
  exact key.2

/-- The **Erdős-Kaplansky Theorem**: the dual of an infinite-dimensional vector space
  over a division ring has dimension equal to its cardinality. -/
theorem rank_dual_eq_card_of_aleph0_le_rank' {V : Type*} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank Kᵐᵒᵖ (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [rank_eq_cardinal_basis' b, aleph0_le_mk_iff] at h
  have e := (b.constr Kᵐᵒᵖ (M' := K)).symm.trans
    (LinearEquiv.piCongrRight fun _ ↦ MulOpposite.opLinearEquiv Kᵐᵒᵖ)
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_pi_infinite

/-- The **Erdős-Kaplansky Theorem** over a field. -/
theorem rank_dual_eq_card_of_aleph0_le_rank {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) : Module.rank K (V →ₗ[K] K) = #(V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [rank_eq_cardinal_basis' b, aleph0_le_mk_iff] at h
  have e := (b.constr K (M' := K)).symm
  rw [e.rank_eq, e.toEquiv.cardinal_eq]
  apply rank_pi_infinite

theorem lift_rank_lt_rank_dual' {V : Type v} [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank Kᵐᵒᵖ (V →ₗ[K] K) := by
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := K) (M := V)
  rw [rank_eq_cardinal_basis' b, rank_dual_eq_card_of_aleph0_le_rank' h,
      ← (b.constr ℕ (M' := K)).toEquiv.cardinal_eq, mk_arrow]
  apply cantor'
  erw [nat_lt_lift_iff, one_lt_iff_nontrivial]
  infer_instance

theorem lift_rank_lt_rank_dual {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (h : ℵ₀ ≤ Module.rank K V) :
    Cardinal.lift.{u} (Module.rank K V) < Module.rank K (V →ₗ[K] K) := by
  rw [rank_dual_eq_card_of_aleph0_le_rank h, ← rank_dual_eq_card_of_aleph0_le_rank' h]
  exact lift_rank_lt_rank_dual' h

end DivisionRing
