/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison, Chris Hughes, Anne Baanen
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Torsion

#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Rank of various constructions

## Main statements

- `rank_quotient_add_rank_le` : `rank M/N + rank N ≤ rank M`.
- `lift_rank_add_lift_rank_le_rank_prod`: `rank M × N ≤ rank M + rank N`.
- `rank_span_le_of_finite`: `rank (span s) ≤ #s` for finite `s`.

For free modules, we have

- `rank_prod` : `rank M × N = rank M + rank N`.
- `rank_finsupp` : `rank (ι →₀ M) = #ι * rank M`
- `rank_directSum`: `rank (⨁ Mᵢ) = ∑ rank Mᵢ`
- `rank_tensorProduct`: `rank (M ⊗ N) = rank M * rank N`.

Lemmas for ranks of submodules and subalgebras are also provided.
We have finrank variants for most lemmas as well.

-/


noncomputable section

universe u v v' u₁' w w'

variable {R S : Type u} {M : Type v} {M' : Type v'} {M₁ : Type v}
variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open BigOperators Cardinal Basis Submodule Function Set FiniteDimensional DirectSum

variable [Ring R] [CommRing S] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M] [Module R M'] [Module R M₁]

section Quotient

theorem rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' ≤ Module.rank R M := by
  simp_rw [Module.rank_def]
  have := nonempty_linearIndependent_set R (M ⧸ M')
  have := nonempty_linearIndependent_set R M'
  rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range.{v, v} _) _ (bddAbove_range.{v, v} _)]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  choose f hf using Quotient.mk_surjective M'
  let g : s ⊕ t → M := Sum.elim (f ·) (·)
  suffices LinearIndependent R g by
    refine le_trans ?_ (le_ciSup (bddAbove_range.{v, v} _) ⟨_, this.to_subtype_range⟩)
    rw [mk_range_eq _ this.injective, mk_sum, lift_id, lift_id]
  refine .sum_type (.of_comp M'.mkQ ?_) (ht.map' M'.subtype M'.ker_subtype) ?_
  · convert hs; ext x; exact hf x
  refine disjoint_def.mpr fun x h₁ h₂ ↦ ?_
  have : x ∈ M' := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ i.1.2) h₂
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₁
  simp_rw [← Quotient.mk_eq_zero, ← mkQ_apply, map_finsupp_sum, map_smul, mkQ_apply, hf] at this
  rw [linearIndependent_iff.mp hs _ this, Finsupp.sum_zero_index]

theorem rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) ≤ Module.rank R M :=
  (mkQ p).rank_le_of_surjective (surjective_quot_mk _)
#align rank_quotient_le rank_quotient_le

theorem rank_quotient_eq_of_le_torsion {R M} [CommRing R] [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hN : M' ≤ torsion R M) : Module.rank R (M ⧸ M') = Module.rank R M :=
  (rank_quotient_le M').antisymm <| by
    nontriviality R
    rw [Module.rank]
    have := nonempty_linearIndependent_set R M
    refine ciSup_le fun ⟨s, hs⟩ ↦ LinearIndependent.cardinal_le_rank (v := (M'.mkQ ·)) ?_
    rw [linearIndependent_iff'] at hs ⊢
    simp_rw [← map_smul, ← map_sum, mkQ_apply, Quotient.mk_eq_zero]
    intro t g hg i hi
    obtain ⟨r, hg⟩ := hN hg
    simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at hg
    exact r.prop _ (mul_comm (g i) r ▸ hs t _ hg i hi)

end Quotient

section ULift

@[simp]
theorem rank_ulift : Module.rank R (ULift.{w} M) = Cardinal.lift.{w} (Module.rank R M) :=
  Cardinal.lift_injective.{v} <| Eq.symm <| (lift_lift _).trans ULift.moduleEquiv.symm.lift_rank_eq

@[simp]
theorem finrank_ulift : finrank R (ULift M) = finrank R M := by
  simp_rw [finrank, rank_ulift, toNat_lift]

end ULift

section Prod

variable (R M M')

open LinearMap in
theorem lift_rank_add_lift_rank_le_rank_prod [Nontrivial R] :
    lift.{v'} (Module.rank R M) + lift.{v} (Module.rank R M') ≤ Module.rank R (M × M') := by
  convert rank_quotient_add_rank_le (ker <| LinearMap.fst R M M')
  · refine Eq.trans ?_ (lift_id'.{v, v'} _)
    rw [(quotKerEquivRange _).lift_rank_eq,
        rank_range_of_surjective _ fst_surjective, lift_umax.{v, v'}]
  · refine Eq.trans ?_ (lift_id'.{v', v} _)
    rw [ker_fst, ← (LinearEquiv.ofInjective _ <| inr_injective (M := M) (M₂ := M')).lift_rank_eq,
        lift_umax.{v', v}]

theorem rank_add_rank_le_rank_prod [Nontrivial R] :
    Module.rank R M + Module.rank R M₁ ≤ Module.rank R (M × M₁) := by
  convert ← lift_rank_add_lift_rank_le_rank_prod R M M₁ <;> apply lift_id

variable {R M M'}
variable [StrongRankCondition R] [Module.Free R M] [Module.Free R M'] [Module.Free R M₁]

open Module.Free

/-- If `M` and `M'` are free, then the rank of `M × M'` is
`(Module.rank R M).lift + (Module.rank R M').lift`. -/
@[simp]
theorem rank_prod : Module.rank R (M × M') =
    Cardinal.lift.{v'} (Module.rank R M) + Cardinal.lift.{v, v'} (Module.rank R M') := by
  simpa [rank_eq_card_chooseBasisIndex R M, rank_eq_card_chooseBasisIndex R M', lift_umax,
    lift_umax'] using ((chooseBasis R M).prod (chooseBasis R M')).mk_eq_rank.symm
#align rank_prod rank_prod

/-- If `M` and `M'` are free (and lie in the same universe), the rank of `M × M'` is
  `(Module.rank R M) + (Module.rank R M')`. -/
theorem rank_prod' : Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁ := by simp
#align rank_prod' rank_prod'

/-- The finrank of `M × M'` is `(finrank R M) + (finrank R M')`. -/
@[simp]
theorem FiniteDimensional.finrank_prod [Module.Finite R M] [Module.Finite R M'] :
    finrank R (M × M') = finrank R M + finrank R M' := by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R M']
#align finite_dimensional.finrank_prod FiniteDimensional.finrank_prod

end Prod

section Finsupp

variable (R M M')
variable [StrongRankCondition R] [Module.Free R M] [Module.Free R M']

open Module.Free BigOperators

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
-- @[simp] -- Porting note (#10618): simp can prove this
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = #m * #n := by simp
#align rank_matrix'' rank_matrix''

variable [Module.Finite R M] [Module.Finite R M']

open Fintype

namespace FiniteDimensional

@[simp]
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ M) = card ι * finrank R M := by
  rw [finrank, finrank, rank_finsupp, ← mk_toNat_eq_card, toNat_mul, toNat_lift, toNat_lift]

/-- The finrank of `(ι →₀ R)` is `Fintype.card ι`. -/
@[simp]
theorem finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
  rw [finrank, rank_finsupp_self, ← mk_toNat_eq_card, toNat_lift]
#align finite_dimensional.finrank_finsupp FiniteDimensional.finrank_finsupp_self

/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp]
theorem finrank_directSum {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) := by
  letI := nontrivial_of_invariantBasisNumber R
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]
#align finite_dimensional.finrank_direct_sum FiniteDimensional.finrank_directSum

/-- If `m` and `n` are `Fintype`, the finrank of `m × n` matrices is
  `(Fintype.card m) * (Fintype.card n)`. -/
theorem finrank_matrix (m n : Type*) [Fintype m] [Fintype n] :
    finrank R (Matrix m n R) = card m * card n := by simp [finrank]
#align finite_dimensional.finrank_matrix FiniteDimensional.finrank_matrix

end FiniteDimensional

end Finsupp

section Pi

variable [StrongRankCondition R] [Module.Free R M]
variable [∀ i, AddCommGroup (φ i)] [∀ i, Module R (φ i)] [∀ i, Module.Free R (φ i)]

open Module.Free

open LinearMap

/-- The rank of a finite product of free modules is the sum of the ranks. -/
-- this result is not true without the freeness assumption
@[simp]
theorem rank_pi [Finite η] : Module.rank R (∀ i, φ i) =
    Cardinal.sum fun i => Module.rank R (φ i) := by
  cases nonempty_fintype η
  let B i := chooseBasis R (φ i)
  let b : Basis _ R (∀ i, φ i) := Pi.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']
#align rank_pi rank_pi

variable (R)

/-- The finrank of `(ι → R)` is `Fintype.card ι`. -/
theorem FiniteDimensional.finrank_pi {ι : Type v} [Fintype ι] :
    finrank R (ι → R) = Fintype.card ι := by
  simp [finrank]
#align finite_dimensional.finrank_pi FiniteDimensional.finrank_pi

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
/-- The finrank of a finite product is the sum of the finranks. -/
theorem FiniteDimensional.finrank_pi_fintype
    {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) := by
  letI := nontrivial_of_invariantBasisNumber R
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, Fintype.card_sigma]
#align finite_dimensional.finrank_pi_fintype FiniteDimensional.finrank_pi_fintype

variable {R}
variable [Fintype η]

theorem rank_fun {M η : Type u} [Fintype η] [AddCommGroup M] [Module R M] [Module.Free R M] :
    Module.rank R (η → M) = Fintype.card η * Module.rank R M := by
  rw [rank_pi, Cardinal.sum_const', Cardinal.mk_fintype]
#align rank_fun rank_fun

theorem rank_fun_eq_lift_mul : Module.rank R (η → M) =
    (Fintype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M) :=
  by rw [rank_pi, Cardinal.sum_const, Cardinal.mk_fintype, Cardinal.lift_natCast]
#align rank_fun_eq_lift_mul rank_fun_eq_lift_mul

theorem rank_fun' : Module.rank R (η → R) = Fintype.card η := by
  rw [rank_fun_eq_lift_mul, rank_self, Cardinal.lift_one, mul_one]
#align rank_fun' rank_fun'

theorem rank_fin_fun (n : ℕ) : Module.rank R (Fin n → R) = n := by simp [rank_fun']
#align rank_fin_fun rank_fin_fun

variable (R)

/-- The vector space of functions on a `Fintype ι` has finrank equal to the cardinality of `ι`. -/
@[simp]
theorem FiniteDimensional.finrank_fintype_fun_eq_card : finrank R (η → R) = Fintype.card η :=
  finrank_eq_of_rank_eq rank_fun'
#align finite_dimensional.finrank_fintype_fun_eq_card FiniteDimensional.finrank_fintype_fun_eq_card

/-- The vector space of functions on `Fin n` has finrank equal to `n`. -/
-- @[simp] -- Porting note (#10618): simp already proves this
theorem FiniteDimensional.finrank_fin_fun {n : ℕ} : finrank R (Fin n → R) = n := by simp
#align finite_dimensional.finrank_fin_fun FiniteDimensional.finrank_fin_fun

variable {R}

-- TODO: merge with the `Finrank` content
/-- An `n`-dimensional `R`-vector space is equivalent to `Fin n → R`. -/
def finDimVectorspaceEquiv (n : ℕ) (hn : Module.rank R M = n) : M ≃ₗ[R] Fin n → R := by
  haveI := nontrivial_of_invariantBasisNumber R
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @rank_fin_fun R _ _ n] at hn
  haveI : Module.Free R (Fin n → R) := Module.Free.pi _ _
  exact Classical.choice (nonempty_linearEquiv_of_lift_rank_eq hn)
#align fin_dim_vectorspace_equiv finDimVectorspaceEquiv

end Pi

section TensorProduct

open TensorProduct

variable [StrongRankCondition S]
variable [Module S M] [Module.Free S M] [Module S M'] [Module.Free S M']
variable [Module S M₁] [Module.Free S M₁]

open Module.Free

/-- The rank of `M ⊗[R] M'` is `(Module.rank R M).lift * (Module.rank R M').lift`. -/
@[simp]
theorem rank_tensorProduct :
    Module.rank S (M ⊗[S] M') =
      Cardinal.lift.{v'} (Module.rank S M) * Cardinal.lift.{v} (Module.rank S M') := by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := S) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := S) (M := M')
  rw [← bM.mk_eq_rank'', ← bN.mk_eq_rank'', ← (bM.tensorProduct bN).mk_eq_rank'', Cardinal.mk_prod]
#align rank_tensor_product rank_tensorProduct

/-- If `M` and `M'` lie in the same universe, the rank of `M ⊗[R] M'` is
  `(Module.rank R M) * (Module.rank R M')`. -/
theorem rank_tensorProduct' :
    Module.rank S (M ⊗[S] M₁) = Module.rank S M * Module.rank S M₁ := by simp
#align rank_tensor_product' rank_tensorProduct'

/-- The finrank of `M ⊗[R] M'` is `(finrank R M) * (finrank R M')`. -/
@[simp]
theorem FiniteDimensional.finrank_tensorProduct :
    finrank S (M ⊗[S] M') = finrank S M * finrank S M' := by simp [finrank]
#align finite_dimensional.finrank_tensor_product FiniteDimensional.finrank_tensorProduct

end TensorProduct

section SubmoduleRank

section

open FiniteDimensional

namespace Submodule

theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule R M} (le : s ≤ t)
    (lt : finrank R s < finrank R t) : s < t :=
  lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])
#align submodule.lt_of_le_of_finrank_lt_finrank Submodule.lt_of_le_of_finrank_lt_finrank

theorem lt_top_of_finrank_lt_finrank {s : Submodule R M} (lt : finrank R s < finrank R M) :
    s < ⊤ := by
  rw [← finrank_top R M] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt
#align submodule.lt_top_of_finrank_lt_finrank Submodule.lt_top_of_finrank_lt_finrank

end Submodule

variable [StrongRankCondition R]

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) :
    finrank R s ≤ finrank R M :=
  toNat_le_toNat (rank_submodule_le s) (rank_lt_aleph0 _ _)
#align submodule.finrank_le Submodule.finrank_le

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem Submodule.finrank_quotient_le [Module.Finite R M] (s : Submodule R M) :
    finrank R (M ⧸ s) ≤ finrank R M :=
  toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective (surjective_quot_mk _))
    (rank_lt_aleph0 _ _)
#align submodule.finrank_quotient_le Submodule.finrank_quotient_le

/-- Pushforwards of finite submodules have a smaller finrank. -/
theorem Submodule.finrank_map_le (f : M →ₗ[R] M') (p : Submodule R M) [Module.Finite R p] :
    finrank R (p.map f) ≤ finrank R p :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph0 _ _)
#align submodule.finrank_map_le Submodule.finrank_map_le

theorem Submodule.finrank_le_finrank_of_le {s t : Submodule R M} [Module.Finite R t] (hst : s ≤ t) :
    finrank R s ≤ finrank R t :=
  calc
    finrank R s = finrank R (s.comap t.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hst).finrank_eq.symm
    _ ≤ finrank R t := Submodule.finrank_le _
#align submodule.finrank_le_finrank_of_le Submodule.finrank_le_finrank_of_le

end

end SubmoduleRank

section Span

variable [StrongRankCondition R]

theorem rank_span_le (s : Set M) : Module.rank R (span R s) ≤ #s := by
  rw [Finsupp.span_eq_range_total, ← lift_strictMono.le_iff_le]
  refine (lift_rank_range_le _).trans ?_
  rw [rank_finsupp_self]
  simp only [lift_lift, ge_iff_le, le_refl]
#align rank_span_le rank_span_le

theorem rank_span_finset_le (s : Finset M) : Module.rank R (span R (s : Set M)) ≤ s.card := by
  simpa using rank_span_le s.toSet

theorem rank_span_of_finset (s : Finset M) : Module.rank R (span R (s : Set M)) < ℵ₀ :=
  (rank_span_finset_le s).trans_lt (Cardinal.nat_lt_aleph0 _)
#align rank_span_of_finset rank_span_of_finset

open Submodule FiniteDimensional

variable (R)

/-- The rank of a set of vectors as a natural number. -/
protected noncomputable def Set.finrank (s : Set M) : ℕ :=
  finrank R (span R s)
#align set.finrank Set.finrank

variable {R}

theorem finrank_span_le_card (s : Set M) [Fintype s] : finrank R (span R s) ≤ s.toFinset.card :=
  finrank_le_of_rank_le (by simpa using rank_span_le (R := R) s)
#align finrank_span_le_card finrank_span_le_card

theorem finrank_span_finset_le_card (s : Finset M) : (s : Set M).finrank R ≤ s.card :=
  calc
    (s : Set M).finrank R ≤ (s : Set M).toFinset.card := finrank_span_le_card (M := M) s
    _ = s.card := by simp
#align finrank_span_finset_le_card finrank_span_finset_le_card

theorem finrank_range_le_card {ι : Type*} [Fintype ι] (b : ι → M) :
    (Set.range b).finrank R ≤ Fintype.card ι := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le
#align finrank_range_le_card finrank_range_le_card

theorem finrank_span_eq_card [Nontrivial R] {ι : Type*} [Fintype ι] {b : ι → M}
    (hb : LinearIndependent R b) :
    finrank R (span R (Set.range b)) = Fintype.card ι :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R (Set.range b)) = #(Set.range b) := rank_span hb
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)
#align finrank_span_eq_card finrank_span_eq_card

theorem finrank_span_set_eq_card {s : Set M} [Fintype s] (hs : LinearIndependent R ((↑) : s → M)) :
    finrank R (span R s) = s.toFinset.card :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)
#align finrank_span_set_eq_card finrank_span_set_eq_card

theorem finrank_span_finset_eq_card {s : Finset M} (hs : LinearIndependent R ((↑) : s → M)) :
    finrank R (span R (s : Set M)) = s.card := by
  convert finrank_span_set_eq_card (s := (s : Set M)) hs
  ext
  simp
#align finrank_span_finset_eq_card finrank_span_finset_eq_card

theorem span_lt_of_subset_of_card_lt_finrank {s : Set M} [Fintype s] {t : Submodule R M}
    (subset : s ⊆ t) (card_lt : s.toFinset.card < finrank R t) : span R s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)
#align span_lt_of_subset_of_card_lt_finrank span_lt_of_subset_of_card_lt_finrank

theorem span_lt_top_of_card_lt_finrank {s : Set M} [Fintype s]
    (card_lt : s.toFinset.card < finrank R M) : span R s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)
#align span_lt_top_of_card_lt_finrank span_lt_top_of_card_lt_finrank

end Span

section SubalgebraRank

open Module

variable {F E : Type*} [CommRing F] [Ring E] [Algebra F E]

@[simp]
theorem Subalgebra.rank_toSubmodule (S : Subalgebra F E) :
    Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S :=
  rfl
#align subalgebra.rank_to_submodule Subalgebra.rank_toSubmodule

@[simp]
theorem Subalgebra.finrank_toSubmodule (S : Subalgebra F E) :
    finrank F (Subalgebra.toSubmodule S) = finrank F S :=
  rfl
#align subalgebra.finrank_to_submodule Subalgebra.finrank_toSubmodule

theorem subalgebra_top_rank_eq_submodule_top_rank :
    Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl
#align subalgebra_top_rank_eq_submodule_top_rank subalgebra_top_rank_eq_submodule_top_rank

theorem subalgebra_top_finrank_eq_submodule_top_finrank :
    finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl
#align subalgebra_top_finrank_eq_submodule_top_finrank subalgebra_top_finrank_eq_submodule_top_finrank

theorem Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E := by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  exact _root_.rank_top F E
#align subalgebra.rank_top Subalgebra.rank_top

section

variable [StrongRankCondition F] [NoZeroSMulDivisors F E] [Nontrivial E]

@[simp]
theorem Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
  (Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.rank_eq.trans <| by
    rw [Algebra.toSubmodule_bot, one_eq_span, rank_span_set, mk_singleton _]
    letI := Module.nontrivial F E
    exact linearIndependent_singleton one_ne_zero
#align subalgebra.rank_bot Subalgebra.rank_bot

@[simp]
theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 :=
  finrank_eq_of_rank_eq (by simp)
#align subalgebra.finrank_bot Subalgebra.finrank_bot

end

end SubalgebraRank
