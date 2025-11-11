/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison, Chris Hughes, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis

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
We have `finrank` variants for most lemmas as well.

-/


noncomputable section

universe u u' v v' u₁' w w'

variable {R : Type u} {S : Type u'} {M : Type v} {M' : Type v'} {M₁ : Type v}
variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open Basis Cardinal DirectSum Function Module Set Submodule

section Quotient

variable [Ring R] [CommRing S] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M]

theorem LinearIndependent.sumElim_of_quotient
    {M' : Submodule R M} {ι₁ ι₂} {f : ι₁ → M'} (hf : LinearIndependent R f) (g : ι₂ → M)
    (hg : LinearIndependent R (Submodule.Quotient.mk (p := M') ∘ g)) :
    LinearIndependent R (Sum.elim (f · : ι₁ → M) g) := by
  refine .sum_type (hf.map' M'.subtype M'.ker_subtype) (.of_comp M'.mkQ hg) ?_
  refine disjoint_def.mpr fun x h₁ h₂ ↦ ?_
  have : x ∈ M' := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (f i).prop) h₁
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₂
  simp_rw [← Quotient.mk_eq_zero, ← mkQ_apply, map_finsuppSum, map_smul, mkQ_apply] at this
  rw [linearIndependent_iff.mp hg _ this, Finsupp.sum_zero_index]

theorem LinearIndepOn.union_of_quotient {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s)
    (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) : LinearIndepOn R f (s ∪ t) := by
  apply hs.union ht.of_comp
  convert (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

theorem LinearIndepOn.union_id_of_quotient {M' : Submodule R M}
    {s : Set M} (hs : s ⊆ M') (hs' : LinearIndepOn R id s) {t : Set M}
    (ht : LinearIndepOn R (mkQ M') t) : LinearIndepOn R id (s ∪ t) :=
  hs'.union_of_quotient <| by
    rw [image_id]
    exact ht.of_comp ((span R s).mapQ M' (LinearMap.id) (span_le.2 hs))

theorem linearIndepOn_union_iff_quotient {s t : Set ι} {f : ι → M} (hst : Disjoint s t) :
    LinearIndepOn R f (s ∪ t) ↔
    LinearIndepOn R f s ∧ LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.union_of_quotient h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm

theorem LinearIndepOn.quotient_iff_union {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s)
    (hst : Disjoint s t) :
    LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t ↔ LinearIndepOn R f (s ∪ t) := by
  rw [linearIndepOn_union_iff_quotient hst, and_iff_right hs]

theorem rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' ≤ Module.rank R M := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range _) _ (bddAbove_range _)]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  choose f hf using Submodule.Quotient.mk_surjective M'
  simpa [add_comm] using (LinearIndependent.sumElim_of_quotient ht (fun (i : s) ↦ f i)
    (by simpa [Function.comp_def, hf] using hs)).cardinal_le_rank

theorem rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) ≤ Module.rank R M :=
  (mkQ p).rank_le_of_surjective Quot.mk_surjective

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem Submodule.finrank_quotient_le [StrongRankCondition R] [Module.Finite R M]
    (s : Submodule R M) : finrank R (M ⧸ s) ≤ finrank R M :=
  toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective Quot.mk_surjective)
    (rank_lt_aleph0 _ _)

end Quotient

variable [Semiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M₁]
variable [Module R M]

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
variable [Module R M₁] [Module R M']

theorem rank_add_rank_le_rank_prod [Nontrivial R] :
    Module.rank R M + Module.rank R M₁ ≤ Module.rank R (M × M₁) := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ (bddAbove_range _) _ (bddAbove_range _)]
  exact ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦
    (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank

theorem lift_rank_add_lift_rank_le_rank_prod [Nontrivial R] :
    lift.{v'} (Module.rank R M) + lift.{v} (Module.rank R M') ≤ Module.rank R (M × M') := by
  rw [← rank_ulift, ← rank_ulift]
  exact (rank_add_rank_le_rank_prod R _).trans_eq
    (ULift.moduleEquiv.prodCongr ULift.moduleEquiv).rank_eq

variable {R M M'}
variable [StrongRankCondition R] [Module.Free R M] [Module.Free R M'] [Module.Free R M₁]

open Module.Free

/-- If `M` and `M'` are free, then the rank of `M × M'` is
`(Module.rank R M).lift + (Module.rank R M').lift`. -/
@[simp]
theorem rank_prod : Module.rank R (M × M') =
    Cardinal.lift.{v'} (Module.rank R M) + Cardinal.lift.{v, v'} (Module.rank R M') := by
  simpa [rank_eq_card_chooseBasisIndex R M, rank_eq_card_chooseBasisIndex R M', lift_umax]
    using ((chooseBasis R M).prod (chooseBasis R M')).mk_eq_rank.symm

/-- If `M` and `M'` are free (and lie in the same universe), the rank of `M × M'` is
  `(Module.rank R M) + (Module.rank R M')`. -/
theorem rank_prod' : Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁ := by simp

/-- The `finrank` of `M × M'` is `(finrank R M) + (finrank R M')`. -/
@[simp]
theorem Module.finrank_prod [Module.Finite R M] [Module.Finite R M'] :
    finrank R (M × M') = finrank R M + finrank R M' := by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R M']

end Prod

section Finsupp

variable (R M M')
variable [StrongRankCondition R] [Module.Free R M] [Module R M'] [Module.Free R M']

open Module.Free

@[simp]
theorem rank_finsupp (ι : Type w) :
    Module.rank R (ι →₀ M) = Cardinal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M) := by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← bs.mk_eq_rank'', ← (Finsupp.basis fun _ : ι => bs).mk_eq_rank'', Cardinal.mk_sigma,
    Cardinal.sum_const]

theorem rank_finsupp' (ι : Type v) : Module.rank R (ι →₀ M) = #ι * Module.rank R M := by
  simp [rank_finsupp]

/-- The rank of `(ι →₀ R)` is `(#ι).lift`. -/
theorem rank_finsupp_self (ι : Type w) : Module.rank R (ι →₀ R) = Cardinal.lift.{u} #ι := by
  simp

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
theorem rank_finsupp_self' {ι : Type u} : Module.rank R (ι →₀ R) = #ι := by simp

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
theorem rank_directSum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) := by
  let B i := chooseBasis R (M i)
  let b : Basis _ R (⨁ i, M i) := DFinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

/-- If `m` and `n` are finite, the rank of `m × n` matrices over a module `M` is
`(#m).lift * (#n).lift * rank R M`. -/
@[simp]
theorem rank_matrix_module (m : Type w) (n : Type w') [Finite m] [Finite n] :
    Module.rank R (Matrix m n M) =
      lift.{max v w'} #m * lift.{max v w} #n * lift.{max w w'} (Module.rank R M) := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  obtain ⟨I, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← (b.matrix m n).mk_eq_rank'']
  simp only [mk_prod, lift_mul, lift_lift, ← mul_assoc, b.mk_eq_rank'']


/-- If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matrices over a
module `M` is `(#m * #n).lift * rank R M`. -/
@[simp high]
theorem rank_matrix_module' (m n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n M) =
      lift.{max v} (#m * #n) * lift.{w} (Module.rank R M) := by
  rw [rank_matrix_module, lift_mul, lift_umax.{w, v}]

/-- If `m` and `n` are finite, the rank of `m × n` matrices is `(#m).lift * (#n).lift`. -/
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) =
      Cardinal.lift.{max v w u, v} #m * Cardinal.lift.{max v w u, w} #n := by
  rw [rank_matrix_module, rank_self, lift_one, mul_one, ← lift_lift.{v, max u w}, lift_id,
    ← lift_lift.{w, max u v}, lift_id]

/-- If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matrices is
  `(#n * #m).lift`. -/
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = Cardinal.lift.{u} (#m * #n) := by
  rw [rank_matrix, lift_mul, lift_umax.{v, u}]

/-- If `m` and `n` are finite and lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = #m * #n := by simp

open Fintype

namespace Module

@[simp]
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ M) = card ι * finrank R M := by
  rw [finrank, finrank, rank_finsupp, ← mk_toNat_eq_card, toNat_mul, toNat_lift, toNat_lift]

/-- The `finrank` of `(ι →₀ R)` is `Fintype.card ι`. -/
@[simp]
theorem finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
  rw [finrank, rank_finsupp_self, ← mk_toNat_eq_card, toNat_lift]

/-- The `finrank` of the direct sum is the sum of the `finrank`s. -/
@[simp]
theorem finrank_directSum {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) := by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]

/-- If `m` and `n` are `Fintype`, the `finrank` of `m × n` matrices over a module `M` is
  `(Fintype.card m) * (Fintype.card n) * finrank R M`. -/
theorem finrank_matrix (m n : Type*) [Fintype m] [Fintype n] :
    finrank R (Matrix m n M) = card m * card n * finrank R M := by simp [finrank]

end Module

end Finsupp

section Pi

variable [StrongRankCondition R] [Module.Free R M]
variable [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] [∀ i, Module.Free R (φ i)]

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

variable (R)

/-- The `finrank` of `(ι → R)` is `Fintype.card ι`. -/
theorem Module.finrank_pi {ι : Type v} [Fintype ι] :
    finrank R (ι → R) = Fintype.card ι := by
  simp [finrank]

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
/-- The `finrank` of a finite product is the sum of the `finrank`s. -/
theorem Module.finrank_pi_fintype
    {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) := by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, Fintype.card_sigma]

variable {R}
variable [Fintype η]

theorem rank_fun {M η : Type u} [Fintype η] [AddCommMonoid M] [Module R M] [Module.Free R M] :
    Module.rank R (η → M) = Fintype.card η * Module.rank R M := by
  rw [rank_pi, Cardinal.sum_const', Cardinal.mk_fintype]

theorem rank_fun_eq_lift_mul : Module.rank R (η → M) =
    (Fintype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M) := by
  rw [rank_pi, Cardinal.sum_const, Cardinal.mk_fintype, Cardinal.lift_natCast]

theorem rank_fun' : Module.rank R (η → R) = Fintype.card η := by
  rw [rank_fun_eq_lift_mul, rank_self, Cardinal.lift_one, mul_one]

theorem rank_fin_fun (n : ℕ) : Module.rank R (Fin n → R) = n := by simp

variable (R)

/-- The vector space of functions on a `Fintype ι` has `finrank` equal to the cardinality of `ι`. -/
@[simp]
theorem Module.finrank_fintype_fun_eq_card : finrank R (η → R) = Fintype.card η :=
  finrank_eq_of_rank_eq rank_fun'

/-- The vector space of functions on `Fin n` has `finrank` equal to `n`. -/
theorem Module.finrank_fin_fun {n : ℕ} : finrank R (Fin n → R) = n := by simp

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

end Pi

section TensorProduct

open TensorProduct

variable [StrongRankCondition R] [StrongRankCondition S]
variable [Module S M] [Module S M'] [Module.Free S M']
variable [Module S M₁] [Module.Free S M₁]
variable [Algebra S R] [IsScalarTower S R M] [Module.Free R M]

open Module.Free

/-- The `S`-rank of `M ⊗[R] M'` is `(Module.rank S M).lift * (Module.rank R M').lift`. -/
@[simp]
theorem rank_tensorProduct :
    Module.rank R (M ⊗[S] M') =
      Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M') := by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := S) (M := M')
  rw [← bM.mk_eq_rank'', ← bN.mk_eq_rank'', ← (bM.tensorProduct bN).mk_eq_rank'', Cardinal.mk_prod]

/-- If `M` and `M'` lie in the same universe, the `S`-rank of `M ⊗[R] M'` is
  `(Module.rank S M) * (Module.rank R M')`. -/
theorem rank_tensorProduct' :
    Module.rank R (M ⊗[S] M₁) = Module.rank R M * Module.rank S M₁ := by simp

theorem Module.rank_baseChange :
    Module.rank R (R ⊗[S] M') = Cardinal.lift.{u} (Module.rank S M') := by simp

/-- The `S`-`finrank` of `M ⊗[R] M'` is `(finrank S M) * (finrank R M')`. -/
@[simp]
theorem Module.finrank_tensorProduct :
    finrank R (M ⊗[S] M') = finrank R M * finrank S M' := by simp [finrank]

theorem Module.finrank_baseChange : finrank R (R ⊗[S] M') = finrank S M' := by simp

end TensorProduct

section SubmoduleRank

section

open Module

namespace Submodule

theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule R M} (le : s ≤ t)
    (lt : finrank R s < finrank R t) : s < t :=
  lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])

theorem lt_top_of_finrank_lt_finrank {s : Submodule R M} (lt : finrank R s < finrank R M) :
    s < ⊤ := by
  rw [← finrank_top R M] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt

end Submodule

variable [StrongRankCondition R]

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) :
    finrank R s ≤ finrank R M :=
  toNat_le_toNat (Submodule.rank_le s) (rank_lt_aleph0 _ _)

/-- Pushforwards of finite submodules have a smaller finrank. -/
theorem Submodule.finrank_map_le
    [Module R M'] (f : M →ₗ[R] M') (p : Submodule R M) [Module.Finite R p] :
    finrank R (p.map f) ≤ finrank R p :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph0 _ _)

theorem Submodule.finrank_mono {s t : Submodule R M} [Module.Finite R t] (hst : s ≤ t) :
    finrank R s ≤ finrank R t :=
  Cardinal.toNat_le_toNat (Submodule.rank_mono hst) (rank_lt_aleph0 R ↥t)

end

end SubmoduleRank

section Span

variable [StrongRankCondition R]

theorem rank_span_le (s : Set M) : Module.rank R (span R s) ≤ #s := by
  rw [Finsupp.span_eq_range_linearCombination, ← lift_strictMono.le_iff_le]
  refine (lift_rank_range_le _).trans ?_
  rw [rank_finsupp_self]
  simp only [lift_lift, le_refl]

theorem rank_span_finset_le (s : Finset M) : Module.rank R (span R (s : Set M)) ≤ s.card := by
  simpa using rank_span_le (s : Set M)

theorem rank_span_of_finset (s : Finset M) : Module.rank R (span R (s : Set M)) < ℵ₀ :=
  (rank_span_finset_le s).trans_lt (Cardinal.nat_lt_aleph0 _)

open Submodule Module

variable (R) in
/-- The rank of a set of vectors as a natural number. -/
protected noncomputable def Set.finrank (s : Set M) : ℕ :=
  finrank R (span R s)

theorem finrank_span_le_card (s : Set M) [Fintype s] : finrank R (span R s) ≤ s.toFinset.card :=
  finrank_le_of_rank_le (by simpa using rank_span_le (R := R) s)

theorem finrank_span_finset_le_card (s : Finset M) : (s : Set M).finrank R ≤ s.card :=
  calc
    (s : Set M).finrank R ≤ (s : Set M).toFinset.card := finrank_span_le_card (M := M) s
    _ = s.card := by simp

theorem finrank_range_le_card {ι : Type*} [Fintype ι] (b : ι → M) :
    (Set.range b).finrank R ≤ Fintype.card ι := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le

theorem finrank_span_eq_card [Nontrivial R] {ι : Type*} [Fintype ι] {b : ι → M}
    (hb : LinearIndependent R b) :
    finrank R (span R (Set.range b)) = Fintype.card ι :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R (Set.range b)) = #(Set.range b) := rank_span hb
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)

theorem finrank_span_set_eq_card {s : Set M} [Fintype s] (hs : LinearIndepOn R id s) :
    finrank R (span R s) = s.toFinset.card :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)

theorem finrank_span_finset_eq_card {s : Finset M} (hs : LinearIndepOn R id (s : Set M)) :
    finrank R (span R (s : Set M)) = s.card := by
  convert finrank_span_set_eq_card (s := (s : Set M)) hs
  ext
  simp

theorem span_lt_of_subset_of_card_lt_finrank {s : Set M} [Fintype s] {t : Submodule R M}
    (subset : s ⊆ t) (card_lt : s.toFinset.card < finrank R t) : span R s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

theorem span_lt_top_of_card_lt_finrank {s : Set M} [Fintype s]
    (card_lt : s.toFinset.card < finrank R M) : span R s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)

lemma finrank_le_of_span_eq_top {ι : Type*} [Fintype ι] {v : ι → M}
    (hv : Submodule.span R (Set.range v) = ⊤) : finrank R M ≤ Fintype.card ι := by
  classical
  rw [← finrank_top, ← hv]
  exact (finrank_span_le_card _).trans (by convert Fintype.card_range_le v; rw [Set.toFinset_card])

end Span

section SubalgebraRank

open Module

section Semiring

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E]

@[simp]
theorem Subalgebra.rank_toSubmodule (S : Subalgebra F E) :
    Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S :=
  rfl

@[simp]
theorem Subalgebra.finrank_toSubmodule (S : Subalgebra F E) :
    finrank F (Subalgebra.toSubmodule S) = finrank F S :=
  rfl

theorem subalgebra_top_rank_eq_submodule_top_rank :
    Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl

theorem subalgebra_top_finrank_eq_submodule_top_finrank :
    finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl

theorem Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E := by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  exact _root_.rank_top F E

end Semiring

section Ring

variable {F E : Type*} [CommRing F] [Ring E] [Algebra F E]
variable [StrongRankCondition F] [NoZeroSMulDivisors F E] [Nontrivial E]

@[simp]
theorem Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
  (Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.rank_eq.trans <| by
    rw [Algebra.toSubmodule_bot, one_eq_span, rank_span_set, mk_singleton _]
    letI := Module.nontrivial F E
    exact LinearIndepOn.id_singleton _ one_ne_zero

@[simp]
theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 :=
  finrank_eq_of_rank_eq (by simp)

end Ring

end SubalgebraRank
