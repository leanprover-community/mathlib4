/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Finrank
import Mathlib.LinearAlgebra.FreeModule.Rank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

#align_import linear_algebra.free_module.finite.rank from "leanprover-community/mathlib"@"e95e4f92c8f8da3c7f693c3ec948bcf9b6683f51"

/-!

# Rank of finite free modules

This is a basic API for the rank of finite free modules.

-/


--TODO: many results from `LinearAlgebra/FiniteDimensional` should be moved here.
--TODO: This file contains many misplaced lemmas and should be reorganized.
universe u v w v'

variable (R : Type u) (M : Type v) (N : Type w)

open TensorProduct DirectSum BigOperators Cardinal

open Cardinal FiniteDimensional Fintype

namespace FiniteDimensional

open Module.Free

section Ring

variable [Ring R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

@[simp]
theorem Submodule.finrank_map_subtype_eq (p : Submodule R M) (q : Submodule R p) :
    finrank R (q.map p.subtype) = finrank R q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq
#align finite_dimensional.submodule.finrank_map_subtype_eq FiniteDimensional.Submodule.finrank_map_subtype_eq

@[simp]
theorem finrank_ulift : finrank R (ULift M) = finrank R M := by
  simp_rw [finrank, rank_ulift, toNat_lift]

end Ring

section RingFinite

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- The rank of a finite module is finite. -/
theorem rank_lt_aleph0 : Module.rank R M < ℵ₀ := by
  simp only [Module.rank_def]
  letI := nontrivial_of_invariantBasisNumber R
  -- porting note: can't use `‹_›` as that pulls the unused `N` into the context
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹Module.Finite R M›
  refine' (ciSup_le' fun i => _).trans_lt (nat_lt_aleph0 S.card)
  exact linearIndependent_le_span_finset _ i.prop S hS
#align finite_dimensional.rank_lt_aleph_0 FiniteDimensional.rank_lt_aleph0

/-- If `M` is finite, `finrank M = rank M`. -/
@[simp]
theorem finrank_eq_rank : ↑(finrank R M) = Module.rank R M := by
  rw [finrank, cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]
#align finite_dimensional.finrank_eq_rank FiniteDimensional.finrank_eq_rank

end RingFinite

section RingFree

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The finrank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
theorem finrank_eq_card_chooseBasisIndex :
    finrank R M = card (ChooseBasisIndex R M) := by
  simp [finrank, rank_eq_card_chooseBasisIndex]
#align finite_dimensional.finrank_eq_card_choose_basis_index FiniteDimensional.finrank_eq_card_chooseBasisIndex

@[simp]
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ M) = card ι * finrank R M := by
  rw [finrank, finrank, rank_finsupp, ← mk_toNat_eq_card, toNat_mul, toNat_lift, toNat_lift]

/-- The finrank of `(ι →₀ R)` is `Fintype.card ι`. -/
@[simp]
theorem finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
  rw [finrank, rank_finsupp_self, ← mk_toNat_eq_card, toNat_lift]
#align finite_dimensional.finrank_finsupp FiniteDimensional.finrank_finsupp_self

/-- The finrank of `(ι → R)` is `Fintype.card ι`. -/
theorem finrank_pi {ι : Type v} [Fintype ι] : finrank R (ι → R) = card ι := by
  simp [finrank]
#align finite_dimensional.finrank_pi FiniteDimensional.finrank_pi

/-- The finrank of the direct sum is the sum of the finranks. -/
@[simp]
theorem finrank_directSum {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) := by
  letI := nontrivial_of_invariantBasisNumber R
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]
#align finite_dimensional.finrank_direct_sum FiniteDimensional.finrank_directSum

/-- The finrank of `M × N` is `(finrank R M) + (finrank R N)`. -/
@[simp]
theorem finrank_prod : finrank R (M × N) = finrank R M + finrank R N := by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R N]
#align finite_dimensional.finrank_prod FiniteDimensional.finrank_prod

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
/-- The finrank of a finite product is the sum of the finranks. -/
theorem finrank_pi_fintype {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommGroup (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) := by
  letI := nontrivial_of_invariantBasisNumber R
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]
#align finite_dimensional.finrank_pi_fintype FiniteDimensional.finrank_pi_fintype

/-- If `m` and `n` are `Fintype`, the finrank of `m × n` matrices is
  `(Fintype.card m) * (Fintype.card n)`. -/
theorem finrank_matrix (m n : Type*) [Fintype m] [Fintype n] :
    finrank R (Matrix m n R) = card m * card n := by simp [finrank]
#align finite_dimensional.finrank_matrix FiniteDimensional.finrank_matrix

variable {R M N}

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
theorem nonempty_linearEquiv_of_finrank_eq (cond : finrank R M = finrank R N) :
    Nonempty (M ≃ₗ[R] N) :=
  nonempty_linearEquiv_of_lift_rank_eq <| by simp only [← finrank_eq_rank, cond, lift_natCast]
#align finite_dimensional.nonempty_linear_equiv_of_finrank_eq FiniteDimensional.nonempty_linearEquiv_of_finrank_eq

/-- Two finite and free modules are isomorphic if and only if they have the same (finite) rank. -/
theorem nonempty_linearEquiv_iff_finrank_eq : Nonempty (M ≃ₗ[R] N) ↔ finrank R M = finrank R N :=
  ⟨fun ⟨h⟩ => h.finrank_eq, fun h => nonempty_linearEquiv_of_finrank_eq h⟩
#align finite_dimensional.nonempty_linear_equiv_iff_finrank_eq FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq

variable (M N)

/-- Two finite and free modules are isomorphic if they have the same (finite) rank. -/
noncomputable def _root_.LinearEquiv.ofFinrankEq (cond : finrank R M = finrank R N) : M ≃ₗ[R] N :=
  Classical.choice <| nonempty_linearEquiv_of_finrank_eq cond
#align linear_equiv.of_finrank_eq LinearEquiv.ofFinrankEq

end RingFree

section CommRing

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The finrank of `M ⊗[R] N` is `(finrank R M) * (finrank R N)`. -/
@[simp]
theorem finrank_tensorProduct (M : Type v) (N : Type w) [AddCommGroup M] [Module R M]
    [Module.Free R M] [AddCommGroup N] [Module R N] [Module.Free R N] :
    finrank R (M ⊗[R] N) = finrank R M * finrank R N := by simp [finrank]
#align finite_dimensional.finrank_tensor_product FiniteDimensional.finrank_tensorProduct

end CommRing

end FiniteDimensional

section

open FiniteDimensional

variable {R M N}

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

theorem LinearMap.finrank_le_finrank_of_injective [Module.Finite R N] {f : M →ₗ[R] N}
    (hf : Function.Injective f) : finrank R M ≤ finrank R N :=
  finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)
#align linear_map.finrank_le_finrank_of_injective LinearMap.finrank_le_finrank_of_injective

theorem LinearMap.finrank_range_le [Module.Finite R M] (f : M →ₗ[R] N) :
    finrank R (LinearMap.range f) ≤ finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)
#align linear_map.finrank_range_le LinearMap.finrank_range_le

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) :
    finrank R s ≤ finrank R M := by
  simpa only [Cardinal.toNat_lift] using
    toNat_le_of_le_of_lt_aleph0 (rank_lt_aleph0 _ _) (rank_submodule_le s)
#align submodule.finrank_le Submodule.finrank_le

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem Submodule.finrank_quotient_le [Module.Finite R M] (s : Submodule R M) :
    finrank R (M ⧸ s) ≤ finrank R M := by
  simpa only [Cardinal.toNat_lift] using
    toNat_le_of_le_of_lt_aleph0 (rank_lt_aleph0 _ _)
      ((Submodule.mkQ s).rank_le_of_surjective (surjective_quot_mk _))
#align submodule.finrank_quotient_le Submodule.finrank_quotient_le

/-- Pushforwards of finite submodules have a smaller finrank. -/
theorem Submodule.finrank_map_le (f : M →ₗ[R] N) (p : Submodule R M) [Module.Finite R p] :
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


open Cardinal Submodule Module Function FiniteDimensional

attribute [local instance] nontrivial_of_invariantBasisNumber

variable {R} {V : Type v}

open IsNoetherian

section DivisionRing

variable [AddCommGroup V] {V₂ : Type v'} [AddCommGroup V₂]
variable [Ring R] [StrongRankCondition R] [Module R V] [Module.Free R V]

/-- See `FiniteDimensional.rank_lt_aleph0` for the inverse direction without `Module.Free R V`. -/
lemma Module.rank_lt_alpeh0_iff :
    Module.rank R V < ℵ₀ ↔ Module.Finite R V := by
  rw [Free.rank_eq_card_chooseBasisIndex, mk_lt_aleph0_iff]
  exact ⟨fun h ↦ Finite.of_basis (Free.chooseBasis R V),
    fun I ↦ Finite.of_fintype (Free.ChooseBasisIndex R V)⟩

theorem FiniteDimensional.finrank_of_not_finite
    (h : ¬Module.Finite R V) :
    finrank R V = 0 :=
  dif_neg (rank_lt_alpeh0_iff.not.mpr h)

theorem Module.finite_of_finrank_pos (h : 0 < finrank R V) :
    Module.Finite R V := by
  contrapose h
  simp [finrank_of_not_finite h]

theorem Module.finite_of_finrank_eq_succ {n : ℕ}
    (hn : finrank R V = n.succ) : Module.Finite R V :=
  Module.finite_of_finrank_pos <| by rw [hn]; exact n.succ_pos

theorem Module.finite_iff_of_rank_eq_nsmul {W} [AddCommGroup W]
    [Module R W] [Module.Free R W] {n : ℕ} (hn : n ≠ 0)
    (hVW : Module.rank R V = n • Module.rank R W) :
    Module.Finite R V ↔ Module.Finite R W := by
  simp only [← rank_lt_alpeh0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

/-- If a free module is of finite rank, then the cardinality of any basis is equal to its
`finrank`. -/
theorem Module.mk_finrank_eq_card_basis [Module.Finite R V]
    {ι : Type w} (h : Basis ι R V) : (finrank R V : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Free.finite_basis h)
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

/-- Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
noncomputable def Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have A : Cardinal.mk ι = ↑(FiniteDimensional.finrank R R) :=
    (Module.mk_finrank_eq_card_basis b).symm
  -- porting note: replace `algebraMap.coe_one` with `Nat.cast_one`
  simp only [Cardinal.eq_one_iff_unique, FiniteDimensional.finrank_self, Nat.cast_one] at A
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 A)
#align basis.unique Basis.unique

namespace FiniteDimensional
variable (R V)

/-- A finite rank free module has a basis indexed by `Fin (finrank R V)`. -/
noncomputable def finBasis [Module.Finite R V] :
    Basis (Fin (finrank R V)) R V :=
  (Free.chooseBasis R V).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R V).symm)
#align finite_dimensional.fin_basis FiniteDimensional.finBasis

/-- A rank `n` free module has a basis indexed by `Fin n`. -/
noncomputable def finBasisOfFinrankEq [Module.Finite R V]
    {n : ℕ} (hn : finrank R V = n) :
    Basis (Fin n) R V :=
  (finBasis R V).reindex (Fin.castIso hn).toEquiv
#align finite_dimensional.fin_basis_of_finrank_eq FiniteDimensional.finBasisOfFinrankEq

variable {R V}

/-- A free module with rank 1 has a basis with one element. -/
noncomputable def basisUnique (ι : Type*) [Unique ι]
    (h : finrank R V = 1) :
    Basis ι R V :=
  haveI : Module.Finite R V :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R V h).reindex (Equiv.equivOfUnique _ _)
#align finite_dimensional.basis_unique FiniteDimensional.basisUnique

@[simp]
theorem basisUnique_repr_eq_zero_iff {ι : Type*} [Unique ι]
    {h : finrank R V = 1} {v : V} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩
#align finite_dimensional.basis_unique.repr_eq_zero_iff FiniteDimensional.basisUnique_repr_eq_zero_iff

theorem cardinal_mk_le_finrank_of_linearIndependent [Module.Finite R V]
    {ι : Type w} {b : ι → V} (h : LinearIndependent R b) : #ι ≤ finrank R V := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using
    cardinal_lift_le_rank_of_linearIndependent h
#align finite_dimensional.cardinal_mk_le_finrank_of_linear_independent FiniteDimensional.cardinal_mk_le_finrank_of_linearIndependent

theorem fintype_card_le_finrank_of_linearIndependent [Module.Finite R V]
    {ι : Type*} [Fintype ι] {b : ι → V} (h : LinearIndependent R b) :
    Fintype.card ι ≤ finrank R V := by
  simpa using cardinal_mk_le_finrank_of_linearIndependent h
#align finite_dimensional.fintype_card_le_finrank_of_linear_independent FiniteDimensional.fintype_card_le_finrank_of_linearIndependent

theorem finset_card_le_finrank_of_linearIndependent [Module.Finite R V]
    {b : Finset V} (h : LinearIndependent R (fun x => x : b → V)) :
    b.card ≤ finrank R V := by
  rw [← Fintype.card_coe]
  exact fintype_card_le_finrank_of_linearIndependent h
#align finite_dimensional.finset_card_le_finrank_of_linear_independent FiniteDimensional.finset_card_le_finrank_of_linearIndependent

end FiniteDimensional

theorem Module.Finite.lt_aleph0_of_linearIndependent {ι : Type w}
    [Module.Finite R V] {v : ι → V} (h : LinearIndependent R v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  apply cardinal_lift_le_rank_of_linearIndependent h
  rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
  apply Cardinal.nat_lt_aleph0

theorem LinearIndependent.finite [Module.Finite R V] {ι : Type*} {f : ι → V}
    (h : LinearIndependent R f) : Finite ι :=
  Cardinal.lt_aleph0_iff_finite.1 <| Module.Finite.lt_aleph0_of_linearIndependent h

theorem LinearIndependent.setFinite [Module.Finite R V] {b : Set V}
    (h : LinearIndependent R fun x : b => (x : V)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp (Module.Finite.lt_aleph0_of_linearIndependent h)
#align linear_independent.finite LinearIndependent.setFinite

theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι] [Module.Finite R V]
    (v : ι → V) : ¬LinearIndependent R v := mt LinearIndependent.finite <| @not_finite _ _
#align finite_dimensional.not_linear_independent_of_infinite Module.Finite.not_linearIndependent_of_infinite

/-- A finite rank torsion-free module has positive `finrank` iff it has a nonzero element. -/
theorem FiniteDimensional.finrank_pos_iff_exists_ne_zero
    [Module.Finite R V] [NoZeroSMulDivisors R V] :
    0 < finrank R V ↔ ∃ x : V, x ≠ 0 :=
  Iff.trans
    (by
      rw [← finrank_eq_rank]
      norm_cast)
    (@rank_pos_iff_exists_ne_zero R V _ _ _ _ _)
#align finite_dimensional.finrank_pos_iff_exists_ne_zero FiniteDimensional.finrank_pos_iff_exists_ne_zero

/-- An `R`-finite torsion-free module has positive `finrank` iff it is nontrivial. -/
theorem FiniteDimensional.finrank_pos_iff [Module.Finite R V] [NoZeroSMulDivisors R V] :
    0 < finrank R V ↔ Nontrivial V :=
  Iff.trans
    (by rw [← finrank_eq_rank]; norm_cast)
    (rank_pos_iff_nontrivial (R := R))
#align finite_dimensional.finrank_pos_iff FiniteDimensional.finrank_pos_iff

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem FiniteDimensional.finrank_pos
    [Module.Finite R V] [NoZeroSMulDivisors R V] [h : Nontrivial V] :
    0 < finrank R V :=
  finrank_pos_iff.mpr h
#align finite_dimensional.finrank_pos FiniteDimensional.finrank_pos

/-- See `FiniteDimensional.finrank_zero_iff`
  for the stronger version with `NoZeroSMulDivisors R V`. -/
theorem FiniteDimensional.finrank_eq_zero_iff [Module.Finite R V] :
    finrank R V = 0 ↔ ∀ x : V, ∃ a : R, a ≠ 0 ∧ a • x = 0 :=
  Iff.trans
    (by rw [← finrank_eq_rank]; norm_cast)
    (rank_eq_zero_iff (R := R))

/-- The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`. -/
theorem FiniteDimensional.finrank_eq_zero_iff_isTorsion {R} [CommRing R] [StrongRankCondition R]
    [IsDomain R] [Module R V] [Module.Finite R V] :
    finrank R V = 0 ↔ IsTorsion R V :=
  Iff.trans
    (by rw [← finrank_eq_rank]; norm_cast)
    (rank_eq_zero_iff_isTorsion (R := R))

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `rank_zero_iff`. -/
theorem FiniteDimensional.finrank_zero_iff [Module.Finite R V] [NoZeroSMulDivisors R V] :
    finrank R V = 0 ↔ Subsingleton V :=
  Iff.trans
    (by rw [← finrank_eq_rank]; norm_cast)
    (rank_zero_iff (R := R))
#align finite_dimensional.finrank_zero_iff FiniteDimensional.finrank_zero_iff

variable (R K)

/-- The submodule generated by a finite set is `R`-finite. -/
theorem Module.Finite.span_of_finite {A : Set V} (hA : Set.Finite A) :
    Module.Finite R (Submodule.span R A) :=
  ⟨(Submodule.fg_top _).mpr ⟨hA.toFinset, hA.coe_toFinset.symm ▸ rfl⟩⟩

/-- The submodule generated by a single element is `R`-finite. -/
instance Module.Finite.span_singleton (x : V) : Module.Finite R (R ∙ x) :=
  Module.Finite.span_of_finite R <| Set.finite_singleton _

/-- The submodule generated by a finset is `R`-finite. -/
instance Module.Finite.span_finset (s : Finset V) : Module.Finite R (span R (s : Set V)) :=
  ⟨(Submodule.fg_top _).mpr ⟨s, rfl⟩⟩

variable {K R}

theorem CompleteLattice.Independent.subtype_ne_bot_le_finrank_aux [Module.Finite R V]
    [NoZeroSMulDivisors R V]
    {ι : Type w} {p : ι → Submodule R V} (hp : CompleteLattice.Independent p) :
    #{ i // p i ≠ ⊥ } ≤ (finrank R V : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{v} (finrank R V : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R V) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R V : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank R V : Cardinal.{w}) := by simp
#align complete_lattice.independent.subtype_ne_bot_le_finrank_aux CompleteLattice.Independent.subtype_ne_bot_le_finrank_aux

/-- If `p` is an independent family of submodules of a `R`-finite module `V`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional
    [Module.Finite R V] [NoZeroSMulDivisors R V] {ι : Type w} {p : ι → Submodule R V}
    (hp : CompleteLattice.Independent p) : Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine' lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux _
  simp [Cardinal.nat_lt_aleph0]
#align complete_lattice.independent.fintype_ne_bot_of_finite_dimensional CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional

/-- If `p` is an independent family of submodules of a `R`-finite module `V`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `V`.

Note that the `Fintype` hypothesis required here can be provided by
`CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional`. -/
theorem CompleteLattice.Independent.subtype_ne_bot_le_finrank
    [Module.Finite R V] [NoZeroSMulDivisors R V]
    {ι : Type w} {p : ι → Submodule R V} (hp : CompleteLattice.Independent p)
    [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank R V := by simpa using hp.subtype_ne_bot_le_finrank_aux
#align complete_lattice.independent.subtype_ne_bot_le_finrank CompleteLattice.Independent.subtype_ne_bot_le_finrank

section

open BigOperators

open Finset

/-- If a finset has cardinality larger than the rank of a module,
then there is a nontrivial linear relation amongst its elements. -/
theorem Module.exists_nontrivial_relation_of_finrank_lt_card
    [Module.Finite R V] {t : Finset V}
    (h : finrank R V < t.card) : ∃ f : V → R, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt FiniteDimensional.finset_card_le_finrank_of_linearIndependent h.not_le)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert sum; apply Subtype.val_injective.extend_apply
#align finite_dimensional.exists_nontrivial_relation_of_rank_lt_card Module.exists_nontrivial_relation_of_finrank_lt_card

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero. -/
theorem Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card [Module.Finite R V]
    {t : Finset V} (h : finrank R V + 1 < t.card) :
    ∃ f : V → R, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  -- Pick an element x₀ ∈ t,
  obtain ⟨x₀, x₀_mem⟩ := card_pos.1 ((Nat.succ_pos _).trans h)
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨(· - x₀), sub_left_injective⟩
  classical
  let t' := (t.erase x₀).map shift
  have h' : finrank R V < t'.card := by
    rw [card_map, card_erase_of_mem x₀_mem]
    exact Nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_finrank_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → R := fun z ↦ if z = x₀ then -∑ z in t.erase x₀, g (z - x₀) else g (z - x₀)
  refine ⟨f, ?_, ?_, ?_⟩
  -- After this, it's a matter of verifying the properties,
  -- based on the corresponding properties for `g`.
  · rw [sum_map, Embedding.coeFn_mk] at gsum
    simp_rw [← t.sum_erase_add _ x₀_mem, if_pos, neg_smul, sum_smul,
             ← sub_eq_add_neg, ← sum_sub_distrib, ← gsum, smul_sub]
    refine sum_congr rfl fun x x_mem ↦ ?_
    rw [if_neg (mem_erase.mp x_mem).1]
  · simp_rw [← t.sum_erase_add _ x₀_mem, if_pos, add_neg_eq_zero]
    exact sum_congr rfl fun x x_mem ↦ if_neg (mem_erase.mp x_mem).1
  · obtain ⟨x₁, x₁_mem', rfl⟩ := Finset.mem_map.mp x₁_mem
    have := mem_erase.mp x₁_mem'
    exact ⟨x₁, by simpa only [Embedding.coeFn_mk, sub_add_cancel, this.2, true_and, if_neg this.1]⟩
#align finite_dimensional.exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card

end

end DivisionRing

section ZeroRank

variable [Ring R] [AddCommGroup V] [Module R V]

open FiniteDimensional

theorem Module.finite_of_rank_eq_nat [Module.Free R V] {n : ℕ} (h : Module.rank R V = n) :
    Module.Finite R V := by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := V)
  have := mk_lt_aleph0_iff.mp <| cardinal_le_rank_of_linearIndependent
    b.linearIndependent |>.trans_eq h |>.trans_lt <| nat_lt_aleph0 n
  exact Module.Finite.of_basis b

theorem Module.finite_of_rank_eq_zero [NoZeroSMulDivisors R V]
    (h : Module.rank R V = 0) :
    Module.Finite R V := by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

theorem Module.finite_of_rank_eq_one [Module.Free R V] (h : Module.rank R V = 1) :
    Module.Finite R V :=
  Module.finite_of_rank_eq_nat <| h.trans Nat.cast_one.symm

theorem FiniteDimensional.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R V = 0) :
    finrank R V = 0 := by
  delta finrank
  rw [h, zero_toNat]
#align finrank_eq_zero_of_rank_eq_zero FiniteDimensional.finrank_eq_zero_of_rank_eq_zero

variable (R V)

instance Module.finite_bot : Module.Finite R (⊥ : Submodule R V) := inferInstance

variable {R V}

theorem Submodule.bot_eq_top_of_rank_eq_zero [NoZeroSMulDivisors R V] (h : Module.rank R V = 0) :
    (⊥ : Submodule R V) = ⊤ := by
  nontriviality R
  rw [rank_zero_iff] at h
  exact Subsingleton.elim _ _
#align bot_eq_top_of_rank_eq_zero Submodule.bot_eq_top_of_rank_eq_zero

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
@[simp]
theorem Submodule.rank_eq_zero [Nontrivial R] [NoZeroSMulDivisors R V] {S : Submodule R V} :
    Module.rank R S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩
#align rank_eq_zero Submodule.rank_eq_zero

@[simp]
theorem Submodule.finrank_eq_zero [StrongRankCondition R] [NoZeroSMulDivisors R V]
    {S : Submodule R V} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Cardinal.natCast_inj]
#align finrank_eq_zero Submodule.finrank_eq_zero

end ZeroRank

namespace Submodule

open IsNoetherian FiniteDimensional

variable [Ring R] [AddCommGroup V] [Module R V]

theorem fg_iff_finite (s : Submodule R V) : s.FG ↔ Module.Finite R s :=
  (finite_def.trans (fg_top s)).symm

/-- The sup of two fg submodules is finite. Also see `Submodule.FG.sup`. -/
instance finite_sup (S₁ S₂ : Submodule R V) [h₁ : Module.Finite R S₁]
    [h₂ : Module.Finite R S₂] : Module.Finite R (S₁ ⊔ S₂ : Submodule R V) := by
  rw [finite_def] at *
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finite_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R (s.sup S : Submodule R V) := by
  refine'
    @Finset.sup_induction _ _ _ _ s S (fun i => Module.Finite R ↑i) (Module.finite_bot R V)
      _ fun i _ => by infer_instance
  · intro S₁ hS₁ S₂ hS₂
    exact Submodule.finite_sup S₁ S₂

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
sort is finite-dimensional. -/
instance finite_iSup {ι : Sort*} [Finite ι] (S : ι → Submodule R V)
    [∀ i, Module.Finite R (S i)] : Module.Finite R ↑(⨆ i, S i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup_univ_eq_iSup]
  exact Submodule.finite_finset_sup _ _

end Submodule

section

variable [Ring R] [AddCommGroup V] [Module R V]

instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end
