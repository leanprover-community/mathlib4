/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Scott Morrison
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `Module.rank : Cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

* The rank of a linear map is defined as the rank of its range.

## Main statements

* `LinearMap.rank_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `LinearMap.rank_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.
* `basis_finite_of_finite_spans`:
  the existence of a finite spanning set implies that any basis is finite.
* `infinite_basis_le_maximal_linearIndependent`:
  if `b` is an infinite basis for a module `M`,
  and `s` is a maximal linearly independent set,
  then the cardinality of `b` is bounded by the cardinality of `s`.

For modules over rings satisfying the rank condition

* `Basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linearIndependent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : Set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linearIndependent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

For vector spaces (i.e. modules over a field), we have

* `rank_quotient_add_rank`: if `V₁` is a submodule of `M`, then
  `Module.rank (M/V₁) + Module.rank V₁ = Module.rank M`.
* `rank_range_add_rank_ker`: the rank-nullity theorem.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `M`, `M'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/


noncomputable section

universe u v v' v'' u₁' w w'

variable {R : Type u} {M V₁ V₂ V₃ : Type v} {M' V'₁ : Type v'} {V'' : Type v''}

variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open BigOperators Cardinal Basis Submodule Function Set DirectSum FiniteDimensional

variable [Ring R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup M'] [Module R M'] [Module.Free R M']

variable [AddCommGroup V₁] [Module R V₁] [Module.Free R V₁]

namespace Module.Free

variable (R M)

/-- The rank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
theorem rank_eq_card_chooseBasisIndex : Module.rank R M = #(ChooseBasisIndex R M) :=
  (chooseBasis R M).mk_eq_rank''.symm
#align module.free.rank_eq_card_choose_basis_index Module.Free.rank_eq_card_chooseBasisIndex

/-- The finrank of a free module `M` over `R` is the cardinality of `ChooseBasisIndex R M`. -/
theorem _root_.FiniteDimensional.finrank_eq_card_chooseBasisIndex [Module.Finite R M] :
    finrank R M = Fintype.card (ChooseBasisIndex R M) := by
  simp [finrank, rank_eq_card_chooseBasisIndex]
#align finite_dimensional.finrank_eq_card_choose_basis_index FiniteDimensional.finrank_eq_card_chooseBasisIndex

/-- The rank of a free module `M` over an infinite scalar ring `R` is the cardinality of `M`
whenever `#R < #M`. -/
lemma rank_eq_mk_of_infinite_lt [Infinite R] (h_lt : lift.{v} #R < lift.{u} #M) :
    Module.rank R M = #M := by
  have : Infinite M := infinite_iff.mpr <| lift_le.mp <| le_trans (by simp) h_lt.le
  have h : lift #M = lift #(ChooseBasisIndex R M →₀ R) := lift_mk_eq'.mpr ⟨(chooseBasis R M).repr⟩
  simp only [mk_finsupp_lift_of_infinite', lift_id', ← rank_eq_card_chooseBasisIndex, lift_max,
    lift_lift] at h
  refine lift_inj.mp ((max_eq_iff.mp h.symm).resolve_right <| not_and_of_not_left _ ?_).left
  exact (lift_umax.{v, u}.symm ▸ h_lt).ne

end Module.Free

open Module.Free

open Cardinal

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linearEquiv_of_lift_rank_eq
    (cnd : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    Nonempty (M ≃ₗ[R] M') := by
  obtain ⟨⟨_, B⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, B'⟩⟩ := Module.Free.exists_basis (R := R) (M := M')
  have : Cardinal.lift.{v', v} #_ = Cardinal.lift.{v, v'} #_ := by
    rw [B.mk_eq_rank'', cnd, B'.mk_eq_rank'']
  exact (Cardinal.lift_mk_eq.{v, v', 0}.1 this).map (B.equiv B')
#align nonempty_linear_equiv_of_lift_rank_eq nonempty_linearEquiv_of_lift_rank_eq

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linearEquiv_of_rank_eq (cond : Module.rank R M = Module.rank R V₁) :
    Nonempty (M ≃ₗ[R] V₁) :=
  nonempty_linearEquiv_of_lift_rank_eq <| congr_arg _ cond
#align nonempty_linear_equiv_of_rank_eq nonempty_linearEquiv_of_rank_eq

section

variable (M M' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofLiftRankEq
    (cond : Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')) :
    M ≃ₗ[R] M' :=
  Classical.choice (nonempty_linearEquiv_of_lift_rank_eq cond)
#align linear_equiv.of_lift_rank_eq LinearEquiv.ofLiftRankEq

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def LinearEquiv.ofRankEq (cond : Module.rank R M = Module.rank R V₁) : M ≃ₗ[R] V₁ :=
  Classical.choice (nonempty_linearEquiv_of_rank_eq cond)
#align linear_equiv.of_rank_eq LinearEquiv.ofRankEq

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_lift_rank_eq : Nonempty (M ≃ₗ[R] M') ↔
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') :=
  ⟨fun ⟨h⟩ => LinearEquiv.lift_rank_eq h, fun h => nonempty_linearEquiv_of_lift_rank_eq h⟩
#align linear_equiv.nonempty_equiv_iff_lift_rank_eq LinearEquiv.nonempty_equiv_iff_lift_rank_eq

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem LinearEquiv.nonempty_equiv_iff_rank_eq :
    Nonempty (M ≃ₗ[R] V₁) ↔ Module.rank R M = Module.rank R V₁ :=
  ⟨fun ⟨h⟩ => LinearEquiv.rank_eq h, fun h => nonempty_linearEquiv_of_rank_eq h⟩
#align linear_equiv.nonempty_equiv_iff_rank_eq LinearEquiv.nonempty_equiv_iff_rank_eq

/-- See `FiniteDimensional.rank_lt_aleph0` for the inverse direction without `Module.Free R M`. -/
lemma Module.rank_lt_alpeh0_iff :
    Module.rank R M < ℵ₀ ↔ Module.Finite R M := by
  rw [Free.rank_eq_card_chooseBasisIndex, mk_lt_aleph0_iff]
  exact ⟨fun h ↦ Finite.of_basis (Free.chooseBasis R M),
    fun I ↦ Finite.of_fintype (Free.ChooseBasisIndex R M)⟩

theorem FiniteDimensional.finrank_of_not_finite
    (h : ¬Module.Finite R M) :
    finrank R M = 0 :=
  dif_neg (Module.rank_lt_alpeh0_iff.not.mpr h)

theorem Module.finite_of_finrank_pos (h : 0 < finrank R M) :
    Module.Finite R M := by
  contrapose h
  simp [finrank_of_not_finite h]

theorem Module.finite_of_finrank_eq_succ {n : ℕ}
    (hn : finrank R M = n.succ) : Module.Finite R M :=
  Module.finite_of_finrank_pos <| by rw [hn]; exact n.succ_pos

theorem Module.finite_iff_of_rank_eq_nsmul {W} [AddCommGroup W]
    [Module R W] [Module.Free R W] {n : ℕ} (hn : n ≠ 0)
    (hVW : Module.rank R M = n • Module.rank R W) :
    Module.Finite R M ↔ Module.Finite R W := by
  simp only [← rank_lt_alpeh0_iff, hVW, nsmul_lt_aleph0_iff_of_ne_zero hn]

namespace FiniteDimensional
variable (R M)

/-- A finite rank free module has a basis indexed by `Fin (finrank R M)`. -/
noncomputable def finBasis [Module.Finite R M] :
    Basis (Fin (finrank R M)) R M :=
  (Module.Free.chooseBasis R M).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R M).symm)
#align finite_dimensional.fin_basis FiniteDimensional.finBasis

/-- A rank `n` free module has a basis indexed by `Fin n`. -/
noncomputable def finBasisOfFinrankEq [Module.Finite R M]
    {n : ℕ} (hn : finrank R M = n) :
    Basis (Fin n) R M :=
  (finBasis R M).reindex (Fin.castIso hn).toEquiv
#align finite_dimensional.fin_basis_of_finrank_eq FiniteDimensional.finBasisOfFinrankEq

variable {R M}

/-- A free module with rank 1 has a basis with one element. -/
noncomputable def basisUnique (ι : Type*) [Unique ι]
    (h : finrank R M = 1) :
    Basis ι R M :=
  haveI : Module.Finite R M :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R M h).reindex (Equiv.equivOfUnique _ _)
#align finite_dimensional.basis_unique FiniteDimensional.basisUnique

@[simp]
theorem basisUnique_repr_eq_zero_iff {ι : Type*} [Unique ι]
    {h : finrank R M = 1} {v : M} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩
#align finite_dimensional.basis_unique.repr_eq_zero_iff FiniteDimensional.basisUnique_repr_eq_zero_iff

end FiniteDimensional
