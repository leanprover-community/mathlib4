/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ApplyCongr

#align_import linear_algebra.finite_dimensional from "leanprover-community/mathlib"@"e95e4f92c8f8da3c7f693c3ec948bcf9b6683f51"

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a division ring `K`. There are (at least) three equivalent
definitions of finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `FiniteDimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the second point of view, i.e., as `Finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `FiniteDimensional`):

- `fintypeBasisIndex` states that a finite-dimensional
  vector space has a finite basis
- `FiniteDimensional.finBasis` and `FiniteDimensional.finBasisOfFinrankEq`
  are bases for finite dimensional vector spaces, where the index type
  is `Fin`
- `of_fintype_basis` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `IsNoetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian

We make use of `finrank`, the dimension of a finite dimensional space, returning a `Nat`, as
opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`. `finrank` is not defined using `FiniteDimensional`.
For basic results that do not need the `FiniteDimensional` class, import
`Mathlib.LinearAlgebra.Finrank`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `finrank_quotient_add_finrank`)
- linear equivs, in `LinearEquiv.finiteDimensional`
- image under a linear map (the rank-nullity formula is in `finrank_range_add_finrank_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `LinearMap.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `LinearMap.mul_eq_one_comm`
and `LinearMap.comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `Mathlib.LinearAlgebra.Dimension`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `Submodule.fg_iff_finiteDimensional`.
-/


universe u v v' w

open Cardinal Submodule Module Function

/-- `FiniteDimensional` vector spaces are defined to be finite modules.
Use `FiniteDimensional.of_fintype_basis` to prove finite dimension from another definition. -/
@[reducible]
def FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V
#align finite_dimensional FiniteDimensional

variable {K : Type u} {V : Type v}

namespace FiniteDimensional

open IsNoetherian

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- If the codomain of an injective linear map is finite dimensional, the domain must be as well. -/
theorem of_injective (f : V →ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] :
    FiniteDimensional K V :=
  have : IsNoetherian K V₂ := IsNoetherian.iff_fg.mpr ‹_›
  Module.Finite.of_injective f w
#align finite_dimensional.of_injective FiniteDimensional.of_injective

/-- If the domain of a surjective linear map is finite dimensional, the codomain must be as well. -/
theorem of_surjective (f : V →ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w
#align finite_dimensional.of_surjective FiniteDimensional.of_surjective

variable (K V)

instance finiteDimensional_pi {ι : Type*} [Finite ι] : FiniteDimensional K (ι → K) :=
  iff_fg.1 isNoetherian_pi
#align finite_dimensional.finite_dimensional_pi FiniteDimensional.finiteDimensional_pi

instance finiteDimensional_pi' {ι : Type*} [Finite ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [I : ∀ i, FiniteDimensional K (M i)] : FiniteDimensional K (∀ i, M i) :=
  haveI : ∀ i : ι, IsNoetherian K (M i) := fun i => iff_fg.2 (I i)
  iff_fg.1 isNoetherian_pi
#align finite_dimensional.finite_dimensional_pi' FiniteDimensional.finiteDimensional_pi'

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintypeOfFintype [Fintype K] [FiniteDimensional K V] : Fintype V :=
  Module.fintypeOfFintype (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))
#align finite_dimensional.fintype_of_fintype FiniteDimensional.fintypeOfFintype

theorem finite_of_finite [Finite K] [FiniteDimensional K V] : Finite V := by
  cases nonempty_fintype K
  -- ⊢ _root_.Finite V
  haveI := fintypeOfFintype K V
  -- ⊢ _root_.Finite V
  infer_instance
  -- 🎉 no goals
#align finite_dimensional.finite_of_finite FiniteDimensional.finite_of_finite

variable {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
theorem of_fintype_basis {ι : Type w} [Finite ι] (h : Basis ι K V) : FiniteDimensional K V := by
  classical
  cases nonempty_fintype ι
  exact ⟨⟨Finset.univ.image h, by
    convert h.span_eq
    simp⟩⟩
#align finite_dimensional.of_fintype_basis FiniteDimensional.of_fintype_basis

/-- If a vector space is `FiniteDimensional`, all bases are indexed by a finite type -/
noncomputable def fintypeBasisIndex {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V) :
    Fintype ι :=
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  IsNoetherian.fintypeBasisIndex b
#align finite_dimensional.fintype_basis_index FiniteDimensional.fintypeBasisIndex

/-- If a vector space is `FiniteDimensional`, `Basis.ofVectorSpace` is indexed by
  a finite type.-/
noncomputable instance [FiniteDimensional K V] : Fintype (Basis.ofVectorSpaceIndex K V) := by
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  -- ⊢ Fintype ↑(Basis.ofVectorSpaceIndex K V)
  infer_instance
  -- 🎉 no goals

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
theorem of_finite_basis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s) :
    FiniteDimensional K V :=
  haveI := hs.fintype
  of_fintype_basis h
#align finite_dimensional.of_finite_basis FiniteDimensional.of_finite_basis

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensional_submodule [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K S := by
  letI : IsNoetherian K V := iff_fg.2 ?_
  -- ⊢ FiniteDimensional K { x // x ∈ S }
  exact
    iff_fg.1
      (IsNoetherian.iff_rank_lt_aleph0.2
        (lt_of_le_of_lt (rank_submodule_le _) (rank_lt_aleph0 K V)))
  infer_instance
  -- 🎉 no goals
#align finite_dimensional.finite_dimensional_submodule FiniteDimensional.finiteDimensional_submodule

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensional_quotient [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K (V ⧸ S) :=
  Module.Finite.of_surjective (Submodule.mkQ S) <| surjective_quot_mk _
#align finite_dimensional.finite_dimensional_quotient FiniteDimensional.finiteDimensional_quotient

variable (K V)

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. This is a copy of `finrank_eq_rank _ _` which creates easier typeclass searches. -/
theorem finrank_eq_rank' [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V :=
  finrank_eq_rank _ _
#align finite_dimensional.finrank_eq_rank' FiniteDimensional.finrank_eq_rank'

variable {K V}

theorem finrank_of_infinite_dimensional (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  dif_neg <| mt IsNoetherian.iff_rank_lt_aleph0.2 <| (not_iff_not.2 iff_fg).2 h
#align finite_dimensional.finrank_of_infinite_dimensional FiniteDimensional.finrank_of_infinite_dimensional

theorem finiteDimensional_of_finrank (h : 0 < finrank K V) : FiniteDimensional K V := by
  contrapose h
  -- ⊢ ¬0 < finrank K V
  simp [finrank_of_infinite_dimensional h]
  -- 🎉 no goals
#align finite_dimensional.finite_dimensional_of_finrank FiniteDimensional.finiteDimensional_of_finrank

theorem finiteDimensional_of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) :
    FiniteDimensional K V :=
  finiteDimensional_of_finrank <| by rw [hn]; exact n.succ_pos
                                     -- ⊢ 0 < Nat.succ n
                                              -- 🎉 no goals
#align finite_dimensional.finite_dimensional_of_finrank_eq_succ FiniteDimensional.finiteDimensional_of_finrank_eq_succ

/-- We can infer `FiniteDimensional K V` in the presence of `[Fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
theorem fact_finiteDimensional_of_finrank_eq_succ (n : ℕ) [Fact (finrank K V = n + 1)] :
    FiniteDimensional K V :=
  finiteDimensional_of_finrank <| by convert Nat.succ_pos n; apply Fact.out
                                     -- ⊢ finrank K V = Nat.succ n
                                                             -- 🎉 no goals
#align finite_dimensional.fact_finite_dimensional_of_finrank_eq_succ FiniteDimensional.fact_finiteDimensional_of_finrank_eq_succ

theorem finiteDimensional_iff_of_rank_eq_nsmul {W} [AddCommGroup W] [Module K W] {n : ℕ}
    (hn : n ≠ 0) (hVW : Module.rank K V = n • Module.rank K W) :
    FiniteDimensional K V ↔ FiniteDimensional K W := by
  simp only [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0, hVW,
    Cardinal.nsmul_lt_aleph0_iff_of_ne_zero hn]
#align finite_dimensional.finite_dimensional_iff_of_rank_eq_nsmul FiniteDimensional.finiteDimensional_iff_of_rank_eq_nsmul

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
theorem finrank_eq_card_basis' [FiniteDimensional K V] {ι : Type w} (h : Basis ι K V) :
    (finrank K V : Cardinal.{w}) = #ι := by
  haveI : IsNoetherian K V := iff_fg.2 inferInstance
  -- ⊢ ↑(finrank K V) = #ι
  haveI : Fintype ι := fintypeBasisIndex h
  -- ⊢ ↑(finrank K V) = #ι
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]
  -- 🎉 no goals
#align finite_dimensional.finrank_eq_card_basis' FiniteDimensional.finrank_eq_card_basis'

/-- Given a basis of a division ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
noncomputable def _root_.Basis.unique {ι : Type*} (b : Basis ι K K) : Unique ι := by
  have A : Cardinal.mk ι = ↑(FiniteDimensional.finrank K K) :=
    (FiniteDimensional.finrank_eq_card_basis' b).symm
  -- porting note: replace `algebraMap.coe_one` with `Nat.cast_one`
  simp only [Cardinal.eq_one_iff_unique, FiniteDimensional.finrank_self, Nat.cast_one] at A
  -- ⊢ Unique ι
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 A)
  -- 🎉 no goals
#align basis.unique Basis.unique

variable (K V)

/-- A finite dimensional vector space has a basis indexed by `Fin (finrank K V)`. -/
noncomputable def finBasis [FiniteDimensional K V] : Basis (Fin (finrank K V)) K V :=
  have h : Fintype.card (@finsetBasisIndex K V _ _ _ (iff_fg.2 inferInstance)) = finrank K V :=
    (finrank_eq_card_basis (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance))).symm
  (@finsetBasis K V _ _ _ (iff_fg.2 inferInstance)).reindex (Fintype.equivFinOfCardEq h)
#align finite_dimensional.fin_basis FiniteDimensional.finBasis

/-- An `n`-dimensional vector space has a basis indexed by `Fin n`. -/
noncomputable def finBasisOfFinrankEq [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = n) :
    Basis (Fin n) K V :=
  (finBasis K V).reindex (Fin.castIso hn).toEquiv
#align finite_dimensional.fin_basis_of_finrank_eq FiniteDimensional.finBasisOfFinrankEq

variable {K V}

/-- A module with dimension 1 has a basis with one element. -/
noncomputable def basisUnique (ι : Type*) [Unique ι] (h : finrank K V = 1) : Basis ι K V :=
  haveI : FiniteDimensional _ _ :=
    finiteDimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq K V h).reindex (Equiv.equivOfUnique _ _)
#align finite_dimensional.basis_unique FiniteDimensional.basisUnique

@[simp]
theorem basisUnique.repr_eq_zero_iff {ι : Type*} [Unique ι] {h : finrank K V = 1} {v : V} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩
                 -- 🎉 no goals
#align finite_dimensional.basis_unique.repr_eq_zero_iff FiniteDimensional.basisUnique.repr_eq_zero_iff

theorem cardinal_mk_le_finrank_of_linearIndependent [FiniteDimensional K V] {ι : Type w} {b : ι → V}
    (h : LinearIndependent K b) : #ι ≤ finrank K V := by
  rw [← lift_le.{max v w}]
  -- ⊢ lift.{max v w, w} #ι ≤ lift.{max v w, w} ↑(finrank K V)
  simpa [← finrank_eq_rank', -finrank_eq_rank] using
    cardinal_lift_le_rank_of_linearIndependent h
#align finite_dimensional.cardinal_mk_le_finrank_of_linear_independent FiniteDimensional.cardinal_mk_le_finrank_of_linearIndependent

theorem fintype_card_le_finrank_of_linearIndependent [FiniteDimensional K V] {ι : Type*}
    [Fintype ι] {b : ι → V} (h : LinearIndependent K b) : Fintype.card ι ≤ finrank K V := by
  simpa using cardinal_mk_le_finrank_of_linearIndependent h
  -- 🎉 no goals
#align finite_dimensional.fintype_card_le_finrank_of_linear_independent FiniteDimensional.fintype_card_le_finrank_of_linearIndependent

theorem finset_card_le_finrank_of_linearIndependent [FiniteDimensional K V] {b : Finset V}
    (h : LinearIndependent K (fun x => x : b → V)) : b.card ≤ finrank K V := by
  rw [← Fintype.card_coe]
  -- ⊢ Fintype.card { x // x ∈ b } ≤ finrank K V
  exact fintype_card_le_finrank_of_linearIndependent h
  -- 🎉 no goals
#align finite_dimensional.finset_card_le_finrank_of_linear_independent FiniteDimensional.finset_card_le_finrank_of_linearIndependent

theorem lt_aleph0_of_linearIndependent {ι : Type w} [FiniteDimensional K V] {v : ι → V}
    (h : LinearIndependent K v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  -- ⊢ lift.{?u.252424, w} #ι < lift.{?u.252424, w} ℵ₀
  apply lt_of_le_of_lt
  apply cardinal_lift_le_rank_of_linearIndependent h
  -- ⊢ lift.{w, v} (Module.rank K V) < lift.{v, w} ℵ₀
  rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
  -- ⊢ ↑(finrank K V) < ℵ₀
  apply Cardinal.nat_lt_aleph0
  -- 🎉 no goals
#align finite_dimensional.lt_aleph_0_of_linear_independent FiniteDimensional.lt_aleph0_of_linearIndependent

theorem _root_.LinearIndependent.finite [FiniteDimensional K V] {b : Set V}
    (h : LinearIndependent K fun x : b => (x : V)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp (FiniteDimensional.lt_aleph0_of_linearIndependent h)
#align linear_independent.finite LinearIndependent.finite

theorem not_linearIndependent_of_infinite {ι : Type w} [inf : Infinite ι] [FiniteDimensional K V]
    (v : ι → V) : ¬LinearIndependent K v := by
  intro h_lin_indep
  -- ⊢ False
  have : ¬ℵ₀ ≤ #ι := not_le.mpr (lt_aleph0_of_linearIndependent h_lin_indep)
  -- ⊢ False
  have : ℵ₀ ≤ #ι := infinite_iff.mp inf
  -- ⊢ False
  contradiction
  -- 🎉 no goals
#align finite_dimensional.not_linear_independent_of_infinite FiniteDimensional.not_linearIndependent_of_infinite

/-- A finite dimensional space has positive `finrank` iff it has a nonzero element. -/
theorem finrank_pos_iff_exists_ne_zero [FiniteDimensional K V] : 0 < finrank K V ↔ ∃ x : V, x ≠ 0 :=
  Iff.trans
    (by
      rw [← finrank_eq_rank]
      -- ⊢ 0 < finrank K V ↔ 0 < ↑(finrank K V)
      norm_cast)
      -- 🎉 no goals
    (@rank_pos_iff_exists_ne_zero K V _ _ _ _ _)
#align finite_dimensional.finrank_pos_iff_exists_ne_zero FiniteDimensional.finrank_pos_iff_exists_ne_zero

/-- A finite dimensional space has positive `finrank` iff it is nontrivial. -/
theorem finrank_pos_iff [FiniteDimensional K V] : 0 < finrank K V ↔ Nontrivial V :=
  Iff.trans
    (by
      rw [← finrank_eq_rank]
      -- ⊢ 0 < finrank K V ↔ 0 < ↑(finrank K V)
      norm_cast)
      -- 🎉 no goals
    (@rank_pos_iff_nontrivial K V _ _ _ _ _)
#align finite_dimensional.finrank_pos_iff FiniteDimensional.finrank_pos_iff

/-- A nontrivial finite dimensional space has positive `finrank`. -/
theorem finrank_pos [FiniteDimensional K V] [h : Nontrivial V] : 0 < finrank K V :=
  finrank_pos_iff.mpr h
#align finite_dimensional.finrank_pos FiniteDimensional.finrank_pos

/-- A finite dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `rank_zero_iff`. -/
theorem finrank_zero_iff [FiniteDimensional K V] : finrank K V = 0 ↔ Subsingleton V :=
  Iff.trans
    (by
      rw [← finrank_eq_rank]
      -- ⊢ finrank K V = 0 ↔ ↑(finrank K V) = 0
      norm_cast)
      -- 🎉 no goals
    (@rank_zero_iff K V _ _ _ _ _)
#align finite_dimensional.finrank_zero_iff FiniteDimensional.finrank_zero_iff

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
theorem _root_.Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V}
    (h : finrank K S = finrank K V) : S = ⊤ := by
  haveI : IsNoetherian K V := iff_fg.2 inferInstance
  -- ⊢ S = ⊤
  set bS := Basis.ofVectorSpace K S with bS_eq
  -- ⊢ S = ⊤
  have : LinearIndependent K ((↑) : ((↑) '' Basis.ofVectorSpaceIndex K S : Set V) → V) :=
    @LinearIndependent.image_subtype _ _ _ _ _ _ _ _ _ (Submodule.subtype S)
      (by simpa using bS.linearIndependent) (by simp)
  set b := Basis.extend this with b_eq
  -- ⊢ S = ⊤
  -- porting note: `letI` now uses `this` so we need to give different names
  letI i1 : Fintype (this.extend _) :=
    (finite_of_linearIndependent (by simpa using b.linearIndependent)).fintype
  letI i2 : Fintype (((↑) : S → V) '' Basis.ofVectorSpaceIndex K S) :=
    (finite_of_linearIndependent this).fintype
  letI i3 : Fintype (Basis.ofVectorSpaceIndex K S) :=
    (finite_of_linearIndependent (by simpa using bS.linearIndependent)).fintype
  have : (↑) '' Basis.ofVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective, ← finrank_eq_card_basis bS, ←
            finrank_eq_card_basis b, h])
  rw [← b.span_eq, b_eq, Basis.coe_extend, Subtype.range_coe, ← this, ← Submodule.coeSubtype,
    span_image]
  have := bS.span_eq
  -- ⊢ S = Submodule.map (Submodule.subtype S) (span K (Basis.ofVectorSpaceIndex K  …
  rw [bS_eq, Basis.coe_ofVectorSpace, Subtype.range_coe] at this
  -- ⊢ S = Submodule.map (Submodule.subtype S) (span K (Basis.ofVectorSpaceIndex K  …
  rw [this, map_top (Submodule.subtype S), range_subtype]
  -- 🎉 no goals
#align finite_dimensional.eq_top_of_finrank_eq Submodule.eq_top_of_finrank_eq
#align submodule.eq_top_of_finrank_eq Submodule.eq_top_of_finrank_eq

variable (K)

instance finiteDimensional_self : FiniteDimensional K K := by infer_instance
                                                              -- 🎉 no goals
#align finite_dimensional.finite_dimensional_self FiniteDimensional.finiteDimensional_self

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  iff_fg.1 <| isNoetherian_span_of_finite K hA
#align finite_dimensional.span_of_finite FiniteDimensional.span_of_finite

/-- The submodule generated by a single element is finite-dimensional. -/
instance span_singleton (x : V) : FiniteDimensional K (K ∙ x) :=
  span_of_finite K <| Set.finite_singleton _
#align finite_dimensional.span_singleton FiniteDimensional.span_singleton

/-- The submodule generated by a finset is finite-dimensional. -/
instance span_finset (s : Finset V) : FiniteDimensional K (span K (s : Set V)) :=
  span_of_finite K <| s.finite_toSet
#align finite_dimensional.span_finset FiniteDimensional.span_finset

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V →ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
    FiniteDimensional K (p.map f) :=
  Module.Finite.map _ _

variable {K}

theorem _root_.CompleteLattice.Independent.subtype_ne_bot_le_finrank_aux [FiniteDimensional K V]
    {ι : Type w} {p : ι → Submodule K V} (hp : CompleteLattice.Independent p) :
    #{ i // p i ≠ ⊥ } ≤ (finrank K V : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{v} (finrank K V : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank K V) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank K V : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank K V : Cardinal.{w}) := by simp
#align complete_lattice.independent.subtype_ne_bot_le_finrank_aux CompleteLattice.Independent.subtype_ne_bot_le_finrank_aux

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is finite. -/
noncomputable def _root_.CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional
    [FiniteDimensional K V] {ι : Type w} {p : ι → Submodule K V}
    (hp : CompleteLattice.Independent p) : Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine' lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux _
  -- ⊢ ↑(finrank K V) < ℵ₀
  simp [Cardinal.nat_lt_aleph0]
  -- 🎉 no goals
#align complete_lattice.independent.fintype_ne_bot_of_finite_dimensional CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional

/-- If `p` is an independent family of subspaces of a finite-dimensional space `V`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `V`.

Note that the `Fintype` hypothesis required here can be provided by
`CompleteLattice.Independent.fintypeNeBotOfFiniteDimensional`. -/
theorem _root_.CompleteLattice.Independent.subtype_ne_bot_le_finrank [FiniteDimensional K V]
    {ι : Type w} {p : ι → Submodule K V} (hp : CompleteLattice.Independent p)
    [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank K V := by simpa using hp.subtype_ne_bot_le_finrank_aux
                                                      -- 🎉 no goals
#align complete_lattice.independent.subtype_ne_bot_le_finrank CompleteLattice.Independent.subtype_ne_bot_le_finrank

section

open BigOperators

open Finset

/-- If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
theorem exists_nontrivial_relation_of_rank_lt_card [FiniteDimensional K V] {t : Finset V}
    (h : finrank K V < t.card) : ∃ f : V → K, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
  have := mt finset_card_le_finrank_of_linearIndependent (by simpa using h)
  rw [not_linearIndependent_iff] at this
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this
  -- Now we have to extend `g` to all of `t`, then to all of `V`.
  let f : V → K := fun x => if h : x ∈ t then if (⟨x, h⟩ : t) ∈ s then g ⟨x, h⟩ else 0 else 0
  -- and finally clean up the mess caused by the extension.
  refine' ⟨f, _, _⟩
  · dsimp
    rw [← (sum)] -- porting note: need parens to disambiguate
    fapply sum_bij_ne_zero fun v hvt _ => (⟨v, hvt⟩ : { v // v ∈ t })
    · intro v hvt H
      dsimp
      rw [dif_pos hvt] at H
      contrapose! H
      rw [if_neg H, zero_smul]
    · intro _ _ _ _ _ _
      exact Subtype.mk.inj
    · intro b hbs hb
      use b
      simpa only [hbs, exists_prop, dif_pos, Finset.mk_coe, and_true_iff, if_true, Finset.coe_mem,
        eq_self_iff_true, exists_prop_of_true, Ne.def] using hb
    · intro a h₁
      dsimp
      rw [dif_pos h₁]
      intro h₂
      rw [if_pos]
      contrapose! h₂
      rw [if_neg h₂, zero_smul]
  · refine' ⟨z, z.2, _⟩
    dsimp only
    erw [dif_pos z.2, if_pos] <;> rwa [Subtype.coe_eta]
#align finite_dimensional.exists_nontrivial_relation_of_rank_lt_card FiniteDimensional.exists_nontrivial_relation_of_rank_lt_card

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card [FiniteDimensional K V]
    {t : Finset V} (h : finrank K V + 1 < t.card) :
    ∃ f : V → K, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
  -- Pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_trans (Nat.succ_pos _) h
  obtain ⟨x₀, m⟩ := (Finset.card_pos.1 card_pos).bex
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨fun x => x - x₀, sub_left_injective⟩
  let t' := (t.erase x₀).map shift
  have h' : finrank K V < t'.card := by
    simp only [card_map, Finset.card_erase_of_mem m]
    exact Nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_rank_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → K := fun z => if z = x₀ then -∑ z in t.erase x₀, g (z - x₀) else g (z - x₀)
  refine' ⟨f, _, _, _⟩
  -- After this, it's a matter of verifying the properties,
  -- based on the corresponding properties for `g`.
  · show (∑ e : V in t, f e • e) = 0
    -- We prove this by splitting off the `x₀` term of the sum,
    -- which is itself a sum over `t.erase x₀`,
    -- combining the two sums, and
    -- observing that after reindexing we have exactly
    -- ∑ (x : V) in t', g x • x = 0.
    simp only
    conv_lhs =>
      apply_congr
      rfl
      rw [ite_smul]
    rw [Finset.sum_ite]
    conv =>
      congr
      congr
      apply_congr
      -- Porting note: the next two steps used to work by `simp [filter_eq', m]`
      erw [filter_eq']
      simp [m]
    conv =>
      congr
      congr
      rfl
      apply_congr
      simp [filter_ne']
    rw [sum_singleton, neg_smul, add_comm, ← sub_eq_add_neg, sum_smul, ← sum_sub_distrib]
    simp only [← smul_sub]
    -- At the end we have to reindex the sum, so we use `change` to
    -- express the summand using `shift`.
    change (∑ x : V in t.erase x₀, (fun e => g e • e) (shift x)) = 0
    -- porting note: last argument can't be inferred
    rw [← sum_map _ shift (fun e => g e • e)]
    exact gsum
  · show (∑ e : V in t, f e) = 0
    -- Again we split off the `x₀` term,
    -- observing that it exactly cancels the other terms.
    rw [← insert_erase m, sum_insert (not_mem_erase x₀ t)]
    dsimp
    rw [if_pos rfl]
    conv_lhs =>
      congr
      rfl
      apply_congr
      rfl
      rw [if_neg (show _ ≠ x₀ from (mem_erase.mp ‹_›).1)]
    exact neg_add_self _
  · show ∃ (x : V), x ∈ t ∧ f x ≠ 0
    -- We can use x₁ + x₀.
    refine' ⟨x₁ + x₀, _, _⟩
    · rw [Finset.mem_map] at x₁_mem
      rcases x₁_mem with ⟨x₁, x₁_mem, rfl⟩
      rw [mem_erase] at x₁_mem
      simp only [x₁_mem, sub_add_cancel, Function.Embedding.coeFn_mk]
    · dsimp only
      rwa [if_neg, add_sub_cancel]
      rw [add_left_eq_self]
      rintro rfl
      simp only [sub_eq_zero, exists_prop, Finset.mem_map, Embedding.coeFn_mk, eq_self_iff_true,
        mem_erase, not_true, exists_eq_right, Ne.def, false_and_iff] at x₁_mem
#align finite_dimensional.exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card FiniteDimensional.exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card

section

variable {L : Type*} [LinearOrderedField L]

variable {W : Type v} [AddCommGroup W] [Module L W]

/-- A slight strengthening of `exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_rank_succ_lt_card [FiniteDimensional L W]
    {t : Finset W} (h : finrank L W + 1 < t.card) :
    ∃ f : W → L, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card h
  -- ⊢ ∃ f, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x, x ∈ t ∧ 0 < f x
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩
  -- 🎉 no goals
#align finite_dimensional.exists_relation_sum_zero_pos_coefficient_of_rank_succ_lt_card FiniteDimensional.exists_relation_sum_zero_pos_coefficient_of_rank_succ_lt_card

end

end

/-- In a vector space with dimension 1, each set {v} is a basis for `v ≠ 0`. -/
@[simps repr_apply]
noncomputable def basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
    (hv : v ≠ 0) : Basis ι K V :=
  let b := basisUnique ι h
  let h : b.repr v default ≠ 0 := mt basisUnique.repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
                     -- 🎉 no goals
      map_smul' := by simp [mul_div]
                      -- 🎉 no goals
      left_inv := fun w => by
        apply_fun b.repr using b.repr.toEquiv.injective
        -- ⊢ ↑b.repr ((fun f => ↑f default • v) (AddHom.toFun { toAddHom := { toFun := fu …
        apply_fun Equiv.finsuppUnique
        -- ⊢ ↑Equiv.finsuppUnique (↑b.repr ((fun f => ↑f default • v) (AddHom.toFun { toA …
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          RingHom.id_apply, smul_eq_mul, Pi.smul_apply, Equiv.finsuppUnique_apply]
        exact div_mul_cancel _ h
        -- 🎉 no goals
      right_inv := fun f => by
        ext
        -- ⊢ ↑(AddHom.toFun { toAddHom := { toFun := fun w => Finsupp.single default (↑(↑ …
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          RingHom.id_apply, smul_eq_mul, Pi.smul_apply]
        exact mul_div_cancel _ h }
        -- 🎉 no goals
#align finite_dimensional.basis_singleton FiniteDimensional.basisSingleton

@[simp]
theorem basisSingleton_apply (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0)
    (i : ι) : basisSingleton ι h v hv i = v := by
  cases Unique.uniq ‹Unique ι› i
  -- ⊢ ↑(basisSingleton ι h v hv) default = v
  simp [basisSingleton]
  -- 🎉 no goals
#align finite_dimensional.basis_singleton_apply FiniteDimensional.basisSingleton_apply

@[simp]
theorem range_basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
    Set.range (basisSingleton ι h v hv) = {v} := by rw [Set.range_unique, basisSingleton_apply]
                                                    -- 🎉 no goals
#align finite_dimensional.range_basis_singleton FiniteDimensional.range_basisSingleton

end DivisionRing

end FiniteDimensional

section ZeroRank

variable [DivisionRing K] [AddCommGroup V] [Module K V]

open FiniteDimensional

theorem finiteDimensional_of_rank_eq_nat {n : ℕ} (h : Module.rank K V = n) :
    FiniteDimensional K V := by
  rw [FiniteDimensional, ← IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0, h]
  -- ⊢ ↑n < ℵ₀
  exact nat_lt_aleph0 n
  -- 🎉 no goals
#align finite_dimensional_of_rank_eq_nat finiteDimensional_of_rank_eq_nat

-- TODO: generalize to free modules over general rings.
theorem finiteDimensional_of_rank_eq_zero (h : Module.rank K V = 0) : FiniteDimensional K V :=
  finiteDimensional_of_rank_eq_nat <| h.trans Nat.cast_zero.symm
#align finite_dimensional_of_rank_eq_zero finiteDimensional_of_rank_eq_zero

theorem finiteDimensional_of_rank_eq_one (h : Module.rank K V = 1) : FiniteDimensional K V :=
  finiteDimensional_of_rank_eq_nat <| h.trans Nat.cast_one.symm
#align finite_dimensional_of_rank_eq_one finiteDimensional_of_rank_eq_one

theorem finrank_eq_zero_of_rank_eq_zero [FiniteDimensional K V] (h : Module.rank K V = 0) :
    finrank K V = 0 := by
  convert finrank_eq_rank K V
  -- ⊢ finrank K V = 0 ↔ ↑(finrank K V) = Module.rank K V
  rw [h]; norm_cast
  -- ⊢ finrank K V = 0 ↔ ↑(finrank K V) = 0
          -- 🎉 no goals
#align finrank_eq_zero_of_rank_eq_zero finrank_eq_zero_of_rank_eq_zero

variable (K V)

instance finiteDimensional_bot : FiniteDimensional K (⊥ : Submodule K V) :=
  finiteDimensional_of_rank_eq_zero <| by simp
                                          -- 🎉 no goals
#align finite_dimensional_bot finiteDimensional_bot

variable {K V}

theorem bot_eq_top_of_rank_eq_zero (h : Module.rank K V = 0) : (⊥ : Submodule K V) = ⊤ := by
  haveI : FiniteDimensional _ _ := finiteDimensional_of_rank_eq_zero h
  -- ⊢ ⊥ = ⊤
  apply eq_top_of_finrank_eq
  -- ⊢ finrank K { x // x ∈ ⊥ } = finrank K V
  rw [finrank_bot, finrank_eq_zero_of_rank_eq_zero h]
  -- 🎉 no goals
#align bot_eq_top_of_rank_eq_zero bot_eq_top_of_rank_eq_zero

@[simp]
theorem rank_eq_zero {S : Submodule K V} : Module.rank K S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩
                -- 🎉 no goals
#align rank_eq_zero rank_eq_zero

@[simp]
theorem finrank_eq_zero {S : Submodule K V} [FiniteDimensional K S] : finrank K S = 0 ↔ S = ⊥ := by
  rw [← rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Cardinal.natCast_inj]
  -- 🎉 no goals
#align finrank_eq_zero finrank_eq_zero

end ZeroRank

namespace Submodule

open IsNoetherian FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finiteDimensional (s : Submodule K V) : s.FG ↔ FiniteDimensional K s :=
  ⟨fun h => Module.finite_def.2 <| (fg_top s).2 h, fun h => (fg_top s).1 <| Module.finite_def.1 h⟩
#align submodule.fg_iff_finite_dimensional Submodule.fg_iff_finiteDimensional

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
theorem finiteDimensional_of_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ ≤ S₂) :
    FiniteDimensional K S₁ :=
  haveI : IsNoetherian K S₂ := iff_fg.2 inferInstance
  iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2
      (lt_of_le_of_lt (rank_le_of_submodule _ _ h) (FiniteDimensional.rank_lt_aleph0 K S₂)))
#align submodule.finite_dimensional_of_le Submodule.finiteDimensional_of_le

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finiteDimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_left
#align submodule.finite_dimensional_inf_left Submodule.finiteDimensional_inf_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finiteDimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_right
#align submodule.finite_dimensional_inf_right Submodule.finiteDimensional_inf_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finiteDimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁]
    [h₂ : FiniteDimensional K S₂] : FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V) := by
  unfold FiniteDimensional at *
  -- ⊢ Module.Finite K { x // x ∈ S₁ ⊔ S₂ }
  rw [finite_def] at *
  -- ⊢ FG ⊤
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))
  -- 🎉 no goals
#align submodule.finite_dimensional_sup Submodule.finiteDimensional_sup

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Submodule K V) := by
  refine'
    @Finset.sup_induction _ _ _ _ s S (fun i => FiniteDimensional K ↑i) (finiteDimensional_bot K V)
      _ fun i _ => by infer_instance
  · intro S₁ hS₁ S₂ hS₂
    -- ⊢ FiniteDimensional K { x // x ∈ S₁ ⊔ S₂ }
    exact Submodule.finiteDimensional_sup S₁ S₂
    -- 🎉 no goals
#align submodule.finite_dimensional_finset_sup Submodule.finiteDimensional_finset_sup

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
sort is finite-dimensional. -/
instance finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K ↑(⨆ i, S i) := by
  cases nonempty_fintype (PLift ι)
  -- ⊢ FiniteDimensional K { x // x ∈ ⨆ (i : ι), S i }
  rw [← iSup_plift_down, ← Finset.sup_univ_eq_iSup]
  -- ⊢ FiniteDimensional K { x // x ∈ Finset.sup Finset.univ fun i => S i.down }
  exact Submodule.finiteDimensional_finset_sup _ _
  -- 🎉 no goals
#align submodule.finite_dimensional_supr Submodule.finiteDimensional_iSup

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem finrank_quotient_add_finrank [FiniteDimensional K V] (s : Submodule K V) :
    finrank K (V ⧸ s) + finrank K s = finrank K V := by
  have := rank_quotient_add_rank s
  -- ⊢ finrank K (V ⧸ s) + finrank K { x // x ∈ s } = finrank K V
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at this
  -- ⊢ finrank K (V ⧸ s) + finrank K { x // x ∈ s } = finrank K V
  exact_mod_cast this
  -- 🎉 no goals
#align submodule.finrank_quotient_add_finrank Submodule.finrank_quotient_add_finrank

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient
space. -/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s < ⊤) :
    finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank, add_comm]
  -- ⊢ finrank K { x // x ∈ s } < finrank K { x // x ∈ s } + finrank K (V ⧸ s)
  exact Nat.lt_add_of_pos_right (finrank_pos_iff.mpr (Quotient.nontrivial_of_lt_top _ h))
  -- 🎉 no goals
#align submodule.finrank_lt Submodule.finrank_lt

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem finrank_sup_add_finrank_inf_eq (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] :
    finrank K ↑(s ⊔ t) + finrank K ↑(s ⊓ t) = finrank K ↑s + finrank K ↑t := by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat' rw [← finrank_eq_rank] at key
  -- ⊢ finrank K { x // x ∈ s ⊔ t } + finrank K { x // x ∈ s ⊓ t } = finrank K { x  …
  norm_cast at key
  -- 🎉 no goals
#align submodule.finrank_sup_add_finrank_inf_eq Submodule.finrank_sup_add_finrank_inf_eq

theorem finrank_add_le_finrank_add_finrank (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] : finrank K (s ⊔ t : Submodule K V) ≤ finrank K s + finrank K t := by
  rw [← finrank_sup_add_finrank_inf_eq]
  -- ⊢ finrank K { x // x ∈ s ⊔ t } ≤ finrank K { x // x ∈ s ⊔ t } + finrank K { x  …
  exact self_le_add_right _ _
  -- 🎉 no goals
#align submodule.finrank_add_le_finrank_add_finrank Submodule.finrank_add_le_finrank_add_finrank

theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K s + finrank K t = finrank K V) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤ := by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le, le_bot_iff] at hdisjoint
    rw [hdisjoint, finrank_bot]
  apply eq_top_of_finrank_eq
  -- ⊢ finrank K { x // x ∈ s ⊔ t } = finrank K V
  rw [← hdim]
  -- ⊢ finrank K { x // x ∈ s ⊔ t } = finrank K { x // x ∈ s } + finrank K { x // x …
  convert s.finrank_sup_add_finrank_inf_eq t
  -- ⊢ finrank K { x // x ∈ s ⊔ t } = finrank K { x // x ∈ s ⊔ t } + finrank K { x  …
  rw [h_finrank_inf]
  -- ⊢ finrank K { x // x ∈ s ⊔ t } = finrank K { x // x ∈ s ⊔ t } + 0
  rfl
  -- 🎉 no goals
#align submodule.eq_top_of_disjoint Submodule.eq_top_of_disjoint

end DivisionRing

end Submodule

namespace LinearEquiv

open FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finiteDimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.equiv f
#align linear_equiv.finite_dimensional LinearEquiv.finiteDimensional

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R M₂]

end LinearEquiv

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

instance finiteDimensional_finsupp {ι : Type*} [Finite ι] [FiniteDimensional K V] :
    FiniteDimensional K (ι →₀ V) :=
  (Finsupp.linearEquivFunOnFinite K V ι).symm.finiteDimensional
#align finite_dimensional_finsupp finiteDimensional_finsupp

end

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  -- ⊢ S₁ = S₂
  exact le_antisymm hle (Submodule.comap_subtype_eq_top.1
    (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))
#align finite_dimensional.eq_of_le_of_finrank_le FiniteDimensional.eq_of_le_of_finrank_le

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.ge
#align finite_dimensional.eq_of_le_of_finrank_eq FiniteDimensional.eq_of_le_of_finrank_eq

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/-- Given isomorphic subspaces `p q` of vector spaces `V` and `V₁` respectively,
  `p.quotient` is isomorphic to `q.quotient`. -/
noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂}
    (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p), Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₁, Submodule.finrank_quotient_add_finrank,
        LinearEquiv.finrank_eq f₂])
#align finite_dimensional.linear_equiv.quot_equiv_of_equiv FiniteDimensional.LinearEquiv.quotEquivOfEquiv

-- TODO: generalize to the case where one of `p` and `q` is finite-dimensional.
/-- Given the subspaces `p q`, if `p.quotient ≃ₗ[K] q`, then `q.quotient ≃ₗ[K] p` -/
noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) :
    (V ⧸ q) ≃ₗ[K] p :=
  LinearEquiv.ofFinrankEq _ _ <|
    add_right_cancel <| by
      rw [Submodule.finrank_quotient_add_finrank, ← LinearEquiv.finrank_eq f, add_comm,
        Submodule.finrank_quotient_add_finrank]
#align finite_dimensional.linear_equiv.quot_equiv_of_quot_equiv FiniteDimensional.LinearEquiv.quotEquivOfQuotEquiv

end DivisionRing

end FiniteDimensional

namespace LinearMap

open FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- On a finite-dimensional space, an injective linear map is surjective. -/
theorem surjective_of_injective [FiniteDimensional K V] {f : V →ₗ[K] V} (hinj : Injective f) :
    Surjective f := by
  have h := rank_range_of_injective _ hinj
  -- ⊢ Surjective ↑f
  rw [← finrank_eq_rank, ← finrank_eq_rank, natCast_inj] at h
  -- ⊢ Surjective ↑f
  exact range_eq_top.1 (eq_top_of_finrank_eq h)
  -- 🎉 no goals
#align linear_map.surjective_of_injective LinearMap.surjective_of_injective

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
theorem finiteDimensional_of_surjective [FiniteDimensional K V] (f : V →ₗ[K] V₂)
    (hf : LinearMap.range f = ⊤) : FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f <| range_eq_top.1 hf
#align linear_map.finite_dimensional_of_surjective LinearMap.finiteDimensional_of_surjective

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensional_range [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    FiniteDimensional K (LinearMap.range f) :=
  Module.Finite.range f
#align linear_map.finite_dimensional_range LinearMap.finiteDimensional_range

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} :
    Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (leftInverse_of_surjective_of_rightInverse (surjective_of_injective this.injective)
        this).injective⟩
#align linear_map.injective_iff_surjective LinearMap.injective_iff_surjective

theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V →ₗ[K] V} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective]
  -- 🎉 no goals
#align linear_map.ker_eq_bot_iff_range_eq_top LinearMap.ker_eq_bot_iff_range_eq_top

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
theorem mul_eq_one_of_mul_eq_one [FiniteDimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) :
    g * f = 1 := by
  have ginj : Injective g :=
    HasLeftInverse.injective ⟨f, fun x => show (f * g) x = (1 : V →ₗ[K] V) x by rw [hfg]⟩
  let ⟨i, hi⟩ :=
    g.exists_rightInverse_of_surjective (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have : f * (g * i) = f * 1 := congr_arg _ hi
  -- ⊢ g * f = 1
  rw [← mul_assoc, hfg, one_mul, mul_one] at this; rwa [← this]
  -- ⊢ g * f = 1
                                                   -- 🎉 no goals
#align linear_map.mul_eq_one_of_mul_eq_one LinearMap.mul_eq_one_of_mul_eq_one

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem mul_eq_one_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
  ⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩
#align linear_map.mul_eq_one_comm LinearMap.mul_eq_one_comm

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem comp_eq_id_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
  mul_eq_one_comm
#align linear_map.comp_eq_id_comm LinearMap.comp_eq_id_comm

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V := by
  rw [← f.quotKerEquivRange.finrank_eq]
  -- ⊢ finrank K (V ⧸ ker f) + finrank K { x // x ∈ ker f } = finrank K V
  exact Submodule.finrank_quotient_add_finrank _
  -- 🎉 no goals
#align linear_map.finrank_range_add_finrank_ker LinearMap.finrank_range_add_finrank_ker

end DivisionRing

end LinearMap

namespace LinearEquiv

open FiniteDimensional

variable [DivisionRing K] [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

/-- The linear equivalence corresponding to an injective endomorphism. -/
noncomputable def ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩
#align linear_equiv.of_injective_endo LinearEquiv.ofInjectiveEndo

@[simp]
theorem coe_ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) :
    ⇑(ofInjectiveEndo f h_inj) = f :=
  rfl
#align linear_equiv.coe_of_injective_endo LinearEquiv.coe_ofInjectiveEndo

@[simp]
theorem ofInjectiveEndo_right_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    f * (ofInjectiveEndo f h_inj).symm = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).apply_symm_apply
#align linear_equiv.of_injective_endo_right_inv LinearEquiv.ofInjectiveEndo_right_inv

@[simp]
theorem ofInjectiveEndo_left_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    ((ofInjectiveEndo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).symm_apply_apply
#align linear_equiv.of_injective_endo_left_inv LinearEquiv.ofInjectiveEndo_left_inv

end LinearEquiv

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem isUnit_iff_ker_eq_bot [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ (LinearMap.ker f) = ⊥ := by
  constructor
  -- ⊢ IsUnit f → ker f = ⊥
  · rintro ⟨u, rfl⟩
    -- ⊢ ker ↑u = ⊥
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
    -- 🎉 no goals
  · intro h_inj
    -- ⊢ IsUnit f
    rw [ker_eq_bot] at h_inj
    -- ⊢ IsUnit f
    exact ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap,
      LinearEquiv.ofInjectiveEndo_right_inv f h_inj, LinearEquiv.ofInjectiveEndo_left_inv f h_inj⟩,
      rfl⟩
#align linear_map.is_unit_iff_ker_eq_bot LinearMap.isUnit_iff_ker_eq_bot

theorem isUnit_iff_range_eq_top [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ (LinearMap.range f) = ⊤ :=
  by rw [isUnit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top]
     -- 🎉 no goals
#align linear_map.is_unit_iff_range_eq_top LinearMap.isUnit_iff_range_eq_top

end LinearMap

open Module FiniteDimensional

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
  finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)
#align finrank_zero_iff_forall_zero finrank_zero_iff_forall_zero

/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
noncomputable def basisOfFinrankZero [FiniteDimensional K V] {ι : Type*} [IsEmpty ι]
    (hV : finrank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _
#align basis_of_finrank_zero basisOfFinrankZero

end

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  -- ⊢ Injective ↑f ↔ Surjective ↑f
  rw [← ker_eq_bot, ← range_eq_top]; refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ ker f = ⊥ ↔ range f = ⊤
                                     -- ⊢ range f = ⊤
  · rw [h, finrank_bot, add_zero, H] at this
    -- ⊢ range f = ⊤
    exact eq_top_of_finrank_eq this
    -- 🎉 no goals
  · rw [h, finrank_top, H] at this
    -- ⊢ ker f = ⊥
    exact finrank_eq_zero.1 (add_right_injective _ this)
    -- 🎉 no goals
#align linear_map.injective_iff_surjective_of_finrank_eq_finrank LinearMap.injective_iff_surjective_of_finrank_eq_finrank

theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V →ₗ[K] V₂} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective_of_finrank_eq_finrank H]
  -- 🎉 no goals
#align linear_map.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank

/-- Given a linear map `f` between two vector spaces with the same dimension, if
`ker f = ⊥` then `linearEquivOfInjective` is the induced isomorphism
between the two vector spaces. -/
noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂]
    (f : V →ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩
#align linear_map.linear_equiv_of_injective LinearMap.linearEquivOfInjective

@[simp]
theorem linearEquivOfInjective_apply [FiniteDimensional K V] [FiniteDimensional K V₂]
    {f : V →ₗ[K] V₂} (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x : V) :
    f.linearEquivOfInjective hf hdim x = f x :=
  rfl
#align linear_map.linear_equiv_of_injective_apply LinearMap.linearEquivOfInjective_apply

end LinearMap

section

lemma FiniteDimensional.exists_mul_eq_one (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x ≠ 0) : ∃ y, x * y = 1 := by
  have : Function.Surjective (LinearMap.mulLeft F x) :=
    LinearMap.injective_iff_surjective.1 fun y z => ((mul_right_inj' H).1 : x * y = x * z → y = z)
  exact this 1
  -- 🎉 no goals

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def divisionRingOfFiniteDimensional (F K : Type*) [Field F] [h : Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : DivisionRing K :=
  { ‹IsDomain K› with
    toRing := h
    inv := fun x =>
      letI := Classical.decEq K
      if H : x = 0 then 0 else Classical.choose <| FiniteDimensional.exists_mul_eq_one F H
    mul_inv_cancel := fun x hx =>
      show x * dite _ (h := _) _ = _ by
        rw [dif_neg hx]
        -- ⊢ x * Classical.choose (_ : ∃ y, x * y = 1) = 1
        exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
        -- 🎉 no goals
    inv_zero := dif_pos rfl }
#align division_ring_of_finite_dimensional divisionRingOfFiniteDimensional

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def fieldOfFiniteDimensional (F K : Type*) [Field F] [h : CommRing K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K with
    toCommRing := h }
#align field_of_finite_dimensional fieldOfFiniteDimensional
end

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem finrank_mono [FiniteDimensional K V] : Monotone fun s : Submodule K V => finrank K s :=
  fun _ _ => finrank_le_finrank_of_le
#align submodule.finrank_mono Submodule.finrank_mono

theorem finrank_lt_finrank_of_lt {s t : Submodule K V} [FiniteDimensional K t] (hst : s < t) :
    finrank K s < finrank K t :=
  (comapSubtypeEquivOfLe hst.le).finrank_eq.symm.trans_lt <|
    finrank_lt (le_top.lt_of_ne <| hst.not_le ∘ comap_subtype_eq_top.1)
#align submodule.finrank_lt_finrank_of_lt Submodule.finrank_lt_finrank_of_lt

theorem finrank_strictMono [FiniteDimensional K V] :
    StrictMono fun s : Submodule K V => finrank K s := fun _ _ => finrank_lt_finrank_of_lt
#align submodule.finrank_strict_mono Submodule.finrank_strictMono

theorem finrank_add_eq_of_isCompl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
    finrank K U + finrank K W = finrank K V := by
  rw [← finrank_sup_add_finrank_inf_eq, h.codisjoint.eq_top, h.disjoint.eq_bot, finrank_bot,
    add_zero]
  exact finrank_top _ _
  -- 🎉 no goals
#align submodule.finrank_add_eq_of_is_compl Submodule.finrank_add_eq_of_isCompl

end DivisionRing

end Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Span

open Submodule

theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 := by
  apply le_antisymm
  -- ⊢ finrank K { x // x ∈ span K {v} } ≤ 1
  · exact finrank_span_le_card ({v} : Set V)
    -- 🎉 no goals
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    -- ⊢ Nontrivial { x // x ∈ span K {v} }
    use ⟨v, mem_span_singleton_self v⟩, 0
    -- ⊢ { val := v, property := (_ : v ∈ span K {v}) } ≠ 0
    simp [hv]
    -- 🎉 no goals
#align finrank_span_singleton finrank_span_singleton

/-- In a one-dimensional space, any vector is a multiple of any nonzero vector -/
lemma exists_smul_eq_of_finrank_eq_one
    (h : finrank K V = 1) {x : V} (hx : x ≠ 0) (y : V) :
    ∃ (c : K), c • x = y := by
  have : Submodule.span K {x} = ⊤ := by
    have : FiniteDimensional K V := finiteDimensional_of_finrank (zero_lt_one.trans_le h.symm.le)
    apply eq_top_of_finrank_eq
    rw [h]
    exact finrank_span_singleton hx
  have : y ∈ Submodule.span K {x} := by rw [this]; trivial
  -- ⊢ ∃ c, c • x = y
  exact mem_span_singleton.1 this
  -- 🎉 no goals

theorem Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s ⊆ t) :
    s.finrank K ≤ t.finrank K :=
  Submodule.finrank_mono (span_mono h)
#align set.finrank_mono Set.finrank_mono

end Span

section Basis

theorem span_eq_top_of_linearIndependent_of_card_eq_finrank {ι : Type*} [hι : Nonempty ι]
    [Fintype ι] {b : ι → V} (lin_ind : LinearIndependent K b)
    (card_eq : Fintype.card ι = finrank K V) : span K (Set.range b) = ⊤ := by
  by_cases fin : FiniteDimensional K V
  -- ⊢ span K (Set.range b) = ⊤
  · -- Porting note: fails without this line
    -- This will presumably be fixed by the changes discussed at
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.232894/near/342121059
    replace fin : FiniteDimensional _ _ := fin
    -- ⊢ span K (Set.range b) = ⊤
    by_contra ne_top
    -- ⊢ False
    have lt_top : span K (Set.range b) < ⊤ := lt_of_le_of_ne le_top ne_top
    -- ⊢ False
    exact ne_of_lt (Submodule.finrank_lt lt_top)
      (_root_.trans (finrank_span_eq_card lin_ind) card_eq)
  · exfalso
    -- ⊢ False
    apply ne_of_lt (Fintype.card_pos_iff.mpr hι)
    -- ⊢ 0 = Fintype.card ι
    symm
    -- ⊢ Fintype.card ι = 0
    replace fin := (not_iff_not.2 IsNoetherian.iff_fg).2 fin
    -- ⊢ Fintype.card ι = 0
    calc
      Fintype.card ι = finrank K V := card_eq
      _ = 0 := dif_neg (mt IsNoetherian.iff_rank_lt_aleph0.mpr fin)
#align span_eq_top_of_linear_independent_of_card_eq_finrank span_eq_top_of_linearIndependent_of_card_eq_finrank

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    Basis ι K V :=
  Basis.mk lin_ind <| (span_eq_top_of_linearIndependent_of_card_eq_finrank lin_ind card_eq).ge
#align basis_of_linear_independent_of_card_eq_finrank basisOfLinearIndependentOfCardEqFinrank

@[simp]
theorem coe_basisOfLinearIndependentOfCardEqFinrank {ι : Type*} [Nonempty ι] [Fintype ι]
    {b : ι → V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b :=
  Basis.coe_mk _ _
#align coe_basis_of_linear_independent_of_card_eq_finrank coe_basisOfLinearIndependentOfCardEqFinrank

/-- A linear independent finset of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  @basisOfLinearIndependentOfCardEqFinrank _ _ _ _ _ _
    ⟨(⟨hs.choose, hs.choose_spec⟩ : s)⟩ _ _ lin_ind (_root_.trans (Fintype.card_coe _) card_eq)
#align finset_basis_of_linear_independent_of_card_eq_finrank finsetBasisOfLinearIndependentOfCardEqFinrank

@[simp]
theorem coe_finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.card = finrank K V) :
    ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = ((↑) : s → V) := by
  -- porting note: added to make the next line unify the `_`s
  rw [finsetBasisOfLinearIndependentOfCardEqFinrank]
  -- ⊢ ↑(basisOfLinearIndependentOfCardEqFinrank lin_ind (_ : Fintype.card { x // x …
  exact Basis.coe_mk _ _
  -- 🎉 no goals
#align coe_finset_basis_of_linear_independent_of_card_eq_finrank coe_finsetBasisOfLinearIndependentOfCardEqFinrank

/-- A linear independent set of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)
#align set_basis_of_linear_independent_of_card_eq_finrank setBasisOfLinearIndependentOfCardEqFinrank

@[simp]
theorem coe_setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s → V)) (card_eq : s.toFinset.card = finrank K V) :
    ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = ((↑) : s → V) := by
  -- porting note: added to make the next line unify the `_`s
  rw [setBasisOfLinearIndependentOfCardEqFinrank]
  -- ⊢ ↑(basisOfLinearIndependentOfCardEqFinrank lin_ind (_ : Fintype.card ↑s = fin …
  exact Basis.coe_mk _ _
  -- 🎉 no goals
#align coe_set_basis_of_linear_independent_of_card_eq_finrank coe_setBasisOfLinearIndependentOfCardEqFinrank

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

/-- A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) :
    finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ :=
  -- porting note: need explicit universe on PUnit
  ⟨fun h => by simpa using (basisSingleton PUnit.{u+1} h v nz).span_eq, fun s =>
               -- 🎉 no goals
    finrank_eq_card_basis
      (Basis.mk (linearIndependent_singleton nz)
        (by
          convert s.ge  -- porting note: added `.ge` to make things easier for `convert`
          -- ⊢ (Set.range fun x => ↑x) = {v}
          simp))⟩
          -- 🎉 no goals
#align finrank_eq_one_iff_of_nonzero finrank_eq_one_iff_of_nonzero

/-- A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) :
    finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w := by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  -- ⊢ span K {v} = ⊤ ↔ ∀ (w : V), ∃ c, c • v = w
  apply span_singleton_eq_top_iff
  -- 🎉 no goals
#align finrank_eq_one_iff_of_nonzero' finrank_eq_one_iff_of_nonzero'

/-- A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.
-/
theorem finrank_eq_one_iff (ι : Type*) [Unique ι] : finrank K V = 1 ↔ Nonempty (Basis ι K V) := by
  constructor
  -- ⊢ finrank K V = 1 → Nonempty (Basis ι K V)
  · intro h
    -- ⊢ Nonempty (Basis ι K V)
    haveI := finiteDimensional_of_finrank (_root_.zero_lt_one.trans_le h.symm.le)
    -- ⊢ Nonempty (Basis ι K V)
    exact ⟨basisUnique ι h⟩
    -- 🎉 no goals
  · rintro ⟨b⟩
    -- ⊢ finrank K V = 1
    simpa using finrank_eq_card_basis b
    -- 🎉 no goals
#align finrank_eq_one_iff finrank_eq_one_iff

/-- A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff' : finrank K V = 1 ↔ ∃ (v : V) (_n : v ≠ 0),
    ∀ w : V, ∃ c : K, c • v = w := by
  -- porting note: was a messy `convert` proof
  rw [finrank_eq_one_iff PUnit.{u+1}, Basis.basis_singleton_iff PUnit]
  -- 🎉 no goals
#align finrank_eq_one_iff' finrank_eq_one_iff'

-- Not sure why this aren't found automatically.
/-- A finite dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_le_one_iff [FiniteDimensional K V] :
    finrank K V ≤ 1 ↔ ∃ v : V, ∀ w : V, ∃ c : K, c • v = w := by
  constructor
  -- ⊢ finrank K V ≤ 1 → ∃ v, ∀ (w : V), ∃ c, c • v = w
  · intro h
    -- ⊢ ∃ v, ∀ (w : V), ∃ c, c • v = w
    by_cases h' : finrank K V = 0
    -- ⊢ ∃ v, ∀ (w : V), ∃ c, c • v = w
    · use 0
      -- ⊢ ∀ (w : V), ∃ c, c • 0 = w
      intro w
      -- ⊢ ∃ c, c • 0 = w
      use 0
      -- ⊢ 0 • 0 = w
      haveI := finrank_zero_iff.mp h'
      -- ⊢ 0 • 0 = w
      apply Subsingleton.elim
      -- 🎉 no goals
    · replace h' := zero_lt_iff.mpr h'
      -- ⊢ ∃ v, ∀ (w : V), ∃ c, c • v = w
      have : finrank K V = 1 := by linarith
      -- ⊢ ∃ v, ∀ (w : V), ∃ c, c • v = w
      obtain ⟨v, -, p⟩ := finrank_eq_one_iff'.mp this
      -- ⊢ ∃ v, ∀ (w : V), ∃ c, c • v = w
      use v, p
      -- 🎉 no goals
  · rintro ⟨v, p⟩
    -- ⊢ finrank K V ≤ 1
    exact finrank_le_one v p
    -- 🎉 no goals
#align finrank_le_one_iff finrank_le_one_iff

theorem Submodule.finrank_le_one_iff_isPrincipal (W : Submodule K V) [FiniteDimensional K W] :
    finrank K W ≤ 1 ↔ W.IsPrincipal := by
  rw [← W.rank_le_one_iff_isPrincipal, ← finrank_eq_rank, ← Cardinal.natCast_le, Nat.cast_one]
  -- 🎉 no goals
#align submodule.finrank_le_one_iff_is_principal Submodule.finrank_le_one_iff_isPrincipal

theorem Module.finrank_le_one_iff_top_isPrincipal [FiniteDimensional K V] :
    finrank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Module.rank_le_one_iff_top_isPrincipal, ← finrank_eq_rank, ← Cardinal.natCast_le,
    Nat.cast_one]
#align module.finrank_le_one_iff_top_is_principal Module.finrank_le_one_iff_top_isPrincipal

-- We use the `LinearMap.CompatibleSMul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[Field K] [Algebra K A] [IsScalarTower K A V] [IsScalarTower K A W]`
theorem surjective_of_nonzero_of_finrank_eq_one {W A : Type*} [Semiring A] [Module A V]
    [AddCommGroup W] [Module K W] [Module A W] [LinearMap.CompatibleSMul V W K A]
    (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : Surjective f := by
  change Surjective (f.restrictScalars K)
  -- ⊢ Surjective ↑(↑K f)
  obtain ⟨v, n⟩ := FunLike.ne_iff.mp w
  -- ⊢ Surjective ↑(↑K f)
  intro z
  -- ⊢ ∃ a, ↑(↑K f) a = z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  -- ⊢ ∃ a, ↑(↑K f) a = c • ↑f v
  exact ⟨c • v, by simp⟩
  -- 🎉 no goals
#align surjective_of_nonzero_of_finrank_eq_one surjective_of_nonzero_of_finrank_eq_one

/-- Any `K`-algebra module that is 1-dimensional over `K` is simple. -/
theorem is_simple_module_of_finrank_eq_one {A} [Semiring A] [Module A V] [SMul K A]
    [IsScalarTower K A V] (h : finrank K V = 1) : IsSimpleOrder (Submodule A V) := by
  haveI := nontrivial_of_finrank_eq_succ h
  -- ⊢ IsSimpleOrder (Submodule A V)
  refine' ⟨fun S => or_iff_not_imp_left.2 fun hn => _⟩
  -- ⊢ S = ⊤
  rw [← restrictScalars_inj K] at hn ⊢
  -- ⊢ restrictScalars K S = restrictScalars K ⊤
  haveI : FiniteDimensional _ _ := finiteDimensional_of_finrank_eq_succ h
  -- ⊢ restrictScalars K S = restrictScalars K ⊤
  refine' eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm _)
  -- ⊢ finrank K V ≤ finrank K { x // x ∈ restrictScalars K S }
  simpa only [h, finrank_bot] using Submodule.finrank_strictMono (Ne.bot_lt hn)
  -- 🎉 no goals
#align is_simple_module_of_finrank_eq_one is_simple_module_of_finrank_eq_one

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

/-
porting note:
Some of the lemmas in this section can be made faster by adding these short-cut instances
```lean4
instance (S : Subalgebra F E) : AddCommMonoid { x // x ∈ S } := inferInstance
instance (S : Subalgebra F E) : AddCommGroup { x // x ∈ S } := inferInstance
```
However, this approach doesn't scale very well, so we should consider holding off on adding
them until we have no choice.
-/

/-- A `Subalgebra` is `FiniteDimensional` iff it is `FiniteDimensional` as a submodule. -/
theorem Subalgebra.finiteDimensional_toSubmodule {S : Subalgebra F E} :
    FiniteDimensional F (Subalgebra.toSubmodule S) ↔ FiniteDimensional F S :=
  Iff.rfl
#align subalgebra.finite_dimensional_to_submodule Subalgebra.finiteDimensional_toSubmodule

alias ⟨FiniteDimensional.of_subalgebra_toSubmodule, FiniteDimensional.subalgebra_toSubmodule⟩ :=
  Subalgebra.finiteDimensional_toSubmodule
#align finite_dimensional.of_subalgebra_to_submodule FiniteDimensional.of_subalgebra_toSubmodule
#align finite_dimensional.subalgebra_to_submodule FiniteDimensional.subalgebra_toSubmodule

instance FiniteDimensional.finiteDimensional_subalgebra [FiniteDimensional F E]
    (S : Subalgebra F E) : FiniteDimensional F S :=
  FiniteDimensional.of_subalgebra_toSubmodule inferInstance
#align finite_dimensional.finite_dimensional_subalgebra FiniteDimensional.finiteDimensional_subalgebra

instance Subalgebra.finiteDimensional_bot : FiniteDimensional F (⊥ : Subalgebra F E) := by
  nontriviality E
  -- ⊢ FiniteDimensional F { x // x ∈ ⊥ }
  exact finiteDimensional_of_rank_eq_one Subalgebra.rank_bot
  -- 🎉 no goals
#align subalgebra.finite_dimensional_bot Subalgebra.finiteDimensional_bot

theorem Subalgebra.eq_bot_of_rank_le_one {S : Subalgebra F E} (h : Module.rank F S ≤ 1) :
    S = ⊥ := by
  nontriviality E
  -- ⊢ S = ⊥
  obtain ⟨m, _, he⟩ := Cardinal.exists_nat_eq_of_le_nat (h.trans_eq Nat.cast_one.symm)
  -- ⊢ S = ⊥
  -- porting note: fails without explicit type
  haveI : FiniteDimensional F S := finiteDimensional_of_rank_eq_nat he
  -- ⊢ S = ⊥
  rw [← not_bot_lt_iff, ← Subalgebra.toSubmodule.lt_iff_lt]
  -- ⊢ ¬↑toSubmodule ⊥ < ↑toSubmodule S
  -- porting note: fails without explicit type
  haveI : FiniteDimensional F (Subalgebra.toSubmodule S) :=
    S.toSubmoduleEquiv.symm.finiteDimensional
  refine fun hl => (Submodule.finrank_lt_finrank_of_lt hl).not_le (natCast_le.1 ?_)
  -- ⊢ ↑(finrank F { x // x ∈ ↑toSubmodule S }) ≤ ↑(finrank F { x // x ∈ ↑toSubmodu …
  iterate 2 rw [Subalgebra.finrank_toSubmodule, finrank_eq_rank]
  -- ⊢ Module.rank F { x // x ∈ S } ≤ Module.rank F { x // x ∈ ⊥ }
  exact h.trans_eq Subalgebra.rank_bot.symm
  -- 🎉 no goals
#align subalgebra.eq_bot_of_rank_le_one Subalgebra.eq_bot_of_rank_le_one

theorem Subalgebra.eq_bot_of_finrank_one {S : Subalgebra F E} (h : finrank F S = 1) : S = ⊥ :=
  Subalgebra.eq_bot_of_rank_le_one <| by
    -- porting note: fails without explicit type
    haveI : FiniteDimensional F S := finiteDimensional_of_finrank_eq_succ h
    -- ⊢ Module.rank F { x // x ∈ S } ≤ 1
    rw [← finrank_eq_rank, h, Nat.cast_one]
    -- 🎉 no goals
#align subalgebra.eq_bot_of_finrank_one Subalgebra.eq_bot_of_finrank_one

@[simp]
theorem Subalgebra.rank_eq_one_iff [Nontrivial E] {S : Subalgebra F E} :
    Module.rank F S = 1 ↔ S = ⊥ :=
  ⟨fun h => Subalgebra.eq_bot_of_rank_le_one h.le, fun h => h.symm ▸ Subalgebra.rank_bot⟩
#align subalgebra.rank_eq_one_iff Subalgebra.rank_eq_one_iff

@[simp]
theorem Subalgebra.finrank_eq_one_iff [Nontrivial E] {S : Subalgebra F E} :
    finrank F S = 1 ↔ S = ⊥ :=
  ⟨Subalgebra.eq_bot_of_finrank_one, fun h => h.symm ▸ Subalgebra.finrank_bot⟩
#align subalgebra.finrank_eq_one_iff Subalgebra.finrank_eq_one_iff

theorem Subalgebra.bot_eq_top_iff_rank_eq_one [Nontrivial E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ Module.rank F E = 1 := by
  -- porting note: removed `subalgebra_top_rank_eq_submodule_top_rank`
  rw [← rank_top, Subalgebra.rank_eq_one_iff, eq_comm]
  -- 🎉 no goals
#align subalgebra.bot_eq_top_iff_rank_eq_one Subalgebra.bot_eq_top_iff_rank_eq_one

theorem Subalgebra.bot_eq_top_iff_finrank_eq_one [Nontrivial E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1 := by
  rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank,
    Subalgebra.finrank_eq_one_iff, eq_comm]
#align subalgebra.bot_eq_top_iff_finrank_eq_one Subalgebra.bot_eq_top_iff_finrank_eq_one

alias ⟨_, Subalgebra.bot_eq_top_of_rank_eq_one⟩ := Subalgebra.bot_eq_top_iff_rank_eq_one
#align subalgebra.bot_eq_top_of_rank_eq_one Subalgebra.bot_eq_top_of_rank_eq_one

alias ⟨_, Subalgebra.bot_eq_top_of_finrank_eq_one⟩ := Subalgebra.bot_eq_top_iff_finrank_eq_one
#align subalgebra.bot_eq_top_of_finrank_eq_one Subalgebra.bot_eq_top_of_finrank_eq_one

attribute [simp] Subalgebra.bot_eq_top_of_finrank_eq_one Subalgebra.bot_eq_top_of_rank_eq_one

theorem Subalgebra.isSimpleOrder_of_finrank (hr : finrank F E = 2) :
    IsSimpleOrder (Subalgebra F E) :=
  let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm)
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩
                          -- 🎉 no goals
    eq_bot_or_eq_top := by
      intro S
      -- ⊢ S = ⊥ ∨ S = ⊤
      haveI : FiniteDimensional F E := finiteDimensional_of_finrank_eq_succ hr
      -- ⊢ S = ⊥ ∨ S = ⊤
      haveI : FiniteDimensional F S :=
        FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S)
      have : finrank F S ≤ 2 := hr ▸ S.toSubmodule.finrank_le
      -- ⊢ S = ⊥ ∨ S = ⊤
      have : 0 < finrank F S := finrank_pos_iff.mpr inferInstance
      -- ⊢ S = ⊥ ∨ S = ⊤
      interval_cases h : finrank F { x // x ∈ S }
      -- ⊢ S = ⊥ ∨ S = ⊤
      · left
        -- ⊢ S = ⊥
        exact Subalgebra.eq_bot_of_finrank_one h
        -- 🎉 no goals
      · right
        -- ⊢ S = ⊤
        rw [← hr] at h
        -- ⊢ S = ⊤
        rw [← Algebra.toSubmodule_eq_top]
        -- ⊢ ↑toSubmodule S = ⊤
        exact eq_top_of_finrank_eq h }
        -- 🎉 no goals
#align subalgebra.is_simple_order_of_finrank Subalgebra.isSimpleOrder_of_finrank

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : End K V) :
    ∃ k : ℕ, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) := by
  classical
    by_contra h_contra
    simp_rw [not_exists, not_and] at h_contra
    have h_le_ker_pow : ∀ n : ℕ, n ≤ (finrank K V).succ →
        n ≤ finrank K (LinearMap.ker (f ^ n)) := by
      intro n hn
      induction' n with n ih
      · exact zero_le (finrank _ _)
      · have h_ker_lt_ker : LinearMap.ker (f ^ n) < LinearMap.ker (f ^ n.succ) := by
          refine' lt_of_le_of_ne _ (h_contra n (Nat.le_of_succ_le_succ hn))
          rw [pow_succ]
          apply LinearMap.ker_le_ker_comp
        have h_finrank_lt_finrank :
            finrank K (LinearMap.ker (f ^ n)) < finrank K (LinearMap.ker (f ^ n.succ)) := by
          apply Submodule.finrank_lt_finrank_of_lt h_ker_lt_ker
        calc
          n.succ ≤ (finrank K ↑(LinearMap.ker (f ^ n))).succ :=
            Nat.succ_le_succ (ih (Nat.le_of_succ_le hn))
          _ ≤ finrank K ↑(LinearMap.ker (f ^ n.succ)) := Nat.succ_le_of_lt h_finrank_lt_finrank
    have h_any_n_lt : ∀ n, n ≤ (finrank K V).succ → n ≤ finrank K V := fun n hn =>
      (h_le_ker_pow n hn).trans (Submodule.finrank_le _)
    show False
    exact Nat.not_succ_le_self _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl)
#align module.End.exists_ker_pow_eq_ker_pow_succ Module.End.exists_ker_pow_eq_ker_pow_succ

theorem ker_pow_constant {f : End K V} {k : ℕ}
    (h : LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ)) :
    ∀ m, LinearMap.ker (f ^ k) = LinearMap.ker (f ^ (k + m))
  | 0 => by simp
            -- 🎉 no goals
  | m + 1 => by
    apply le_antisymm
    -- ⊢ LinearMap.ker (f ^ k) ≤ LinearMap.ker (f ^ (k + (m + 1)))
    · rw [add_comm, pow_add]
      -- ⊢ LinearMap.ker (f ^ k) ≤ LinearMap.ker (f ^ (m + 1) * f ^ k)
      apply LinearMap.ker_le_ker_comp
      -- 🎉 no goals
    · rw [ker_pow_constant h m, add_comm m 1, ← add_assoc, pow_add, pow_add f k m,
        LinearMap.mul_eq_comp, LinearMap.mul_eq_comp, LinearMap.ker_comp, LinearMap.ker_comp, h,
        Nat.add_one]
#align module.End.ker_pow_constant Module.End.ker_pow_constant

theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m : ℕ}
    (hm : finrank K V ≤ m) : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ finrank K V) := by
  obtain ⟨k, h_k_le, hk⟩ :
    ∃ k, k ≤ finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (k + (m - k))) := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = LinearMap.ker (f ^ k) := by rw [ker_pow_constant hk _]
    _ = LinearMap.ker (f ^ (k + (finrank K V - k))) := (ker_pow_constant hk (finrank K V - k))
    _ = LinearMap.ker (f ^ finrank K V) := by rw [add_tsub_cancel_of_le h_k_le]
#align module.End.ker_pow_eq_ker_pow_finrank_of_le Module.End.ker_pow_eq_ker_pow_finrank_of_le

theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : ℕ) :
    LinearMap.ker (f ^ m) ≤ LinearMap.ker (f ^ finrank K V) := by
  by_cases h_cases : m < finrank K V
  -- ⊢ LinearMap.ker (f ^ m) ≤ LinearMap.ker (f ^ finrank K V)
  · rw [← add_tsub_cancel_of_le (Nat.le_of_lt h_cases), add_comm, pow_add]
    -- ⊢ LinearMap.ker (f ^ m) ≤ LinearMap.ker (f ^ (finrank K V - m) * f ^ m)
    apply LinearMap.ker_le_ker_comp
    -- 🎉 no goals
  · rw [ker_pow_eq_ker_pow_finrank_of_le (le_of_not_lt h_cases)]
    -- 🎉 no goals
#align module.End.ker_pow_le_ker_pow_finrank Module.End.ker_pow_le_ker_pow_finrank

end End

end Module

section Module

open Module

open Cardinal

theorem cardinal_mk_eq_cardinal_mk_field_pow_rank (K V : Type u) [DivisionRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : #V = #K ^ Module.rank K V := by
  let s := Basis.ofVectorSpaceIndex K V
  -- ⊢ #V = #K ^ Module.rank K V
  let hs := Basis.ofVectorSpace K V
  -- ⊢ #V = #K ^ Module.rank K V
  calc
    #V = #(s →₀ K) := Quotient.sound ⟨hs.repr.toEquiv⟩
    _ = #(s → K) := (Quotient.sound ⟨Finsupp.equivFunOnFinite⟩)
    _ = _ := by rw [← Cardinal.lift_inj.1 hs.mk_eq_rank, Cardinal.power_def]
#align cardinal_mk_eq_cardinal_mk_field_pow_rank cardinal_mk_eq_cardinal_mk_field_pow_rank

theorem cardinal_lt_aleph0_of_finiteDimensional (K V : Type u) [DivisionRing K] [AddCommGroup V]
    [Module K V] [Finite K] [FiniteDimensional K V] : #V < ℵ₀ := by
  letI : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  -- ⊢ #V < ℵ₀
  rw [cardinal_mk_eq_cardinal_mk_field_pow_rank K V]
  -- ⊢ #K ^ Module.rank K V < ℵ₀
  exact Cardinal.power_lt_aleph0 (Cardinal.lt_aleph0_of_finite K) (IsNoetherian.rank_lt_aleph0 K V)
  -- 🎉 no goals
#align cardinal_lt_aleph_0_of_finite_dimensional cardinal_lt_aleph0_of_finiteDimensional

end Module
