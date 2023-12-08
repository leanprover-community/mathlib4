/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Module.Torsion
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

open Cardinal Submodule Module Function FiniteDimensional

attribute [local instance] nontrivial_of_invariantBasisNumber

variable {R : Type u} {V : Type v}

open IsNoetherian

section DivisionRing

variable [AddCommGroup V] {V₂ : Type v'} [AddCommGroup V₂]
variable [Ring R] [StrongRankCondition R] [Module R V]

/-- See `FiniteDimensional.rank_lt_aleph0` for the inverse direction without `Module.Free R V`. -/
lemma Module.rank_lt_alpeh0_iff [Module.Free R V] :
    Module.rank R V < ℵ₀ ↔ Module.Finite R V := by
  rw [Free.rank_eq_card_chooseBasisIndex, mk_lt_aleph0_iff]
  exact ⟨fun h ↦ Finite.of_basis (Free.chooseBasis R V),
    fun I ↦ Finite.of_fintype (Free.ChooseBasisIndex R V)⟩

theorem FiniteDimensional.finrank_of_not_finite [Module.Free R V]
    (h : ¬Module.Finite R V) :
    FiniteDimensional.finrank R V = 0 :=
  dif_neg (rank_lt_alpeh0_iff.not.mpr h)

theorem Module.finite_of_finrank_pos [Module.Free R V] (h : 0 < finrank R V) :
    Module.Finite R V := by
  contrapose h
  simp [finrank_of_not_finite h]

theorem Module.finite_of_finrank_eq_succ [Module.Free R V] {n : ℕ}
    (hn : finrank R V = n.succ) : Module.Finite R V :=
  Module.finite_of_finrank_pos <| by rw [hn]; exact n.succ_pos
#align finite_dimensional.finite_dimensional_of_finrank_eq_succ Module.finite_of_finrank_eq_succ

theorem Module.finite_iff_of_rank_eq_nsmul [Module.Free R V] {W} [AddCommGroup W]
    [Module R W] [Module.Free R W] {n : ℕ} (hn : n ≠ 0)
    (hVW : Module.rank R V = n • Module.rank R W) :
    Module.Finite R V ↔ Module.Finite R W := by
  simp only [← rank_lt_alpeh0_iff, hVW,
    Cardinal.nsmul_lt_aleph0_iff_of_ne_zero hn]

/-- If a free module is of finite rank, then the cardinality of any basis is equal to its
`finrank`. -/
theorem Module.mk_finrank_eq_card_basis [Module.Finite R V] [Module.Free R V]
    {ι : Type w} (h : Basis ι R V) : (finrank R V : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Free.finite_basis h)
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

/-- Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
noncomputable def _root_.Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have A : Cardinal.mk ι = ↑(FiniteDimensional.finrank R R) :=
    (Module.mk_finrank_eq_card_basis b).symm
  -- porting note: replace `algebraMap.coe_one` with `Nat.cast_one`
  simp only [Cardinal.eq_one_iff_unique, FiniteDimensional.finrank_self, Nat.cast_one] at A
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 A)
#align basis.unique Basis.unique

variable (R V)

/-- A finite rank free module has a basis indexed by `Fin (finrank R V)`. -/
noncomputable def Module.Finite.finBasis [Module.Free R V] [Module.Finite R V] :
    Basis (Fin (finrank R V)) R V :=
  (Free.chooseBasis R V).reindex (Fintype.equivFinOfCardEq
    (finrank_eq_card_chooseBasisIndex R V).symm)

/-- A rank `n` free module has a basis indexed by `Fin n`. -/
noncomputable def Module.Finite.finBasisOfFinrankEq [Module.Free R V] [Module.Finite R V] {n : ℕ}
    (hn : finrank R V = n) :
    Basis (Fin n) R V :=
  (finBasis R V).reindex (Fin.castIso hn).toEquiv

variable {R V}

/-- A free module with rank 1 has a basis with one element. -/
noncomputable def Module.Finite.basisUnique [Module.Free R V] (ι : Type*) [Unique ι]
    (h : finrank R V = 1) :
    Basis ι R V :=
  haveI : Module.Finite R V :=
    Module.finite_of_finrank_pos (_root_.zero_lt_one.trans_le h.symm.le)
  (finBasisOfFinrankEq R V h).reindex (Equiv.equivOfUnique _ _)

@[simp]
theorem Module.Finite.basisUnique_repr_eq_zero_iff [Module.Free R V] {ι : Type*} [Unique ι]
    {h : finrank R V = 1} {v : V} {i : ι} :
    (basisUnique ι h).repr v i = 0 ↔ v = 0 :=
  ⟨fun hv =>
    (basisUnique ι h).repr.map_eq_zero_iff.mp (Finsupp.ext fun j => Subsingleton.elim i j ▸ hv),
    fun hv => by rw [hv, LinearEquiv.map_zero, Finsupp.zero_apply]⟩

theorem Module.Finite.cardinal_mk_le_finrank_of_linearIndependent [Module.Finite R V]
    {ι : Type w} {b : ι → V} (h : LinearIndependent R b) : #ι ≤ finrank R V := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using
    cardinal_lift_le_rank_of_linearIndependent h
#align finite_dimensional.cardinal_mk_le_finrank_of_linear_independent Module.Finite.cardinal_mk_le_finrank_of_linearIndependent

theorem Module.Finite.fintype_card_le_finrank_of_linearIndependent [Module.Finite R V]
    {ι : Type*} [Fintype ι] {b : ι → V} (h : LinearIndependent R b) :
    Fintype.card ι ≤ finrank R V := by
  simpa using Module.Finite.cardinal_mk_le_finrank_of_linearIndependent h
#align finite_dimensional.fintype_card_le_finrank_of_linear_independent Module.Finite.fintype_card_le_finrank_of_linearIndependent

theorem Module.Finite.finset_card_le_finrank_of_linearIndependent [Module.Finite R V]
    {b : Finset V} (h : LinearIndependent R (fun x => x : b → V)) :
    b.card ≤ finrank R V := by
  rw [← Fintype.card_coe]
  exact Module.Finite.fintype_card_le_finrank_of_linearIndependent h
#align finite_dimensional.finset_card_le_finrank_of_linear_independent Module.Finite.finset_card_le_finrank_of_linearIndependent

theorem Module.Finite.lt_aleph0_of_linearIndependent {ι : Type w}
    [Module.Finite R V] {v : ι → V} (h : LinearIndependent R v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  apply cardinal_lift_le_rank_of_linearIndependent h
  rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
  apply Cardinal.nat_lt_aleph0

theorem LinearIndependent.finite [Module.Finite R V] {b : Set V}
    (h : LinearIndependent R fun x : b => (x : V)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp (Module.Finite.lt_aleph0_of_linearIndependent h)
#align linear_independent.finite LinearIndependent.finite

theorem Module.Finite.not_linearIndependent_of_infinite
    {ι : Type w} [inf : Infinite ι] [Module.Finite R V]
    (v : ι → V) : ¬LinearIndependent R v := by
  intro h_lin_indep
  have : ¬ℵ₀ ≤ #ι := not_le.mpr (Module.Finite.lt_aleph0_of_linearIndependent h_lin_indep)
  have : ℵ₀ ≤ #ι := infinite_iff.mp inf
  contradiction

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
#align finite_dimensional.span_of_finite Module.Finite.span_of_finite

/-- The submodule generated by a single element is `R`-finite. -/
instance Module.Finite.span_singleton (x : V) : Module.Finite R (R ∙ x) :=
  Module.Finite.span_of_finite R <| Set.finite_singleton _
#align finite_dimensional.span_singleton Module.Finite.span_singleton

/-- The submodule generated by a finset is `R`-finite. -/
instance Module.Finite.span_finset (s : Finset V) : Module.Finite R (span R (s : Set V)) :=
  ⟨(Submodule.fg_top _).mpr ⟨s, rfl⟩⟩
#align finite_dimensional.span_finset Module.Finite.span_finset

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
theorem _root_.CompleteLattice.Independent.subtype_ne_bot_le_finrank
    [Module.Finite R V] [NoZeroSMulDivisors R V]
    {ι : Type w} {p : ι → Submodule R V} (hp : CompleteLattice.Independent p)
    [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank R V := by simpa using hp.subtype_ne_bot_le_finrank_aux
#align complete_lattice.independent.subtype_ne_bot_le_finrank CompleteLattice.Independent.subtype_ne_bot_le_finrank

section

open BigOperators

open Finset

/-- If a finset has cardinality larger than the rank of a module,
then there is a nontrivial linear relation amongst its elements.
-/
theorem Module.exists_nontrivial_relation_of_finrank_lt_card
    [Module.Finite R V] {t : Finset V}
    (h : finrank R V < t.card) : ∃ f : V → R, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
  have := mt Module.Finite.finset_card_le_finrank_of_linearIndependent (by simpa using h)
  rw [not_linearIndependent_iff] at this
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this
  -- Now we have to extend `g` to all of `t`, then to all of `V`.
  let f : V → R := fun x => if h : x ∈ t then if (⟨x, h⟩ : t) ∈ s then g ⟨x, h⟩ else 0 else 0
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
#align finite_dimensional.exists_nontrivial_relation_of_rank_lt_card Module.exists_nontrivial_relation_of_finrank_lt_card

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card [Module.Finite R V]
    {t : Finset V} (h : finrank R V + 1 < t.card) :
    ∃ f : V → R, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
  -- Pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_trans (Nat.succ_pos _) h
  obtain ⟨x₀, m⟩ := (Finset.card_pos.1 card_pos).bex
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨fun x => x - x₀, sub_left_injective⟩
  let t' := (t.erase x₀).map shift
  have h' : finrank R V < t'.card := by
    simp only [card_map, Finset.card_erase_of_mem m]
    exact Nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_finrank_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → R := fun z => if z = x₀ then -∑ z in t.erase x₀, g (z - x₀) else g (z - x₀)
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
#align finite_dimensional.exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card

end

end DivisionRing

section ZeroRank

variable [Ring R] [StrongRankCondition R] [AddCommGroup V] [Module R V]

attribute [local instance] nontrivial_of_invariantBasisNumber

open FiniteDimensional

theorem Module.finite_of_rank_eq_nat [Module.Free R V] {n : ℕ} (h : Module.rank R V = n) :
    Module.Finite R V := by
  have := Cardinal.mk_lt_aleph0_iff.mp
    (((Free.rank_eq_card_chooseBasisIndex R V).symm.trans h).trans_lt (nat_lt_aleph0 n))
  exact Module.Finite.of_basis (Free.chooseBasis R V)
#align finite_dimensional_of_rank_eq_nat Module.finite_of_rank_eq_nat

theorem Module.finite_of_rank_eq_zero [NoZeroSMulDivisors R V]
    (h : Module.rank R V = 0) :
    Module.Finite R V := by
  rw [rank_zero_iff] at h
  infer_instance
#align finite_dimensional_of_rank_eq_zero Module.finite_of_rank_eq_zero

theorem Module.finite_of_rank_eq_one [Module.Free R V] (h : Module.rank R V = 1) :
    Module.Finite R V :=
  Module.finite_of_rank_eq_nat <| h.trans Nat.cast_one.symm
#align finite_dimensional_of_rank_eq_one Module.finite_of_rank_eq_one

theorem FiniteDimensional.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R V = 0) :
    finrank R V = 0 := by
  delta finrank
  rw [h, zero_toNat]
#align finrank_eq_zero_of_rank_eq_zero FiniteDimensional.finrank_eq_zero_of_rank_eq_zero

variable (R V)

instance Module.finite_bot : Module.Finite R (⊥ : Submodule R V) := inferInstance
#align finite_dimensional_bot Module.finite_bot

variable {R V}

theorem Submodule.bot_eq_top_of_rank_eq_zero [NoZeroSMulDivisors R V] (h : Module.rank R V = 0) :
    (⊥ : Submodule R V) = ⊤ := by
  rw [rank_zero_iff] at h
  exact Subsingleton.elim _ _
#align bot_eq_top_of_rank_eq_zero Submodule.bot_eq_top_of_rank_eq_zero

@[simp]
theorem Submodule.rank_eq_zero [NoZeroSMulDivisors R V] {S : Submodule R V} :
    Module.rank R S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩
#align rank_eq_zero Submodule.rank_eq_zero

@[simp]
theorem Submodule.finrank_eq_zero [NoZeroSMulDivisors R V] {S : Submodule R V} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Cardinal.natCast_inj]
#align finrank_eq_zero Submodule.finrank_eq_zero

end ZeroRank

namespace Submodule

open IsNoetherian FiniteDimensional

variable [AddCommGroup V] [Ring R] [StrongRankCondition R] [Module R V]

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

variable [Ring R] [StrongRankCondition R] [AddCommGroup V] [Module R V]

instance Module.Finite.finsupp {ι : Type*} [_root_.Finite ι] [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

end
