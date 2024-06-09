/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.InvariantBasisNumber

#align_import linear_algebra.dimension from "leanprover-community/mathlib"@"47a5f8186becdbc826190ced4312f8199f9db6a5"

/-!
# Lemmas about rank and finrank in rings satisfying strong rank condition.

## Main statements

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

-/


noncomputable section

universe u v w w'

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {ι : Type w} {ι' : Type w'}

open Cardinal Basis Submodule Function Set

attribute [local instance] nontrivial_of_invariantBasisNumber

section InvariantBasisNumber

variable [InvariantBasisNumber R]

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι' := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    haveI := basis_finite_of_finite_spans _ (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Cardinal.natCast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    haveI : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂
#align mk_eq_mk_of_basis mk_eq_mk_of_basis

/-- Given two bases indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι'`. -/
def Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some
#align basis.index_equiv Basis.indexEquiv

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #ι = #ι' :=
  Cardinal.lift_inj.1 <| mk_eq_mk_of_basis v v'
#align mk_eq_mk_of_basis' mk_eq_mk_of_basis'

end InvariantBasisNumber

section RankCondition

variable [RankCondition R]

/-- An auxiliary lemma for `Basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : Basis ι R M`,
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w]
    (s : span R w = ⊤) : Fintype.card ι ≤ Fintype.card w := by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.toLinearMap.comp (Finsupp.total w M R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top, Finsupp.range_total]
    simpa using s
#align basis.le_span'' Basis.le_span''

/--
Another auxiliary lemma for `Basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
theorem basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    #ι ≤ Fintype.card w := by
  haveI := nontrivial_of_invariantBasisNumber R
  haveI := basis_finite_of_finite_spans w (toFinite _) s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Cardinal.natCast_le]
  exact Basis.le_span'' b s
#align basis_le_span' basis_le_span'

-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linearIndependent_le_span` below.
/-- If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
theorem Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) : #(range v) ≤ #J := by
  haveI := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    simp
  · let S : J → Set ι := fun j => ↑(v.repr j).support
    let S' : J → Set M := fun j => v '' S j
    have hs : range v ⊆ ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J ≤ comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) ∈ Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self, Finsupp.mem_supported, Finsupp.support_single_ne_zero _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine le_of_not_lt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_lt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa
#align basis.le_span Basis.le_span

end RankCondition

section StrongRankCondition

variable [StrongRankCondition R]

open Submodule

-- An auxiliary lemma for `linearIndependent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
theorem linearIndependent_le_span_aux' {ι : Type*} [Fintype ι] (v : ι → M)
    (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : range v ≤ span R w) :
    Fintype.card ι ≤ Fintype.card w := by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.total
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun Finsupp.total w M R (↑) at h
    simp only [Finsupp.total_total, Submodule.coe_mk, Span.finsupp_total_repr] at h
    rw [← sub_eq_zero, ← LinearMap.map_sub] at h
    exact sub_eq_zero.mp (linearIndependent_iff.mp i _ h)
#align linear_independent_le_span_aux' linearIndependent_le_span_aux'

/-- If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
is itself finite.
-/
lemma LinearIndependent.finite_of_le_span_finite {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Set M) [Finite w] (s : range v ≤ span R w) : Finite ι :=
  letI := Fintype.ofFinite w
  Fintype.finite <| fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s
    simpa using linearIndependent_le_span_aux' v' i' w s'
#align linear_independent_fintype_of_le_span_fintype LinearIndependent.finite_of_le_span_finite

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span' {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : range v ≤ span R w) : #ι ≤ Fintype.card w := by
  haveI : Finite ι := i.finite_of_le_span_finite v w s
  letI := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype]
  simp only [Cardinal.natCast_le]
  exact linearIndependent_le_span_aux' v i w s
#align linear_independent_le_span' linearIndependent_le_span'

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : span R w = ⊤) : #ι ≤ Fintype.card w := by
  apply linearIndependent_le_span' v i w
  rw [s]
  exact le_top
#align linear_independent_le_span linearIndependent_le_span

/-- A version of `linearIndependent_le_span` for `Finset`. -/
theorem linearIndependent_le_span_finset {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι ≤ w.card := by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s
#align linear_independent_le_span_finset linearIndependent_le_span_finset

/-- An auxiliary lemma for `linearIndependent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
theorem linearIndependent_le_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
    (v : κ → M) (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  by_contra h
  rw [not_le, ← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber Φ h (by infer_instance)
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Finite (Φ ⁻¹' {s}) := by
    apply i'.finite_of_le_span_finite v' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Subtype.coe_mk, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false
#align linear_independent_le_infinite_basis linearIndependent_le_infinite_basis

/-- Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
theorem linearIndependent_le_basis {ι : Type w} (b : Basis ι R M) {κ : Type w} (v : κ → M)
    (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    haveI : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i
#align linear_independent_le_basis linearIndependent_le_basis

/-- Let `R` satisfy the strong rank condition. If `m` elements of a free rank `n` `R`-module are
linearly independent, then `m ≤ n`. -/
theorem Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Ring R] [StrongRankCondition R]
    (n : ℕ) {m : ℕ} (v : Fin m → Fin n → R) : LinearIndependent R v → m ≤ n := fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h
#align basis.card_le_card_of_linear_independent_aux Basis.card_le_card_of_linearIndependent_aux

-- When the basis is not infinite this need not be true!
/-- Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
theorem maximal_linearIndependent_eq_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #κ = #ι := by
  apply le_antisymm
  · exact linearIndependent_le_basis b v i
  · haveI : Nontrivial R := nontrivial_of_invariantBasisNumber R
    exact infinite_basis_le_maximal_linearIndependent b v i m
#align maximal_linear_independent_eq_infinite_basis maximal_linearIndependent_eq_infinite_basis

theorem Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.rank R M := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup (Cardinal.bddAbove_range.{v, v} _)
      exact
        ⟨Set.range v, by
          convert v.reindexRange.linearIndependent
          ext
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li
#align basis.mk_eq_rank'' Basis.mk_eq_rank''

theorem Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank R M :=
  v.reindexRange.mk_eq_rank''
#align basis.mk_range_eq_rank Basis.mk_range_eq_rank

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
theorem rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    Module.rank R M = Fintype.card ι := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank, Cardinal.mk_fintype, Set.card_range_of_injective h.injective]
#align rank_eq_card_basis rank_eq_card_basis

theorem Basis.card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M)
    {ι' : Type*} [Fintype ι'] {v : ι' → M} (hv : LinearIndependent R v) :
    Fintype.card ι' ≤ Fintype.card ι := by
  letI := nontrivial_of_invariantBasisNumber R
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank
#align basis.card_le_card_of_linear_independent Basis.card_le_card_of_linearIndependent

theorem Basis.card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent (b'.linearIndependent.map' N.subtype N.ker_subtype)
#align basis.card_le_card_of_submodule Basis.card_le_card_of_submodule

theorem Basis.card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι] (b : Basis ι R O)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map' (Submodule.inclusion hNO) (N.ker_inclusion O _))
#align basis.card_le_card_of_le Basis.card_le_card_of_le

theorem Basis.mk_eq_rank (v : Basis ι R M) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} (Module.rank R M) := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank, Cardinal.mk_range_eq_of_injective v.injective]
#align basis.mk_eq_rank Basis.mk_eq_rank

theorem Basis.mk_eq_rank'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M) :=
  Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank
#align basis.mk_eq_rank' Basis.mk_eq_rank'

theorem rank_span {v : ι → M} (hv : LinearIndependent R v) :
    Module.rank R ↑(span R (range v)) = #(range v) := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj, ← (Basis.span hv).mk_eq_rank,
    Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]
#align rank_span rank_span

theorem rank_span_set {s : Set M} (hs : LinearIndependent R (fun x => x : s → M)) :
    Module.rank R ↑(span R s) = #s := by
  rw [← @setOf_mem_eq _ s, ← Subtype.range_coe_subtype]
  exact rank_span hs
#align rank_span_set rank_span_set

/-- An induction (and recursion) principle for proving results about all submodules of a fixed
finite free module `M`. A property is true for all submodules of `M` if it satisfies the following
"inductive step": the property is true for a submodule `N` if it's true for all submodules `N'`
of `N` with the property that there exists `0 ≠ x ∈ N` such that the sum `N' + Rx` is direct. -/
def Submodule.inductionOnRank [IsDomain R] [Finite ι] (b : Basis ι R M)
    (P : Submodule R M → Sort*) (ih : ∀ N : Submodule R M,
    (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli
#align submodule.induction_on_rank Submodule.inductionOnRank

/-- If `S` a module-finite free `R`-algebra, then the `R`-rank of a nonzero `R`-free
ideal `I` of `S` is the same as the rank of `S`. -/
theorem Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] [IsDomain S]
    [Algebra R S] {n m : Type*} [Fintype n] [Fintype m] (b : Basis n R S) {I : Ideal S}
    (hI : I ≠ ⊥) (c : Basis m R I) : Fintype.card m = Fintype.card n := by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I →ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)
#align ideal.rank_eq Ideal.rank_eq

open FiniteDimensional

theorem finrank_eq_nat_card_basis (h : Basis ι R M) :
    finrank R M = Nat.card ι := by
  rw [Nat.card, ← toNat_lift.{v}, h.mk_eq_rank, toNat_lift, finrank]

namespace FiniteDimensional

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. -/
theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    finrank R M = Fintype.card ι :=
  finrank_eq_of_rank_eq (rank_eq_card_basis h)
#align finite_dimensional.finrank_eq_card_basis FiniteDimensional.finrank_eq_card_basis

/-- If a free module is of finite rank, then the cardinality of any basis is equal to its
`finrank`. -/
theorem _root_.Module.mk_finrank_eq_card_basis [Module.Finite R M]
    {ι : Type w} (h : Basis ι R M) : (finrank R M : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. This lemma uses a `Finset` instead of indexed types. -/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b R M) :
    finrank R M = Finset.card b := by rw [finrank_eq_card_basis h, Fintype.card_coe]
#align finite_dimensional.finrank_eq_card_finset_basis FiniteDimensional.finrank_eq_card_finset_basis

end FiniteDimensional

open FiniteDimensional

variable (R)

@[simp]
theorem rank_self : Module.rank R R = 1 := by
  rw [← Cardinal.lift_inj, ← (Basis.singleton PUnit R).mk_eq_rank, Cardinal.mk_punit]
#align rank_self rank_self

/-- A ring satisfying `StrongRankCondition` (such as a `DivisionRing`) is one-dimensional as a
module over itself. -/
@[simp]
theorem FiniteDimensional.finrank_self : finrank R R = 1 :=
  finrank_eq_of_rank_eq (by simp)
#align finite_dimensional.finrank_self FiniteDimensional.finrank_self

/-- Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
noncomputable def Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have A : Cardinal.mk ι = ↑(FiniteDimensional.finrank R R) :=
    (Module.mk_finrank_eq_card_basis b).symm
  -- Porting note: replace `algebraMap.coe_one` with `Nat.cast_one`
  simp only [Cardinal.eq_one_iff_unique, FiniteDimensional.finrank_self, Nat.cast_one] at A
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 A)
#align basis.unique Basis.unique

variable (M)

/-- The rank of a finite module is finite. -/
theorem rank_lt_aleph0 [Module.Finite R M] : Module.rank R M < ℵ₀ := by
  simp only [Module.rank_def]
  -- Porting note: can't use `‹_›` as that pulls the unused `N` into the context
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹Module.Finite R M›
  refine (ciSup_le' fun i => ?_).trans_lt (nat_lt_aleph0 S.card)
  exact linearIndependent_le_span_finset _ i.prop S hS
#align finite_dimensional.rank_lt_aleph_0 rank_lt_aleph0

@[deprecated (since := "2024-01-01")]
protected alias FiniteDimensional.rank_lt_aleph0 := rank_lt_aleph0

/-- If `M` is finite, `finrank M = rank M`. -/
@[simp]
theorem finrank_eq_rank [Module.Finite R M] :
    ↑(FiniteDimensional.finrank R M) = Module.rank R M := by
  rw [FiniteDimensional.finrank, cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]
#align finite_dimensional.finrank_eq_rank finrank_eq_rank

@[deprecated (since := "2024-01-01")]
protected alias FiniteDimensional.finrank_eq_rank := finrank_eq_rank

variable {R M}
variable {M'} [AddCommGroup M'] [Module R M']

theorem LinearMap.finrank_le_finrank_of_injective [Module.Finite R M'] {f : M →ₗ[R] M'}
    (hf : Function.Injective f) : finrank R M ≤ finrank R M' :=
  finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)
#align linear_map.finrank_le_finrank_of_injective LinearMap.finrank_le_finrank_of_injective

theorem LinearMap.finrank_range_le [Module.Finite R M] (f : M →ₗ[R] M') :
    finrank R (LinearMap.range f) ≤ finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)
#align linear_map.finrank_range_le LinearMap.finrank_range_le

end StrongRankCondition
