/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.InvariantBasisNumber

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

## Additional definition

* `Algebra.IsQuadraticExtension`: An extension of rings `R ⊆ S` is quadratic if `S` is a
  free `R`-algebra of rank `2`.

-/


noncomputable section

universe u v w w'

variable {R : Type u} {S : Type*} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type w} {ι' : Type w'}

open Cardinal Basis Submodule Function Set Module

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
    haveI := basis_finite_of_finite_spans (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Nat.cast_inj]
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

/-- Given two bases indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι'`. -/
def Module.Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #ι = #ι' :=
  Cardinal.lift_inj.1 <| mk_eq_mk_of_basis v v'

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
  · exact b.repr.toLinearMap.comp (Finsupp.linearCombination R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa using s

/--
Another auxiliary lemma for `Basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
theorem basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    #ι ≤ Fintype.card w := by
  haveI := nontrivial_of_invariantBasisNumber R
  haveI := basis_finite_of_finite_spans w.toFinite s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Nat.cast_le]
  exact Basis.le_span'' b s

-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linearIndependent_le_span` below.
/-- If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
theorem Module.Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) :
    #(range v) ≤ #J := by
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
    refine le_of_not_gt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_gt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa

end RankCondition

section StrongRankCondition

variable [StrongRankCondition R]

open Submodule Finsupp

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
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w → M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

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
  simp only [Nat.cast_le]
  exact linearIndependent_le_span_aux' v i w s

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

/-- A version of `linearIndependent_le_span` for `Finset`. -/
theorem linearIndependent_le_span_finset {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι ≤ w.card := by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s

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
    simp only [SetLike.mem_coe, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

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

/-- `StrongRankCondition` implies that if there is an injective linear map `(α →₀ R) →ₗ[R] β →₀ R`,
then the cardinal of `α` is smaller than or equal to the cardinal of `β`.
-/
theorem card_le_of_injective'' {α : Type v} {β : Type v} (f : (α →₀ R) →ₗ[R] β →₀ R)
    (i : Injective f) : #α ≤ #β := by
  let b : Basis β R (β →₀ R) := ⟨1⟩
  apply linearIndependent_le_basis b (fun (i : α) ↦ f (Finsupp.single i 1))
  rw [LinearIndependent]
  have : (linearCombination R fun i ↦ f (Finsupp.single i 1)) = f := by ext a b; simp
  exact this.symm ▸ i

/-- If `R` satisfies the strong rank condition, then for any linearly independent family `v : ι → M`
and spanning set `w : Set M`, the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span'' {ι : Type v} {v : ι → M} (i : LinearIndependent R v) (w : Set M)
    (s : span R w = ⊤) : #ι ≤ #w := by
  fapply card_le_of_injective'' (R := R)
  · apply Finsupp.linearCombination
    exact fun i ↦ Span.repr R w ⟨v i, s ▸ trivial⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w → M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

/-- Let `R` satisfy the strong rank condition. If `m` elements of a free rank `n` `R`-module are
linearly independent, then `m ≤ n`. -/
theorem Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Semiring R] [StrongRankCondition R]
    (n : ℕ) {m : ℕ} (v : Fin m → Fin n → R) : LinearIndependent R v → m ≤ n := fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h

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

theorem Module.Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.rank R M := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup (Cardinal.bddAbove_range _)
      exact
        ⟨Set.range v, by
          rw [LinearIndepOn]
          convert v.reindexRange.linearIndependent
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li

theorem Module.Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank R M :=
  v.reindexRange.mk_eq_rank''

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
theorem rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    Module.rank R M = Fintype.card ι := by
  classical
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank, Cardinal.mk_fintype, Set.card_range_of_injective h.injective]

namespace Module.Basis

theorem card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M)
    {ι' : Type*} [Fintype ι'] {v : ι' → M} (hv : LinearIndependent R v) :
    Fintype.card ι' ≤ Fintype.card ι := by
  letI := nontrivial_of_invariantBasisNumber R
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank

theorem card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn N.subtype N.injective_subtype.injOn)

theorem card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι]
    (b : Basis ι R O) [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn (inclusion hNO) (N.inclusion_injective _).injOn)

theorem mk_eq_rank (v : Basis ι R M) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} (Module.rank R M) := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank, Cardinal.mk_range_eq_of_injective v.injective]

theorem mk_eq_rank'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M) :=
  Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank

end Module.Basis

theorem rank_span {v : ι → M} (hv : LinearIndependent R v) :
    Module.rank R ↑(span R (range v)) = #(range v) := by
  haveI := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj, ← (Basis.span hv).mk_eq_rank,
    Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]

theorem rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : Module.rank R ↑(span R s) = #s := by
  rw [← @setOf_mem_eq _ s, ← Subtype.range_coe_subtype]
  exact rank_span hs

theorem toENat_rank_span_set {v : ι → M} {s : Set ι} (hs : LinearIndepOn R v s) :
    (Module.rank R <| span R <| v '' s).toENat = s.encard := by
  rw [image_eq_range, ← hs.injOn.encard_image, ← toENat_cardinalMk, image_eq_range,
    ← rank_span hs.linearIndependent]

/-- An induction (and recursion) principle for proving results about all submodules of a fixed
finite free module `M`. A property is true for all submodules of `M` if it satisfies the following
"inductive step": the property is true for a submodule `N` if it's true for all submodules `N'`
of `N` with the property that there exists `0 ≠ x ∈ N` such that the sum `N' + Rx` is direct. -/
def Submodule.inductionOnRank {R M} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
    [IsDomain R] [Finite ι] (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli

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

namespace Module

theorem finrank_eq_nat_card_basis (h : Basis ι R M) :
    finrank R M = Nat.card ι := by
  rw [Nat.card, ← toNat_lift.{v}, h.mk_eq_rank, toNat_lift, finrank]

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. -/
theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    finrank R M = Fintype.card ι :=
  finrank_eq_of_rank_eq (rank_eq_card_basis h)

/-- If a free module is of finite rank, then the cardinality of any basis is equal to its
`finrank`. -/
theorem mk_finrank_eq_card_basis [Module.Finite R M] {ι : Type w} (h : Basis ι R M) :
    (finrank R M : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. This lemma uses a `Finset` instead of indexed types. -/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b R M) :
    finrank R M = Finset.card b := by rw [finrank_eq_card_basis h, Fintype.card_coe]

variable (R)

@[simp]
theorem rank_self : Module.rank R R = 1 := by
  rw [← Cardinal.lift_inj, ← (Basis.singleton PUnit R).mk_eq_rank, Cardinal.mk_punit]

/-- A ring satisfying `StrongRankCondition` (such as a `DivisionRing`) is one-dimensional as a
module over itself. -/
@[simp]
theorem finrank_self : finrank R R = 1 :=
  finrank_eq_of_rank_eq (by simp)

/-- Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
noncomputable def _root_.Module.Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have : Cardinal.mk ι = ↑(Module.finrank R R) := (Module.mk_finrank_eq_card_basis b).symm
  have : Subsingleton ι ∧ Nonempty ι := by simpa [Cardinal.eq_one_iff_unique]
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 this)

variable (M)

/-- The rank of a finite module is finite. -/
theorem rank_lt_aleph0 [Module.Finite R M] : Module.rank R M < ℵ₀ := by
  simp only [Module.rank_def]
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹_›
  refine (ciSup_le' fun i => ?_).trans_lt (nat_lt_aleph0 S.card)
  exact linearIndependent_le_span_finset _ i.prop S hS

noncomputable instance {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set M} [Module.Finite R (span R t)]
    (hs : LinearIndepOn R id s) (hst : s ⊆ t) :
    Fintype (hs.extend hst) := by
  refine Classical.choice (Cardinal.lt_aleph0_iff_fintype.1 ?_)
  rw [← rank_span_set (hs.linearIndepOn_extend hst), hs.span_extend_eq_span]
  exact Module.rank_lt_aleph0 ..

/-- If `M` is finite, `finrank M = rank M`. -/
@[simp]
theorem finrank_eq_rank [Module.Finite R M] : ↑(finrank R M) = Module.rank R M := by
  rw [Module.finrank, cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]

/-- If `M` is finite, then `finrank N = rank N` for all `N : Submodule M`. Note that
such an `N` need not be finitely generated. -/
protected theorem _root_.Submodule.finrank_eq_rank [Module.Finite R M] (N : Submodule R M) :
    finrank R N = Module.rank R N := by
  rw [finrank, Cardinal.cast_toNat_of_lt_aleph0]
  exact lt_of_le_of_lt (Submodule.rank_le N) (rank_lt_aleph0 R M)

end Module

variable {M'} [AddCommMonoid M'] [Module R M']

theorem LinearMap.finrank_le_finrank_of_injective [Module.Finite R M'] {f : M →ₗ[R] M'}
    (hf : Function.Injective f) : finrank R M ≤ finrank R M' :=
  finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)

theorem LinearMap.finrank_range_le [Module.Finite R M] (f : M →ₗ[R] M') :
    finrank R (LinearMap.range f) ≤ finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)

theorem LinearMap.finrank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsScalarTower S R M] (L L' : Submodule R M) [Module.Finite R L'] {s : S}
    (hr : IsSMulRegular M s) (h : ∀ x ∈ L, s • x ∈ L') :
    Module.finrank R L ≤ Module.finrank R L' := by
  refine finrank_le_finrank_of_rank_le_rank (lift_le.mpr <| rank_le_of_isSMulRegular L L' hr h) ?_
  rw [← Module.finrank_eq_rank R L']
  exact nat_lt_aleph0 (finrank R ↥L')

variable (R S M) in
/-- Also see `Module.finrank_top_le_finrank_of_isScalarTower_of_free`
for a version with different typeclass constraints. -/
lemma Module.finrank_top_le_finrank_of_isScalarTower [Module.Finite R M] [Semiring S]
    [Module S M] [Module R S] [IsScalarTower R S S] [FaithfulSMul R S] [IsScalarTower R S M] :
    finrank S M ≤ finrank R M := by
  rw [finrank, finrank, Cardinal.toNat_le_iff_le_of_lt_aleph0]
  · exact rank_top_le_rank_of_isScalarTower R S M
  · exact lt_of_le_of_lt (rank_top_le_rank_of_isScalarTower R S M) (Module.rank_lt_aleph0 R M)
  · exact Module.rank_lt_aleph0 _ _

variable (R) in
/-- Also see `Module.finrank_bot_le_finrank_of_isScalarTower_of_free`
for a version with different typeclass constraints. -/
lemma Module.finrank_bot_le_finrank_of_isScalarTower (S T : Type*) [Semiring S] [Semiring T]
    [Module R T] [Module S T] [Module R S] [IsScalarTower R S T]
    [IsScalarTower S T T] [FaithfulSMul S T] [Module.Finite R T] :
    finrank R S ≤ finrank R T :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_bot_le_lift_rank_of_isScalarTower R S T)
    (Module.rank_lt_aleph0 _ _)

@[deprecated (since := "2024-11-21")]
alias LinearMap.finrank_le_of_smul_regular := LinearMap.finrank_le_of_isSMulRegular

end StrongRankCondition

namespace Submodule

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] {s : Set M} {x : M}
  [Module.Finite K (span K s)]

variable (K s) in
/-- This is a version of `exists_linearIndependent`
with an upper estimate on the size of the finite set we choose. -/
theorem exists_finset_span_eq_linearIndepOn :
    ∃ t : Finset M, ↑t ⊆ s ∧ t.card = finrank K (span K s) ∧
      span K t = span K s ∧ LinearIndepOn K id (t : Set M) := by
  rcases exists_linearIndependent K s with ⟨t, ht_sub, ht_span, ht_indep⟩
  obtain ⟨t, rfl, ht_card⟩ : ∃ u : Finset M, ↑u = t ∧ u.card = finrank K (span K s) := by
    rw [← Cardinal.mk_set_eq_nat_iff_finset, finrank_eq_rank, ← ht_span, rank_span_set ht_indep]
  exact ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩

variable (K s) in
theorem exists_fun_fin_finrank_span_eq :
    ∃ f : Fin (finrank K (span K s)) → M, (∀ i, f i ∈ s) ∧ span K (range f) = span K s ∧
      LinearIndependent K f := by
  rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, hts, ht_card, ht_span, ht_indep⟩
  set e := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨(↑) ∘ e, fun i ↦ hts (e i).2, by simpa, ht_indep.comp _ e.injective⟩

/-- This is a version of `mem_span_set` with an estimate on the number of terms in the sum. -/
theorem mem_span_set_iff_exists_finsupp_le_finrank :
    x ∈ span K s ↔ ∃ c : M →₀ K, c.support.card ≤ finrank K (span K s) ∧
      ↑c.support ⊆ s ∧ c.sum (fun mi r ↦ r • mi) = x := by
  constructor
  · intro h
    rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
    rcases mem_span_set.mp (ht_span ▸ h) with ⟨c, hct, hx⟩
    refine ⟨c, ?_, hct.trans ht_sub, hx⟩
    exact ht_card ▸ Finset.card_mono hct
  · rintro ⟨c, -, hcs, hx⟩
    exact mem_span_set.mpr ⟨c, hcs, hx⟩

end Submodule

namespace Algebra

/--
An extension of rings `R ⊆ S` is quadratic if `S` is a free `R`-algebra of rank `2`.
-/
-- TODO. use this in connection with `NumberTheory.Zsqrtd`
class IsQuadraticExtension (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S]
    [Algebra R S] extends Module.Free R S where
  finrank_eq_two' : Module.finrank R S = 2

theorem IsQuadraticExtension.finrank_eq_two (R S : Type*) [CommSemiring R] [StrongRankCondition R]
    [Semiring S] [Algebra R S] [IsQuadraticExtension R S] :
    Module.finrank R S = 2 := finrank_eq_two'

end Algebra
