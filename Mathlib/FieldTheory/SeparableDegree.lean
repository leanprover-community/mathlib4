/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.NormalClosure
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.Polynomial.SeparableDegree
import Mathlib.FieldTheory.IsSepClosed

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Field.Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`
  (mathematically, it should be the algebraic closure of `F`, but in order to make its cardinality
  has the same type with `Module.rank F E`, we use the algebraic closure of `E`).
  Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

  **Remark:** if `E / F` is not algebraic, then this definition makes no mathematical sense,
  and if it is infinite, then it behaves badly. For example,
  $\operatorname{Hom}_{\mathbb{Q}\text{-alg}}(\mathbb{Q}(\mu_{p^\infty}),
  \overline{\mathbb{Q}})\cong\mathbb{Z}_p^\times$ which is uncontable, while
  $[\mathbb{Q}(\mu_{p^\infty}):\mathbb{Q}]$ is countable.

- `Field.finSepDegree F E`: the (finite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the number of `F`-algebra homomorphisms from `E` to the algebraic
  closure of `E`, as a natural number. It is zero if `Field.Emb F E` is not finite.
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

  **Remark:** the (infinite) separable degree for a general algebraic extension `E / F` is defined
  to be the degree of `L / F`, where `L` is the (relative) separable closure of `E / F`, which is
  not defined in this file yet. Later we will show that, if `Field.Emb F E` is finite, then these
  two definitions coincide.

- `Polynomial.natSepDegree`: the separable degree of a polynomial is a natural number,
  defined to be the number of distinct roots of it over its splitting field.

- `Polynomial.rootsExpandEquivRoots`, `Polynomial.rootsExpandPowEquivRoots`: if `f` is a polynomial
  over a perfect ring `R` of characteristic `p`, then there is a bijection from the set of roots of
  `Polynomial.expand R p f` (resp. `Polynomial.expand R (p ^ n) f`) to the set of roots of `f`.
  In fact it's given by `x ↦ x ^ p` (resp. `x ↦ x ^ (p ^ n)`), but we don't give a proof here.

- `Field.separableClosure`: the (relative) separable closure of `E / F`, or called maximal separable
  subextension of `E / F`, is defined to be the intermediate field of `E / F` consisting of all
  separable elements.

## Main results

- `Field.embEquivOfEquiv`, `Field.finSepDegree_eq_of_equiv`:
  a random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
  as `F`-algebras. In particular, they have the same cardinality (so their
  `Field.finSepDegree` are equal).

- `Field.embEquivOfAdjoinSplits`,
  `Field.finSepDegree_eq_of_adjoin_splits`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F`
  and whose minimal polynomial splits in `K`. In particular, they have the same cardinality.

- `Field.embEquivOfIsAlgClosed`,
  `Field.finSepDegree_eq_of_isAlgClosed`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` when `E / F` is algebraic and `K / F` is algebraically closed.
  In particular, they have the same cardinality.

- `Field.embProdEmbOfIsAlgebraic`, `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`:
  if `K / E / F` is a field extension tower, such that `K / E` is algebraic,
  then there is a non-canonical bijection `Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`.
  In particular, the separable degree satisfies the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see also `FiniteDimensional.finrank_mul_finrank'`).

- `Polynomial.natSepDegree_le_natDegree`: the separable degree of a polynomial is smaller than
  its degree.

- `Polynomial.natSepDegree_eq_natDegree_iff`: the separable degree of a non-zero polynomial is
  equal to its degree if and only if it is separable.

- `Polynomial.natSepDegree_eq_of_splits`: if a polynomial splits over `E`, then its separable degree
  is equal to the number of distinct roots of it over `E`.

- `Polynomial.natSepDegree_eq_of_isAlgClosed`,
  `Polynomial.natSepDegree_eq_natSepDegree_algebraicClosure` : the separable degree of a polynomial
  is equal to the number of distinct roots of it over any algebraically closed field (resp. the
  algebraic closure of the base field).

- `Polynomial.natSepDegree_expand_eq_natSepDegree`: if a field `F` is of exponential characteristic
  `q`, then `Polynomial.expand F (q ^ n) f` and `f` have the same separable degree.

- `Polynomial.natSepDegree_eq_hasSeparableContraction_degree`: if a polynomial has separable
  contraction, then its separable degree is equal to its separable contraction degree.

- `Polynomial.natSepDegree_dvd_natDegree_of_irreducible`: the separable degree of an irreducible
  polynomial divides its degree.

- `Field.finSepDegree_adjoin_simple_eq_natSepDegree`: the (finite) separable degree of `F⟮α⟯ / F`
  is equal to the separable degree of the minimal polynomial of `α` over `F`.

- `Field.finSepDegree_adjoin_simple_eq_finrank_iff`: if `α` is algebraic over `F`, then the
  separable degree of `F⟮α⟯ / F` is equal to the degree of `F⟮α⟯ / F` if and only if `α` is a
  separable element.

- `Field.finSepDegree_dvd_finrank`: the separable degree of any field extension `E / F` divides
  the degree of `E / F`.

- `Field.finSepDegree_le_finrank`: the separable degree of a finite extension `E / F` is smaller
  than the degree of `E / F`.

- `Field.finSepDegree_eq_finrank_iff`: if `E / F` is a finite extension, then its separable degree
  is equal to its degree if and only if it is a separable extension.

- `Field.isSeparable_adjoin_simple_iff_separable`: `F⟮x⟯ / F` is a separable extension if and only
  if `x` is a separable element.

- `Field.le_separableClosure_iff`: an intermediate field of `E / F` is contained in the (relative)
  separable closure of `E / F` if and only if it is separable over `F`.

- `Field.separableClosure.normalClosure_eq_self`: the normal closure of the (relative) separable
  closure of `E / F` is equal to itself.

- `Field.isSeparable_adjoin_iff_separable`: `F(S) / F` is a separable extension if and only if
  all elements of `S` are separable elements.

## Tags

separable degree, degree, polynomial, separable closure

## TODO

- Define the inseparable degree $[E:F]_i$ to be $[E:F]$ divided by $[E:F]_s$.

- Prove that the degree of `separableClosure F E` over `F` is $[E:F]_s$ if `E / F` is finite.

- Prove that `separableClosure F (AlgebraicClosure F)` is a separable closure of `F`.

- Prove that `[E:F]_s = 1` if and only if `E / F` is purely inseparable.

- ...

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

namespace Field

/-- `Field.Emb F E` is the type of `F`-algebra homomorphisms from `E` to the algebraic closure
of `E`. -/
def Emb := E →ₐ[F] AlgebraicClosure E

/-- If `E / F` is an algebraic extension, then the (finite) separable degree of `E / F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`,
as a natural number. It is defined to be zero if there are infinitely many of them.
Note that if `E / F` is not algebraic, then this definition makes no mathematical sense. -/
def finSepDegree : ℕ := Cardinal.toNat <| Cardinal.mk (Emb F E)

instance instNonemptyEmb : Nonempty (Emb F E) := ⟨IsScalarTower.toAlgHom F E _⟩

instance instNeZeroFinSepDegree [FiniteDimensional F E] : NeZero (finSepDegree F E) :=
  ⟨Nat.card_ne_zero.2 ⟨inferInstance, Fintype.finite <| minpoly.AlgHom.fintype _ _ _⟩⟩

/-- A random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
as `F`-algebras. -/
def embEquivOfEquiv (i : E ≃ₐ[F] K) :
    Emb F E ≃ Emb F K := AlgEquiv.arrowCongr i <| AlgEquiv.symm <| by
  letI : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  apply AlgEquiv.restrictScalars (R := F) (S := E)
  apply IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)
  intro x
  have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
  rw [show ∀ y : E, (algebraMap E K) y = i.toAlgHom y from fun y ↦ rfl] at h
  simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.apply_symm_apply] using h

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same `Field.finSepDegree`
over `F`. -/
theorem finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finSepDegree F E = finSepDegree F K := by
  have := congr_arg Cardinal.toNat <| (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfEquiv F E K i) |>.trans
      (Equiv.ulift.{v} (α := Emb F K)).symm |>.cardinal_eq
  simpa only [Cardinal.mk_uLift, Cardinal.toNat_lift] using this

@[simp]
theorem finSepDegree_self : finSepDegree F F = 1 := by
  have : Cardinal.mk (Emb F F) = 1 := le_antisymm
    (Cardinal.le_one_iff_subsingleton.2 AlgHom.subsingleton)
    (Cardinal.one_le_iff_ne_zero.2 <| Cardinal.mk_ne_zero _)
  rw [finSepDegree, this, Cardinal.one_toNat]

@[simp]
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finSepDegree_eq_of_equiv _ _ _ (botEquiv F E), finSepDegree_self]

@[simp]
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField F E) = finSepDegree F E :=
  finSepDegree_eq_of_equiv F _ E topEquiv

section

variable [Algebra E K] [IsScalarTower F E K]

@[simp]
theorem finSepDegree_bot' : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E :=
  finSepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
theorem finSepDegree_top' : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K :=
  finSepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

end

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` if `E = F(S)` such that every
element `s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`.
Combined with `Field.instNonemptyEmb`, it can be viewed as a stronger version of
`IntermediateField.nonempty_algHom_of_adjoin_splits`. -/
def embEquivOfAdjoinSplits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    Emb F E ≃ (E →ₐ[F] K) :=
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
    (hS ▸ isAlgebraic_adjoin (S := S) <| fun x hx ↦ (hK x hx).1)
  Classical.choice <| Function.Embedding.antisymm
    (halg.algHomEmbeddingOfSplits (fun _ ↦ splits_of_mem_adjoin F (S := S) hK (hS ▸ mem_top)) _)
    (halg.algHomEmbeddingOfSplits (fun _ ↦ IsAlgClosed.splits_codomain _) _)

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
theorem finSepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  have := congr_arg Cardinal.toNat <| (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfAdjoinSplits F E K hS hK) |>.cardinal_eq
  simpa only [Cardinal.mk_uLift, Cardinal.toNat_lift] using this

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` when `E / F` is algebraic
and `K / F` is algebraically closed. -/
def embEquivOfIsAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) :=
  embEquivOfAdjoinSplits F E K (adjoin_univ F E) <| fun s _ ↦
    ⟨(halg s).isIntegral, IsAlgClosed.splits_codomain _⟩

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
theorem finSepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  have := congr_arg Cardinal.toNat <| (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfIsAlgClosed F E K halg) |>.cardinal_eq
  simpa only [Cardinal.mk_uLift, Cardinal.toNat_lift] using this

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic,
then there is a non-canonical bijection
`Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`. A corollary of `algHomEquivSigma`. -/
def embProdEmbOfIsAlgebraic [Algebra E K] [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    Emb F E × Emb E K ≃ Emb F K :=
  let e : ∀ f : E →ₐ[F] AlgebraicClosure K,
      @AlgHom E K _ _ _ _ _ f.toRingHom.toAlgebra ≃ Emb E K := fun f ↦
    (@embEquivOfIsAlgClosed E K _ _ _ _ _ f.toRingHom.toAlgebra halg).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
    (Equiv.sigmaEquivProdOfEquiv e) |>.trans <| Equiv.prodCongrLeft <|
      fun _ : Emb E K ↦ AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _) <|
        (IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)
          halg).restrictScalars F).symm

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then their
(finite) separable degree satisfies the tower law
$[E:F]_s [K:E]_s = [K:F]_s$. See also `FiniteDimensional.finrank_mul_finrank'`. -/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  have := congr_arg Cardinal.toNat <| (embProdEmbOfIsAlgebraic F E K halg).trans
    (Equiv.ulift.{v} (α := Emb F K)).symm |>.cardinal_eq
  simpa only [Cardinal.mk_prod, Cardinal.toNat_mul, Cardinal.toNat_lift,
    Cardinal.mk_uLift] using this

end Field

namespace Polynomial

/-- TODO: remove once #8563 is merged -/
axiom one_lt_rootMultiplicity_iff_isRoot_gcd
    {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid R[X]] {p : R[X]} {t : R} (h : p ≠ 0) :
    1 < p.rootMultiplicity t ↔ (gcd p (derivative p)).IsRoot t

variable {F E}

variable (f : F[X])

/-- If a polynomial has all roots over a field, then it has no repeated roots on that field
if and only if it is separable. -/
theorem nodup_roots_iff_of_splits (hf : f ≠ 0) (h : f.Splits (RingHom.id F)) :
    f.roots.Nodup ↔ f.Separable := by
  refine ⟨not_imp_not.1 fun hnsep ↦ ?_, nodup_roots⟩
  set g := gcd f (derivative f)
  have hg : g ≠ 0 := gcd_ne_zero_of_left hf
  by_cases hdeg : g.degree = 0
  · simp only [Separable, ← gcd_isUnit_iff, isUnit_iff] at hnsep
    rw [eq_C_of_degree_eq_zero hdeg] at hg
    exact False.elim <| hnsep ⟨coeff g 0, isUnit_iff_ne_zero.2 (ne_zero_of_map hg),
      (eq_C_of_degree_eq_zero hdeg).symm⟩
  obtain ⟨x, hx⟩ := exists_root_of_splits _
    (splits_of_splits_of_dvd _ hf h (show g ∣ f from gcd_dvd_left f _)) hdeg
  rw [Multiset.nodup_iff_count_le_one, not_forall]
  exact ⟨x, by rw [count_roots]; exact Nat.not_le.mpr <|
    (one_lt_rootMultiplicity_iff_isRoot_gcd hf).2 hx⟩

/-- The separable degree `Polynomial.natSepDegree` of a polynomial is a natural number,
defined to be the number of distinct roots of it over its splitting field. -/
def natSepDegree : ℕ := (f.aroots f.SplittingField).toFinset.card

/-- The separable degree of a polynomial is smaller than its degree. -/
theorem natSepDegree_le_natDegree : f.natSepDegree ≤ f.natDegree := by
  have := f.map (algebraMap F f.SplittingField) |>.card_roots'
  rw [← aroots_def, natDegree_map] at this
  exact (f.aroots f.SplittingField).toFinset_card_le.trans this

@[simp]
theorem natSepDegree_X_sub_C {x : F} : (X - C x).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X_sub_C, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]
theorem natSepDegree_X : (X : F[X]).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]
theorem natSepDegree_C {x : F} : (C x).natSepDegree = 0 := by
  simp only [natSepDegree, aroots_C, Multiset.toFinset_zero, Finset.card_empty]

@[simp]
theorem natSepDegree_zero : (0 : F[X]).natSepDegree = 0 := by
  simp only [natSepDegree, aroots_zero, Multiset.toFinset_zero, Finset.card_empty]

@[simp]
theorem natSepDegree_one : (1 : F[X]).natSepDegree = 0 := by
  simp only [natSepDegree, aroots_one, Multiset.toFinset_zero, Finset.card_empty]

/-- A constant polynomial has zero separable degree. -/
theorem natSepDegree_eq_zero (h : f.natDegree = 0) : f.natSepDegree = 0 := by
  linarith only [natSepDegree_le_natDegree f, h]

/-- A non-constant polynomial has non-zero separable degree. -/
theorem natSepDegree_ne_zero (h : f.natDegree ≠ 0) : f.natSepDegree ≠ 0 := by
  rw [natSepDegree, ne_eq, Finset.card_eq_zero, ← ne_eq, ← Finset.nonempty_iff_ne_empty]
  use rootOfSplits _ (SplittingField.splits f) (ne_of_apply_ne _ h)
  rw [Multiset.mem_toFinset, mem_aroots]
  exact ⟨ne_of_apply_ne _ h, map_rootOfSplits _ (SplittingField.splits f) (ne_of_apply_ne _ h)⟩

/-- A polynomial has zero separable degree if and only if it is constant. -/
theorem natSepDegree_eq_zero_iff : f.natSepDegree = 0 ↔ f.natDegree = 0 :=
  ⟨by simpa only [ne_eq, not_not] using mt (natSepDegree_ne_zero f), natSepDegree_eq_zero f⟩

/-- A polynomial has non-zero separable degree if and only if it is non-constant. -/
theorem natSepDegree_ne_zero_iff : f.natSepDegree ≠ 0 ↔ f.natDegree ≠ 0 :=
  Iff.not <| natSepDegree_eq_zero_iff f

/-- The separable degree of a non-zero polynomial is equal to its degree if and only if
it is separable. -/
theorem natSepDegree_eq_natDegree_iff (hf : f ≠ 0) :
    f.natSepDegree = f.natDegree ↔ f.Separable := by
  simp only [natSepDegree]
  rw [natDegree_eq_card_roots (SplittingField.splits f), aroots_def,
    Multiset.toFinset_card_eq_card_iff_nodup,
    ← Polynomial.separable_map (algebraMap F f.SplittingField)]
  refine nodup_roots_iff_of_splits _ (map_ne_zero hf) ?_
  rw [splits_map_iff, RingHom.id_comp]
  exact SplittingField.splits f

/-- If a polynomial is separable, then its separable degree is equal to its degree. -/
theorem natSepDegree_eq_natDegree_of_separable (h : f.Separable) :
    f.natSepDegree = f.natDegree :=
  (natSepDegree_eq_natDegree_iff f (fun h' ↦ not_separable_zero (h' ▸ h))).2 h

/-- If a polynomial splits over `E`, then its separable degree is equal to
the number of distinct roots of it over `E`. -/
theorem natSepDegree_eq_of_splits (h : f.Splits (algebraMap F E)) :
    f.natSepDegree = (f.aroots E).toFinset.card := by
  let i := SplittingField.lift f h
  have heq := (f.map (algebraMap F f.SplittingField)).map_roots_le_of_injective i.injective
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_map, AlgHom.comp_algebraMap_of_tower] at heq
  replace heq := congr_arg Finset.card <| congr_arg Multiset.toFinset <|
    Multiset.eq_of_le_of_card_le heq <| by rw [Multiset.card_map, ← natDegree_eq_card_roots h,
      ← natDegree_eq_card_roots <| SplittingField.splits f]
  have := Finset.card_image_of_injective
    (f.map (algebraMap F f.SplittingField)).roots.toFinset i.injective
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [Multiset.toFinset_map, this] at heq
  convert heq

/-- The separable degree of a polynomial is equal to
the number of distinct roots of it over any algebraically closed field. -/
theorem natSepDegree_eq_of_isAlgClosed [IsAlgClosed E] :
    f.natSepDegree = (f.aroots E).toFinset.card :=
  natSepDegree_eq_of_splits f (IsAlgClosed.splits_codomain f)

/-- The separable degree of a polynomial over `F` is equal to
the number of distinct roots of it over the algebraic closure of `F`. -/
theorem natSepDegree_eq_natSepDegree_algebraicClosure :
    f.natSepDegree = (f.aroots (AlgebraicClosure F)).toFinset.card :=
  natSepDegree_eq_of_isAlgClosed f

@[simp]
theorem natSepDegree_C_mul {x : F} (hx : x ≠ 0) :
    (C x * f).natSepDegree = f.natSepDegree := by
  simp only [natSepDegree_eq_natSepDegree_algebraicClosure, aroots_C_mul _ hx]

@[simp]
theorem natSepDegree_smul_nonzero {x : F} (hx : x ≠ 0) :
    (x • f).natSepDegree = f.natSepDegree := by
  simp only [natSepDegree_eq_natSepDegree_algebraicClosure, aroots_smul_nonzero _ hx]

@[simp]
theorem natSepDegree_pow {n : ℕ} : (f ^ n).natSepDegree = if n = 0 then 0 else f.natSepDegree := by
  simp only [natSepDegree_eq_natSepDegree_algebraicClosure, aroots_pow]
  by_cases h : n = 0
  · simp only [h, zero_smul, Multiset.toFinset_zero, Finset.card_empty, ite_true]
  simp only [h, Multiset.toFinset_nsmul _ n h, ite_false]

theorem natSepDegree_X_pow {n : ℕ} : ((X : F[X]) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_pow, natSepDegree_X]

theorem natSepDegree_X_sub_C_pow {x : F} {n : ℕ} :
    ((X - C x) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_pow, natSepDegree_X_sub_C]

theorem natSepDegree_C_mul_X_sub_C_pow {x y : F} {n : ℕ} (hx : x ≠ 0) :
    (C x * (X - C y) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_C_mul _ hx, natSepDegree_X_sub_C_pow]

theorem natSepDegree_mul (g : F[X]) :
    (f * g).natSepDegree ≤ f.natSepDegree + g.natSepDegree := by
  by_cases h : f * g = 0
  · simp only [h, natSepDegree_zero, zero_le]
  simp only [natSepDegree_eq_natSepDegree_algebraicClosure, aroots_mul h, Multiset.toFinset_add]
  exact Finset.card_union_le _ _

theorem natSepDegree_le_of_dvd (g : F[X]) (h1 : f ∣ g) (h2 : g ≠ 0) :
    f.natSepDegree ≤ g.natSepDegree := by
  simp only [natSepDegree_eq_natSepDegree_algebraicClosure, aroots]
  set f' := f.map (algebraMap F (AlgebraicClosure F))
  set g' := g.map (algebraMap F (AlgebraicClosure F))
  have : f'.roots.dedup ≤ g'.roots.dedup :=
    (Multiset.Nodup.le_dedup_iff_le <| Multiset.nodup_dedup _).2 <| (Multiset.dedup_le _).trans <|
      roots.le_of_dvd (map_ne_zero h2) <| map_dvd _ h1
  exact Multiset.card_le_of_le this

/-- If `f` is a polynomial over a perfect ring `R` of characteristic `p`, then there is a bijection
from the set of roots of `Polynomial.expand R p f` to the set of roots of `f`.
In fact it's given by `x ↦ x ^ p`, but we don't give a proof here. -/
def rootsExpandEquivRoots
    (R : Type u) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p] {f : R[X]} :
    (expand R p f).roots.toFinset ≃ f.roots.toFinset := by
  rw [polynomial_expand_eq, roots_pow, Multiset.toFinset_nsmul _ p (NeZero.ne p)]
  let g := f.map (frobeniusEquiv R p).symm.toRingHom
  let toFun : g.roots.toFinset → f.roots.toFinset := fun ⟨x, h⟩ ↦ ⟨frobeniusEquiv R p x, by
    simp only [RingEquiv.toRingHom_eq_coe, Multiset.mem_toFinset, mem_roots',
      ne_eq, IsRoot.def] at h ⊢
    use fun hf ↦ by simp [hf, Polynomial.map_zero, not_true, false_and] at h
    replace h := congr_arg (frobeniusEquiv R p) h.2
    have := eval₂_hom (p := g) (frobeniusEquiv R p).toRingHom x
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    simpa only [← this, eval₂_map, RingEquiv.comp_symm, map_zero] using h⟩
  let invFun : f.roots.toFinset → g.roots.toFinset := fun ⟨x, h⟩ ↦ ⟨(frobeniusEquiv R p).symm x, by
    simp only [RingEquiv.toRingHom_eq_coe, Multiset.mem_toFinset, mem_roots',
      ne_eq, IsRoot.def] at h ⊢
    use (Polynomial.map_ne_zero_iff <| EquivLike.injective _).2 h.1
    replace h := congr_arg (frobeniusEquiv R p).symm h.2
    have := eval₂_hom (p := f) (frobeniusEquiv R p).symm.toRingHom x
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    simpa only [← this, eval_map, map_zero] using h⟩
  refine ⟨toFun, invFun, fun ⟨x, h⟩ ↦ ?_, fun ⟨x, h⟩ ↦ ?_⟩
  · simp only [RingEquiv.toRingHom_eq_coe, frobeniusEquiv_apply,
      frobeniusEquiv_symm_apply_frobenius]
  · simp only [RingEquiv.toRingHom_eq_coe, frobeniusEquiv_apply,
      frobenius_apply_frobeniusEquiv_symm]

/-- If `f` is a polynomial over a perfect ring `R` of characteristic `p`, then there is a bijection
from the set of roots of `Polynomial.expand R (p ^ n) f` to the set of roots of `f`.
In fact it's given by `x ↦ x ^ (p ^ n)`, but we don't give a proof here. -/
def rootsExpandPowEquivRoots
    (R : Type u) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] [CharP R p] [PerfectRing R p] {f : R[X]} {n : ℕ} :
    (expand R (p ^ n) f).roots.toFinset ≃ f.roots.toFinset := by
  induction' n with n ih
  · rw [pow_zero, expand_one]
  · rw [pow_succ, ← expand_expand]
    exact (rootsExpandEquivRoots R p).trans <| ih

/-- If a field `F` is of exponential characteristic `q`, then `Polynomial.expand F (q ^ n) f`
and `f` have the same separable degree. -/
theorem natSepDegree_expand_eq_natSepDegree (q : ℕ) [hF : ExpChar F q] {n : ℕ} :
    (expand F (q ^ n) f).natSepDegree = f.natSepDegree := by
  cases' hF with _ _ hprime _
  · simp only [one_pow, expand_one]
  haveI := Fact.mk hprime
  simpa only [natSepDegree_eq_natSepDegree_algebraicClosure, aroots_def, map_expand,
    Fintype.card_coe] using Fintype.card_eq.2 ⟨rootsExpandPowEquivRoots q
      (f := f.map (algebraMap F (AlgebraicClosure F))) (n := n)⟩

/-- If a polynomial has separable contraction, then its separable degree is equal to its
separable contraction degree. -/
theorem natSepDegree_eq_hasSeparableContraction_degree
    (q : ℕ) [ExpChar F q] (hf : f.HasSeparableContraction q) :
    f.natSepDegree = hf.degree := by
  have hf' := hf
  obtain ⟨g, h1⟩ := hf'
  rw [← IsSeparableContraction.degree_eq q hf g h1]
  obtain ⟨h1, m, h2⟩ := h1
  rw [← h2, natSepDegree_expand_eq_natSepDegree]
  exact natSepDegree_eq_natDegree_of_separable g h1

/-- The separable degree of an irreducible polynomial divides its degree. -/
theorem natSepDegree_dvd_natDegree_of_irreducible (h : Irreducible f) :
    f.natSepDegree ∣ f.natDegree := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hf := Irreducible.hasSeparableContraction q f h
  rw [natSepDegree_eq_hasSeparableContraction_degree f q hf]
  exact HasSeparableContraction.dvd_degree hf

/-- A monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one if and only if it is of form `Polynomial.expand F (q ^ n) (X - C y)`
for some `n ∈ ℕ` and `y ∈ F`. -/
theorem natSepDegree_eq_one_iff_of_monic_irreducible' (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔ ∃ (n : ℕ) (y : F),
      f = expand F (q ^ n) (X - C y) := by
  have hq : 0 < q := by
    rcases expChar_is_prime_or_one F q with h | rfl
    exacts [Nat.Prime.pos h, Nat.one_pos]
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := Irreducible.hasSeparableContraction q _ hi
    have h3 : g.natDegree = 1 := by
      rwa [← h2, natSepDegree_expand_eq_natSepDegree _ q,
        natSepDegree_eq_natDegree_of_separable g h1] at h
    replace h3 : g.degree = 1 := (degree_eq_iff_natDegree_eq_of_pos Nat.one_pos).2 h3
    have hg := eq_X_add_C_of_degree_eq_one h3
    -- TODO: should extract this as a converse to `Polynomial.Monic.expand`
    have : g.leadingCoeff = 1 := by
      have hq' : 0 < q ^ n := Nat.pos_pow_of_pos n hq
      rw [Monic, leadingCoeff, ← h2, natDegree_expand, coeff_expand hq'] at hm
      simpa only [dvd_mul_left, ite_true, Nat.mul_div_cancel _ hq'] using hm
    rw [this, map_one, one_mul] at hg
    exact ⟨n, -(g.coeff 0), by rw [map_neg, sub_neg_eq_add, ← hg, h2]⟩
  rw [h, natSepDegree_expand_eq_natSepDegree _ q, natSepDegree_X_sub_C]

/-- A monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one if and only if it is of form `X ^ (q ^ n) - C y`
for some `n ∈ ℕ` and `y ∈ F`. -/
theorem natSepDegree_eq_one_iff_of_monic_irreducible (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔ ∃ (n : ℕ) (y : F), f = X ^ (q ^ n) - C y := by
  simp only [natSepDegree_eq_one_iff_of_monic_irreducible' f q hm hi, map_sub, expand_X, expand_C]

end Polynomial

namespace Field

/-- The (finite) separable degree of `F⟮α⟯ / F` is equal to the separable degree of the
minimal polynomial of `α` over `F`. -/
theorem finSepDegree_adjoin_simple_eq_natSepDegree (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = (minpoly F α).natSepDegree := by
  have : finSepDegree F F⟮α⟯ = _ := congr_arg Cardinal.toNat <|
    (algHomAdjoinIntegralEquiv F (K := AlgebraicClosure F⟮α⟯) halg.isIntegral).cardinal_eq
  rw [this, natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯),
    Cardinal.mk_fintype, Cardinal.toNat_cast]
  exact Eq.trans (by simp only [Multiset.mem_toFinset]) (Fintype.card_coe _)

-- The separable degree of `F⟮α⟯ / F` divides the degree of `F⟮α⟯ / F`.
-- Marked as `private` because it is an unconditional special case of `finSepDegree_dvd_finrank`.
private theorem finSepDegree_adjoin_simple_dvd_finrank (α : E) :
    finSepDegree F F⟮α⟯ ∣ finrank F F⟮α⟯ := by
  by_cases halg : IsAlgebraic F α
  · rw [finSepDegree_adjoin_simple_eq_natSepDegree F E α halg, adjoin.finrank halg.isIntegral]
    exact natSepDegree_dvd_natDegree_of_irreducible _ (minpoly.irreducible halg.isIntegral)
  have : finrank F F⟮α⟯ = 0 := finrank_of_infinite_dimensional <| fun _ ↦
    halg ((AdjoinSimple.isIntegral_gen F α).1 (IsIntegral.of_finite F _)).isAlgebraic
  rw [this]
  exact dvd_zero _

/-- The separable degree of `F⟮α⟯ / F` is smaller than the degree of `F⟮α⟯ / F` if `α` is
algebraic over `F`. -/
theorem finSepDegree_adjoin_simple_le_finrank (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ ≤ finrank F F⟮α⟯ := by
  haveI := adjoin.finiteDimensional halg.isIntegral
  exact Nat.le_of_dvd finrank_pos <| finSepDegree_adjoin_simple_dvd_finrank F E α

/-- If `α` is algebraic over `F`, then the separable degree of `F⟮α⟯ / F` is equal to the degree
of `F⟮α⟯ / F` if and only if `α` is a separable element. -/
theorem finSepDegree_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = finrank F F⟮α⟯ ↔ (minpoly F α).Separable := by
  rw [finSepDegree_adjoin_simple_eq_natSepDegree F E α halg, adjoin.finrank halg.isIntegral,
    natSepDegree_eq_natDegree_iff _ (minpoly.ne_zero halg.isIntegral)]

/-- The separable degree of any field extension `E / F` divides the degree of `E / F`. -/
theorem finSepDegree_dvd_finrank : finSepDegree F E ∣ finrank F E := by
  by_cases hfd : FiniteDimensional F E
  · let P : IntermediateField F E → Prop := fun K ↦ finSepDegree F K ∣ finrank F K
    rw [← finSepDegree_top, ← finrank_top F E]
    refine induction_on_adjoin P ?_ (fun L x h ↦ ?_) ⊤
    · simp only [finSepDegree_bot, IntermediateField.finrank_bot, one_dvd]
    simp only at h ⊢
    have hdvd := mul_dvd_mul h <| finSepDegree_adjoin_simple_dvd_finrank L E x
    set M := L⟮x⟯; clear_value M
    letI : Algebra L M := Subalgebra.algebra M.toSubalgebra
    letI : Module L M := Algebra.toModule
    letI : SMul L M := Algebra.toSMul
    haveI : IsScalarTower F L M := IntermediateField.isScalarTower M
    rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M (Algebra.IsAlgebraic.of_finite L M),
      FiniteDimensional.finrank_mul_finrank F L M] at hdvd
  rw [finrank_of_infinite_dimensional hfd]
  exact dvd_zero _

/-- The separable degree of a finite extension `E / F` is smaller than the degree of `E / F`. -/
theorem finSepDegree_le_finrank [FiniteDimensional F E] :
    finSepDegree F E ≤ finrank F E := Nat.le_of_dvd finrank_pos <| finSepDegree_dvd_finrank F E

/-- If `E / F` is a finite separable extension, then its separable degree is equal to its degree. -/
theorem finSepDegree_eq_finrank_of_isSeparable [FiniteDimensional F E] [IsSeparable F E] :
    finSepDegree F E = finrank F E := by
  let P : IntermediateField F E → Prop := fun K ↦ finSepDegree F K = finrank F K
  rw [← finSepDegree_top, ← finrank_top F E]
  refine induction_on_adjoin P ?_ (fun L x h ↦ ?_) ⊤
  · simp only [finSepDegree_bot, IntermediateField.finrank_bot]
  simp only at h ⊢
  have heq : _ * _ = _ * _ := congr_arg₂ (· * ·) h <|
    (finSepDegree_adjoin_simple_eq_finrank_iff L E x (IsAlgebraic.of_finite L x)).2 <|
      (IsSeparable.separable F x).map (f := algebraMap F L) |>.of_dvd
        (minpoly.dvd_map_of_isScalarTower F L x)
  set M := L⟮x⟯; clear_value M
  letI : Algebra L M := Subalgebra.algebra M.toSubalgebra
  letI : Module L M := Algebra.toModule
  letI : SMul L M := Algebra.toSMul
  haveI : IsScalarTower F L M := IntermediateField.isScalarTower M
  rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M (Algebra.IsAlgebraic.of_finite L M),
    FiniteDimensional.finrank_mul_finrank F L M] at heq

/-- If `E / F` is a finite extension, then its separable degree is equal to its degree if and
only if it is a separable extension. -/
theorem finSepDegree_eq_finrank_iff [FiniteDimensional F E] :
    finSepDegree F E = finrank F E ↔ IsSeparable F E :=
  ⟨fun heq ↦ ⟨IsIntegral.of_finite F, fun x ↦ by
    have halg := IsAlgebraic.of_finite F x
    refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 <| le_antisymm
      (finSepDegree_adjoin_simple_le_finrank F E x halg) <| le_of_not_lt fun h ↦ ?_
    have := Nat.mul_lt_mul h (finSepDegree_le_finrank F⟮x⟯ E) Fin.size_pos'
    rw [finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E (Algebra.IsAlgebraic.of_finite _ E),
      FiniteDimensional.finrank_mul_finrank F F⟮x⟯ E] at this
    linarith only [heq, this]⟩, fun _ ↦ finSepDegree_eq_finrank_of_isSeparable F E⟩

lemma separable_of_mem_isSeparable {L : IntermediateField F E} [IsSeparable F L]
    {x : E} (h : x ∈ L) : IsIntegral F x ∧ (minpoly F x).Separable :=
  ⟨isIntegral_iff.1 <| IsSeparable.isIntegral F (K := L) ⟨x, h⟩, by
    simpa only [minpoly_eq] using IsSeparable.separable F (K := L) ⟨x, h⟩⟩

/-- `F⟮x⟯ / F` is a separable extension if and only if `x` is a separable element.
As a consequence, any rational function of `x` is also a separable element. -/
theorem isSeparable_adjoin_simple_iff_separable {x : E} :
    IsSeparable F F⟮x⟯ ↔ IsIntegral F x ∧ (minpoly F x).Separable := by
  refine ⟨fun hsep ↦ ?_, fun ⟨h, hsep⟩ ↦ ?_⟩
  · exact separable_of_mem_isSeparable F E <| mem_adjoin_simple_self F x
  · haveI := adjoin.finiteDimensional h
    rwa [← finSepDegree_eq_finrank_iff,
      finSepDegree_adjoin_simple_eq_finrank_iff F E x h.isAlgebraic]

/-- If `x` and `y` are both separable elements, then `F⟮x, y⟯ / F` is a separable extension.
As a consequence, any rational function of `x` and `y` is also a separable element. -/
theorem isSeparable_adjoin_two_of_separable {x y : E}
    (hx : IsIntegral F x ∧ (minpoly F x).Separable)
    (hy : IsIntegral F y ∧ (minpoly F y).Separable) :
    IsSeparable F F⟮x, y⟯ := by
  let L := F⟮x⟯
  haveI : FiniteDimensional F F⟮x, y⟯ := finiteDimensional_adjoin fun _ ↦ by
    rintro (rfl | rfl)
    exacts [hx.1, hy.1]
  rw [← finSepDegree_eq_finrank_iff]
  have halg' := hy.1.isAlgebraic.tower_top L
  have heq : _ * _ = _ * _ := congr_arg₂ (· * ·)
    (finSepDegree_adjoin_simple_eq_finrank_iff F E x hx.1.isAlgebraic |>.2 hx.2)
    (finSepDegree_adjoin_simple_eq_finrank_iff L E y halg' |>.2
      (hy.2.map (f := algebraMap F F⟮x⟯) |>.of_dvd (minpoly.dvd_map_of_isScalarTower F L y)))
  let M := L⟮y⟯
  letI : Algebra L M := Subalgebra.algebra M.toSubalgebra
  letI : Module L M := Algebra.toModule
  letI : SMul L M := Algebra.toSMul
  haveI : IsScalarTower F L M := IntermediateField.isScalarTower M
  haveI : FiniteDimensional F L := adjoin.finiteDimensional hx.1
  haveI : FiniteDimensional L M := adjoin.finiteDimensional halg'.isIntegral
  rw [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M (Algebra.IsAlgebraic.of_finite L M),
    FiniteDimensional.finrank_mul_finrank F L M] at heq
  change finSepDegree F (restrictScalars F M) = finrank F (restrictScalars F M) at heq
  rwa [adjoin_adjoin_left F {x} {y}, Set.union_comm, Set.union_singleton] at heq

/-- If `E / F` and `K / E` are both separable extensions, then `K / F` is also separable. -/
theorem _root_.IsSeparable.trans [Algebra E K] [IsScalarTower F E K]
    [IsSeparable F E] [IsSeparable E K] : IsSeparable F K := isSeparable_iff.2 fun x ↦ by
  let f := minpoly E x
  let E' : IntermediateField F E := adjoin F f.frange
  haveI : FiniteDimensional F E' := finiteDimensional_adjoin fun x _ ↦ IsSeparable.isIntegral F x
  have h : f ∈ lifts (algebraMap E' E) := (lifts_iff_coeff_lifts f).2 fun n ↦ Set.mem_range.2 <| by
    by_cases h : f.coeff n = 0
    · simp only [h, _root_.map_eq_zero, exists_eq]
    have : F⟮f.coeff n⟯ ≤ E' := adjoin.mono _ _ _ <|
      Set.singleton_subset_iff.2 <| f.coeff_mem_frange n h
    exact ⟨⟨f.coeff n, this <| mem_adjoin_simple_self F (f.coeff n)⟩, rfl⟩
  obtain ⟨g, h⟩ := f.mem_lifts.1 h
  have hx : x ∈ restrictScalars F E'⟮x⟯ := mem_adjoin_simple_self _ x
  have hzero : aeval x g = 0 := by
    simpa only [← h, aeval_map_algebraMap] using minpoly.aeval E x
  have halg : IsIntegral E' x := (IsSeparable.isAlgebraic F E).trans
    (IsSeparable.isAlgebraic E K) x |>.isIntegral.tower_top
  have hsep : f.Separable := IsSeparable.separable E x
  rw [← h, separable_map] at hsep
  replace hsep := hsep.of_dvd <| minpoly.dvd _ _ hzero
  haveI : IsSeparable F E' := isSeparable_tower_bot_of_isSeparable F E' E
  haveI := (isSeparable_adjoin_simple_iff_separable _ _).2 ⟨halg, hsep⟩
  haveI := adjoin.finiteDimensional halg
  letI : Algebra E' E'⟮x⟯ := Subalgebra.algebra E'⟮x⟯.toSubalgebra
  letI : Module E' E'⟮x⟯ := Algebra.toModule
  letI : SMul E' E'⟮x⟯ := Algebra.toSMul
  haveI : IsScalarTower F E' E'⟮x⟯ := IntermediateField.isScalarTower E'⟮x⟯
  haveI : FiniteDimensional F E'⟮x⟯ := FiniteDimensional.trans F E' E'⟮x⟯
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F E' E'⟮x⟯ (IsSeparable.isAlgebraic _ _)
  rw [finSepDegree_eq_finrank_of_isSeparable F E',
    finSepDegree_eq_finrank_of_isSeparable E' E'⟮x⟯,
    FiniteDimensional.finrank_mul_finrank F E' E'⟮x⟯,
    eq_comm, finSepDegree_eq_finrank_iff F E'⟮x⟯] at this
  change IsSeparable F (restrictScalars F E'⟮x⟯) at this
  exact separable_of_mem_isSeparable F K hx

/-- If `x` and `y` are both separable elements, then `x * y` is also a separable element. -/
theorem separable_mul {x y : E}
    (hx : IsIntegral F x ∧ (minpoly F x).Separable)
    (hy : IsIntegral F y ∧ (minpoly F y).Separable) :
    IsIntegral F (x * y) ∧ (minpoly F (x * y)).Separable :=
  haveI := isSeparable_adjoin_two_of_separable F E hx hy
  separable_of_mem_isSeparable F E <| F⟮x, y⟯.mul_mem (subset_adjoin F _ (Set.mem_insert x {y}))
    (subset_adjoin F _ (Set.mem_insert_of_mem x rfl))

/-- If `x` and `y` are both separable elements, then `x + y` is also a separable element. -/
theorem separable_add {x y : E}
    (hx : IsIntegral F x ∧ (minpoly F x).Separable)
    (hy : IsIntegral F y ∧ (minpoly F y).Separable) :
    IsIntegral F (x + y) ∧ (minpoly F (x + y)).Separable :=
  haveI := isSeparable_adjoin_two_of_separable F E hx hy
  separable_of_mem_isSeparable F E <| F⟮x, y⟯.add_mem (subset_adjoin F _ (Set.mem_insert x {y}))
    (subset_adjoin F _ (Set.mem_insert_of_mem x rfl))

/-- Any element `x` of `F` is a separable element of `E / F` when embedded into `E`. -/
theorem separable_algebraMap (x : F) :
    IsIntegral F ((algebraMap F E) x) ∧ (minpoly F ((algebraMap F E) x)).Separable :=
  ⟨isIntegral_algebraMap, by
    rw [minpoly.algebraMap_eq (algebraMap F E).injective]; exact IsSeparable.separable F x⟩

/-- If `x` is a separable element, then `x⁻¹` is also a separable element. -/
theorem separable_inv (x : E) (hx : IsIntegral F x ∧ (minpoly F x).Separable) :
    IsIntegral F x⁻¹ ∧ (minpoly F x⁻¹).Separable :=
  haveI := (isSeparable_adjoin_simple_iff_separable F E).2 hx
  separable_of_mem_isSeparable F E <| F⟮x⟯.inv_mem <| mem_adjoin_simple_self F x

end Field

section separableClosure

/-- The (relative) separable closure of `E / F`, or called maximal separable subextension
of `E / F`, is defined to be the intermediate field of `E / F` consisting of all separable
elements. The previous results prove that these elements are closed under field operations. -/
def separableClosure : IntermediateField F E where
  carrier := {x | IsIntegral F x ∧ (minpoly F x).Separable}
  mul_mem' := separable_mul F E
  one_mem' := (map_one (algebraMap F E)) ▸ separable_algebraMap F E 1
  add_mem' := separable_add F E
  zero_mem' := (map_zero (algebraMap F E)) ▸ separable_algebraMap F E 0
  algebraMap_mem' := separable_algebraMap F E
  inv_mem' := separable_inv F E

/-- An element is contained in the (relative) separable closure of `E / F` if and only if
it is a separable element. -/
theorem mem_separableClosure_iff {x : E} :
    x ∈ separableClosure F E ↔ IsIntegral F x ∧ (minpoly F x).Separable := by
  simp only [separableClosure]; rfl

/-- The (relative) separable closure of `E / F` is algebraic over `F`. -/
theorem separableClosure.isAlgebraic : Algebra.IsAlgebraic F (separableClosure F E) :=
  fun x ↦ isAlgebraic_iff.2 x.2.1.isAlgebraic

/-- The (relative) separable closure of `E / F` is separable over `F`. -/
instance separableClosure.isSeparable : IsSeparable F (separableClosure F E) :=
  ⟨fun x ↦ isIntegral_iff.2 x.2.1, fun x ↦ by simpa only [minpoly_eq] using x.2.2⟩

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if all of its elements are separable over `F`. -/
theorem le_separableClosure' {L : IntermediateField F E} (halg : Algebra.IsAlgebraic F L)
    (hsep : ∀ x : L, (minpoly F x).Separable) : L ≤ separableClosure F E := fun x h ↦
  ⟨isIntegral_iff.1 (halg ⟨x, h⟩).isIntegral, by simpa only [minpoly_eq] using hsep ⟨x, h⟩⟩

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if it is separable over `F`. -/
theorem le_separableClosure (L : IntermediateField F E)
    [IsSeparable F L] : L ≤ separableClosure F E :=
  le_separableClosure' F E (fun x ↦ (IsSeparable.isIntegral F x).isAlgebraic)
    (IsSeparable.separable F)

/-- An intermediate field of `E / F` is contained in the (relative) separable closure of `E / F`
if and only if it is separable over `F`. -/
theorem le_separableClosure_iff (L : IntermediateField F E) :
    L ≤ separableClosure F E ↔ IsSeparable F L :=
  ⟨fun h ↦ isSeparable_iff.2 fun x ↦ by simpa only [isIntegral_iff, minpoly_eq] using h x.2,
    fun _ ↦ le_separableClosure _ _ _⟩

/-- The normal closure of the (relative) separable closure of `E / F` is equal to itself. -/
theorem separableClosure.normalClosure_eq_self :
    normalClosure F (separableClosure F E) E = separableClosure F E := by
  apply le_antisymm ?_ (le_normalClosure _)
  rw [normalClosure_le_iff]
  intro i
  let i' : (separableClosure F E) ≃ₐ[F] i.fieldRange := AlgEquiv.ofInjectiveField i
  haveI := i'.isSeparable
  exact le_separableClosure F E _

/-- If `E` is normal over `F`, then the (relative) separable closure of `E / F` is also normal
over `F`. -/
instance separableClosure.normal [Normal F E] : Normal F (separableClosure F E) := by
  rw [← separableClosure.normalClosure_eq_self]
  exact normalClosure.normal F _ E

/-- If `E` is algebraically closed, then the (relative) separable closure of `E / F` is a
separable closure of `F`. -/
instance separableClosure.isSepClosure [IsAlgClosed E] : IsSepClosure F (separableClosure F E) := by
  refine ⟨IsSepClosed.of_exists_root _ fun p hp hirr hsep ↦ ?_, isSeparable F E⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (ne_of_gt (degree_pos_of_irreducible hirr))
  haveI := (isSeparable_adjoin_simple_iff_separable _ E).2
    ⟨IsAlgebraic.isIntegral ⟨p, hp.ne_zero, hx⟩, hsep.of_dvd <| minpoly.dvd _ x hx⟩
  let L := separableClosure F E
  letI : Algebra L L⟮x⟯ := Subalgebra.algebra L⟮x⟯.toSubalgebra
  letI : Module L L⟮x⟯ := Algebra.toModule
  letI : SMul L L⟮x⟯ := Algebra.toSMul
  haveI : IsScalarTower F L L⟮x⟯ := IntermediateField.isScalarTower L⟮x⟯
  haveI : IsSeparable F (restrictScalars F L⟮x⟯) := IsSeparable.trans F L L⟮x⟯
  have : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  use ⟨x, le_separableClosure F E (restrictScalars F L⟮x⟯) this⟩
  apply_fun algebraMap L E using (algebraMap L E).injective
  rwa [map_zero, ← aeval_algebraMap_apply_eq_algebraMap_eval]

/-- `F(S) / F` is a separable extension if and only if all elements of `S` are
separable elements. -/
theorem Field.isSeparable_adjoin_iff_separable {S : Set E} :
    IsSeparable F (adjoin F S) ↔ ∀ x ∈ S, IsIntegral F x ∧ (minpoly F x).Separable := by
  simp only [← le_separableClosure_iff, ← mem_separableClosure_iff]
  exact ⟨fun h x hx ↦ (adjoin.mono F _ _ <| Set.singleton_subset_iff.2 hx).trans h <|
    mem_adjoin_simple_self F x, adjoin_le_iff.2⟩

/-- The (relative) separable closure of `E / F` is equal to `E` if and only if `E / F` is
separable. -/
theorem separableClosure.eq_top_iff : separableClosure F E = ⊤ ↔ IsSeparable F E :=
  ⟨fun h ↦ isSeparable_iff.2 fun _ ↦ (mem_separableClosure_iff F E).1 (h ▸ mem_top),
    fun h ↦ top_unique <| fun x _ ↦ (mem_separableClosure_iff F E).2 ((isSeparable_iff.1 h) x)⟩

end separableClosure

section IsPurelyInseparable

/-- Typeclass for purely inseparable field extension: an algebraic extension `E / F` is purely
inseparable if and only if the minimal polynomial of every element of `E ∖ F` is not separable. -/
class IsPurelyInseparable : Prop where
  isIntegral' (x : E) : IsIntegral F x
  inseparable' (x : E) : (minpoly F x).Separable → x ∈ (algebraMap F E).range

theorem IsPurelyInseparable.isAlgebraic [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := fun x ↦ (IsPurelyInseparable.isIntegral' x).isAlgebraic

variable {E}

theorem IsPurelyInseparable.isIntegral [IsPurelyInseparable F E] :
    ∀ x : E, IsIntegral F x :=
  IsPurelyInseparable.isIntegral'

theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    ∀ x : E, (minpoly F x).Separable → x ∈ (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'

variable {F K}

theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ ∀ x : E,
    IsIntegral F x ∧ ((minpoly F x).Separable → x ∈ (algebraMap F E).range) :=
  ⟨fun h x ↦ ⟨h.isIntegral' x, h.inseparable' x⟩, fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩⟩

/-- Transfer `IsPurelyInseparable` across an `AlgEquiv`. -/
theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨fun _ ↦ by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral F _,
    fun x h ↦ ?_⟩
  rw [← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ e.isPurelyInseparable, fun _ ↦ e.symm.isPurelyInseparable⟩

variable (F E K)

/-- If `E / F` is purely inseparable, then the (relative) separable closure of `E / F` is
equal to `F`. -/
theorem separableClosure.eq_bot_of_isPurelyInseparable [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x ((mem_separableClosure_iff F E).1 h).2

/-- If `E / F` is an algebraic extension, then the (relative) separable closure of `E / F` is
equal to `F` if and only if `E / F` is purely inseparable. -/
theorem separableClosure.eq_bot_iff (halg : Algebra.IsAlgebraic F E) :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ have hx := (halg x).isIntegral; ⟨hx, fun hs ↦ by
    simpa only [h] using (mem_separableClosure_iff F E).2 ⟨hx, hs⟩⟩,
      fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩

instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨fun _ ↦ isIntegral_algebraMap, fun x _ ↦ ⟨x, rfl⟩⟩

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
theorem isPurelyInseparable_iff_mem_pow (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ n : ℕ, x ^ (q ^ n) ∈ (algebraMap F E).range := by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := Irreducible.hasSeparableContraction q _ (minpoly.irreducible (h x).1)
    exact ⟨n, (h _).2 <| Separable.of_dvd h1 <| minpoly.dvd F _ <| by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  cases' hF with _ _ hprime _
  · simp only [one_pow, pow_one, exists_const] at h
    exact ⟨by obtain ⟨_, rfl⟩ := h x; exact isIntegral_algebraMap, fun _ ↦ h x⟩
  haveI := Fact.mk hprime
  haveI : ExpChar F q := ExpChar.prime hprime
  obtain ⟨n, y, hx⟩ := h x
  let g := X - C y
  have hzero : aeval x (expand F (q ^ n) g) = 0 := by
    simp only [map_sub, expand_X, expand_C, map_pow, aeval_X, aeval_C, hx, sub_self]
  have hnezero : expand F (q ^ n) g ≠ 0 := (expand_ne_zero Fin.size_pos').2 <| X_sub_C_ne_zero y
  have halg := IsAlgebraic.isIntegral ⟨_, hnezero, hzero⟩
  refine ⟨halg, fun hsep ↦ ?_⟩
  have hdeg := natSepDegree_le_of_dvd _ _ (minpoly.dvd F x hzero) hnezero
  rw [natSepDegree_expand_eq_natSepDegree, natSepDegree_X_sub_C,
    natSepDegree_eq_natDegree_of_separable _ hsep] at hdeg
  replace hdeg := le_antisymm hdeg (minpoly.natDegree_pos halg)
  rw [← adjoin.finrank halg, IntermediateField.finrank_eq_one_iff] at hdeg
  simpa only [hdeg] using mem_adjoin_simple_self F x

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `E / F` is also purely inseparable. -/
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨fun x ↦ (isIntegral F (algebraMap E K x)).tower_bot_of_field, fun x h ↦ ?_⟩
  rw [← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  use y
  apply_fun algebraMap E K using (algebraMap E K).injective
  exact h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `K / E` is also purely inseparable. -/
theorem IsPurelyInseparable.tower_top [Algebra E K] [IsScalarTower F E K]
    [h : IsPurelyInseparable F K] : IsPurelyInseparable E K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_mem_pow _ _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩

/-- If `E / F` and `K / E` are both purely inseparable extensions, then `K / F` is also
purely inseparable. -/
theorem IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K]
    [h1 : IsPurelyInseparable F E] [h2 : IsPurelyInseparable E K] : IsPurelyInseparable F K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_mem_pow _ _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K, h1, map_pow, h2, ← pow_mul, ← pow_add]

/-- A field extension `E / F` is purely inseparable if and only if for every element `x` of `E`,
its minimal polynomial has separable degree one. -/
theorem isPurelyInseparable_iff_natSepDegree_eq_one :
    IsPurelyInseparable F E ↔ ∀ x : E, (minpoly F x).natSepDegree = 1 := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hq : 0 < q := by
    rcases expChar_is_prime_or_one F q with h | rfl
    exacts [Nat.Prime.pos h, Nat.one_pos]
  refine ⟨fun h x ↦ ?_, fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ?_⟩
  · rw [isPurelyInseparable_iff_mem_pow _ _ q] at h
    obtain ⟨n, y, hx⟩ := h x
    let g := X - C y
    have hzero : aeval x (expand F (q ^ n) g) = 0 := by
      simp only [map_sub, expand_X, expand_C, map_pow, aeval_X, aeval_C, hx, sub_self]
    have hnezero : expand F (q ^ n) g ≠ 0 :=
      (expand_ne_zero (Nat.pos_pow_of_pos n hq)).2 <| X_sub_C_ne_zero y
    have hdeg := natSepDegree_le_of_dvd _ _ (minpoly.dvd F x hzero) hnezero
    rw [natSepDegree_expand_eq_natSepDegree, natSepDegree_X_sub_C] at hdeg
    have := minpoly.natDegree_pos <| IsAlgebraic.isIntegral ⟨_, hnezero, hzero⟩
    rw [Nat.pos_iff_ne_zero, ← natSepDegree_ne_zero_iff, ← Nat.pos_iff_ne_zero] at this
    exact le_antisymm hdeg this
  refine ⟨by_contra fun g ↦ (ne_of_apply_ne natDegree <| (natSepDegree_ne_zero_iff _).1 <|
    ne_zero_of_eq_one (h x)) (minpoly.eq_zero g), fun g ↦ minpoly.mem_range_of_degree_eq_one F x ?_⟩
  simpa only [natSepDegree_eq_natDegree_of_separable _ g,
    ← degree_eq_iff_natDegree_eq_of_pos Nat.one_pos] using h x

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, the minimal polynomial of `x` over `F` is of form
`X ^ (q ^ n) - y` for some natural number `n` and some element `y` of `F`. -/
theorem isPurelyInseparable_iff_minpoly_eq (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ (n : ℕ) (y : F), minpoly F x = X ^ (q ^ n) - C y := by
  refine ⟨fun h x ↦ ?_, fun h ↦ (isPurelyInseparable_iff_natSepDegree_eq_one F E).2 fun x ↦ ?_⟩
  · have halg := h.isIntegral' x
    exact natSepDegree_eq_one_iff_of_monic_irreducible _ q (minpoly.monic halg)
      (minpoly.irreducible halg) |>.1 <| (isPurelyInseparable_iff_natSepDegree_eq_one F E).1 h x
  obtain ⟨n, y, h⟩ := h x
  replace h : minpoly F x = expand F (q ^ n) (X - C y) := by rwa [map_sub, expand_X, expand_C]
  apply_fun natSepDegree at h
  rwa [natSepDegree_expand_eq_natSepDegree, natSepDegree_X_sub_C] at h

theorem isPurelyInseparable_of_finSepDegree_eq_one (halg : Algebra.IsAlgebraic F E)
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff]
  refine fun x ↦ ⟨(halg x).isIntegral, fun hsep ↦ ?_⟩
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E <| halg.tower_top (L := F⟮x⟯)
  rw [hdeg, mul_eq_one, (finSepDegree_adjoin_simple_eq_finrank_iff F E x (halg x)).2 hsep,
    IntermediateField.finrank_eq_one_iff] at this
  simpa only [this.1] using mem_adjoin_simple_self F x



end IsPurelyInseparable
