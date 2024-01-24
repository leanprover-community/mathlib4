/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.NormalClosure
import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Field.Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`
  (the algebraic closure of `F` is usually used in the literature, but our definition has the
  advantage that `Field.Emb F E` lies in the same universe as `E` rather than the maximum over `F`
  and `E`). Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

  **Remark:** if `E / F` is not algebraic, then this definition makes no mathematical sense,
  and if it is infinite, then its cardinality doesn't behave as expected (namely, not equal to the
  field extension degree of `separableClosure F E / F`). For example, if $F = \mathbb{Q}$ and
  $E = \mathbb{Q}( \mu_{p^\infty} )$, then $\operatorname{Emb}_F (E)$ is in bijection with
  $\operatorname{Gal}(E/F)$, which is isomorphic to
  $\mathbb{Z}_p^\times$, which is uncountable, while $[E:F]$ is countable.

  **TODO:** prove or disprove that if `E / F` is algebraic and `Emb F E` is infinite, then
  `Field.Emb F E` has cardinality `2 ^ Module.rank F (separableClosure F E)`.

- `Field.finSepDegree F E`: the (finite) separable degree $[E:F]_s$ of an algebraic extension
  `E / F` of fields, defined to be the number of `F`-algebra homomorphisms from `E` to the algebraic
  closure of `E`, as a natural number. It is zero if `Field.Emb F E` is not finite.
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

  **Remark:** the `Cardinal`-valued, potentially infinite separable degree `Field.sepDegree F E`
  for a general algebraicextension `E / F` is defined to be the degree of `L / F`, where `L` is
  the (relative) separable closure `separableClosure F E` of `E / F`, which is not defined in
  this file yet. Later we will show that (`Field.finSepDegree_eq`), if `Field.Emb F E` is finite,
  then these two definitions coincide.

- `Polynomial.natSepDegree`: the separable degree of a polynomial is a natural number,
  defined to be the number of distinct roots of it over its splitting field.

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
  In particular, the separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see also `FiniteDimensional.finrank_mul_finrank`).

- `Polynomial.natSepDegree_le_natDegree`: the separable degree of a polynomial is smaller than
  its degree.

- `Polynomial.natSepDegree_eq_natDegree_iff`: the separable degree of a non-zero polynomial is
  equal to its degree if and only if it is separable.

- `Polynomial.natSepDegree_eq_of_splits`: if a polynomial splits over `E`, then its separable degree
  is equal to the number of distinct roots of it over `E`.

- `Polynomial.natSepDegree_eq_of_isAlgClosed`: the separable degree of a polynomial is equal to
  the number of distinct roots of it over any algebraically closed field.

- `Polynomial.natSepDegree_expand`: if a field `F` is of exponential characteristic
  `q`, then `Polynomial.expand F (q ^ n) f` and `f` have the same separable degree.

- `Polynomial.HasSeparableContraction.natSepDegree_eq`: if a polynomial has separable
  contraction, then its separable degree is equal to its separable contraction degree.

- `Irreducible.natSepDegree_dvd_natDegree`: the separable degree of an irreducible
  polynomial divides its degree.

- `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree`: the separable degree of
  `F⟮α⟯ / F` is equal to the separable degree of the minimal polynomial of `α` over `F`.

- `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`: if `α` is algebraic over `F`, then
  the separable degree of `F⟮α⟯ / F` is equal to the degree of `F⟮α⟯ / F` if and only if `α` is a
  separable element.

- `Field.finSepDegree_dvd_finrank`: the separable degree of any field extension `E / F` divides
  the degree of `E / F`.

- `Field.finSepDegree_le_finrank`: the separable degree of a finite extension `E / F` is smaller
  than the degree of `E / F`.

- `Field.finSepDegree_eq_finrank_iff`: if `E / F` is a finite extension, then its separable degree
  is equal to its degree if and only if it is a separable extension.

- `IntermediateField.isSeparable_adjoin_simple_iff_separable`: `F⟮x⟯ / F` is a separable extension
  if and only if `x` is a separable element.

- `IsSeparable.trans`: if `E / F` and `K / E` are both separable, then `K / F` is also separable.

## Tags

separable degree, degree, polynomial

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
def finSepDegree : ℕ := Nat.card (Emb F E)

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
    finSepDegree F E = finSepDegree F K := Nat.card_congr (embEquivOfEquiv F E K i)

@[simp]
theorem finSepDegree_self : finSepDegree F F = 1 := by
  have : Cardinal.mk (Emb F F) = 1 := le_antisymm
    (Cardinal.le_one_iff_subsingleton.2 AlgHom.subsingleton)
    (Cardinal.one_le_iff_ne_zero.2 <| Cardinal.mk_ne_zero _)
  rw [finSepDegree, Nat.card, this, Cardinal.one_toNat]

end Field

namespace IntermediateField

@[simp]
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finSepDegree_eq_of_equiv _ _ _ (botEquiv F E), finSepDegree_self]

section Tower

variable {F}

variable [Algebra E K] [IsScalarTower F E K]

@[simp]
theorem finSepDegree_bot' : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E :=
  finSepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K :=
  finSepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

end Tower

end IntermediateField

namespace Field

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` if `E = F(S)` such that every
element `s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`.
Combined with `Field.instNonemptyEmb`, it can be viewed as a stronger version of
`IntermediateField.nonempty_algHom_of_adjoin_splits`. -/
def embEquivOfAdjoinSplits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    Emb F E ≃ (E →ₐ[F] K) :=
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
    (hS ▸ isAlgebraic_adjoin (S := S) fun x hx ↦ (hK x hx).1)
  Classical.choice <| Function.Embedding.antisymm
    (halg.algHomEmbeddingOfSplits (fun _ ↦ splits_of_mem_adjoin F (S := S) hK (hS ▸ mem_top)) _)
    (halg.algHomEmbeddingOfSplits (fun _ ↦ IsAlgClosed.splits_codomain _) _)

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
theorem finSepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    finSepDegree F E = Nat.card (E →ₐ[F] K) := Nat.card_congr (embEquivOfAdjoinSplits F E K hS hK)

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` when `E / F` is algebraic
and `K / F` is algebraically closed. -/
def embEquivOfIsAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) :=
  embEquivOfAdjoinSplits F E K (adjoin_univ F E) fun s _ ↦
    ⟨(halg s).isIntegral, IsAlgClosed.splits_codomain _⟩

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
theorem finSepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    finSepDegree F E = Nat.card (E →ₐ[F] K) := Nat.card_congr (embEquivOfIsAlgClosed F E K halg)

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
separable degrees satisfy the tower law
$[E:F]_s [K:E]_s = [K:F]_s$. See also `FiniteDimensional.finrank_mul_finrank`. -/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  simpa only [Nat.card_prod] using Nat.card_congr (embProdEmbOfIsAlgebraic F E K halg)

end Field

namespace Polynomial

variable {F E}

variable (f : F[X])

/-- The separable degree `Polynomial.natSepDegree` of a polynomial is a natural number,
defined to be the number of distinct roots of it over its splitting field.
This is similar to `Polynomial.natDegree` but not to `Polynomial.degree`, namely, the separable
degree of `0` is `0`, not negative infinity. -/
def natSepDegree : ℕ := (f.aroots f.SplittingField).toFinset.card

/-- The separable degree of a polynomial is smaller than its degree. -/
theorem natSepDegree_le_natDegree : f.natSepDegree ≤ f.natDegree := by
  have := f.map (algebraMap F f.SplittingField) |>.card_roots'
  rw [← aroots_def, natDegree_map] at this
  exact (f.aroots f.SplittingField).toFinset_card_le.trans this

@[simp]
theorem natSepDegree_X_sub_C (x : F) : (X - C x).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X_sub_C, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]
theorem natSepDegree_X : (X : F[X]).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X, Multiset.toFinset_singleton, Finset.card_singleton]

/-- A constant polynomial has zero separable degree. -/
theorem natSepDegree_eq_zero (h : f.natDegree = 0) : f.natSepDegree = 0 := by
  linarith only [natSepDegree_le_natDegree f, h]

@[simp]
theorem natSepDegree_C (x : F) : (C x).natSepDegree = 0 := natSepDegree_eq_zero _ (natDegree_C _)

@[simp]
theorem natSepDegree_zero : (0 : F[X]).natSepDegree = 0 := by
  rw [← C_0, natSepDegree_C]

@[simp]
theorem natSepDegree_one : (1 : F[X]).natSepDegree = 0 := by
  rw [← C_1, natSepDegree_C]

/-- A non-constant polynomial has non-zero separable degree. -/
theorem natSepDegree_ne_zero (h : f.natDegree ≠ 0) : f.natSepDegree ≠ 0 := by
  rw [natSepDegree, ne_eq, Finset.card_eq_zero, ← ne_eq, ← Finset.nonempty_iff_ne_empty]
  use rootOfSplits _ (SplittingField.splits f) (ne_of_apply_ne _ h)
  rw [Multiset.mem_toFinset, mem_aroots]
  exact ⟨ne_of_apply_ne _ h, map_rootOfSplits _ (SplittingField.splits f) (ne_of_apply_ne _ h)⟩

/-- A polynomial has zero separable degree if and only if it is constant. -/
theorem natSepDegree_eq_zero_iff : f.natSepDegree = 0 ↔ f.natDegree = 0 :=
  ⟨(natSepDegree_ne_zero f).mtr, natSepDegree_eq_zero f⟩

/-- A polynomial has non-zero separable degree if and only if it is non-constant. -/
theorem natSepDegree_ne_zero_iff : f.natSepDegree ≠ 0 ↔ f.natDegree ≠ 0 :=
  Iff.not <| natSepDegree_eq_zero_iff f

/-- The separable degree of a non-zero polynomial is equal to its degree if and only if
it is separable. -/
theorem natSepDegree_eq_natDegree_iff (hf : f ≠ 0) :
    f.natSepDegree = f.natDegree ↔ f.Separable := by
  simp_rw [← card_rootSet_eq_natDegree_iff_of_splits hf (SplittingField.splits f),
    rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rfl

/-- If a polynomial is separable, then its separable degree is equal to its degree. -/
theorem natSepDegree_eq_natDegree_of_separable (h : f.Separable) :
    f.natSepDegree = f.natDegree := (natSepDegree_eq_natDegree_iff f h.ne_zero).2 h

variable {f} in
/-- Same as `Polynomial.natSepDegree_eq_natDegree_of_separable`, but enables the use of
dot notation. -/
theorem Separable.natSepDegree_eq_natDegree (h : f.Separable) :
    f.natSepDegree = f.natDegree := natSepDegree_eq_natDegree_of_separable f h

/-- If a polynomial splits over `E`, then its separable degree is equal to
the number of distinct roots of it over `E`. -/
theorem natSepDegree_eq_of_splits (h : f.Splits (algebraMap F E)) :
    f.natSepDegree = (f.aroots E).toFinset.card := by
  rw [aroots, ← (SplittingField.lift f h).comp_algebraMap, ← map_map,
    roots_map _ ((splits_id_iff_splits _).mpr <| SplittingField.splits f),
    Multiset.toFinset_map, Finset.card_image_of_injective _ (RingHom.injective _)]
  rfl

variable (E) in
/-- The separable degree of a polynomial is equal to
the number of distinct roots of it over any algebraically closed field. -/
theorem natSepDegree_eq_of_isAlgClosed [IsAlgClosed E] :
    f.natSepDegree = (f.aroots E).toFinset.card :=
  natSepDegree_eq_of_splits f (IsAlgClosed.splits_codomain f)

@[simp]
theorem natSepDegree_C_mul {x : F} (hx : x ≠ 0) :
    (C x * f).natSepDegree = f.natSepDegree := by
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_C_mul _ hx]

@[simp]
theorem natSepDegree_smul_nonzero {x : F} (hx : x ≠ 0) :
    (x • f).natSepDegree = f.natSepDegree := by
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_smul_nonzero _ hx]

@[simp]
theorem natSepDegree_pow {n : ℕ} : (f ^ n).natSepDegree = if n = 0 then 0 else f.natSepDegree := by
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_pow]
  by_cases h : n = 0
  · simp only [h, zero_smul, Multiset.toFinset_zero, Finset.card_empty, ite_true]
  simp only [h, Multiset.toFinset_nsmul _ n h, ite_false]

theorem natSepDegree_X_pow {n : ℕ} : (X ^ n : F[X]).natSepDegree = if n = 0 then 0 else 1 := by
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
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add]
  exact Finset.card_union_le _ _

theorem natSepDegree_le_of_dvd (g : F[X]) (h1 : f ∣ g) (h2 : g ≠ 0) :
    f.natSepDegree ≤ g.natSepDegree := by
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F)]
  exact Finset.card_le_card <| Multiset.toFinset_subset.mpr <|
    Multiset.Le.subset <| roots.le_of_dvd (map_ne_zero h2) <| map_dvd _ h1

/-- If a field `F` is of exponential characteristic `q`, then `Polynomial.expand F (q ^ n) f`
and `f` have the same separable degree. -/
theorem natSepDegree_expand (q : ℕ) [hF : ExpChar F q] {n : ℕ} :
    (expand F (q ^ n) f).natSepDegree = f.natSepDegree := by
  cases' hF with _ _ hprime _
  · simp only [one_pow, expand_one]
  haveI := Fact.mk hprime
  simpa only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_def, map_expand,
    Fintype.card_coe] using Fintype.card_eq.2
      ⟨(f.map (algebraMap F (AlgebraicClosure F))).rootsExpandPowEquivRoots q n⟩

theorem natSepDegree_X_pow_char_sub_C (q : ℕ) [ExpChar F q] (n : ℕ) (y : F) :
    (X ^ q ^ n - C y).natSepDegree = 1 := by
  rw [← expand_X, ← expand_C (q ^ n), ← map_sub, natSepDegree_expand, natSepDegree_X_sub_C]

variable {f} in
/-- If `g` is a separable contraction of `f`, then the separable degree of `f` is equal to
the degree of `g`. -/
theorem IsSeparableContraction.natSepDegree_eq {g : Polynomial F} {q : ℕ} [ExpChar F q]
    (h : IsSeparableContraction q f g) : f.natSepDegree = g.natDegree := by
  obtain ⟨h1, m, h2⟩ := h
  rw [← h2, natSepDegree_expand, h1.natSepDegree_eq_natDegree]

variable {f} in
/-- If a polynomial has separable contraction, then its separable degree is equal to the degree of
the given separable contraction. -/
theorem HasSeparableContraction.natSepDegree_eq
    {q : ℕ} [ExpChar F q] (hf : f.HasSeparableContraction q) :
    f.natSepDegree = hf.degree := hf.isSeparableContraction.natSepDegree_eq

end Polynomial

namespace Irreducible

variable {F}

variable {f : F[X]}

/-- The separable degree of an irreducible polynomial divides its degree. -/
theorem natSepDegree_dvd_natDegree (h : Irreducible f) :
    f.natSepDegree ∣ f.natDegree := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hf := h.hasSeparableContraction q
  rw [hf.natSepDegree_eq]
  exact hf.dvd_degree

/-- A monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one if and only if it is of the form `Polynomial.expand F (q ^ n) (X - C y)`
for some `n : ℕ` and `y : F`. -/
theorem natSepDegree_eq_one_iff_of_monic' (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔
    ∃ (n : ℕ) (y : F), f = expand F (q ^ n) (X - C y) := by
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · obtain ⟨g, h1, n, rfl⟩ := hi.hasSeparableContraction q
    have h2 : g.natDegree = 1 := by
      rwa [natSepDegree_expand _ q, h1.natSepDegree_eq_natDegree] at h
    rw [((monic_expand_iff <| expChar_pow_pos F q n).mp hm).eq_X_add_C h2]
    exact ⟨n, -(g.coeff 0), by rw [map_neg, sub_neg_eq_add]⟩
  rw [h, natSepDegree_expand _ q, natSepDegree_X_sub_C]

/-- A monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one if and only if it is of the form `X ^ (q ^ n) - C y`
for some `n : ℕ` and `y : F`. -/
theorem natSepDegree_eq_one_iff_of_monic (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔ ∃ (n : ℕ) (y : F), f = X ^ q ^ n - C y := by
  simp only [hi.natSepDegree_eq_one_iff_of_monic' q hm, map_sub, expand_X, expand_C]

end Irreducible

namespace minpoly

variable {F E}

variable (q : ℕ) [hF : ExpChar F q] {x : E}

/-- The minimal polynomial of an element of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`Polynomial.expand F (q ^ n) (X - C y)` for some `n : ℕ` and `y : F`. -/
theorem natSepDegree_eq_one_iff_eq_expand_X_sub_C : (minpoly F x).natSepDegree = 1 ↔
    ∃ (n : ℕ) (y : F), minpoly F x = expand F (q ^ n) (X - C y) := by
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · have halg : IsIntegral F x := by_contra fun h' ↦ by
      simp only [eq_zero h', natSepDegree_zero, zero_ne_one] at h
    exact (minpoly.irreducible halg).natSepDegree_eq_one_iff_of_monic' q
      (minpoly.monic halg) |>.1 h
  rw [h, natSepDegree_expand _ q, natSepDegree_X_sub_C]

/-- The minimal polynomial of an element of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`X ^ (q ^ n) - C y` for some `n : ℕ` and `y : F`. -/
theorem natSepDegree_eq_one_iff_eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔
    ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp only [minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C q, map_sub, expand_X, expand_C]

/-- The minimal polynomial of an element `x` of `E / F` of exponential characteristic `q` has
separable degree one if and only if `x ^ (q ^ n) ∈ F` for some `n : ℕ`. -/
theorem natSepDegree_eq_one_iff_mem_pow : (minpoly F x).natSepDegree = 1 ↔
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  convert_to _ ↔ ∃ (n : ℕ) (y : F), Polynomial.aeval x (X ^ q ^ n - C y) = 0
  · simp_rw [RingHom.mem_range, map_sub, map_pow, aeval_C, aeval_X, sub_eq_zero, eq_comm]
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · obtain ⟨n, y, hx⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    exact ⟨n, y, hx ▸ aeval F x⟩
  have hnezero := X_pow_sub_C_ne_zero (expChar_pow_pos F q n) y
  refine ((natSepDegree_le_of_dvd _ _ (minpoly.dvd F x h) hnezero).trans_eq <|
    natSepDegree_X_pow_char_sub_C q n y).antisymm ?_
  rw [Nat.one_le_iff_ne_zero, natSepDegree_ne_zero_iff, ← Nat.one_le_iff_ne_zero]
  exact minpoly.natDegree_pos <| IsAlgebraic.isIntegral ⟨_, hnezero, h⟩

/-- The minimal polynomial of an element `x` of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`(X - x) ^ (q ^ n)` for some `n : ℕ`. -/
theorem natSepDegree_eq_one_iff_eq_X_sub_C_pow : (minpoly F x).natSepDegree = 1 ↔
    ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  haveI := expChar_of_injective_algebraMap (NoZeroSMulDivisors.algebraMap_injective E E[X]) q
  refine ⟨fun h ↦ ?_, fun ⟨n, h⟩ ↦ (natSepDegree_eq_one_iff_mem_pow q).2 ?_⟩
  · obtain ⟨n, y, h⟩ := (natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    have hx := congr_arg (Polynomial.aeval x) h.symm
    rw [minpoly.aeval, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero, eq_comm] at hx
    use n
    rw [h, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, hx, map_pow, ← sub_pow_expChar_pow]
  apply_fun constantCoeff at h
  simp_rw [map_pow, map_sub, constantCoeff_apply, coeff_map, coeff_X_zero, coeff_C_zero] at h
  rw [zero_sub, neg_pow, ExpChar.neg_one_pow_expChar_pow] at h
  exact ⟨n, -(minpoly F x).coeff 0, by rw [map_neg, h]; ring1⟩

end minpoly

namespace IntermediateField

/-- The separable degree of `F⟮α⟯ / F` is equal to the separable degree of the
minimal polynomial of `α` over `F`. -/
theorem finSepDegree_adjoin_simple_eq_natSepDegree {α : E} (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = (minpoly F α).natSepDegree := by
  have : finSepDegree F F⟮α⟯ = _ := Nat.card_congr
    (algHomAdjoinIntegralEquiv F (K := AlgebraicClosure F⟮α⟯) halg.isIntegral)
  rw [this, Nat.card_eq_fintype_card, natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯)]
  exact Eq.trans (by simp only [Multiset.mem_toFinset]) (Fintype.card_coe _)

-- The separable degree of `F⟮α⟯ / F` divides the degree of `F⟮α⟯ / F`.
-- Marked as `private` because it is a special case of `finSepDegree_dvd_finrank`.
private theorem finSepDegree_adjoin_simple_dvd_finrank (α : E) :
    finSepDegree F F⟮α⟯ ∣ finrank F F⟮α⟯ := by
  by_cases halg : IsAlgebraic F α
  · rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral]
    exact (minpoly.irreducible halg.isIntegral).natSepDegree_dvd_natDegree
  have : finrank F F⟮α⟯ = 0 := finrank_of_infinite_dimensional fun _ ↦
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
  rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral,
    natSepDegree_eq_natDegree_iff _ (minpoly.ne_zero halg.isIntegral)]

end IntermediateField

namespace Field

/-- The separable degree of any field extension `E / F` divides the degree of `E / F`. -/
theorem finSepDegree_dvd_finrank : finSepDegree F E ∣ finrank F E := by
  by_cases hfd : FiniteDimensional F E
  · rw [← finSepDegree_top F, ← finrank_top F E]
    refine induction_on_adjoin (fun K : IntermediateField F E ↦ finSepDegree F K ∣ finrank F K)
      (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot, one_dvd]) (fun L x h ↦ ?_) ⊤
    simp only at h ⊢
    have hdvd := mul_dvd_mul h <| finSepDegree_adjoin_simple_dvd_finrank L E x
    set M := L⟮x⟯
    rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M (Algebra.IsAlgebraic.of_finite L M),
      FiniteDimensional.finrank_mul_finrank F L M] at hdvd
  rw [finrank_of_infinite_dimensional hfd]
  exact dvd_zero _

/-- The separable degree of a finite extension `E / F` is smaller than the degree of `E / F`. -/
theorem finSepDegree_le_finrank [FiniteDimensional F E] :
    finSepDegree F E ≤ finrank F E := Nat.le_of_dvd finrank_pos <| finSepDegree_dvd_finrank F E

/-- If `E / F` is a separable extension, then its separable degree is equal to its degree.
When `E / F` is infinite, it means that `Field.Emb F E` has infinitely many elements.
(But the cardinality of `Field.Emb F E` is not equal to `Module.rank F E` in general!) -/
theorem finSepDegree_eq_finrank_of_isSeparable [IsSeparable F E] :
    finSepDegree F E = finrank F E := by
  wlog hfd : FiniteDimensional F E generalizing E with H
  · rw [finrank_of_infinite_dimensional hfd]
    have halg := IsSeparable.isAlgebraic F E
    obtain ⟨L, h, h'⟩ := exists_lt_finrank_of_infinite_dimensional halg hfd (finSepDegree F E)
    haveI : IsSeparable F L := isSeparable_tower_bot_of_isSeparable F L E
    have hd := finSepDegree_mul_finSepDegree_of_isAlgebraic F L E (halg.tower_top L)
    rw [H L h] at hd
    by_cases hd' : finSepDegree L E = 0
    · rw [← hd, hd', mul_zero]
    linarith only [h', hd, Nat.le_mul_of_pos_right (finrank F L) (Nat.pos_of_ne_zero hd')]
  rw [← finSepDegree_top F, ← finrank_top F E]
  refine induction_on_adjoin (fun K : IntermediateField F E ↦ finSepDegree F K = finrank F K)
    (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot]) (fun L x h ↦ ?_) ⊤
  simp only at h ⊢
  have heq : _ * _ = _ * _ := congr_arg₂ (· * ·) h <|
    (finSepDegree_adjoin_simple_eq_finrank_iff L E x (IsAlgebraic.of_finite L x)).2 <|
      (IsSeparable.separable F x).map_minpoly L
  set M := L⟮x⟯
  rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M (Algebra.IsAlgebraic.of_finite L M),
    FiniteDimensional.finrank_mul_finrank F L M] at heq

/-- If `E / F` is a finite extension, then its separable degree is equal to its degree if and
only if it is a separable extension. -/
theorem finSepDegree_eq_finrank_iff [FiniteDimensional F E] :
    finSepDegree F E = finrank F E ↔ IsSeparable F E :=
  ⟨fun heq ↦ ⟨fun x ↦ by
    have halg := IsAlgebraic.of_finite F x
    refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 <| le_antisymm
      (finSepDegree_adjoin_simple_le_finrank F E x halg) <| le_of_not_lt fun h ↦ ?_
    have := Nat.mul_lt_mul_of_lt_of_le' h (finSepDegree_le_finrank F⟮x⟯ E) Fin.size_pos'
    rw [finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E (Algebra.IsAlgebraic.of_finite _ E),
      FiniteDimensional.finrank_mul_finrank F F⟮x⟯ E] at this
    linarith only [heq, this]⟩, fun _ ↦ finSepDegree_eq_finrank_of_isSeparable F E⟩

end Field

lemma IntermediateField.separable_of_mem_isSeparable {L : IntermediateField F E} [IsSeparable F L]
    {x : E} (h : x ∈ L) : (minpoly F x).Separable := by
  simpa only [minpoly_eq] using IsSeparable.separable F (K := L) ⟨x, h⟩

/-- `F⟮x⟯ / F` is a separable extension if and only if `x` is a separable element.
As a consequence, any rational function of `x` is also a separable element. -/
theorem IntermediateField.isSeparable_adjoin_simple_iff_separable {x : E} :
    IsSeparable F F⟮x⟯ ↔ (minpoly F x).Separable := by
  refine ⟨fun _ ↦ ?_, fun hsep ↦ ?_⟩
  · exact separable_of_mem_isSeparable F E <| mem_adjoin_simple_self F x
  · have h := hsep.isIntegral
    haveI := adjoin.finiteDimensional h
    rwa [← finSepDegree_eq_finrank_iff,
      finSepDegree_adjoin_simple_eq_finrank_iff F E x h.isAlgebraic]

variable {E K} in
/-- If `K / E / F` is an extension tower such that `E / F` is separable,
`x : K` is separable over `E`, then it's also separable over `F`. -/
theorem Polynomial.Separable.comap_minpoly_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [IsSeparable F E] {x : K} (hsep : (minpoly E x).Separable) : (minpoly F x).Separable := by
  let f := minpoly E x
  let E' : IntermediateField F E := adjoin F f.frange
  haveI : FiniteDimensional F E' := finiteDimensional_adjoin fun x _ ↦ IsSeparable.isIntegral F x
  let g : E'[X] := f.toSubring E'.toSubring (subset_adjoin F _)
  have h : g.map (algebraMap E' E) = f := f.map_toSubring E'.toSubring (subset_adjoin F _)
  clear_value g
  have hx : x ∈ restrictScalars F E'⟮x⟯ := mem_adjoin_simple_self _ x
  have hzero : aeval x g = 0 := by
    simpa only [← h, aeval_map_algebraMap] using minpoly.aeval E x
  have halg : IsIntegral E' x :=
    isIntegral_trans (IsSeparable.isAlgebraic F E).isIntegral _ hsep.isIntegral |>.tower_top
  simp_rw [← h, separable_map] at hsep
  replace hsep := hsep.of_dvd <| minpoly.dvd _ _ hzero
  haveI : IsSeparable F E' := isSeparable_tower_bot_of_isSeparable F E' E
  haveI := (isSeparable_adjoin_simple_iff_separable _ _).2 hsep
  haveI := adjoin.finiteDimensional halg
  haveI : FiniteDimensional F E'⟮x⟯ := FiniteDimensional.trans F E' E'⟮x⟯
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F E' E'⟮x⟯ (IsSeparable.isAlgebraic _ _)
  rw [finSepDegree_eq_finrank_of_isSeparable F E',
    finSepDegree_eq_finrank_of_isSeparable E' E'⟮x⟯,
    FiniteDimensional.finrank_mul_finrank F E' E'⟮x⟯,
    eq_comm, finSepDegree_eq_finrank_iff F E'⟮x⟯] at this
  change IsSeparable F (restrictScalars F E'⟮x⟯) at this
  exact separable_of_mem_isSeparable F K hx

/-- If `E / F` and `K / E` are both separable extensions, then `K / F` is also separable. -/
theorem IsSeparable.trans [Algebra E K] [IsScalarTower F E K]
    [IsSeparable F E] [IsSeparable E K] : IsSeparable F K :=
  ⟨fun x ↦ (IsSeparable.separable E x).comap_minpoly_of_isSeparable F⟩

/-- If `x` and `y` are both separable elements, then `F⟮x, y⟯ / F` is a separable extension.
As a consequence, any rational function of `x` and `y` is also a separable element. -/
theorem IntermediateField.isSeparable_adjoin_pair_of_separable {x y : E}
    (hx : (minpoly F x).Separable) (hy : (minpoly F y).Separable) :
    IsSeparable F F⟮x, y⟯ := by
  rw [← adjoin_simple_adjoin_simple]
  replace hy := hy.map_minpoly F⟮x⟯
  rw [← isSeparable_adjoin_simple_iff_separable] at hx hy
  exact IsSeparable.trans F F⟮x⟯ F⟮x⟯⟮y⟯

namespace Field

variable {F}

/-- Any element `x` of `F` is a separable element of `E / F` when embedded into `E`. -/
theorem separable_algebraMap (x : F) : (minpoly F ((algebraMap F E) x)).Separable := by
  rw [minpoly.algebraMap_eq (algebraMap F E).injective]
  exact IsSeparable.separable F x

variable {E}

/-- If `x` and `y` are both separable elements, then `x * y` is also a separable element. -/
theorem separable_mul {x y : E} (hx : (minpoly F x).Separable) (hy : (minpoly F y).Separable) :
    (minpoly F (x * y)).Separable :=
  haveI := isSeparable_adjoin_pair_of_separable F E hx hy
  separable_of_mem_isSeparable F E <| F⟮x, y⟯.mul_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/-- If `x` and `y` are both separable elements, then `x + y` is also a separable element. -/
theorem separable_add {x y : E} (hx : (minpoly F x).Separable) (hy : (minpoly F y).Separable) :
    (minpoly F (x + y)).Separable :=
  haveI := isSeparable_adjoin_pair_of_separable F E hx hy
  separable_of_mem_isSeparable F E <| F⟮x, y⟯.add_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/-- If `x` is a separable element, then `x⁻¹` is also a separable element. -/
theorem separable_inv (x : E) (hx : (minpoly F x).Separable) : (minpoly F x⁻¹).Separable :=
  haveI := (isSeparable_adjoin_simple_iff_separable F E).2 hx
  separable_of_mem_isSeparable F E <| F⟮x⟯.inv_mem <| mem_adjoin_simple_self F x

end Field
