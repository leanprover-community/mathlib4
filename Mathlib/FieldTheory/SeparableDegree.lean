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
  for a general algebraic extension `E / F` is defined to be the degree of `L / F`, where `L` is
  the (relative) separable closure `separableClosure F E` of `F` in `E`, which is not defined in
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

instance instInhabitedEmb : Inhabited (Emb F E) := ⟨IsScalarTower.toAlgHom F E _⟩

instance instNeZeroFinSepDegree [FiniteDimensional F E] : NeZero (finSepDegree F E) :=
  ⟨Nat.card_ne_zero.2 ⟨inferInstance, Fintype.finite <| minpoly.AlgHom.fintype _ _ _⟩⟩

/-- A random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
as `F`-algebras. -/
def embEquivOfEquiv (i : E ≃ₐ[F] K) :
    Emb F E ≃ Emb F K := AlgEquiv.arrowCongr i <| AlgEquiv.symm <| by
  let _ : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic E K := by
    constructor
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
    rw [show ∀ y : E, (algebraMap E K) y = i.toAlgHom y from fun y ↦ rfl] at h
    simpa only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.apply_symm_apply] using h
  apply AlgEquiv.restrictScalars (R := F) (S := E)
  exact IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)

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
Combined with `Field.instInhabitedEmb`, it can be viewed as a stronger version of
`IntermediateField.nonempty_algHom_of_adjoin_splits`. -/
def embEquivOfAdjoinSplits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    Emb F E ≃ (E →ₐ[F] K) :=
  have : Algebra.IsAlgebraic F (⊤ : IntermediateField F E) :=
    (hS ▸ isAlgebraic_adjoin (S := S) fun x hx ↦ (hK x hx).1)
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
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
def embEquivOfIsAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) :=
  embEquivOfAdjoinSplits F E K (adjoin_univ F E) fun s _ ↦
    ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits_codomain _⟩

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
theorem finSepDegree_eq_of_isAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    finSepDegree F E = Nat.card (E →ₐ[F] K) := Nat.card_congr (embEquivOfIsAlgClosed F E K)

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic,
then there is a non-canonical bijection
`Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`. A corollary of `algHomEquivSigma`. -/
def embProdEmbOfIsAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K] :
    Emb F E × Emb E K ≃ Emb F K :=
  let e : ∀ f : E →ₐ[F] AlgebraicClosure K,
      @AlgHom E K _ _ _ _ _ f.toRingHom.toAlgebra ≃ Emb E K := fun f ↦
    (@embEquivOfIsAlgClosed E K _ _ _ _ _ f.toRingHom.toAlgebra).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
    (Equiv.sigmaEquivProdOfEquiv e) |>.trans <| Equiv.prodCongrLeft <|
      fun _ : Emb E K ↦ AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _) <|
        (IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K)
          (AlgebraicClosure E)).restrictScalars F).symm

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then their
separable degrees satisfy the tower law
$[E:F]_s [K:E]_s = [K:F]_s$. See also `FiniteDimensional.finrank_mul_finrank`. -/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K] :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  simpa only [Nat.card_prod] using Nat.card_congr (embProdEmbOfIsAlgebraic F E K)

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
    Multiset.toFinset_map, Finset.card_image_of_injective _ (RingHom.injective _), natSepDegree]

variable (E) in
/-- The separable degree of a polynomial is equal to
the number of distinct roots of it over any algebraically closed field. -/
theorem natSepDegree_eq_of_isAlgClosed [IsAlgClosed E] :
    f.natSepDegree = (f.aroots E).toFinset.card :=
  natSepDegree_eq_of_splits f (IsAlgClosed.splits_codomain f)

variable (E) in
theorem natSepDegree_map : (f.map (algebraMap F E)).natSepDegree = f.natSepDegree := by
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure E), aroots_def, map_map,
    ← IsScalarTower.algebraMap_eq]

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

theorem natSepDegree_pow_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (f ^ n).natSepDegree = f.natSepDegree := by simp_rw [natSepDegree_pow, hn, ite_false]

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

theorem natSepDegree_mul_eq_iff (g : F[X]) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree ↔ (f = 0 ∧ g = 0) ∨ IsCoprime f g := by
  by_cases h : f * g = 0
  · rw [mul_eq_zero] at h
    wlog hf : f = 0 generalizing f g
    · simpa only [mul_comm, add_comm, and_comm,
        isCoprime_comm] using this g f h.symm (h.resolve_left hf)
    rw [hf, zero_mul, natSepDegree_zero, zero_add, isCoprime_zero_left, isUnit_iff, eq_comm,
      natSepDegree_eq_zero_iff, natDegree_eq_zero]
    refine ⟨fun ⟨x, h⟩ ↦ ?_, ?_⟩
    · by_cases hx : x = 0
      · exact .inl ⟨rfl, by rw [← h, hx, map_zero]⟩
      exact .inr ⟨x, Ne.isUnit hx, h⟩
    rintro (⟨-, h⟩ | ⟨x, -, h⟩)
    · exact ⟨0, by rw [h, map_zero]⟩
    exact ⟨x, h⟩
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add,
    Finset.card_union_eq_card_add_card, Finset.disjoint_iff_ne, Multiset.mem_toFinset, mem_aroots]
  rw [mul_eq_zero, not_or] at h
  refine ⟨fun H ↦ .inr (isCoprime_of_irreducible_dvd (not_and.2 fun _ ↦ h.2)
    fun u hu ⟨v, hf⟩ ⟨w, hg⟩ ↦ ?_), ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero
      (AlgebraicClosure F) _ (degree_pos_of_irreducible hu).ne'
    exact H x ⟨h.1, by simpa only [map_mul, hx, zero_mul] using congr(aeval x $hf)⟩
      x ⟨h.2, by simpa only [map_mul, hx, zero_mul] using congr(aeval x $hg)⟩ rfl
  rintro (⟨rfl, rfl⟩ | hc)
  · exact (h.1 rfl).elim
  rintro x hf _ hg rfl
  obtain ⟨u, v, hfg⟩ := hc
  simpa only [map_add, map_mul, map_one, hf.2, hg.2, mul_zero, add_zero,
    zero_ne_one] using congr(aeval x $hfg)

theorem natSepDegree_mul_of_isCoprime (g : F[X]) (hc : IsCoprime f g) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree :=
  (natSepDegree_mul_eq_iff f g).2 (.inr hc)

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

theorem natSepDegree_X_pow_char_pow_sub_C (q : ℕ) [ExpChar F q] (n : ℕ) (y : F) :
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
  simp_rw [hi.natSepDegree_eq_one_iff_of_monic' q hm, map_sub, expand_X, expand_C]

end Irreducible

namespace Polynomial

namespace Monic

variable {F}
variable {f : F[X]}

alias natSepDegree_eq_one_iff_of_irreducible' := Irreducible.natSepDegree_eq_one_iff_of_monic'

alias natSepDegree_eq_one_iff_of_irreducible := Irreducible.natSepDegree_eq_one_iff_of_monic

/-- If a monic polynomial of separable degree one splits, then it is of form `(X - C y) ^ m` for
some non-zero natural number `m` and some element `y` of `F`. -/
theorem eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits (hm : f.Monic)
    (hs : f.Splits (RingHom.id F))
    (h : f.natSepDegree = 1) : ∃ (m : ℕ) (y : F), m ≠ 0 ∧ f = (X - C y) ^ m := by
  have h1 := eq_prod_roots_of_monic_of_splits_id hm hs
  have h2 := (natSepDegree_eq_of_splits f hs).symm
  rw [h, aroots_def, Algebra.id.map_eq_id, map_id, Multiset.toFinset_card_eq_one_iff] at h2
  obtain ⟨h2, y, h3⟩ := h2
  exact ⟨_, y, h2, by rwa [h3, Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
    Multiset.prod_singleton] at h1⟩

/-- If a monic irreducible polynomial over a field `F` of exponential characteristic `q` has
separable degree one, then it is of the form `X ^ (q ^ n) - C y` for some natural number `n`,
and some element `y` of `F`, such that either `n = 0` or `y` has no `q`-th root in `F`. -/
theorem eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible (q : ℕ) [ExpChar F q]
    (hm : f.Monic) (hi : Irreducible f) (h : f.natSepDegree = 1) : ∃ (n : ℕ) (y : F),
      (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = X ^ q ^ n - C y := by
  obtain ⟨n, y, hf⟩ := (hm.natSepDegree_eq_one_iff_of_irreducible q hi).1 h
  cases id ‹ExpChar F q› with
  | zero =>
    simp_rw [one_pow, pow_one] at hf ⊢
    exact ⟨0, y, .inl rfl, hf⟩
  | prime hq =>
    refine ⟨n, y, (em _).imp id fun hn ⟨z, hy⟩ ↦ ?_, hf⟩
    haveI := expChar_of_injective_ringHom (R := F) C_injective q
    rw [hf, ← Nat.succ_pred hn, pow_succ, pow_mul, ← hy, frobenius_def, map_pow,
      ← sub_pow_expChar] at hi
    exact not_irreducible_pow hq.ne_one hi

/-- If a monic polynomial over a field `F` of exponential characteristic `q` has separable degree
one, then it is of the form `(X ^ (q ^ n) - C y) ^ m` for some non-zero natural number `m`,
some natural number `n`, and some element `y` of `F`, such that either `n = 0` or `y` has no
`q`-th root in `F`. -/
theorem eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one (q : ℕ) [ExpChar F q] (hm : f.Monic)
    (h : f.natSepDegree = 1) : ∃ (m n : ℕ) (y : F),
      m ≠ 0 ∧ (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = (X ^ q ^ n - C y) ^ m := by
  obtain ⟨p, hM, hI, hf⟩ := exists_monic_irreducible_factor _ <| not_isUnit_of_natDegree_pos _
    <| Nat.pos_of_ne_zero <| (natSepDegree_ne_zero_iff _).1 (h.symm ▸ Nat.one_ne_zero)
  have hD := (h ▸ natSepDegree_le_of_dvd p f hf hm.ne_zero).antisymm <|
    Nat.pos_of_ne_zero <| (natSepDegree_ne_zero_iff _).2 hI.natDegree_pos.ne'
  obtain ⟨n, y, H, hp⟩ := hM.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible q hI hD
  have hF := multiplicity_finite_of_degree_pos_of_monic (degree_pos_of_irreducible hI) hM hm.ne_zero
  have hne := (multiplicity.pos_of_dvd hF hf).ne'
  refine ⟨_, n, y, hne, H, ?_⟩
  obtain ⟨c, hf, H⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd hF
  rw [hf, natSepDegree_mul_of_isCoprime _ c <| IsCoprime.pow_left <|
    (hI.coprime_or_dvd c).resolve_right H, natSepDegree_pow_of_ne_zero _ hne, hD,
    add_right_eq_self, natSepDegree_eq_zero_iff] at h
  simpa only [eq_one_of_monic_natDegree_zero ((hM.pow _).of_mul_monic_left (hf ▸ hm)) h,
    mul_one, ← hp] using hf

/-- A monic polynomial over a field `F` of exponential characteristic `q` has separable degree one
if and only if it is of the form `(X ^ (q ^ n) - C y) ^ m` for some non-zero natural number `m`,
some natural number `n`, and some element `y` of `F`. -/
theorem natSepDegree_eq_one_iff (q : ℕ) [ExpChar F q] (hm : f.Monic) :
    f.natSepDegree = 1 ↔ ∃ (m n : ℕ) (y : F), m ≠ 0 ∧ f = (X ^ q ^ n - C y) ^ m := by
  refine ⟨fun h ↦ ?_, fun ⟨m, n, y, hm, h⟩ ↦ ?_⟩
  · obtain ⟨m, n, y, hm, -, h⟩ := hm.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one q h
    exact ⟨m, n, y, hm, h⟩
  simp_rw [h, natSepDegree_pow, hm, ite_false, natSepDegree_X_pow_char_pow_sub_C]

end Monic

end Polynomial

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
theorem natSepDegree_eq_one_iff_pow_mem : (minpoly F x).natSepDegree = 1 ↔
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  convert_to _ ↔ ∃ (n : ℕ) (y : F), Polynomial.aeval x (X ^ q ^ n - C y) = 0
  · simp_rw [RingHom.mem_range, map_sub, map_pow, aeval_C, aeval_X, sub_eq_zero, eq_comm]
  refine ⟨fun h ↦ ?_, fun ⟨n, y, h⟩ ↦ ?_⟩
  · obtain ⟨n, y, hx⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    exact ⟨n, y, hx ▸ aeval F x⟩
  have hnezero := X_pow_sub_C_ne_zero (expChar_pow_pos F q n) y
  refine ((natSepDegree_le_of_dvd _ _ (minpoly.dvd F x h) hnezero).trans_eq <|
    natSepDegree_X_pow_char_pow_sub_C q n y).antisymm ?_
  rw [Nat.one_le_iff_ne_zero, natSepDegree_ne_zero_iff, ← Nat.one_le_iff_ne_zero]
  exact minpoly.natDegree_pos <| IsAlgebraic.isIntegral ⟨_, hnezero, h⟩

/-- The minimal polynomial of an element `x` of `E / F` of exponential characteristic `q` has
separable degree one if and only if the minimal polynomial is of the form
`(X - x) ^ (q ^ n)` for some `n : ℕ`. -/
theorem natSepDegree_eq_one_iff_eq_X_sub_C_pow : (minpoly F x).natSepDegree = 1 ↔
    ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  haveI := expChar_of_injective_algebraMap (NoZeroSMulDivisors.algebraMap_injective E E[X]) q
  refine ⟨fun h ↦ ?_, fun ⟨n, h⟩ ↦ (natSepDegree_eq_one_iff_pow_mem q).2 ?_⟩
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
  rw [this, Nat.card_eq_fintype_card, natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯),
    ← Fintype.card_coe]
  simp_rw [Multiset.mem_toFinset]

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
    have := Algebra.IsAlgebraic.of_finite L M
    rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M,
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
    obtain ⟨L, h, h'⟩ := exists_lt_finrank_of_infinite_dimensional hfd (finSepDegree F E)
    have : IsSeparable F L := isSeparable_tower_bot_of_isSeparable F L E
    have := (halg.tower_top L)
    have hd := finSepDegree_mul_finSepDegree_of_isAlgebraic F L E
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
  have := Algebra.IsAlgebraic.of_finite L M
  rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M,
    FiniteDimensional.finrank_mul_finrank F L M] at heq

alias _root_.IsSeparable.finSepDegree_eq := finSepDegree_eq_finrank_of_isSeparable

/-- If `E / F` is a finite extension, then its separable degree is equal to its degree if and
only if it is a separable extension. -/
theorem finSepDegree_eq_finrank_iff [FiniteDimensional F E] :
    finSepDegree F E = finrank F E ↔ IsSeparable F E :=
  ⟨fun heq ↦ ⟨fun x ↦ by
    have halg := IsAlgebraic.of_finite F x
    refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 <| le_antisymm
      (finSepDegree_adjoin_simple_le_finrank F E x halg) <| le_of_not_lt fun h ↦ ?_
    have := Nat.mul_lt_mul_of_lt_of_le' h (finSepDegree_le_finrank F⟮x⟯ E) Fin.size_pos'
    rw [finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E,
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
  set f := minpoly E x with hf
  let E' : IntermediateField F E := adjoin F f.coeffs
  haveI : FiniteDimensional F E' := finiteDimensional_adjoin fun x _ ↦ IsSeparable.isIntegral F x
  let g : E'[X] := f.toSubring E'.toSubring (subset_adjoin F _)
  have h : g.map (algebraMap E' E) = f := f.map_toSubring E'.toSubring (subset_adjoin F _)
  clear_value g
  have hx : x ∈ restrictScalars F E'⟮x⟯ := mem_adjoin_simple_self _ x
  have hzero : aeval x g = 0 := by
    simpa only [← hf, ← h, aeval_map_algebraMap] using minpoly.aeval E x
  have halg : IsIntegral E' x :=
    isIntegral_trans (R := F) (A := E) _ hsep.isIntegral |>.tower_top
  simp_rw [← h, separable_map] at hsep
  replace hsep := hsep.of_dvd <| minpoly.dvd _ _ hzero
  haveI : IsSeparable F E' := isSeparable_tower_bot_of_isSeparable F E' E
  haveI := (isSeparable_adjoin_simple_iff_separable _ _).2 hsep
  haveI := adjoin.finiteDimensional halg
  haveI : FiniteDimensional F E'⟮x⟯ := FiniteDimensional.trans F E' E'⟮x⟯
  have : Algebra.IsAlgebraic E' E'⟮x⟯ := IsSeparable.isAlgebraic _ _
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F E' E'⟮x⟯
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

/-- A field is a perfect field (which means that any irreducible polynomial is separable)
if and only if every separable degree one polynomial splits. -/
theorem perfectField_iff_splits_of_natSepDegree_eq_one (F : Type*) [Field F] :
    PerfectField F ↔ ∀ f : F[X], f.natSepDegree = 1 → f.Splits (RingHom.id F) := by
  refine ⟨fun ⟨h⟩ f hf ↦ or_iff_not_imp_left.2 fun hn g hg hd ↦ ?_, fun h ↦ ?_⟩
  · rw [map_id] at hn hd
    have := natSepDegree_le_of_dvd g f hd hn
    rw [hf, (h hg).natSepDegree_eq_natDegree] at this
    exact (degree_eq_iff_natDegree_eq_of_pos one_pos).2 <| this.antisymm <|
      natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hg)
  obtain ⟨p, _⟩ := ExpChar.exists F
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, hy⟩ := exists_root_of_splits _
      (h _ (pow_one p ▸ natSepDegree_X_pow_char_pow_sub_C p 1 x))
      ((degree_X_pow_sub_C (expChar_pos F p) x).symm ▸ Nat.cast_pos.2 (expChar_pos F p)).ne'
    exact ⟨y, by rwa [← eval, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy⟩
  exact PerfectRing.toPerfectField F p
