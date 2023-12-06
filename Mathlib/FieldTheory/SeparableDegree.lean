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

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Field.Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
  Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

- `Field.sepDegree F E`: the separable degree $[E:F]_s$ of an algebraic extension `E / F` of fields,
  defined to be the cardinal of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
  (Mathematically, it should be the algebraic closure of `F`, but in order to make the type
  compatible with `Module.rank F E`, we use the algebraic closure of `E`.)
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

- `Field.finSepDegree F E`: the separable degree $[E:F]_s$ of `E / F` as a natural number,
  which is zero if `Field.sepDegree F E` is not finite.

## Main results

- `Field.embEquivOfEquiv`, `Field.sepDegree_eq_of_equiv`, `Field.finSepDegree_eq_of_equiv`:
  a random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
  as `F`-algebras. In particular, they have the same cardinality (so their `Field.sepDegree` and
  `Field.finSepDegree` are equal).

- `Field.embEquivOfAdjoinSplits`, `Field.sepDegree_eq_of_adjoin_splits`,
  `Field.finSepDegree_eq_of_adjoin_splits`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F`
  and whose minimal polynomial splits in `K`. In particular, they have the same cardinality.

- `Field.embEquivOfIsAlgClosed`, `Field.sepDegree_eq_of_isAlgClosed`,
  `Field.finSepDegree_eq_of_isAlgClosed`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` when `E / F` is algebraic and `K / F` is algebraically closed.
  In particular, they have the same cardinality.

- `Field.embProdEmbOfIsAlgebraic`, `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`,
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic`,
  `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`:
  if `K / E / F` is a field extension tower, such that `K / E` is algebraic,
  then there is a non-canonical bijection `Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`.
  In particular, the separable degree satisfies the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see `lift_rank_mul_lift_rank`).

## Tags

separable degree, degree, polynomial

## TODO

- If `E / F` is a finite extension, then $[E:F]_s \mid [E:F]$. Thus we can define the inseparable
  degree $[E:F]_i$ to be $[E:F]$ divided by $[E:F]_s$.

- Define the separable degree of a polynomial over a field to be the number of distinct roots
  in algebraic closure, and prove that it's equal to `Polynomial.HasSeparableContraction.degree`.

- If `a` is an element algebraic over `F`, then $[F(a):F]_s$ is equal to the separable degree of
  the minimal polynomial of `a` over `F`. In particular, `a` is separable over `F` if and only if
  $[F(a):F]_s = [F(a):F]$.

- If `E / F` is a finite extension, then $[E:F]_s = [E:F]$ if and only if every element of `E` is
  separable over `F`, namely, `E / F` is a separable extension.

- As a corollary, if `S` is a subset of `E` consisting of separable elements, then `F(S) / F` is a
  separable extension.

- Define maximal separable subextension (or called relative separable closure)
  `separableClosure F E : IntermediateField F E` of `E / F`, and prove that its degree over `F`
  is $[E:F]_s$ if `E / F` is finite.

- Prove that `separableClosure F (AlgebraicClosure F)` is a separable closure of `F`.

- Prove that `[E:F]_s = 1` if and only if `E / F` is purely inseparable.

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

namespace Field

/-- `Field.Emb F E` is the type of `F`-algebra homomorphisms from `E` to the algebraic closure
of `E`. -/
def Emb := E →ₐ[F] AlgebraicClosure E

/-- If `E / F` is an algebraic extension, then the separable degree of `E / F`
is the number of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`.
Note that if `E / F` is not algebraic, then this definition makes no mathematical sense. -/
def sepDegree := Cardinal.mk (Emb F E)

/-- The separable degree of `E / F` as a natural number. -/
def finSepDegree : ℕ := Cardinal.toNat (sepDegree F E)

instance instNonemptyEmb : Nonempty (Emb F E) := ⟨IsScalarTower.toAlgHom F E _⟩

instance instNeZeroSepDegree : NeZero (sepDegree F E) := ⟨Cardinal.mk_ne_zero _⟩

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

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same separable degree
over `F`. -/
theorem sepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.lift.{v} (sepDegree F K) := by
  have := (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfEquiv F E K i) |>.trans
      (Equiv.ulift.{v} (α := Emb F K)).symm |>.cardinal_eq
  simpa only [Cardinal.mk_uLift] using this

/-- If `E` and `K` are isomorphic as `F`-algebras, then they have the same `Field.finSepDegree`
over `F`. -/
theorem finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finSepDegree F E = finSepDegree F K := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_equiv F E K i)

@[simp]
theorem sepDegree_self : sepDegree F F = 1 :=
  le_antisymm (Cardinal.le_one_iff_subsingleton.2 AlgHom.subsingleton)
    (Cardinal.one_le_iff_ne_zero.2 (instNeZeroSepDegree F F).out)

@[simp]
theorem finSepDegree_self : finSepDegree F F = 1 := by
  simp only [finSepDegree, sepDegree_self, Cardinal.one_toNat]

@[simp]
theorem sepDegree_bot : sepDegree F (⊥ : IntermediateField F E) = 1 := by
  have := sepDegree_eq_of_equiv _ _ _ (botEquiv F E)
  rwa [sepDegree_self, Cardinal.lift_one, ← Cardinal.lift_one.{u, v}, Cardinal.lift_inj] at this

@[simp]
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  simp only [finSepDegree, sepDegree_bot, Cardinal.one_toNat]

@[simp]
theorem sepDegree_top : sepDegree F (⊤ : IntermediateField F E) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv F _ E topEquiv

@[simp]
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField F E) = finSepDegree F E := by
  simp only [finSepDegree, sepDegree_top]

section

variable [Algebra E K] [IsScalarTower F E K]

theorem sepDegree_bot' : Cardinal.lift.{v} (sepDegree F (⊥ : IntermediateField E K)) =
    Cardinal.lift.{w} (sepDegree F E) :=
  sepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
theorem sepDegree_bot'' (K : Type v) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K] :
    sepDegree F (⊥ : IntermediateField E K) = sepDegree F E := by
  simpa only [Cardinal.lift_id] using sepDegree_bot' F E K

@[simp]
theorem finSepDegree_bot' : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat (sepDegree_bot' F E K)

@[simp]
theorem sepDegree_top' : sepDegree F (⊤ : IntermediateField E K) = sepDegree F K := by
  simpa only [Cardinal.lift_id] using sepDegree_eq_of_equiv _ _ _
    ((topEquiv (F := E) (E := K)).restrictScalars F)

@[simp]
theorem finSepDegree_top' : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K := by
  simp only [finSepDegree, sepDegree_top']

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

/-- The separable degree of `E / F` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
theorem sepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.mk (E →ₐ[F] K) := by
  simpa only [Cardinal.mk_uLift] using (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfAdjoinSplits F E K hS hK) |>.cardinal_eq

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K`
if `E = F(S)` such that every element
`s` of `S` is integral (= algebraic) over `F` and whose minimal polynomial splits in `K`. -/
theorem finSepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : ∀ s ∈ S, IsIntegral F s ∧ Splits (algebraMap F K) (minpoly F s)) :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_adjoin_splits F E K hS hK)

/-- A random bijection between `Field.Emb F E` and `E →ₐ[F] K` when `E / F` is algebraic
and `K / F` is algebraically closed. -/
def embEquivOfIsAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    Emb F E ≃ (E →ₐ[F] K) :=
  embEquivOfAdjoinSplits F E K (adjoin_univ F E) <| fun s _ ↦
    ⟨(halg s).isIntegral, IsAlgClosed.splits_codomain _⟩

/-- The separable degree of `E / F` is equal to the cardinality of `E →ₐ[F] K` when `E / F`
is algebraic and `K / F` is algebraically closed. -/
theorem sepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    Cardinal.lift.{w} (sepDegree F E) = Cardinal.mk (E →ₐ[F] K) := by
  simpa only [Cardinal.mk_uLift] using (Equiv.ulift.{w} (α := Emb F E)).trans
    (embEquivOfIsAlgClosed F E K halg) |>.cardinal_eq

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
theorem finSepDegree_eq_of_isAlgClosed (halg : Algebra.IsAlgebraic F E) [IsAlgClosed K] :
    finSepDegree F E = Cardinal.toNat (Cardinal.mk (E →ₐ[F] K)) := by
  simpa only [Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (sepDegree_eq_of_isAlgClosed F E K halg)

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

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then
$[E:F]_s [K:E]_s = [K:F]_s$. See also `lift_rank_mul_lift_rank`. -/
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
      Cardinal.lift.{v} (sepDegree F K) := by
  have := (embProdEmbOfIsAlgebraic F E K halg).trans
    (Equiv.ulift.{v} (α := Emb F K)).symm |>.cardinal_eq
  simpa only [Cardinal.mk_prod, Cardinal.mk_uLift] using this

/-- The same-universe version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`.
See also `rank_mul_rank`. -/
theorem sepDegree_mul_sepDegree_of_isAlgebraic
    (A : Type u) (B : Type u) [Field A] [Field B] [Algebra A B]
    (C : Type u) [Field C] [Algebra A C] [Algebra B C]
    [IsScalarTower A B C] (halg : Algebra.IsAlgebraic B C) :
    sepDegree A B * sepDegree B C = sepDegree A C := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic A B C halg

/-- The `Field.finSepDegree` version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`.
See also `FiniteDimensional.finrank_mul_finrank'`. -/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] (halg : Algebra.IsAlgebraic E K) :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  simpa only [Cardinal.toNat_mul, Cardinal.toNat_lift] using congr_arg Cardinal.toNat
    (lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K halg)

end Field
