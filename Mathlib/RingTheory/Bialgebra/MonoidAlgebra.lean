/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

/-!
# The bialgebra structure on monoid algebras

Given a monoid `M`, a commutative semiring `R` and an `R`-bialgebra `A`, this file collects results
about the `R`-bialgebra instance on `A[M]` inherited from the corresponding structure on its
coefficients, building upon results in `Mathlib/RingTheory/Coalgebra/MonoidAlgebra.lean` about the
coalgebra structure.

## Main definitions

* `(Add)MonoidAlgebra.instBialgebra`: the `R`-bialgebra structure on `A[M]` when `M` is an (add)
  monoid and `A` is an `R`-bialgebra.
* `LaurentPolynomial.instBialgebra`: the `R`-bialgebra structure on the Laurent polynomials
  `A[T;T⁻¹]` when `A` is an `R`-bialgebra.
-/

@[expose] public section

noncomputable section

open Bialgebra

variable {R A M N O : Type*}

namespace MonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Monoid M] [Monoid N] [Monoid O]

variable (R A M) in
@[to_additive (dont_translate := R A)]
instance instBialgebra : Bialgebra R A[M] where
  counit_one := by simp only [one_def, counit_single, Bialgebra.counit_one]
  mul_compr₂_counit := by ext; simp
  comul_one := by
    simp only [one_def, comul_single, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, lsingle_apply]
  mul_compr₂_comul := by
    ext a b c d
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearMap.compr₂_apply,
      LinearMap.mul_apply', single_mul_single, comul_single, Bialgebra.comul_mul,
      ← (Coalgebra.Repr.arbitrary R b).eq, ← (Coalgebra.Repr.arbitrary R d).eq, Finset.sum_mul_sum,
      Algebra.TensorProduct.tmul_mul_tmul, map_sum, TensorProduct.map_tmul, lsingle_apply,
      LinearMap.compl₁₂_apply, LinearMap.coe_sum, Finset.sum_apply,
      Finset.sum_comm (s := (Coalgebra.Repr.arbitrary R b).index)]

set_option backward.isDefEq.respectTransparency false in
-- TODO: Generalise to `A[M] →ₐc[R] A[N]` under `Bialgebra R A`
variable (R) [AddMonoid M] [AddMonoid N] in
/-- If `f : M → N` is a monoid hom, then `AddMonoidAlgebra.mapDomain f` is a bialgebra hom between
their additive monoid algebras. -/
noncomputable def _root_.AddMonoidAlgebra.mapDomainBialgHom (f : M →+ N) :
    AddMonoidAlgebra R M →ₐc[R] AddMonoidAlgebra R N :=
  .ofAlgHom (AddMonoidAlgebra.mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

set_option backward.isDefEq.respectTransparency false in
-- TODO: Generalise to `A[M] →ₐc[R] A[N]` under `Bialgebra R A`
variable (R) in
/-- If `f : M → N` is a monoid hom, then `MonoidAlgebra.mapDomain f` is a bialgebra hom between
their monoid algebras. -/
@[to_additive existing (attr := simps!)]
noncomputable def mapDomainBialgHom (f : M →* N) : R[M] →ₐc[R] R[N] :=
  .ofAlgHom (mapDomainAlgHom R R f) (by ext; simp) (by ext; simp)

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
lemma mapDomainBialgHom_id : mapDomainBialgHom R (.id M) = .id R R[M] := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
lemma mapDomainBialgHom_comp (f : N →* O) (g : M →* N) :
    mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

@[to_additive]
lemma mapDomainBialgHom_mapDomainBialgHom (f : N →* O) (g : M →* N) (x : R[M]) :
    mapDomainBialgHom R f (mapDomainBialgHom R g x) = mapDomainBialgHom R (f.comp g) x := by
  ext; simp

end MonoidAlgebra

namespace AddMonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [AddMonoid M]

variable (R A M) in
/-- The bialgebra equivalence between `AddMonoidAlgebra` and `MonoidAlgebra` in terms of
`Multiplicative`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[simps! -isSimp]
def toMultiplicativeBialgEquiv : A[M] ≃ₐc[R] MonoidAlgebra A (Multiplicative M) :=
  .ofAlgEquiv (toMultiplicativeAlgEquiv R A M) (by ext <;> simp) <| by
    ext a
    · simp [Algebra.TensorProduct.one_def]
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
lemma toMultiplicativeBialgEquiv_single (m : M) (a : A) :
    toMultiplicativeBialgEquiv R A M (single m a) = .single (.ofAdd m) a := by
  simp [toMultiplicativeBialgEquiv]

end AddMonoidAlgebra

namespace MonoidAlgebra
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Monoid M]

variable (R A M) in
/-- The bialgebra equivalence between `MonoidAlgebra` and `AddMonoidAlgebra` in terms of
`Additive`. -/
-- TODO: Make `BialgEquiv.toCoalgEquiv` the simp normal form so that this can be simp
@[simps! -isSimp]
def toAdditiveBialgEquiv : A[M] ≃ₐc[R] AddMonoidAlgebra A (Additive M) :=
  .ofAlgEquiv (toAdditiveAlgEquiv R A M) (by ext <;> simp) <| by
    ext a
    · simp [Algebra.TensorProduct.one_def]
    · simp [← (Coalgebra.Repr.arbitrary R a).eq]

@[simp]
lemma toAdditiveBialgEquiv_single (m : M) (a : A) :
    toAdditiveBialgEquiv R A M (single m a) = .single (.ofMul m) a := by
  simp [toAdditiveBialgEquiv]

end MonoidAlgebra

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]

instance instBialgebra : Bialgebra R A[T;T⁻¹] :=
  inferInstanceAs <| Bialgebra R A[ℤ]

@[simp]
theorem comul_T (n : ℤ) :
    Coalgebra.comul (R := R) (T n : A[T;T⁻¹]) = T n ⊗ₜ[R] T n := by
  simp [T, -single_eq_C_mul_T, Algebra.TensorProduct.one_def]

@[simp]
theorem counit_T (n : ℤ) :
    Coalgebra.counit (R := R) (T n : A[T;T⁻¹]) = 1 := by
  simp [T, -single_eq_C_mul_T]

end LaurentPolynomial
