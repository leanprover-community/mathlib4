/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.MvPolynomial.Basic

#align_import data.mv_polynomial.counit from "leanprover-community/mathlib"@"abb3121f210743a930dea73cd766d988079bdf8b"

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `MvPolynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `MvPolynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `MvPolynomial.ACounit R A` is the natural surjective algebra homomorphism
  `MvPolynomial A R →ₐ[R] A` obtained by `X a ↦ a`
* `MvPolynomial.counit` is an “absolute” variant with `R = ℤ`
* `MvPolynomial.counitNat` is an “absolute” variant with `R = ℕ`

-/


namespace MvPolynomial

open Function

variable (A B R : Type*) [CommSemiring A] [CommSemiring B] [CommRing R] [Algebra A B]

/-- `MvPolynomial.ACounit A B` is the natural surjective algebra homomorphism
`MvPolynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`,
and `MvPolynomial.counitNat` for the “absolute” variant with `A = ℕ`. -/
noncomputable def ACounit : MvPolynomial B A →ₐ[A] B :=
  aeval id
#align mv_polynomial.acounit MvPolynomial.ACounit

variable {B}

@[simp]
theorem ACounit_X (b : B) : ACounit A B (X b) = b :=
  aeval_X _ b
set_option linter.uppercaseLean3 false in
#align mv_polynomial.acounit_X MvPolynomial.ACounit_X

variable {A} (B)

@[simp]
theorem ACounit_C (a : A) : ACounit A B (C a) = algebraMap A B a :=
  aeval_C _ a
set_option linter.uppercaseLean3 false in
#align mv_polynomial.acounit_C MvPolynomial.ACounit_C

variable (A)

theorem ACounit_surjective : Surjective (ACounit A B) := fun b => ⟨X b, ACounit_X A b⟩
#align mv_polynomial.acounit_surjective MvPolynomial.ACounit_surjective

/-- `MvPolynomial.counit R` is the natural surjective ring homomorphism
`MvPolynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base ring,
and `MvPolynomial.counitNat` for the “absolute” variant with `R = ℕ`. -/
noncomputable def counit : MvPolynomial R ℤ →+* R :=
  (ACounit ℤ R).toRingHom
#align mv_polynomial.counit MvPolynomial.counit

/-- `MvPolynomial.counitNat A` is the natural surjective ring homomorphism
`MvPolynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `MvPolynomial.ACounit` for a “relative” variant for algebras over a base ring
and `MvPolynomial.counit` for the “absolute” variant with `A = ℤ`. -/
noncomputable def counitNat : MvPolynomial A ℕ →+* A :=
  ACounit ℕ A
#align mv_polynomial.counit_nat MvPolynomial.counitNat

theorem counit_surjective : Surjective (counit R) :=
  ACounit_surjective ℤ R
#align mv_polynomial.counit_surjective MvPolynomial.counit_surjective

theorem counitNat_surjective : Surjective (counitNat A) :=
  ACounit_surjective ℕ A
#align mv_polynomial.counit_nat_surjective MvPolynomial.counitNat_surjective

theorem counit_C (n : ℤ) : counit R (C n) = n :=
  ACounit_C _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.counit_C MvPolynomial.counit_C

theorem counitNat_C (n : ℕ) : counitNat A (C n) = n :=
  ACounit_C _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.counit_nat_C MvPolynomial.counitNat_C

variable {R A}

@[simp]
theorem counit_X (r : R) : counit R (X r) = r :=
  ACounit_X _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.counit_X MvPolynomial.counit_X

@[simp]
theorem counitNat_X (a : A) : counitNat A (X a) = a :=
  ACounit_X _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.counit_nat_X MvPolynomial.counitNat_X

end MvPolynomial
