/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.Extension.Basic
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Loop Lie algebras and their central extensions

Given a Lie algebra `L`, the loop algebra is the Lie algebra of maps from a circle into `L`. This
can mean many different things, e.g., continuous maps, smooth maps, polynomial maps. In this file,
we consider the simplest case of polynomial maps, meaning we take a base change with the ring of
Laurent polynomials.

Representations of loop algebras are not particularly interesting - a theorem of Rao (1993) asserts
that when `L` is complex semisimple, any irreducible representation of `L[z,z^{-1}]` is just given
by evaluation of loops at a finite set of specific points. However, the theory becomes much richer
when one considers projective representations, i.e., representations of a central extension. Common
examples include generalized Verma modules, given by pulling a representation of `L` back to a
representation of `L[z] ⊕ C` along the homomorphism `z ↦ 0` together with a central character, and
inducing to the central extension of the loop algebra.


## Main definitions

* Loop Algebra
* Evaluation representation
* Construction of central extensions from invariant forms. (todo)
* representation with fixed central character (todo)
* Positive energy representation (todo)

## Tags

lie ring, lie algebra, base change, Laurent polynomial, central extension
-/

suppress_compilation

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- A loop algebra is the base change of a Lie algebra `L` over `R` by `R[z,z^{-1}]`, seen
as a Lie algebra over `R`. -/
abbrev LoopAlgebra := RestrictScalars R (LaurentPolynomial R) (LaurentPolynomial R ⊗[R] L)

namespace Loop

instance instLieRing : LieRing (LoopAlgebra R L) :=
  ExtendScalars.instLieRing R (LaurentPolynomial R) L

instance instLieAlgebra : LieAlgebra R (LoopAlgebra R L) :=
  LieAlgebra.RestrictScalars.lieAlgebra R (LaurentPolynomial R) (LaurentPolynomial R ⊗[R] L)

-- I need a way to construct linear maps out of LoopAlgebra, by specifying the map on
-- `x ⊗ T ^ n` for `x ∈ L`.  Maybe first a lemma saying LoopAlgebra is spanned by such things.

/-!
/-- The evaluation representation, given by composing a representation with the evaluation map
`L[z,z^{-1}] → L` attached to a unit in `R`. -/
--define eval (x : Units R) : (LoopAlgebra R L) →ₗ⁅R⁆ L where
  toFun l := sorry
  map_add' := sorry
  map_smul' := sorry
  map_lie' := sorry

/-- The evaluation module -/
-- define eval.LieModule
-/

section CentralExt
/-!
/-- The residue pairing on a Loop algebra. -/
def residuePairing (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) :
    (LoopAlgebra R L) →ₗ[R] (LoopAlgebra R L) →ₗ[R] R where
  toFun f := {
    toFun := fun g => by

      sorry -- Res_{z = 0} f dg.
    map_add' := sorry
    map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- A 2-cocycle on a loop algebra given by an invariant bilinear form. -/
def twoCocycle_of_Bilinear (Φ : LinearMap.BilinForm R L)
    (hΦ : LinearMap.BilinForm.lieInvariant L Φ) :
    LieExtension.twoCocycleTriv R (LoopAlgebra R L) R where
  toFun := sorry -- residue pairing
  map_eq_zero_of_eq' := sorry
  cocycle := sorry

--⁅A ⊗ f(t), B ⊗ g(t)⁆ = ⁅A,B⁆ ⊗ f(t)*g(t) + (Res fdg) * (A,B) • K
-/
-- show that an invariant bilinear form on `L` produces a 2-cocycle for `LoopAlgebra R L`.
-- define central extensions given by invariant bilinear forms
-- extend central characters to reps of positive part
-- induce positive part reps to centrally extended loop algebra
-- monomial basis of induced rep (needs PBW)
-- define positive energy reps (positive part `U+` acts locally nilpotently - `U+ • v` fin dim.)

end CentralExt

end Loop

end LieAlgebra
