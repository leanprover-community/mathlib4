/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Lie.Basic

/-!
# Lie algebras as non-unital, non-associative algebras

The definition of Lie algebras uses the `Bracket` typeclass for multiplication whereas we have a
separate `Mul` typeclass used for general algebras.

It is useful to have a special typeclass for Lie algebras because:
 * it enables us to use the traditional notation `⁅x, y⁆` for the Lie multiplication,
 * associative algebras carry a natural Lie algebra structure via the ring commutator and so we
   need them to carry both `Mul` and `Bracket` simultaneously,
 * more generally, Poisson algebras (not yet defined) need both typeclasses.

However there are times when it is convenient to be able to regard a Lie algebra as a general
algebra and we provide some basic definitions for doing so here.

## Main definitions

  * `CommutatorRing` turns a Lie ring into a `NonUnitalNonAssocSemiring` by turning its
    `Bracket` (denoted `⁅ , ⁆`) into a `Mul` (denoted `*`).
  * `LieHom.toNonUnitalAlgHom`

## Tags

lie algebra, non-unital, non-associative
-/


universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Type synonym for turning a `LieRing` into a `NonUnitalNonAssocSemiring`.

A `LieRing` can be regarded as a `NonUnitalNonAssocSemiring` by turning its
`Bracket` (denoted `⁅, ⁆`) into a `Mul` (denoted `*`). -/
def CommutatorRing (L : Type v) : Type v := L

/-- A `LieRing` can be regarded as a `NonUnitalNonAssocSemiring` by turning its
`Bracket` (denoted `⁅, ⁆`) into a `Mul` (denoted `*`). -/
instance : NonUnitalNonAssocSemiring (CommutatorRing L) :=
  show NonUnitalNonAssocSemiring L from
    { (inferInstance : AddCommMonoid L) with
      mul := Bracket.bracket
      left_distrib := lie_add
      right_distrib := add_lie
      zero_mul := zero_lie
      mul_zero := lie_zero }

namespace LieAlgebra

instance (L : Type v) [Nonempty L] : Nonempty (CommutatorRing L) := ‹Nonempty L›

instance (L : Type v) [Inhabited L] : Inhabited (CommutatorRing L) := ‹Inhabited L›

instance : LieRing (CommutatorRing L) := show LieRing L by infer_instance

instance : LieAlgebra R (CommutatorRing L) := show LieAlgebra R L by infer_instance

/-- Regarding the `LieRing` of a `LieAlgebra` as a `NonUnitalNonAssocSemiring`, we can
reinterpret the `smul_lie` law as an `IsScalarTower`. -/
instance isScalarTower : IsScalarTower R (CommutatorRing L) (CommutatorRing L) := ⟨smul_lie⟩

/-- Regarding the `LieRing` of a `LieAlgebra` as a `NonUnitalNonAssocSemiring`, we can
reinterpret the `lie_smul` law as an `SMulCommClass`. -/
instance smulCommClass : SMulCommClass R (CommutatorRing L) (CommutatorRing L) :=
  ⟨fun t x y => (lie_smul t x y).symm⟩

end LieAlgebra

namespace LieHom

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

/-- Regarding the `LieRing` of a `LieAlgebra` as a `NonUnitalNonAssocSemiring`, we can
regard a `LieHom` as a `NonUnitalAlgHom`. -/
@[simps]
def toNonUnitalAlgHom (f : L →ₗ⁅R⁆ L₂) : CommutatorRing L →ₙₐ[R] CommutatorRing L₂ :=
  { f with
    toFun := f
    map_zero' := f.map_zero
    map_mul' := f.map_lie }

theorem toNonUnitalAlgHom_injective :
    Function.Injective (toNonUnitalAlgHom : _ → CommutatorRing L →ₙₐ[R] CommutatorRing L₂) :=
  fun _ _ h => ext <| NonUnitalAlgHom.congr_fun h

end LieHom
