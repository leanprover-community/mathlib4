/-
Copyright (c) 2024 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Chosen finite products in the category of affine schemes.

The category of affine schemes is known to have all limits and colimits, see
`AffineScheme.lean`. In this file, we construct a `ChosenFiniteProducts`
instance on the category of affine schemes using the tensor product. This gives
us access to a `MonoidalCategory` instance with good definitional properties:
In particluar, the product `X ⊗ Y` of two affine schemes is definitionally
equal to the spectrum of the tensor product of the global section rings of `X`
and `Y`, see `AffineScheme.tensorObj`, while the tensor unit `𝟙_ AffineScheme`
is definitionally equal to $Spec(ℤ)$, see `AffineScheme.tensorUnit`.

## Implementation notes

The terminal object $Spec(ℤ)$ naturally lives in `Type 0`, because `ℤ` does. To
have good definitional properties in all type universes, we provide one
instance for type universe zero, and one lower priority universe-polymorphic
instance, which includes `ULift`s.

-/

universe u

noncomputable section

open AlgebraicGeometry hiding Spec
open AffineScheme CategoryTheory Limits Opposite CommRingCat
open scoped MonoidalCategory TensorProduct

namespace AffineScheme

section
variable (X Y : AffineScheme.{u})

/-- The category of binary fans over `X` and `Y` (cones over `pair X Y`) is
equivalent to the category of cones over `(pair (Γ.obj (op X)) (Γ.obj (op
Y))).op ⋙ Spec`. This is needed in the `ChosenFiniteProducts` instance, since
we construct our limit cone by applying Spec to the colimit cocone given by the
tensor product `Γ.obj (op X) ⊗[ℤ] Γ.obj (op Y))`. -/
def chosen_finite_products_aux :
    Cone ((pair (Γ.obj (op X)) (Γ.obj (op Y))).op ⋙ Spec) ≌ BinaryFan X Y :=
  (Cones.whiskeringEquivalence (Discrete.opposite _)).symm.trans <| Cones.postcomposeEquivalence <|
    isoWhiskerLeft (Discrete.opposite WalkingPair).inverse
      (isoWhiskerRight (NatIso.op (pairComp (Γ.obj (op X)) (Γ.obj (op Y)) Spec.rightOp)).symm
        (unopUnop _)) ≪≫
    Discrete.natIso (fun ⟨j⟩ => by cases j <;> rfl) ≪≫
    mapPairIso X.isoSpec.symm Y.isoSpec.symm

instance : ChosenFiniteProducts AffineScheme.{0} where
  product (X Y : AffineScheme) := ⟨_, IsLimit.ofPreservesConeTerminal
    (chosen_finite_products_aux X Y).functor <|
    isLimitOfPreserves Spec <| IsColimit.op <| coproductCoconeIsColimit _ _⟩
  terminal := ⟨_, AffineScheme.specZIsTerminal⟩

instance (priority := 100) : ChosenFiniteProducts AffineScheme.{u} where
  product (X Y : AffineScheme) := ⟨_, IsLimit.ofPreservesConeTerminal
    (chosen_finite_products_aux X Y).functor <|
    isLimitOfPreserves Spec <| IsColimit.op <| coproductCoconeIsColimit _ _⟩
  terminal := ⟨_, AffineScheme.isTerminal⟩

lemma tensorObj : X ⊗ Y = Spec.obj (op (of (Γ.obj (op X) ⊗[ℤ] Γ.obj (op Y)))) := rfl

lemma tensorUnit_ULift : 𝟙_ AffineScheme.{u} = Spec.obj (op (of (ULift.{u} ℤ))) := rfl

lemma tensorUnit : 𝟙_ AffineScheme.{0} = Spec.obj (op (of ℤ)) := rfl
end

end AffineScheme
