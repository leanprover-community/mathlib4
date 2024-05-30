/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib

noncomputable section -- Much of the category theory library is noncomputable,
                      -- so lets get this out of the way at the beginning!

/-!
# Category theory in Mathlib

* Basics
* Constructing functors
  * Forgetful functors
  * Free commutative ring on a type
  * Abelianization of a group
* Constructing the category of pointed spaces
  * Prove the equivalence between `PointedSpace` and `Under (TopCat.of Unit)`

* Advanced topics:
  * Schemes
  * Setting up singular homology
-/

/-!
## Basics
-/

/-!
Much of Mathlib happily takes over the root namespace.
Category theory is nearly all in the `CategoryTheory` namespace, so we need:
-/
open CategoryTheory

section

/-! To talk about an arbitrary category, we write something like: -/
variable (C : Type) [Category C]

/-- We start by proving an easy fact:

If the two squares in
```
  X₁ --f₁--> X₂ --f₂--> X₃
  |          |          |
  g₁         g₂         g₃
  |          |          |
  v          v          v
  Y₁ --h₁--> Y₂ --h₂--> Y₃
```
commutes, then the outer rectangle commutes as well.
-/
example {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {g₁ : X₁ ⟶ Y₁} {g₂ : X₂ ⟶ Y₂} {g₃ : X₃ ⟶ Y₃}
    {h₁ : Y₁ ⟶ Y₂} {h₂ : Y₂ ⟶ Y₃}
    (comm₁ : g₁ ≫ h₁ = f₁ ≫ g₂) (comm₂ : g₂ ≫ h₂ = f₂ ≫ g₃) :
    g₁ ≫ h₁ ≫ h₂ = f₁ ≫ f₂ ≫ g₃ := by
  sorry

/-!
For people who've already seen this, here are two alternative proofs of the same fact:
```
  simp [reassoc_of% comm₁, comm₂]
```
or
```
  slice_lhs 1 2 => rw [comm₁]
  slice_lhs 2 3 => rw [comm₂]
```
How do these work?
-/

end

/-!
## Constructing functors.
-/

/-!
Sometimes we want to talk about the category consisting of all algebraic structures of some flavour.
Most of these are set up already in Mathlib.

Typically, for each algebraic typeclass `Foo`, there is a category `FooCat` of "bundled foos",
i.e. a pair consisting of a type, and the typeclass instance for it.
-/

/-- Let's build the forgetful functor from commutative rings to rings. -/
def forget : CommRingCat ⥤ RingCat where
  obj R := sorry
  map f := sorry

-- Why didn't we need to prove anything about this actually being functorial
-- (preserving identities and composition)?
-- Most categorical structures in Mathlib are set up so that the proof fields have a default value
-- which will be filled in by tactics. Since most proofs in category theory are really boring,
-- this saves us a lot of typing! A lot of the design of the category theory library is based around
-- making this automation effective.
-- If we want to provide the functoriality proofs by hand we can:
def forget' : CommRingCat ⥤ RingCat where
  obj R := RingCat.of R
  map f := f
  map_id := sorry
  map_comp := sorry

/-!
### Example: the free commutative ring on a type.

This should send each `X : Type` to
multivariable polynomials with integer coefficients in `X` variables.

A function between types `X → Y` should induce a ring homomorphism given be renaming variables.
-/

example : Type ⥤ CommRingCat where
  obj X := CommRingCat.of (MvPolynomial X ℤ)
  map {X Y} f := sorry





/-!
### Example: the abelianization of a group.

We send each group to it abelianization.

Given a morphism `G → H` of groups, we can build a morphism `Abelianization G ⟶ Abelianization H`
using the adjunction `Abelianization.lift : (G →* A) ≃ (Abelianization G →* A)` and
the projection `Abelianization.of : G →* Abelianization G`.
-/

def abelianize : GroupCat ⥤ CommGroupCat where
  obj G := sorry
  map f := sorry

/-!
## Example: Constructing the category of pointed spaces.
-/

/--
A `PointedSpace` consists of
* an underlying type `X`
* the topological space structure on `X`
* and a distinguished point `base : X`.
-/
structure PointedSpace where
  -- TODO

namespace PointedSpace

/--
A morphism of `PointedSpace`s is a continuous map between the underlying topological spaces,
which takes the base point to the base point.
-/
structure Hom (X Y : PointedSpace) where
  -- TODO

namespace Hom

/-- The identity morphism on a `PointedSpace`. -/
def id (X : PointedSpace) : Hom X X := sorry

/-- Composition of morphisms of `PointedSpace`s. -/
def comp {X Y Z : PointedSpace} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
   sorry

end Hom

instance : Category PointedSpace where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  -- 🎉 No proofs required!

end PointedSpace

/-!
### We next construct the equivalence between `PointedSpace` and `Under (TopCat.of Unit)`.

`Under (TopCat.of Unit)` means "topological spaces equipped with a map from the one-point space".
-/

-- We'll use
#check Under.mk -- Under.mk (f : P ⟶ Q) : Under P
#check Under.homMk -- Under.homMk (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom) : U ⟶ V

/-- The forward direction. -/
def PointedSpaceEquiv_functor : PointedSpace ⥤ Under (TopCat.of Unit) where
  obj := fun X => sorry
  map := fun f => sorry

/-- The reverse direction. -/
def PointedSpaceEquiv_inverse : Under (TopCat.of Unit) ⥤ PointedSpace where
  obj := fun X =>
  { carrier := X.right
    base := X.hom () }
  map := fun f =>
  { map := f.right
    base := by
      -- Our first proof today!
      -- We just need to take `f.w`, which is an equation of continuous maps,
      -- and evaluate both sides at the unique point in `TopCat.of Unit`,
      -- and then massage things into shape.
      sorry }

/-- Putting it all together. -/
def equiv : PointedSpace ≌ Under (TopCat.of Unit) where
  functor := PointedSpaceEquiv_functor
  inverse := PointedSpaceEquiv_inverse
  unitIso := NatIso.ofComponents fun X => Iso.refl _ -- 🎉 naturality is checked by automation
  counitIso := NatIso.ofComponents fun X => Iso.refl _
  -- 🎉 the triangle identity is checked by automation!
