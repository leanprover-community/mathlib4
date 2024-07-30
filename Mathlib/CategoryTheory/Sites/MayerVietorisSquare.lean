/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X₄` is an open subset
of a topological space that is covered by two open subsets `X₂` and `X₃`,
it is known that there is a long exact sequence
`... ⟶ H^q(X₄) ⟶ H^q(X₂) ⊞ H^q(X₃) ⟶ H^q(X₁) ⟶ H^{q+1}(X₄) ⟶ ...`
where `X₁` is the intersection of `X₂` and `X₃`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which extends `Squace C`,
and asserts properties which shall imply the existence of long
exact Mayer-Vietoris sequences in sheaf cohomology (TODO).
We require that the map `X₁ ⟶ X₃` is a monomorphism and
that the square in `C` becomes a pushout square in
the category of sheaves after the application of the
functor `yoneda ⋙ presheafToSheaf J _`. Note that in the
standard case of a covering by two open subsets, all
the morphisms in the square would be monomorphisms,
but this dissymetry allows the example of Nisnevich distinguished
squares in the case of the Nisnevich topology on schemes (in which case
`f₂₄ : X₂ ⟶ X₄` shall be an open immersion and
`f₃₄ : X₃ ⟶ X₄` an étale map that is an isomorphism over
the closed (reduced) subscheme `X₄ - X₂`,
and `X₁` shall be the pullback of `f₂₄` and `f₃₄`.).

## TODO
* show that when "evaluating" a sheaf on a Mayer-Vietoris
square, one obtains a pullback square
* provide constructors for `MayerVietorisSquare`

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe v u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄` in `C`
such that `f₁₃` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare extends Square C where
  mono_f₁₃ : Mono toSquare.f₁₃ := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

end GrothendieckTopology

end CategoryTheory
