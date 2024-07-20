/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X` is an open subset
of a topological space that is covered by two open subsets `U` and `V`,
it is known that there is a long exact sequence
`... ⟶ H^q(X) ⟶ H^q(U) ⊞ H^q(V) ⟶ H^q(W) ⟶ H^{q+1}(X) ⟶ ...`
when `W` is the intersection of `U` and `V`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which contains the data
of a commutative square in a category `C` equipped with a Grothendieck
topology `J`, which share some properties with the square formed by
the open subsets `W`, `U`, `V`, `X` in the example above.
In particular, we require that the square become a pushout square
when it is understood as a square in the category of sheaves of sets.
We also require that `U ⟶ X` is a monomorphism. The morphism `V ⟶ X`
does not have to be a monomorphism, which shall allow the example
of Nisnevich distinguished squares in the case of the Nisnevich
topology on schemes (in which case `i : U ⟶ X` shall be an open
immersion and `j : V ⟶ X` an étale map that is an
isomorphism over the closed (reduced) subscheme `X - U`,
and `W` is the fibre product of `i` and `j`.).

## TODO
* show that when "evaluating" a sheaf on a Mayer-Vietoris
square, one obtains a pullback square
* provide constructors for `MayerVietorisSquare`

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe w v u

namespace CategoryTheory

open Limits Opposite

namespace Limits

namespace PullbackCone

variable {X Y Z }

end PullbackCone

end Limits

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrp.{v}]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `p ≫ i = q ≫ j` in `C`
such that `i` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare where
  /-- the object that is covered -/
  X : C
  /-- the first object of the covering -/
  U : C
  /-- the second object of the covering -/
  V : C
  /-- the top-left corner of the square -/
  W : C
  /-- the inclusion of `U` in `X` -/
  i : U ⟶ X
  /-- the morphism from `V` to `X` -/
  j : V ⟶ X
  /-- the morphism from `W` to `U` -/
  p : W ⟶ U
  /-- the morphism from `W` to `V` -/
  q : W ⟶ V
  fac : p ≫ i = q ≫ j
  hi : Mono i := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isColimit :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsColimit (PushoutCocone.mk
      (f := F.map p) (g := F.map q) (F.map i) (F.map j) (by
        simp only [← Functor.map_comp, fac]))

initialize_simps_projections MayerVietorisSquare (-isColimit)

namespace MayerVietorisSquare

variable {J}
variable (S : J.MayerVietorisSquare)

lemma isPushout :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) where
  w := by simp only [← Functor.map_comp, S.fac]
  isColimit' := ⟨S.isColimit⟩

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
