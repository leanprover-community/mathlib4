/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheaves on Over categories, as a pseudofunctor

Given a Grothendieck topology `J` on a category `C` and
a category `A`, we define the pseudofunctor
`J.pseudofunctorOver A : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat`
which sends `X : C` to the category of shaves on `Over X`
with values in `A`.

-/

universe v' v u' u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

/-- Given a Grothendieck topology `J` on a category `C` and a category `A`,
this is the pseudofunctor which sends `X : C` to the categories of
sheaves on `Over X` with values in `A`. -/
@[simps!]
def pseudofunctorOver : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Sheaf (J.over X.unop) A))
    (fun f ↦ J.overMapPullback A f.unop)
    (fun X ↦ J.overMapPullbackId A X.unop)
    (fun f g ↦ (J.overMapPullbackComp A g.unop f.unop).symm)
    (fun f g h ↦ by simpa [overMapPullbackCongr_eq_eqToIso] using
      J.overMapPullback_assoc A h.unop g.unop f.unop)
    (fun f ↦ by simpa [overMapPullbackCongr_eq_eqToIso] using
      J.overMapPullback_comp_id A f.unop)
    (fun f ↦ by simpa [overMapPullbackCongr_eq_eqToIso] using
      J.overMapPullback_id_comp A f.unop)

end GrothendieckTopology

end CategoryTheory
