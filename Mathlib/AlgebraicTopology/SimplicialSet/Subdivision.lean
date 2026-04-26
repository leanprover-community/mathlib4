/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.Order.NonemptyFiniteChains

/-!
# The subdivision functors

In this file, we define the subdivision functor `sd : SSet ⥤ SSet`
and its right adjoint `ex`.

## TODO (@joelriou)
* define another functor `SSet.B : SSet ⥤ SSet` by sending `X` to
the nerve of the partially ordered type `X.N` of nondegenerate
simplices in `X`, define a natural transformation `sd ⟶ B`,
and show that on suitable simplicial sets `X`, this natural
transformation is an isomorphism.

## References
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

@[expose] public section

universe v u

open CategoryTheory

/-- The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the nerve of the
partially ordered type of nonempty finite chains in `{0, ..., n}` (ulifted to `Type u`).
Vertices in `SimplexCategory.sd.obj ⦋n⦌` identify to nonempty subsets of `{0, ..., n}`. -/
noncomputable def SimplexCategory.sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

namespace SSet

/-- The subdivision functor on simplicial sets. -/
noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.leftKanExtension SimplexCategory.sd

/-- The right adjoint to the subdivision functor on simplicial sets. -/
noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between the subdivision functor `sd` and `ex`. -/
noncomputable def sdExAdjunction : sd.{u} ⊣ ex :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

namespace stdSimplex

/-- The natural isomorphism `stdSimplex ⋙ sd ≅ SimplexCategory.sd`. -/
noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  Presheaf.isExtensionAlongULiftYoneda _

end stdSimplex

instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

end SSet
