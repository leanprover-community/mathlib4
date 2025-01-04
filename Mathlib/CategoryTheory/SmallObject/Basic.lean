/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# The small object argument

Let `C` be a category. A class of morphisms `I : MorphismProperty C`
permits the small object argument (typeclass `HasSmallObjectArgument.{w} I`
where `w` is an auxiliary universe) if there exists a regular
cardinal `κ : Cardinal.{w}` such that `IsCardinalForSmallObjectArgument I κ`
holds. This technical condition is defined in the file
`SmallObject.IsCardinalForSmallObjectArgument`. It involves certain
smallness conditions relative to `w`, the existence of certain colimits,
and for each object `A` which is the source of a morphism in `I`,
the `Hom(A, _)` functor (`coyoneda.obj (op A)`) should commute
to transfinite compositions of pushouts of coproducts of morphisms in `I`
(this condition is automatically satisfied when `A` is a `κ`-presentable
object of `C`).

## Main reulsts

Assuming `I` permits the small object argument, the two main results
obtained in this file are:
* the class `I.rlp.llp` of morphisms that have the left lifting property with
respect to the maps that have the right lifting property with respect
to `I` are exactly the retracts of transfinite compositions
of pushouts of coproducts of morphisms in `I`;
* morphisms in `C` have a functorial factorization as a morphism in
`I.rlp.llp` followed by a morphism in `I.rlp`.

## Structure of the proof

The main part in the proof is the construction of the functorial factorization.
This involves a construction by transfinite induction. A general
procedure for constructions by transfinite
induction in categories (including the iteration of a functor)
is done in the file `SmallObject.TransfiniteIteration`.
The factorization of the small object argument is obtained by doing
a transfinite of a specific functor `Arrow C ⥤ Arrow C` which
is defined in the file `SmallObject.Construction` (this definition
involves coproducts and pushout). These ingredients are combined
in the file `SmallObject.IsCardinalForSmallObjectArgument`
where the main results are obtaned under a `IsCardinalForSmallObjectArgument I κ`
assumption.


## References
- https://ncatlab.org/nlab/show/small+object+argument

--In the context of model categories, this result is known as Quillen's small object
--argument (originally for `J := ℕ`). Actually, the more general construction by
--transfinite induction already appeared in the proof of the existence of enough
--injectives in abelian categories with AB5 and a generator by Grothendieck, who then
--wrote that the "proof was essentially known". Indeed, the argument appears
--in *Homological algebra* by Cartan and Eilenberg (p. 9-10) in the case of modules,
--and they mention that the result was initially obtained by Baer.

-/

universe w v u

namespace CategoryTheory

open Category Limits SmallObject

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (I : MorphismProperty C)

class HasSmallObjectArgument : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.toType),
    IsCardinalForSmallObjectArgument I κ

variable [HasSmallObjectArgument.{w} I]

noncomputable def smallObjectκ : Cardinal.{w} :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose

local instance smallObjectκ_isRegular : Fact I.smallObjectκ.IsRegular :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose_spec.choose

noncomputable instance : OrderBot I.smallObjectκ.ord.toType :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose_spec.choose_spec.choose

instance isCardinalForSmallObjectArgument_smallObjectκ :
    IsCardinalForSmallObjectArgument.{w} I I.smallObjectκ :=
  (HasSmallObjectArgument.exists_cardinal (I := I)).choose_spec.choose_spec.choose_spec

instance : HasFunctorialFactorization I.rlp.llp I.rlp :=
  hasFunctorialFactorization I I.smallObjectκ

/-- If `I : MorphismProperty C` permits the small object argument,
then the class of morphism that have the left lifting property with respect to
the maps that have the right lifting property with respect to `I` are
exactly the retracts of transfinite compositions (indexed by `I.smallObjectκ.ord.toType`)
of pushouts of coproducts of morphisms in `C`. -/
lemma rlp_llp_of_hasSmallObjectArgument' :
    I.rlp.llp = (transfiniteCompositionsOfShape (coproducts.{w} I).pushouts
        I.smallObjectκ.ord.toType).retracts :=
  rlp_llp_of_isCardinalForSmallObjectArgument' I I.smallObjectκ

/-- If `I : MorphismProperty C` permits the small object argument,
then the class of morphism that have the left lifting property with respect to
the maps that have the right lifting property with respect to `I` are
exactly the retracts of transfinite compositions
of pushouts of coproducts of morphisms in `C`. -/
lemma rlp_llp_of_hasSmallObjectArgument :
    I.rlp.llp =
      (transfiniteCompositions.{w} (coproducts.{w} I).pushouts).retracts :=
  rlp_llp_of_isCardinalForSmallObjectArgument I I.smallObjectκ

end MorphismProperty

end CategoryTheory
