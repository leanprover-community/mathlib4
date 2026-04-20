/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Type-valued flat functors

A functor `F : C ⥤ Type w` is a flat Type-valued functor if the category
`F.Elements` is cofiltered. (This is not equivalent to saying that `F`
is representably flat in the sense of the typeclass `RepresentablyFlat`
defined in the file `Mathlib/CategoryTheory/Functor/Flat.lean`, see also
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
for a clarification about the differences between these notions.)

In this file, we show that if finite limits exist in `C` and are preserved by `F`,
then `F.Elements` is cofiltered.

-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

lemma Functor.isCofiltered_elements
    (F : C ⥤ Type w) [HasFiniteLimits C] [PreservesFiniteLimits F] :
    IsCofiltered F.Elements where
  nonempty := ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨prod.fst, congr_fun (h'.conePointUniqueUpToIso_hom_comp h (.mk .left)) _⟩,
      ⟨prod.snd, congr_fun (h'.conePointUniqueUpToIso_hom_comp h (.mk .right)) _⟩, by tauto⟩
  cone_maps := by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, hf⟩ ⟨g, hg⟩
    dsimp at f g hf hg
    subst hg
    let h := isLimitForkMapOfIsLimit F _ (equalizerIsEqualizer f g)
    let h' := (Types.equalizerLimit (g := F.map f) (h := F.map g)).isLimit
    exact ⟨⟨equalizer f g, (h'.conePointUniqueUpToIso h).hom ⟨x, hf⟩⟩,
      ⟨equalizer.ι f g, congr_fun (h'.conePointUniqueUpToIso_hom_comp h .zero) ⟨x, hf⟩⟩,
      by ext; exact equalizer.condition f g⟩

namespace FunctorToTypes

variable (F : C ⥤ Type w) {X : C} (x : F.obj X)

set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the subfunctor of the functor `Over.forget X ⋙ F : Over X ⥤ Type w`
which sends an object of `Over X` corresponding to a morphism `f : Y ⟶ X`
to the subset of `F.obj Y` consisting of those elements `y : F.obj Y`
such that `F.map f y = x`. -/
def fromOverSubfunctor : Subfunctor (Over.forget X ⋙ F) where
  obj U := F.map U.hom ⁻¹' {x}
  map _ _ _ := by simpa [← map_comp_apply]

@[simp]
lemma mem_fromOverSubfunctor_iff {U : Over X} (u : F.obj U.left) :
    u ∈ (fromOverSubfunctor F x).obj U ↔ F.map U.hom u = x := Iff.rfl

/-- Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the functor `Over X ⥤ Type w` which sends an object of `Over X`
corresponding to a morphism `f : Y ⟶ X` to the subtype of `F.obj Y`
consisting of those elements `y : F.obj Y` such that `F.map f y = x`. -/
abbrev fromOverFunctor : Over X ⥤ Type w := (fromOverSubfunctor F x).toFunctor

set_option backward.isDefEq.respectTransparency false in
open CategoryOfElements in
/-- Given a functor `F : C ⥤ Type w`, an object `X : C` and `x : F.obj X`,
this is the equivalence between the category of elements of `fromOverFunctor F x`
with the `Over` category of `x` considered as an object of `F.Elements`. -/
def fromOverFunctorElementsEquivalence :
    (fromOverFunctor F x).Elements ≌ Over (F.elementsMk X x) where
  functor.obj u :=
    Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom u.snd.2)
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd, u.hom.2⟩
  inverse.map f := homMk _ _ (Over.homMk f.left.val (Subtype.ext_iff.1 (Over.w f)))
    (by cat_disch)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  -- `cat_disch` can fill in this proof, but is unfortunately quite slow.
  functor_unitIso_comp X := by simp_all; rfl

instance [IsCofiltered F.Elements] : IsCofiltered (fromOverFunctor F x).Elements :=
  .of_equivalence (fromOverFunctorElementsEquivalence F x).symm

end FunctorToTypes

end CategoryTheory
