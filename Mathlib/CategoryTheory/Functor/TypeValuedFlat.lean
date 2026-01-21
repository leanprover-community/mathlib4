/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Products

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

end CategoryTheory
