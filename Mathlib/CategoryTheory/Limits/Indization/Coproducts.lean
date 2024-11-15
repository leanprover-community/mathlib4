/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Coproducts in the category of Ind-objects

We show that if `C` has finite coproducts, then `Ind C` has small coproducts. It is shown elsewhere
that the functor `C ⥤ Inc C` preserves finite coproducts if `C` has finite colimits. It is not true
that the functors `C ⥤ Ind C` or `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserves coproducts in general.
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {α : Type v} {I : α → Type v} [∀ s, SmallCategory (I s)] [∀ s, IsFiltered (I s)]
  (F : ∀ s, I s ⥤ C) [HasColimitsOfShape (Discrete α) C]

-- This is the λ in my notes
noncomputable def pointwiseCoproduct : (∀ s, I s) ⥤ C where
  obj i := ∐ (fun s => (F s).obj (i s))
  map f := Sigma.map (fun s => (F s).map (f s))

section step1

variable (i : ∀ s, I s)

noncomputable def collection : α → Ind C := fun s => Ind.yoneda.obj ((F s).obj (i s))

-- Could be streamlined using a `Cofan.map` definition
noncomputable def cofan : Cofan (collection F i) :=
  Cofan.mk (Ind.yoneda.obj (∐ fun s => (F s).obj (i s)))
    (fun s => Ind.yoneda.map (Sigma.ι (fun s => (F s).obj (i s)) s))

def step1 : IsColimit (cofan F i) := sorry

end step1

section step2

noncomputable def collection2 : α → Ind C := fun s => colimit (F s ⋙ Ind.yoneda)

noncomputable def cocone2 (s : α) : Cocone (F s ⋙ Ind.yoneda) where
  pt := colimit (pointwiseCoproduct F ⋙ Ind.yoneda)
  ι := sorry

noncomputable def cofan2 : Cofan (collection2 F) :=
  Cofan.mk (colimit (pointwiseCoproduct F ⋙ Ind.yoneda))
    (fun s => _ ≫ colimit.ι _ _)

end step2

end

end CategoryTheory.Limits
