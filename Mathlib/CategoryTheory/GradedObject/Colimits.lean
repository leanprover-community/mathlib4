/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.GradedObject

/-!
# Colimits in graded objects

-/

namespace CategoryTheory

open Limits

namespace GradedObject

variable {C : Type*} [Category C]

section HasColimitsOfShape

variable {I : Type*} {K : Type*} [Category K]

def evalJointlyReflectsColimits {F : K ⥤ GradedObject I C} {c : Cocone F}
    (hc : ∀ i, IsColimit ((eval i).mapCocone c)):
    IsColimit c where
  desc s i := (hc i).desc ((eval i).mapCocone s)
  fac s k := by
    ext i
    exact (hc i).fac ((eval i).mapCocone s) k
  uniq s m hm := by
    ext i
    apply (hc i).hom_ext (fun k ↦ ?_)
    replace hm := congr_fun (hm k) i
    dsimp at hm ⊢
    rw [hm]
    exact ((hc i).fac ((eval i).mapCocone s) k).symm

section

variable [HasColimitsOfShape K C]

noncomputable def colimitCocone (F : K ⥤ GradedObject I C) :
    Cocone F where
  pt i := colimit (F ⋙ eval i)
  ι :=
    { app k i := colimit.ι (F ⋙ eval i) k
      naturality k k' f := by
        ext i
        simpa using  colimit.w (F ⋙ eval i) f }

noncomputable def isColimitColimitCocone (F : K ⥤ GradedObject I C) :
    IsColimit (colimitCocone F) :=
  evalJointlyReflectsColimits (fun _ ↦ colimit.isColimit _)

instance [HasColimitsOfShape K C] : HasColimitsOfShape K (GradedObject I C) where
  has_colimit F := ⟨⟨_, isColimitColimitCocone F⟩⟩

instance (i : I) : PreservesColimitsOfShape K (eval i : _ ⥤ C) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitColimitCocone F) (colimit.isColimit _)

end

end HasColimitsOfShape

end GradedObject

end CategoryTheory
