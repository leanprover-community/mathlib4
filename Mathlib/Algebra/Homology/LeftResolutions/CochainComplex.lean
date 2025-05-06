/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.LeftResolutions.CochainComplexMinus
import Mathlib.Algebra.Homology.Embedding.CochainComplexTrunc

/-!
# Resolutions of unbounded complexes

-/

open CategoryTheory Limits

namespace CochainComplex

variable {A : Type*} [Category A] [Abelian A]
  [HasColimitsOfShape ℤ A]
  (L : Minus A ⥤ Minus A)

noncomputable def leftResolutionObj
    (K : CochainComplex A ℤ) : CochainComplex A ℤ :=
  colimit (K.filtrationLEMinus ⋙ L ⋙ Minus.ι _)

variable {L} (α : L ⟶ 𝟭 _)

noncomputable def leftResolutionNatTransApp (K : CochainComplex A ℤ) :
    leftResolutionObj L K ⟶ K :=
  colimit.desc (K.filtrationLEMinus ⋙ L ⋙ Minus.ι _) (Cocone.mk _
    { app n := (Minus.ι A).map (α.app _) ≫ K.ιTruncLE n
      naturality _ _ _ := by
        dsimp
        rw [← Functor.map_comp_assoc]
        simp })

variable (hα : Minus.quasiIso.functorCategory _ α)

end CochainComplex
