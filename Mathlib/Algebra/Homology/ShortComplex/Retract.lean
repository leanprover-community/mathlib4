/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Quasi-isomorphisms of short complexes are stable under retracts

-/

namespace CategoryTheory

open Limits

namespace ShortComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  {S₁ T₁ S₂ T₂ : ShortComplex C}
  [S₁.HasHomology] [T₁.HasHomology] [S₂.HasHomology] [T₂.HasHomology]
  {f₁ : S₁ ⟶ T₁} {f₂ : S₂ ⟶ T₂}

lemma quasiIso_of_retract (h : RetractArrow f₁ f₂) [hf₂ : QuasiIso f₂] :
    QuasiIso f₁ := by
  rw [quasiIso_iff] at hf₂ ⊢
  have h : RetractArrow (homologyMap f₁) (homologyMap f₂) :=
    { i := Arrow.homMk (u := homologyMap (show S₁ ⟶ S₂ from h.i.left))
        (v := homologyMap (show T₁ ⟶ T₂ from h.i.right)) (by simp [← homologyMap_comp])
      r := Arrow.homMk (u := homologyMap (show S₂ ⟶ S₁ from h.r.left))
        (v := homologyMap (show T₂ ⟶ T₁ from h.r.right)) (by simp [← homologyMap_comp])
      retract := by ext <;> simp [← homologyMap_comp] }
  exact (MorphismProperty.isomorphisms C).of_retract h hf₂

end ShortComplex

end CategoryTheory
