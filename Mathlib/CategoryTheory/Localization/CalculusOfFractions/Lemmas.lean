/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

/-!
# Lemmas about calculus of fractions

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C D E : Type*} [Category C] [Category D] [Category E]

lemma Functor.faithful_of_precomp_cancel_zero_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    [Preadditive D] [Preadditive E] [F.Additive]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f : L.obj X₁ ⟶ L.obj X₂), F.map f = 0 → f = 0) :
    Faithful F :=
  F.faithful_of_precomp_essSurj L (fun X₁ X₂ f g hfg => by
    rw [← sub_eq_zero]
    exact h _ (by rw [F.map_sub, hfg, sub_self]))

end CategoryTheory
