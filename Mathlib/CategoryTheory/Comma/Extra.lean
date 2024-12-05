/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# ...

-/

namespace CategoryTheory

open Category

namespace Comma

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category C₁] [Category C₂] [Category D]
  [Category C₁'] [Category C₂'] [Category D']

variable {L : C₁ ⥤ D} {R : C₂ ⥤ D} {L' : C₁' ⥤ D'} {R' : C₂' ⥤ D'}
  {F₁ : C₁ ⥤ C₁'} {F₂ : C₂ ⥤ C₂'} {F : D ⥤ D'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F)
  (β : R ⋙ F ⟶ F₂ ⋙ R')

noncomputable instance
    [F₁.Faithful] [F₂.Faithful] [F.Faithful] [F₁.Full] [F₂.Full]
    [F₁.EssSurj] [F₂.EssSurj] [F.Full] [IsIso α] [IsIso β] :
    (map α β).IsEquivalence where

end Comma

namespace StructuredArrow

variable {C D C' D' : Type*} [Category C] [Category D]
  [Category C'] [Category D']

variable {L : D} {R : C ⥤ D} {L' : D'} {R' : C' ⥤ D'}
  {F : C ⥤ C'} {G : D ⥤ D'}
  (α : L' ⟶ G.obj L)
  (β : R ⋙ G ⟶ F ⋙ R')

instance {I : Type*} {F G : Discrete I ⥤ C} (f : ∀ i, F.obj i ⟶ G.obj i)
    [∀ i, IsIso (f i)] :
    IsIso (Discrete.natTrans f) := by
  change IsIso (Discrete.natIso (fun i => asIso (f i))).hom
  infer_instance

noncomputable instance
    [F.Faithful] [G.Faithful] [F.EssSurj] [F.Full] [G.Full] [IsIso α] [IsIso β] :
    (map₂ α β).IsEquivalence where

end StructuredArrow

end CategoryTheory
