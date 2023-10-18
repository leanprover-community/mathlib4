import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} {α : Type} [Category C] {F : Cᵒᵖ ⥤ Type*} {Z : α → C}
    [HasCoproduct Z] (hF : (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)).IsSheafFor F)

noncomputable
instance : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F := by
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ _ _ _ ?_
  sorry

end CategoryTheory
