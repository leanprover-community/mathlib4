import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.GoalTypePanel
import ProofWidgets.Component.Panel.SelectionPanel

open CategoryTheory Limits ProofWidgets

variable {C D E : Type*} [Category C] [Category D] [Category E]

variable {X Y Z X' Y' Z' : C} [HasBinaryProduct X X'] [HasBinaryProduct Y X']
  [HasBinaryProduct Z X'] [HasBinaryProduct X Y'] [HasBinaryProduct Y Y']
  [HasBinaryProduct Z Y'] [HasBinaryProduct X Z'] [HasBinaryProduct Y Z']
  [HasBinaryProduct Z Z']

variable {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}

variable {F : C ⥤ D} [Limits.PreservesLimit (pair X X') F]
  [Limits.PreservesLimit (pair Y Y') F]

variable [HasBinaryProduct (F.obj X) (F.obj X')] [HasBinaryProduct (F.obj Y) (F.obj X')]
  [HasBinaryProduct (F.obj Z) (F.obj X')] [HasBinaryProduct (F.obj X) (F.obj Y')] [HasBinaryProduct (F.obj Y) (F.obj Y')]
  [HasBinaryProduct (F.obj Z) (F.obj Y')] [HasBinaryProduct (F.obj X) (F.obj Z')] [HasBinaryProduct (F.obj Y) (F.obj Z')]
  [HasBinaryProduct (F.obj Z) (F.obj Z')]

namespace CategoryTheory

namespace Limits

lemma prod_map_comp_left_id_right :
    prod.map (f ≫ g) (𝟙 X') = prod.map f (𝟙 X') ≫ prod.map g (𝟙 X') := by
  simp only [prod.map_map, Category.comp_id]

lemma prod_map_comp_right_id_left :
    prod.map (𝟙 X) (f' ≫ g') = prod.map (𝟙 X) f' ≫ prod.map (𝟙 X) g' := by
  simp only [prod.map_map, Category.comp_id]

lemma PreservesLimitPair.iso.inv_natural :
    prod.map (F.map f) (F.map f') ≫ (PreservesLimitPair.iso F _ _).inv =
    (PreservesLimitPair.iso F _ _).inv ≫ F.map (prod.map f f') := by
    with_panel_widgets [GoalTypePanel]
    refine Mono.right_cancellation (f := (PreservesLimitPair.iso F Y Y').hom) _ _ ?_
    conv_rhs => rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_natural]
    refine Epi.left_cancellation (f := (PreservesLimitPair.iso F X X').hom) _ _ ?_
    conv_lhs => rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesLimitPair.iso_hom]
    slice_rhs 1 2 =>
      rw [Iso.hom_inv_id]
    rw [Category.id_comp]

lemma prodCompAssoc [HasBinaryProducts C] [HasBinaryProducts D] :
    prodComparison F (X ⨯ Y) Z ≫ prod.map (prodComparison F X Y) (𝟙 (F.obj Z))
    ≫ (prod.associator _ _ _).hom =
    F.map (prod.associator _ _ _).hom ≫ prodComparison F X (Y ⨯ Z) ≫ prod.map (𝟙 (F.obj X))
    (prodComparison F Y Z) := by
  ext <;> simp?
  sorry



end Limits

end CategoryTheory
