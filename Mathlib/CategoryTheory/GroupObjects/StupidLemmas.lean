import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.GoalTypePanel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import ProofWidgets.Component.Panel.SelectionPanel

universe u v u' v' u'' v''

open CategoryTheory Limits ProofWidgets

variable {C : Type u} {D : Type u'} [Category.{v,u} C] [Category.{v', u'} D]

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

@[simp]
lemma PreservesLimitPair.iso_inv :
    (PreservesLimitPair.iso F X X').inv = inv (prodComparison F X X') := by
  simp_rw [← PreservesLimitPair.iso_hom]; rw [IsIso.Iso.inv_hom]

variable [HasTerminal C] [HasTerminal D] [PreservesLimit (CategoryTheory.Functor.empty C) F]

@[simp]
lemma PreservesTerminal.iso_inv :
    (PreservesTerminal.iso F).inv = inv (terminalComparison F) := by
  simp_rw [← PreservesTerminal.iso_hom]; rw [IsIso.Iso.inv_hom]


lemma prod.associator_comp_prodComparison [HasBinaryProducts C] [HasBinaryProducts D] :
    prodComparison F (X ⨯ Y) Z ≫ prod.map (prodComparison F X Y) (𝟙 (F.obj Z))
    ≫ (prod.associator _ _ _).hom =
    F.map (prod.associator _ _ _).hom ≫ prodComparison F X (Y ⨯ Z) ≫ prod.map (𝟙 (F.obj X))
    (prodComparison F Y Z) := by
  with_panel_widgets [GoalTypePanel]
  ext <;> simp only [prod.associator_hom, prod.comp_lift, prod.map_fst_assoc, prodComparison_fst,
    prodComparison_snd, prod.map_snd, Category.comp_id, prodComparison_fst_assoc, limit.lift_π,
    BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst, Category.assoc, prod.map_fst]
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst]
  · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_left, BinaryFan.mk_fst, prodComparison_snd_assoc]
    repeat' rw [← Functor.map_comp]
    congr 1
    simp only [limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right, BinaryFan.π_app_right,
      BinaryFan.mk_snd, limit.lift_π, BinaryFan.π_app_left, BinaryFan.mk_fst]
  · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, limit.lift_π, BinaryFan.mk_pt,
    prodComparison_snd_assoc]
    repeat' rw [← F.map_comp]
    congr 1
    simp only [limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right, BinaryFan.π_app_right,
      BinaryFan.mk_snd, limit.lift_π]

variable (F X Y Z)

lemma PreservesLimitsPair.iso.inv_comp_prod.associator [HasBinaryProducts C] [HasBinaryProducts D]
    [PreservesLimit (pair (X ⨯ Y) Z) F] [PreservesLimit (pair X Y) F]
    [PreservesLimit (pair Y Z) F] [PreservesLimit (pair X (Y ⨯ Z)) F] :
    prod.map (PreservesLimitPair.iso F X Y).inv (𝟙 (F.obj Z)) ≫
    (PreservesLimitPair.iso F (X ⨯ Y) Z).inv ≫ F.map (prod.associator _ _ _).hom =
    (prod.associator _ _ _).hom ≫ prod.map (𝟙 F.obj X) (PreservesLimitPair.iso F Y Z).inv ≫
    (PreservesLimitPair.iso F X (Y ⨯ Z)).inv := by
  refine Mono.right_cancellation (f := (PreservesLimitPair.iso F X (Y ⨯ Z)).hom) _ _ ?_
  refine Mono.right_cancellation (f := prod.map (𝟙 (F.obj X)) (PreservesLimitPair.iso F Y Z).hom)
    _ _ ?_
  conv_lhs => rw [Category.assoc, Category.assoc, Category.assoc]
              erw [← prod.associator_comp_prodComparison]
              rw [← PreservesLimitPair.iso_hom, ← PreservesLimitPair.iso_hom]
  slice_lhs 2 3 => rw [Iso.inv_hom_id]
  rw [Category.id_comp, ← Category.assoc, ← prod_map_comp_left_id_right, Iso.inv_hom_id,
    prod.map_id_id, Category.id_comp]
  slice_rhs 3 4 => rw [Iso.inv_hom_id]
  rw [Category.id_comp]; erw [← prod_map_comp_right_id_left]
  rw [Iso.inv_hom_id, prod.map_id_id, Category.comp_id]

variable {F X Y Z}

variable {h : X ⟶ Z} [HasBinaryProduct Y Z] [HasBinaryProduct X Y]
  [HasBinaryProduct (F.obj Y) (F.obj Z)]

lemma prodComparison_comp_lift :
    F.map (prod.lift f h) ≫ prodComparison F Y Z = prod.lift (F.map f) (F.map h) := by
  ext
  · simp only [Category.assoc, prodComparison_fst, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_left, BinaryFan.mk_fst]
    rw [← F.map_comp]; congr 1; simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left,
      BinaryFan.mk_fst]
  · simp only [Category.assoc, prodComparison_snd, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_right, BinaryFan.mk_snd]
    rw [← F.map_comp]; congr 1; simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right,
      BinaryFan.mk_snd]

variable [PreservesLimit (pair Y Z) F]

lemma PreservesLimitPair.iso.inv_comp_lift :
    prod.lift (F.map f) (F.map h) ≫ (PreservesLimitPair.iso F Y Z).inv = F.map (prod.lift f h) := by
  refine Mono.right_cancellation (f := (PreservesLimitPair.iso F Y Z).hom) _ _ ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesLimitPair.iso_hom,
    prodComparison_comp_lift]

variable {G : C ⥤ D}

variable [HasBinaryProduct (G.obj X) (G.obj Y)] [HasBinaryProduct (F.obj X) (F.obj Y)]

lemma prodComparison_natTrans (α : F ⟶ G) :
    prodComparison F X Y ≫ prod.map (α.app X) (α.app Y) =
    α.app (X ⨯ Y) ≫ prodComparison G X Y := by
  ext
  · rw [Category.assoc]; simp only [prod.map_fst, prodComparison_fst_assoc, NatTrans.naturality,
    Category.assoc, prodComparison_fst]
  · rw [Category.assoc]; simp only [prod.map_snd, prodComparison_snd_assoc, NatTrans.naturality,
    Category.assoc, prodComparison_snd]

lemma inv_prodComparison_natTrans [IsIso (prodComparison F X Y)] [IsIso (prodComparison G X Y)]
    (α : F ⟶ G) : inv (prodComparison F X Y) ≫ α.app (X ⨯ Y) =
    prod.map (α.app X) (α.app Y) ≫ inv (prodComparison G X Y) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natTrans]

end Limits

end CategoryTheory
