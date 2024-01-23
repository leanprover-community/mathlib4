import Mathlib.CategoryTheory.Equivalence

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Let `C`,`D`,`E` be categories. Then an equivalence from `C` to `D` defines an equivalence
from the functor category `C ⥤ E` to `D ⥤ E`.-/
instance equivalence_functorCategory (C : Type u₁) (D : Type u₂) (E : Type u₃)
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] (Eq : Equivalence C D) :
    Equivalence (C ⥤ E) (D ⥤ E) := by
  apply Equivalence.mk
  case F => exact
    {
    obj := fun H => Eq.inverse ⋙ H
    map := fun α => whiskerLeft Eq.inverse α
    map_id := by tauto
    map_comp := by tauto
    }
  case G => exact
    {
    obj := fun H => Eq.functor ⋙ H
    map := fun α => whiskerLeft Eq.functor α
    map_id := by tauto
    map_comp := by tauto
    }
  case η =>
    apply NatIso.ofComponents
    case app =>
      intro H
      simp only [id_obj, comp_obj]
      exact isoWhiskerRight Eq.unitIso H
    case naturality =>
      intro X Y f
      ext A
      simp only [id_obj, whiskerLeft_id', whiskerLeft_comp, comp_obj, Functor.id_map, id_eq, isoWhiskerRight_hom,
        NatTrans.comp_app, whiskerRight_app, Functor.comp_map, whiskerLeft_twice, whiskerLeft_app, NatTrans.naturality]
  case ε =>
    apply NatIso.ofComponents
    case app =>
      intro H
      simp only [comp_obj, id_obj]
      exact isoWhiskerRight Eq.counitIso H
    case naturality =>
      intro X Y f
      ext A
      simp only [whiskerLeft_id', whiskerLeft_comp, comp_obj, id_obj, Functor.comp_map, whiskerLeft_twice, id_eq,
        isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.id_map, NatTrans.naturality]
