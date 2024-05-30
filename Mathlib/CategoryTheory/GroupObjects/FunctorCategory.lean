import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.ApplyFun

universe u v u' v'

open CategoryTheory Limits ProofWidgets

noncomputable section
suppress_compilation

variable {C : Type u} [Category.{v, u} C] {D : Type u'} [Category.{v', u'} D] [HasFiniteProducts D]

instance functorCategoryHasFiniteProducts : HasFiniteProducts (C ⥤ D) where
  out _ := inferInstance
-- This should be an instance in mathlib, but it doesn't
-- seem to be there. TODO: add it.

--set_option diagnostics true
-- set_option maxHeartbeats 5000000
--set_option profiler true
-- set_option trace.profiler true

namespace GroupObjectFunctorToFunctorGroupObject

def obj_obj_one (G : GroupObject (C ⥤ D)) (X : C) :
    ⊤_ D ⟶ G.X.obj X := (PreservesTerminal.iso ((evaluation _ _).obj X)).inv ≫ G.one.app X

def obj_obj_mul (G : GroupObject (C ⥤ D)) (X : C) :
    G.X.obj X ⨯ G.X.obj X ⟶ G.X.obj X :=
  (PreservesLimitPair.iso ((evaluation _ _).obj X) G.X G.X).inv ≫ G.mul.app X

def obj_obj (G : GroupObject (C ⥤ D)) (X : C) :
    GroupObject D where
    X := G.X.obj X
    one := obj_obj_one G X
    mul := obj_obj_mul G X
    inv := G.inv.app X
    one_mul := by
      simp only [obj_obj_one, obj_obj_mul, evaluation_obj_obj, prod.leftUnitor_hom]
      rw [prod_map_comp_left_id_right, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      conv_lhs => congr; rfl; congr
                  rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                    PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                    ((evaluation C D).obj X) G.one (𝟙 G.X), evaluation_obj_map]
      rw [Category.assoc, ← NatTrans.comp_app, G.one_mul, prod.leftUnitor_hom,
        ← PreservesLimitPair.iso_inv, ← evaluation_obj_map, PreservesLimitPair.iso_inv_snd]
      simp only [evaluation_obj_obj, prod.map_snd, Category.comp_id]
    mul_one := by
      simp only [obj_obj_one, obj_obj_mul, evaluation_obj_obj, prod.rightUnitor_hom]
      rw [prod_map_comp_right_id_left, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      conv_lhs => congr; rfl; congr
                  rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                  ((evaluation C D).obj X) (𝟙 G.X) G.one, evaluation_obj_map]
      rw [Category.assoc, ← NatTrans.comp_app, G.mul_one, prod.rightUnitor_hom,
        ← PreservesLimitPair.iso_inv, ← evaluation_obj_map, PreservesLimitPair.iso_inv_fst]
      simp only [evaluation_obj_obj, prod.map_fst, Category.comp_id]
    mul_assoc := by
      rw [obj_obj_mul, prod_map_comp_left_id_right]
      slice_lhs 2 3 =>
        rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                  ((evaluation C D).obj X) G.mul (𝟙 G.X), evaluation_obj_map]
      slice_lhs 3 4 => rw [← NatTrans.comp_app, G.mul_assoc]
      rw [prod_map_comp_right_id_left]
      slice_rhs 3 4 =>
        rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural ((evaluation C D).obj X)
                         (𝟙 G.X) G.mul, evaluation_obj_map]
      rw [NatTrans.comp_app, ← Category.assoc, ← Category.assoc, ← PreservesLimitPair.iso_inv]
      conv_lhs => rw [← evaluation_obj_map, Category.assoc _
        (PreservesLimitPair.iso ((evaluation C D).obj X) (G.X ⨯ G.X) G.X).inv _]
      have : 𝟙 (G.X.obj X) = 𝟙 (((evaluation C D).obj X).obj G.X) := by
        simp only [evaluation_obj_obj]
      rw [this, PreservesLimitsPair.iso.inv_comp_prod.associator G.X G.X G.X
        ((CategoryTheory.evaluation C D).obj X)]
      simp only [evaluation_obj_obj, prod.associator_hom, Pi.id_apply, PreservesLimitPair.iso_inv,
        prod.lift_map_assoc, Category.comp_id, NatTrans.comp_app, Category.assoc]
    mul_left_inv := by
      rw [obj_obj_mul, obj_obj_one, ← Category.assoc]
      rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map]
      conv_lhs => congr
                  erw [PreservesLimitPair.iso.inv_comp_lift (F := (evaluation C D).obj X)
                    (f := G.inv) (h := 𝟙 G.X)]
      rw [evaluation_obj_map, ← NatTrans.comp_app, G.mul_left_inv, NatTrans.comp_app]
      simp only [evaluation_obj_obj]
      rw [← Category.assoc]
      congr 1
      simp only [evaluation_obj_obj, PreservesTerminal.iso_inv, IsIso.eq_comp_inv]
      exact Subsingleton.elim _ _

def obj (G : GroupObject (C ⥤ D)) :
    C ⥤ (GroupObject D) where
  obj X := obj_obj G X
  map f := {
    hom := G.X.map f
    one_hom := by
      simp only [obj_obj, obj_obj_one]
      rw [Category.assoc, ← G.one.naturality, ← Category.assoc]
      congr 1
      simp only [evaluation_obj_obj, PreservesTerminal.iso_inv, IsIso.inv_comp_eq,
        IsIso.eq_comp_inv]
      exact Subsingleton.elim _ _
    mul_hom := by
      simp only [obj_obj, obj_obj_mul]
      rw [Category.assoc, ← G.mul.naturality, ← Category.assoc, ← Category.assoc]
      congr 1
      simp only [evaluation_obj_obj, PreservesLimitPair.iso_inv, IsIso.eq_comp_inv, Category.assoc,
        IsIso.inv_comp_eq]
      rw [← evaluation_map_app, ← evaluation_map_app _ _ f G.X]
      exact (prodComparison_natTrans (α := (evaluation C D).map f) (X := G.X) (Y := G.X)).symm
    inv_hom := by simp only [obj_obj, NatTrans.naturality]
  }

def map {G H : GroupObject (C ⥤ D)} (α : G ⟶ H) : obj G ⟶ obj H where
  app X := by
    simp only [obj, obj_obj]
    exact
     { hom := α.hom.app X
       one_hom := by
         simp only [obj_obj_one, evaluation_obj_obj, PreservesTerminal.iso_inv, Category.assoc,
           IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc]
         rw [← NatTrans.comp_app, α.one_hom]
       mul_hom := by
         simp only [obj_obj_mul, evaluation_obj_obj, PreservesLimitPair.iso_inv, Category.assoc,
           IsIso.inv_comp_eq]
         rw [← NatTrans.comp_app, α.mul_hom]
         slice_rhs 2 3 => rw [← evaluation_obj_map, ← prodComparison_inv_natural
           ((evaluation C D).obj X) α.hom α.hom]
         simp only [NatTrans.comp_app, evaluation_obj_obj, evaluation_obj_map, Category.assoc,
           IsIso.hom_inv_id_assoc]
       inv_hom := by rw [← NatTrans.comp_app, α.inv_hom, NatTrans.comp_app]
     }
  naturality X Y f := by
    simp only [obj, id_eq]
    ext
    simp only [GroupObject.comp_hom', NatTrans.naturality]

end GroupObjectFunctorToFunctorGroupObject

variable (C D)

def GroupObjectFunctorToFunctorGroupObject :
    GroupObject (C ⥤ D) ⥤ C ⥤ GroupObject D where
  obj G := GroupObjectFunctorToFunctorGroupObject.obj G
  map α := GroupObjectFunctorToFunctorGroupObject.map α

namespace GroupObjectFunctorToFunctorGroupObject

variable {C D}

def faithful : (GroupObjectFunctorToFunctorGroupObject C D).Faithful where
map_injective := by
  intro G H α β
  simp only [GroupObjectFunctorToFunctorGroupObject, map, id_eq]
  intro h
  ext X
  apply_fun (fun a ↦ (a.app X).hom) at h
  exact h

def full : (GroupObjectFunctorToFunctorGroupObject C D).Full where
  map_surjective := by
    intro G H
    simp only [GroupObjectFunctorToFunctorGroupObject, obj, map, id_eq, obj_obj]
    intro a
    set αhom : G.X ⟶ H.X :=
     {
      app := fun X ↦ (a.app X).hom
      naturality := by
        intro X Y f
        have := a.naturality f
        apply_fun (fun h ↦ h.hom) at this
        simp only [GroupObject.comp_hom'] at this
        exact this
     }
    existsi
     {
      hom := αhom
      one_hom := ?_
      mul_hom := ?_
      inv_hom := ?_
     }
    · ext X
      simp only [NatTrans.comp_app, αhom]
      have := (a.app X).one_hom
      simp only [obj_obj_one, evaluation_obj_obj, PreservesTerminal.iso_inv, Category.assoc,
        IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc] at this
      exact this
    · ext X
      simp only [NatTrans.comp_app, αhom]
      have := (a.app X).mul_hom
      simp only [obj_obj_mul, evaluation_obj_obj, PreservesLimitPair.iso_inv, Category.assoc,
        IsIso.inv_comp_eq] at this
      rw [← Category.assoc] at this
      have that := prodComparison_natural ((evaluation C D).obj X) αhom αhom
      simp only [evaluation_obj_obj, evaluation_obj_map, αhom] at that
      rw [← that] at this
      simp only [evaluation_obj_obj, Category.assoc, IsIso.hom_inv_id_assoc] at this
      exact this
    · ext X; dsimp
      rw [(a.app X).inv_hom]
    · ext; simp only

/-
def essSurj_aux (F : C ⥤ (GroupObject D)) : GroupObject (C ⥤ D) where
  X :=
   {
    obj := fun X ↦ (F.obj X).X
    map := fun f ↦ (F.map f).hom
   }
  one :=
   {
    app := fun X ↦ terminalComparison ((evaluation C D).obj X) ≫ (F.obj X).one
    naturality := by
      intro X Y f
      rw [Category.assoc, GroupObject.Hom.one_hom, ← Category.assoc]
      congr 1
      exact Subsingleton.elim _ _
   }
  mul :=
   {
    app := fun X ↦ prodComparison ((evaluation C D).obj X) X X ≫ (F.obj X).mul
    naturality := by
      intro X Y f
      simp only [evaluation_obj_obj, Category.assoc, GroupObject.Hom.mul_hom]
      have := prodComparison_natTrans ((evaluation C D).map f) (X := X) (Y :=GX)
      simp only [evaluation_obj_obj, evaluation_map_app] at this
      conv_rhs => rw [← Category.assoc, this]
      simp only [Category.assoc]
   }
  inv :=
   {
    app := fun X ↦ (F.obj X).inv
    naturality :=  fun _ _ f ↦ by
      sorry
   }
-/


def essSurj : (GroupObjectFunctorToFunctorGroupObject C D).EssSurj where
  mem_essImage F := by
    set GX : C ⥤ D :=
     {
      obj := fun X ↦ (F.obj X).X
      map := fun f ↦ (F.map f).hom
     }
    set G : GroupObject (C ⥤ D) :=
     {
      X := GX
      one :=
       {
        app := fun X ↦ terminalComparison ((evaluation C D).obj X) ≫ (F.obj X).one
        naturality := by
          intro X Y f
          rw [Category.assoc, GroupObject.Hom.one_hom, ← Category.assoc]
          congr 1
          exact Subsingleton.elim _ _
       }
      mul :=
       {
        app := fun X ↦ prodComparison ((evaluation C D).obj X) _ _ ≫ (F.obj X).mul
        naturality := by
          intro _ _ f
          simp only [evaluation_obj_obj, Category.assoc, GroupObject.Hom.mul_hom]
          have := prodComparison_natTrans ((evaluation C D).map f) (X := GX) (Y := GX)
          simp only [evaluation_obj_obj, evaluation_map_app] at this
          conv_rhs => rw [← Category.assoc, this]
          simp only [Category.assoc]
       }
      inv :=
       {
        app := fun X ↦ (F.obj X).inv
        naturality :=  fun _ _ f ↦ by rw [(F.map f).inv_hom]
       }
      one_mul := by
        ext X
        simp only [evaluation_obj_obj, NatTrans.comp_app, prod.leftUnitor_hom]
        rw [← Category.assoc]
        erw [prodComparison_natural ((evaluation C D).obj X)]
        simp only [evaluation_obj_obj, evaluation_obj_map, NatTrans.id_app, Category.assoc]
        rw [prod_map_comp_left_id_right]
        slice_lhs 3 4 => rw [(F.obj X).one_mul]
        simp only [prod.leftUnitor_hom, prod.map_snd, Category.comp_id]
        erw [prodComparison_snd]
        simp only [evaluation_obj_map] 
      mul_one := sorry
      mul_assoc := sorry
      mul_left_inv := sorry
     }
    refine Functor.essImage.ofIso (NatIso.ofComponents ?_ ?_) (Functor.obj_mem_essImage _ G)
    · intro X
      simp only [GroupObjectFunctorToFunctorGroupObject, obj, obj_obj, GroupObject.id_hom',
        GroupObject.comp_hom', id_eq, eq_mpr_eq_cast]
      refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_
      · simp only [obj_obj_one, evaluation_obj_obj, GroupObject.id_hom', GroupObject.comp_hom',
        id_eq, eq_mpr_eq_cast, PreservesTerminal.iso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom,
        Category.comp_id]
      · sorry --simp? [obj_obj_mul]
      · sorry
    · sorry


end GroupObjectFunctorToFunctorGroupObject

#exit
def GroupObjectFunctorToFunctorGroupObject_obj (G : GroupObject (C ⥤ D)) :
    C ⥤ (GroupObject D) where
  obj X := {
    X := G.X.obj X
    one := (PreservesTerminal.iso ((evaluation _ _).obj X)).inv ≫ G.one.app X
    mul := (PreservesLimitPair.iso ((evaluation _ _).obj X) G.X G.X).inv ≫ G.mul.app X
    inv := G.inv.app X
    one_mul := by
      simp only [evaluation_obj_obj, prod.leftUnitor_hom]
      rw [prod_map_comp_left_id_right, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      conv_lhs => congr; rfl; congr
                  rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                    PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                    ((evaluation C D).obj X) G.one (𝟙 G.X), evaluation_obj_map]
      rw [Category.assoc, ← NatTrans.comp_app, G.one_mul, prod.leftUnitor_hom,
        ← PreservesLimitPair.iso_inv, ← evaluation_obj_map, PreservesLimitPair.iso_inv_snd]
      simp only [evaluation_obj_obj, prod.map_snd, Category.comp_id]
    mul_one := by sorry
/-      simp only [evaluation_obj_obj, prod.rightUnitor_hom]
      rw [prod_map_comp_right_id_left, Category.assoc, ← Category.assoc _ _ (G.mul.app X)]
      conv_lhs => congr; rfl; congr
                  rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                  ((evaluation C D).obj X) (𝟙 G.X) G.one, evaluation_obj_map]
      rw [Category.assoc, ← NatTrans.comp_app, G.mul_one, prod.rightUnitor_hom,
        ← PreservesLimitPair.iso_inv, ← evaluation_obj_map, PreservesLimitPair.iso_inv_fst]
      simp only [evaluation_obj_obj, prod.map_fst, Category.comp_id]-/
    mul_assoc := by sorry
/-      rw [prod_map_comp_left_id_right]
      slice_lhs 2 3 =>
        rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural
                  ((evaluation C D).obj X) G.mul (𝟙 G.X), evaluation_obj_map]
      slice_lhs 3 4 => rw [← NatTrans.comp_app, G.mul_assoc]
      rw [prod_map_comp_right_id_left]
      slice_rhs 3 4 =>
        rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map,
                  PreservesLimitPair.iso_inv, ← prodComparison_inv_natural ((evaluation C D).obj X)
                         (𝟙 G.X) G.mul, evaluation_obj_map]
      rw [NatTrans.comp_app, ← Category.assoc, ← Category.assoc, ← PreservesLimitPair.iso_inv]
      conv_lhs => rw [← evaluation_obj_map, Category.assoc _
        (PreservesLimitPair.iso ((evaluation C D).obj X) (G.X ⨯ G.X) G.X).inv _]
      have : 𝟙 (G.X.obj X) = 𝟙 (((evaluation C D).obj X).obj G.X) := by
        simp only [evaluation_obj_obj]
      rw [this, PreservesLimitsPair.iso.inv_comp_prod.associator G.X G.X G.X
        ((CategoryTheory.evaluation C D).obj X)]
      simp only [evaluation_obj_obj, prod.associator_hom, Pi.id_apply, PreservesLimitPair.iso_inv,
        prod.lift_map_assoc, Category.comp_id, NatTrans.comp_app, Category.assoc]-/
    mul_left_inv := by sorry
/-      rw [← Category.assoc]
      rw [← NatTrans.id_app, ← evaluation_obj_map, ← evaluation_obj_map]
      conv_lhs => congr
                  erw [PreservesLimitPair.iso.inv_comp_lift (F := (evaluation C D).obj X)
                    (f := G.inv) (h := 𝟙 G.X)]
      rw [evaluation_obj_map, ← NatTrans.comp_app, G.mul_left_inv, NatTrans.comp_app]
      simp only [evaluation_obj_obj]
      rw [← Category.assoc]
      congr 1
/-      suffices h : (default : G.X ⟶ ⊤_ (C ⥤ D)).app X =
          default ≫ (PreservesTerminal.iso ((evaluation C D).obj X)).inv by
        rw [h]-/
      simp only [evaluation_obj_obj, PreservesTerminal.iso_inv, IsIso.eq_comp_inv]
      exact Subsingleton.elim _ _-/
  }
  map f := {
    hom := G.X.map f
    one_hom := by sorry
/-      simp only
      rw [Category.assoc, ← G.one.naturality, ← Category.assoc]
      congr 1
--      rename_i X Y
/-      suffices h : ((PreservesTerminal.iso ((evaluation C D).obj X)).inv ≫ (⊤_ C ⥤ D).map f) =
          (PreservesTerminal.iso ((evaluation C D).obj Y)).inv by
        rw [h]-/
      simp only [evaluation_obj_obj, PreservesTerminal.iso_inv, IsIso.inv_comp_eq,
        IsIso.eq_comp_inv]
      exact Subsingleton.elim _ _-/
    mul_hom := by sorry
/-      simp only
      rw [Category.assoc, ← G.mul.naturality, ← Category.assoc, ← Category.assoc]
      congr 1
      /-rename_i X Y
      suffices h : ((PreservesLimitPair.iso ((evaluation C D).obj X) G.X G.X).inv ≫ (G.X ⨯ G.X).map f) =
          (prod.map (G.X.map f) (G.X.map f) ≫ (PreservesLimitPair.iso
          ((evaluation C D).obj Y) G.X G.X).inv) by
        rw [h]-/
      simp only [evaluation_obj_obj, PreservesLimitPair.iso_inv, IsIso.eq_comp_inv, Category.assoc,
        IsIso.inv_comp_eq]
      rw [← evaluation_map_app, ← evaluation_map_app _ _ f G.X]
      exact (prodComparison_natTrans (α := (evaluation C D).map f) (X := G.X) (Y := G.X)).symm-/
  }
  map_id X := by sorry
/-    ext; simp only [evaluation_obj_obj, prod.leftUnitor_hom, id_eq, evaluation_obj_map,
      NatTrans.id_app, NatTrans.comp_app, eq_mpr_eq_cast, prod.rightUnitor_hom, prod.associator_hom,
      Pi.id_apply, cast_eq, evaluation_map_app, CategoryTheory.Functor.map_id, GroupObject.id_hom']-/
  map_comp f g := by sorry
/-      ext; simp only [evaluation_obj_obj, prod.leftUnitor_hom, id_eq, evaluation_obj_map,
      NatTrans.id_app, NatTrans.comp_app, eq_mpr_eq_cast, prod.rightUnitor_hom, prod.associator_hom,
      Pi.id_apply, cast_eq, evaluation_map_app, Functor.map_comp, GroupObject.comp_hom']-/
