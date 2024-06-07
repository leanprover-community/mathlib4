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


namespace GroupObjectFunctorToFunctorGroupObject

@[simp]
def obj_obj_one (G : GroupObject (C ⥤ D)) (X : C) :
    ⊤_ D ⟶ G.X.obj X := (PreservesTerminal.iso ((evaluation _ _).obj X)).inv ≫ G.one.app X

@[simp]
def obj_obj_mul (G : GroupObject (C ⥤ D)) (X : C) :
    G.X.obj X ⨯ G.X.obj X ⟶ G.X.obj X :=
  (PreservesLimitPair.iso ((evaluation _ _).obj X) G.X G.X).inv ≫ G.mul.app X

@[simp]
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

@[simp]
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

@[simp]
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

@[simp]
def GroupObjectFunctorToFunctorGroupObject :
    GroupObject (C ⥤ D) ⥤ C ⥤ GroupObject D where
  obj G := GroupObjectFunctorToFunctorGroupObject.obj G
  map α := GroupObjectFunctorToFunctorGroupObject.map α

variable {C D}

namespace GroupObjectFunctorToFunctorGroupObject

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

end GroupObjectFunctorToFunctorGroupObject

namespace FunctorGroupObjectToGroupObjectFunctor

variable (F : C ⥤ (GroupObject D))

@[simp]
def obj_X : C ⥤ D where
  obj := fun X ↦ (F.obj X).X
  map := fun f ↦ (F.map f).hom

@[simp]
def obj_one : ⊤_ (C ⥤ D) ⟶ obj_X F where
  app := fun X ↦ terminalComparison ((evaluation C D).obj X) ≫ (F.obj X).one
  naturality := by
    intro X Y f
    simp only [obj_X, Category.assoc, GroupObject.Hom.one_hom]
    rw [← Category.assoc]
    congr 1
    exact Subsingleton.elim _ _

@[simp]
def obj_mul : obj_X F ⨯ obj_X F ⟶ obj_X F where
  app := fun X ↦ prodComparison ((evaluation C D).obj X) (obj_X F) (obj_X F) ≫ (F.obj X).mul
  naturality := by
    intro X Y f
    simp only [evaluation_obj_obj, Category.assoc, GroupObject.Hom.mul_hom]
    have := prodComparison_natTrans ((evaluation C D).map f) (X := obj_X F) (Y := obj_X F)
    simp only [evaluation_obj_obj, evaluation_map_app] at this
    conv_lhs => rw [← Category.assoc, ← this]
    simp only [obj_X, Category.assoc, GroupObject.Hom.mul_hom]

@[simp]
def obj_inv : obj_X F ⟶ obj_X F where
  app := fun X ↦ (F.obj X).inv
  naturality :=  fun X Y f ↦ by
    simp only [obj_X]
    rw [(F.map f).inv_hom]

@[simp]
def obj : GroupObject (C ⥤ D) where
  X := obj_X F
  one := obj_one F
  mul := obj_mul F
  inv := obj_inv F
  one_mul := by
    ext X
    simp only [obj_mul, evaluation_obj_obj, NatTrans.comp_app, prod.leftUnitor_hom]
    have := prodComparison_natural ((evaluation C D).obj X) (obj_one F) (𝟙 (obj_X F))
    simp only [evaluation_obj_obj, evaluation_obj_map, NatTrans.id_app] at this
    rw [← Category.assoc, this]
    simp only [obj_one, Category.assoc, obj_X]
    rw [prod_map_comp_left_id_right]
    slice_lhs 3 4 => rw [(F.obj X).one_mul]
    simp only [prod.leftUnitor_hom, prod.map_snd, Category.comp_id]
    erw [prodComparison_snd]
    simp only [evaluation_obj_map]
  mul_one := by
    ext X
    simp only [obj_mul, evaluation_obj_obj, NatTrans.comp_app, prod.rightUnitor_hom]
    have := prodComparison_natural ((evaluation C D).obj X) (𝟙 (obj_X F)) (obj_one F)
    simp only [evaluation_obj_obj, evaluation_obj_map, NatTrans.id_app] at this
    rw [← Category.assoc, this]
    simp only [obj_one, Category.assoc, obj_X]
    rw [prod_map_comp_right_id_left]
    slice_lhs 3 4 => rw [(F.obj X).mul_one]
    simp only [prod.rightUnitor_hom, prod.map_fst, Category.comp_id]
    erw [prodComparison_fst]
    simp only [evaluation_obj_map]
  mul_assoc := by
    ext X
    conv_lhs => congr; congr; rfl; rw [obj_mul]
    simp only [evaluation_obj_obj, NatTrans.comp_app]
    have := prodComparison_natural ((evaluation C D).obj X) (obj_mul F) (𝟙 (obj_X F))
    simp only [evaluation_obj_obj, evaluation_obj_map, NatTrans.id_app] at this
    rw [← Category.assoc, this]
    conv_rhs => congr; rfl; rw [obj_mul]
    simp only [Category.assoc, evaluation_obj_obj]
    conv_lhs => congr; rfl
                rw [obj_mul, prod_map_comp_left_id_right]
    simp only [evaluation_obj_obj]
    have heq : 𝟙 ((obj_X F).obj X) = 𝟙 (F.obj X).X := by simp only [obj_X]
    rw [Category.assoc, heq, (F.obj X).mul_assoc]
    conv_rhs => rw [← Category.assoc, ← Category.assoc]
    conv_lhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    have := prod.associator_comp_prodComparison (F := (evaluation C D).obj X)
      (X := obj_X F) (Y := obj_X F) (Z := obj_X F)
    simp only [evaluation_obj_obj, evaluation_obj_map] at this
    rw [← Category.assoc] at this
    erw [this]
    conv_lhs => rw [Category.assoc]
    conv_rhs => rw [Category.assoc]
    congr 1
    have := prodComparison_natural ((evaluation C D).obj X) (𝟙 (obj_X F)) (obj_mul F)
    simp only [evaluation_obj_obj, evaluation_obj_map, NatTrans.id_app] at this
    erw [this]
    rw [Category.assoc]
    congr 1
    ext
    · simp only [obj_X, prod.map_map, Category.comp_id, prod.map_fst]
    · simp only [obj_X, prod.map_map, Category.comp_id, prod.map_snd, obj_mul, evaluation_obj_obj]
  mul_left_inv := by
    ext X
    simp only [NatTrans.comp_app, obj_one]
    rw [← Category.assoc, Subsingleton.elim ((default : obj_X F ⟶ ⊤_ (C ⥤ D)).app X ≫
      terminalComparison ((evaluation C D).obj X)) default, ← (F.obj X).mul_left_inv]
    simp only [obj_mul, evaluation_obj_obj]
    rw [← Category.assoc]
    congr 1
    ext
    · have := prodComparison_fst ((evaluation C D).obj X) (obj_X F) (obj_X F)
      simp only [evaluation_obj_obj, evaluation_obj_map] at this
      rw [Category.assoc, this]
      simp only [obj_X, obj_inv, limit.lift_π_app, BinaryFan.mk_pt, Functor.const_obj_obj,
        pair_obj_left, BinaryFan.π_app_left, BinaryFan.mk_fst, limit.lift_π]
    · have := prodComparison_snd ((evaluation C D).obj X) (obj_X F) (obj_X F)
      simp only [evaluation_obj_obj, evaluation_obj_map] at this
      rw [Category.assoc, this]
      simp only [obj_X, obj_inv, limit.lift_π_app, BinaryFan.mk_pt, Functor.const_obj_obj,
        pair_obj_right, BinaryFan.π_app_right, BinaryFan.mk_snd, NatTrans.id_app, limit.lift_π]

end FunctorGroupObjectToGroupObjectFunctor

namespace GroupObjectFunctorToFunctorGroupObject

def essSurj : (GroupObjectFunctorToFunctorGroupObject C D).EssSurj where
  mem_essImage F := by
    refine Functor.essImage.ofIso (NatIso.ofComponents ?_ ?_) (Functor.obj_mem_essImage _
      (FunctorGroupObjectToGroupObjectFunctor.obj F))
    · intro X
      simp only [GroupObjectFunctorToFunctorGroupObject, obj, obj_obj,
        FunctorGroupObjectToGroupObjectFunctor.obj, FunctorGroupObjectToGroupObjectFunctor.obj_X]
      refine GroupObject.isoOfIso (Iso.refl _) ?_ ?_ ?_
      · simp only [FunctorGroupObjectToGroupObjectFunctor.obj_one, obj_obj_one, evaluation_obj_obj,
        PreservesTerminal.iso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
      · simp only [FunctorGroupObjectToGroupObjectFunctor.obj_mul,
        FunctorGroupObjectToGroupObjectFunctor.obj_X, evaluation_obj_obj, obj_obj_mul,
        PreservesLimitPair.iso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id,
        prod.map_id_id, Category.id_comp]
      · dsimp; rw [Category.comp_id, Category.id_comp]
    · intro X Y f
      ext
      simp only [GroupObjectFunctorToFunctorGroupObject, FunctorGroupObjectToGroupObjectFunctor.obj,
        id_eq, GroupObject.comp_hom', GroupObject.isoOfIso_hom_hom, Iso.refl_hom]
      simp only [FunctorGroupObjectToGroupObjectFunctor.obj_X, obj]
      erw [Category.id_comp, Category.comp_id]

def isEquivalence : (GroupObjectFunctorToFunctorGroupObject C D).IsEquivalence where
  full := full
  faithful := faithful
  essSurj := essSurj

end GroupObjectFunctorToFunctorGroupObject
