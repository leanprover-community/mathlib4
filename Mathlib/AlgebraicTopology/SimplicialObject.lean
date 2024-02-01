/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.AugmentedSimplexCategory
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Opposites

#align_import algebraic_topology.simplicial_object from "leanprover-community/mathlib"@"5ed51dc37c6b891b79314ee11a50adc2b1df6fd6"

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly a cosimplicial object is functor `SimplexCategory ⥤ C`.)

Use the notation `X _[n]` in the `Simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

-/

set_option autoImplicit true


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

-- porting note: removed @[nolint has_nonempty_instance]
/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `SimplexCategory` to `C`. -/
def SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C
#align category_theory.simplicial_object CategoryTheory.SimplicialObject

@[simps!]
instance : Category (SimplicialObject C) := by
  dsimp only [SimplicialObject]
  infer_instance

namespace SimplicialObject

set_option quotPrecheck false in
/-- `X _[n]` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation3:1000 X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)

variable (X : SimplicialObject C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op
#align category_theory.simplicial_object.δ CategoryTheory.SimplicialObject.δ

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.σ i).op
#align category_theory.simplicial_object.σ CategoryTheory.SimplicialObject.σ

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (CategoryTheory.eqToIso (by congr))
#align category_theory.simplicial_object.eq_to_iso CategoryTheory.SimplicialObject.eqToIso

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  simp [eqToIso]
#align category_theory.simplicial_object.eq_to_iso_refl CategoryTheory.SimplicialObject.eqToIso_refl

/-- The generic case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.simplicial_object.δ_comp_δ CategoryTheory.SimplicialObject.δ_comp_δ

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.simplicial_object.δ_comp_δ' CategoryTheory.SimplicialObject.δ_comp_δ'
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.simplicial_object.δ_comp_δ'' CategoryTheory.SimplicialObject.δ_comp_δ''

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self CategoryTheory.SimplicialObject.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  rw [δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self' CategoryTheory.SimplicialObject.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.simplicial_object.δ_comp_σ_of_le CategoryTheory.SimplicialObject.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_self CategoryTheory.SimplicialObject.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]
#align category_theory.simplicial_object.δ_comp_σ_self' CategoryTheory.SimplicialObject.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_succ CategoryTheory.SimplicialObject.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]
#align category_theory.simplicial_object.δ_comp_σ_succ' CategoryTheory.SimplicialObject.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.σ (Fin.castSucc j) ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt CategoryTheory.SimplicialObject.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) ≫
        X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt' CategoryTheory.SimplicialObject.δ_comp_σ_of_gt'

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.simplicial_object.σ_comp_σ CategoryTheory.SimplicialObject.σ_comp_σ

open Simplicial

@[reassoc (attr := simp)]
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op [n]) = f.app (op [n + 1]) ≫ X'.δ i :=
  f.naturality _
#align category_theory.simplicial_object.δ_naturality CategoryTheory.SimplicialObject.δ_naturality

@[reassoc (attr := simp)]
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op [n + 1]) = f.app (op [n]) ≫ X'.σ i :=
  f.naturality _
#align category_theory.simplicial_object.σ_naturality CategoryTheory.SimplicialObject.σ_naturality

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps!]
def whiskering (D : Type*) [Category D] : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _
#align category_theory.simplicial_object.whiskering CategoryTheory.SimplicialObject.whiskering

-- porting note: removed @[nolint has_nonempty_instance]
/-- Truncated simplicial objects. -/
def Truncated (n : ℕ) :=
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C
#align category_theory.simplicial_object.truncated CategoryTheory.SimplicialObject.Truncated

instance : Category (Truncated C n) := by
  dsimp [Truncated]
  infer_instance

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps!]
def whiskering {n} (D : Type*) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _
#align category_theory.simplicial_object.truncated.whiskering CategoryTheory.SimplicialObject.Truncated.whiskering

variable {C}

end Truncated

section Skeleton

/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion.op
#align category_theory.simplicial_object.sk CategoryTheory.SimplicialObject.sk

end Skeleton

variable (C)

/-- The constant simplicial object is the constant functor. -/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _
#align category_theory.simplicial_object.const CategoryTheory.SimplicialObject.const

-- porting note: removed @[nolint has_nonempty_instance]
/-- The category of augmented simplicial objects, defined as a comma category. -/
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)
#align category_theory.simplicial_object.augmented CategoryTheory.SimplicialObject.Augmented

@[simps!]
instance : Category (Augmented C) := by
  dsimp only [Augmented]
  infer_instance

variable {C}

namespace Augmented

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _
#align category_theory.simplicial_object.augmented.drop CategoryTheory.SimplicialObject.Augmented.drop

/-- The point of the augmentation. -/
@[simps!]
def point : Augmented C ⥤ C :=
  Comma.snd _ _
#align category_theory.simplicial_object.augmented.point CategoryTheory.SimplicialObject.Augmented.point

/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := drop.obj X _[0]
      right := point.obj X
      hom := X.hom.app _ }
  map η :=
    { left := (drop.map η).app _
      right := point.map η
      w := by
        dsimp
        rw [← NatTrans.comp_app]
        erw [η.w]
        rfl }
#align category_theory.simplicial_object.augmented.to_arrow CategoryTheory.SimplicialObject.Augmented.toArrow

/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    (Augmented.drop.map f).app (op (SimplexCategory.mk 0)) ≫ Y.hom.app (op (SimplexCategory.mk 0)) =
      X.hom.app (op (SimplexCategory.mk 0)) ≫ Augmented.point.map f :=
  by convert congr_app f.w (op (SimplexCategory.mk 0))
#align category_theory.simplicial_object.augmented.w₀ CategoryTheory.SimplicialObject.Augmented.w₀

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskeringObj (D : Type*) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      hom := whiskerRight X.hom F ≫ (Functor.constComp _ _ _).hom }
  map η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w := by
        ext
        dsimp [whiskerRight]
        simp only [Category.comp_id, ← F.map_comp, ← NatTrans.comp_app]
        erw [η.w]
        rfl }
#align category_theory.simplicial_object.augmented.whiskering_obj CategoryTheory.SimplicialObject.Augmented.whiskeringObj

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w := by
            ext n
            dsimp
            rw [Category.comp_id, Category.comp_id, η.naturality] } }
  map_comp := fun _ _ => by ext <;> rfl
#align category_theory.simplicial_object.augmented.whiskering CategoryTheory.SimplicialObject.Augmented.whiskering

variable {C}

end Augmented

/-- Augment a simplicial object with an object. -/
@[simps]
def augment (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ([0] : SimplexCategory) ⟶ i),
      X.map g₁.op ≫ f = X.map g₂.op ≫ f) :
    SimplicialObject.Augmented C where
  left := X
  right := X₀
  hom :=
    { app := fun i => X.map (SimplexCategory.const i.unop 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }
#align category_theory.simplicial_object.augment CategoryTheory.SimplicialObject.augment

-- porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op [0]) = f := by
  dsimp
  rw [SimplexCategory.hom_zero_zero ([0].const 0), op_id, X.map_id, Category.id_comp]
#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zero

-- We now want to give an equivelent definition of augmented  simplicial objects using the
-- augmented simplex category.


def augmented'_obj (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) :
    SimplicialObject.Augmented C where
    left := (simplexCategoryToAugmentedSimplexCategory.op ⋙ X)
    right := (X.obj (op [0]ₐ))
    hom :=
    {
      app := fun d => X.map (AugmentedSimplexCategory.map_from_initial
       (simplexCategoryToAugmentedSimplexCategory.obj d.unop).len ).op
      naturality := by
        intro Z Y f
        dsimp only [Functor.id_obj, Functor.comp_obj, Functor.op_obj, Functor.const_obj_obj,
          Functor.comp_map, Functor.op_map, unop_op, Functor.const_obj_map]
        rw [← X.map_comp,← op_comp,Category.comp_id]
        congr
        apply IsInitial.hom_ext  (AugmentedSimplexCategory.zero_isInitial)
    }
lemma augmented'_obj_left (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) :
    (augmented'_obj X).left =(simplexCategoryToAugmentedSimplexCategory.op ⋙ X) := by
      rfl
def augmented'_map {X  Y : AugmentedSimplexCategoryᵒᵖ ⥤ C} (f : X⟶ Y) :
    augmented'_obj X ⟶ augmented'_obj Y where
    left := whiskerLeft simplexCategoryToAugmentedSimplexCategory.op f
    right := f.app  (op [0]ₐ)
    w := by
       rw [Functor.id_map]
       ext d
       rw [NatTrans.comp_app,NatTrans.comp_app]
       simp only [Functor.id_obj, Functor.const_obj_obj, whiskerLeft_app, Functor.op_obj,
         Functor.const_map_app,augmented'_obj,Functor.id_obj, Functor.op_obj, Functor.comp_obj, NatTrans.naturality]

def augmented' : (AugmentedSimplexCategoryᵒᵖ ⥤ C)⥤ SimplicialObject.Augmented C  where
   obj := augmented'_obj
   map := augmented'_map

--We now define the inverse function
def augmented'_inv_obj_obj (X: SimplicialObject.Augmented C) (Y : AugmentedSimplexCategoryᵒᵖ  ):
    C := if Y.unop.len=0 then X.right else X.left.obj (op [Y.unop.len-1])
lemma augmented'_inv_obj_obj_ne0 (X: SimplicialObject.Augmented C) {Y : AugmentedSimplexCategoryᵒᵖ}
    (hY: Y.unop.len ≠ 0): (𝟭 (SimplicialObject C)).obj X.left _[AugmentedSimplexCategory.len Y.unop - 1]
        = augmented'_inv_obj_obj X Y := by
          unfold augmented'_inv_obj_obj
          exact (if_neg hY).symm

lemma augmented'_inv_obj_obj_eq0 (X: SimplicialObject.Augmented C) {Y : AugmentedSimplexCategoryᵒᵖ}
    (hY: Y.unop.len = 0): augmented'_inv_obj_obj X Y=X.right:= by
          unfold augmented'_inv_obj_obj
          exact if_pos hY


--To be moved
def sourceInNA {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y) (hZ : Z.len≠ 0):
    Y.len≠ 0:= by
      let f': Fin (Z.len) →o Fin (Y.len) := f.toOrderHom
      by_contra  hYn
      rw [hYn] at f'
      exact ((fun a ↦ IsEmpty.false a) ∘ f') (⟨ 0 ,Nat.pos_of_ne_zero hZ⟩:Fin (Z.len) )
--To be moved
def toNAObj (Z : AugmentedSimplexCategory)  : SimplexCategory := [Z.len-1]
--To be moved
lemma toNAObj_self {Z : AugmentedSimplexCategory} (hZ: Z.len ≠ 0) :
   simplexCategoryToAugmentedSimplexCategory.obj (toNAObj Z) = Z:= by
      unfold simplexCategoryToAugmentedSimplexCategory
      dsimp
      apply AugmentedSimplexCategory.ext
      exact Nat.succ_pred hZ
--To be moved
def toNAMap' {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y)
    (hZ :Z.len≠ 0) : (toNAObj Z) ⟶ (toNAObj Y) :=
    SimplexCategory.Hom.mk ((OrderHomClass.toOrderHom
    (Fin.castIso (Nat.succ_pred (sourceInNA f hZ)).symm)).comp
     ((f.toOrderHom).comp (OrderHomClass.toOrderHom (Fin.castIso (Nat.succ_pred hZ))) ))
def toNAMap {Y Z: AugmentedSimplexCategory} (f: Z ⟶ Y)
    (hZ :Z.len≠ 0) : (toNAObj Z) ⟶ (toNAObj Y) := SimplexCategory.Hom.mk (  (eqToHom (toNAObj_self (hZ))) ≫  f≫
    (eqToHom (toNAObj_self (sourceInNA f hZ)).symm) )
--To be moved
lemma toNAMap_id { Z: AugmentedSimplexCategory}  (hZ :Z.len≠ 0) :
     toNAMap (𝟙 Z) hZ = 𝟙 ([Z.len-1] :SimplexCategory) := by
       unfold toNAMap
       rw [← eqToHom_refl,← eqToHom_refl,eqToHom_trans,eqToHom_trans]
       all_goals rfl
--To be moved
lemma toNAMap_comp { Y Z  W: AugmentedSimplexCategory}  (hW :W.len≠ 0)
    (f: Z ⟶ Y) (g : W ⟶ Z) :
     toNAMap (g ≫ f) hW = (toNAMap g hW) ≫  (toNAMap f (sourceInNA g hW))   := by
       have ht: (toNAMap g hW) ≫  (toNAMap f (sourceInNA g hW)) =
       SimplexCategory.Hom.mk ( (eqToHom (toNAObj_self (hW)))≫ g
       ≫  ((eqToHom (toNAObj_self (sourceInNA g hW)).symm) ≫
      (eqToHom (toNAObj_self (sourceInNA g hW)))) ≫ f ≫
      (eqToHom (toNAObj_self (sourceInNA f (sourceInNA g hW))).symm)
      ) := by
        rfl
       rw [ht,eqToHom_trans,eqToHom_refl]
       rfl
 --To be moved
lemma imagSC_ne_zero (Z : SimplexCategory ):
    (simplexCategoryToAugmentedSimplexCategory.obj  Z).len ≠  0 := by
      unfold  simplexCategoryToAugmentedSimplexCategory
      exact Nat.succ_ne_zero (SimplexCategory.len Z)
--To be moved
lemma image_morphism {X Z : SimplexCategory  } (f: Z ⟶ X):
 toNAMap (simplexCategoryToAugmentedSimplexCategory.map f)
  (imagSC_ne_zero Z) = f := by
    unfold simplexCategoryToAugmentedSimplexCategory toNAMap
    dsimp
    change _= SimplexCategory.Hom.mk (f.toOrderHom)
    congr
    apply OrderHom.ext
    rfl
--To be moved
lemma toNAMap_self {X Z : AugmentedSimplexCategory  } (f: Z ⟶ X ) (hZ :Z.len ≠ 0):
   eqToHom (toNAObj_self hZ).symm≫ simplexCategoryToAugmentedSimplexCategory.map (toNAMap f hZ)
    ≫ eqToHom (toNAObj_self (sourceInNA f hZ)) =  f
    := by
      rw [eqToHom_comp_iff,comp_eqToHom_iff]
      rfl


def augmented'_inv_obj_map' (X: SimplicialObject.Augmented C) (Y : AugmentedSimplexCategoryᵒᵖ  )
    : augmented'_inv_obj_obj X Y ⟶ X.right :=  by
    by_cases h: Y.unop.len=0
    · exact eqToHom (augmented'_inv_obj_obj_eq0 X h)
    · exact (eqToHom (augmented'_inv_obj_obj_ne0 X h).symm) ≫  X.hom.app (op [Y.unop.len-1])

def augmented'_inv_obj_map (X: SimplicialObject.Augmented C) {Y Z: AugmentedSimplexCategoryᵒᵖ}
    (f: Y ⟶ Z): augmented'_inv_obj_obj X Y ⟶ augmented'_inv_obj_obj X Z :=  by
    by_cases hZ : Z.unop.len =0
    · exact  (augmented'_inv_obj_map' X Y)≫ (eqToHom (augmented'_inv_obj_obj_eq0 X hZ).symm)
    · exact (eqToHom (augmented'_inv_obj_obj_ne0 X (sourceInNA f.unop hZ)).symm)
       ≫ X.left.map (toNAMap f.unop hZ).op
        ≫ (eqToHom (augmented'_inv_obj_obj_ne0 X hZ))

def augmented'_inv_obj (X: SimplicialObject.Augmented C) :
  (AugmentedSimplexCategoryᵒᵖ ⥤ C) where
   obj := augmented'_inv_obj_obj X
   map := augmented'_inv_obj_map X
   map_id := by {
    simp only
    intro Y
    by_cases hY: Y.unop.len=0
    ·  unfold augmented'_inv_obj_map augmented'_inv_obj_map'
       rw [dif_pos hY,dif_pos hY]
       simp only [eqToHom_trans, eqToHom_refl]
    ·  unfold augmented'_inv_obj_map
       rw [dif_neg hY]
       rw [unop_id,toNAMap_id]
       have th: (𝟙 ([AugmentedSimplexCategory.len Y.unop - 1]:SimplexCategory)).op =
         (𝟙 (op [AugmentedSimplexCategory.len Y.unop - 1]:SimplexCategoryᵒᵖ )):= by
         rfl
       rw [th,X.left.map_id,← eqToHom_refl,← eqToHom_refl,← eqToHom_refl,eqToHom_trans,
       eqToHom_trans]
       all_goals rfl
   }
   map_comp := by {
    intro Y Z W f g
    by_cases hW : W.unop.len=0
    · dsimp only
      unfold augmented'_inv_obj_map
      rw [dif_pos hW,dif_pos hW]
      by_cases hZ : Z.unop.len=0
      · unfold augmented'_inv_obj_map'
        rw [dif_pos hZ,dif_pos hZ]
        simp only [Functor.id_obj, eqToHom_trans, Category.assoc]
      · unfold augmented'_inv_obj_map'
        rw [dif_neg hZ,dif_neg hZ,dif_neg (sourceInNA f.unop hZ)]
        rw [← Category.assoc,← Category.assoc,← Category.assoc]
        rw [Category.assoc _ (eqToHom _) (eqToHom _)]
        rw [eqToHom_trans,eqToHom_refl]
        simp only [Functor.id_obj, Category.assoc, Category.comp_id]
        rw [← Category.assoc,← Category.assoc,← Category.assoc]
        rw [Category.assoc (eqToHom _) (X.left.map _) _]
        have hx:= X.hom.naturality (toNAMap f.unop hZ).op
        unfold toNAObj at hx
        rw [show X.left.map (toNAMap f.unop hZ).op = ((𝟭 (SimplicialObject C)).obj X.left).map
        (toNAMap f.unop hZ).op from rfl, hx]
        simp only [Functor.id_obj, Category.assoc, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id]
    · have hZ := sourceInNA g.unop hW
      dsimp only
      unfold augmented'_inv_obj_map
      rw [dif_neg hW,dif_neg hW,dif_neg hZ,unop_comp,toNAMap_comp,op_comp,X.left.map_comp]
      simp only [Functor.id_obj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
   }



lemma augmented'_inv_obj_left  (X: Augmented C) :
simplexCategoryToAugmentedSimplexCategory.op ⋙ augmented'_inv_obj X = X.left := by
  apply Functor.ext
  intro Y Z f
  rw [Functor.comp_map]
  unfold augmented'_inv_obj augmented'_inv_obj_map
  dsimp
  rw [dif_neg (imagSC_ne_zero Z.unop)]
  simp
  congr
  exact image_morphism f.unop
  --obj
  intro Y
  rw [Functor.comp_obj]
  unfold augmented'_inv_obj augmented'_inv_obj_obj
  dsimp
  rw [if_neg (imagSC_ne_zero Y.unop)]
  congr






def augmented'_inv_map_app  {X1 X2: SimplicialObject.Augmented C}  (f :X1 ⟶ X2)
    (Y : AugmentedSimplexCategoryᵒᵖ): (augmented'_inv_obj X1).obj Y⟶ (augmented'_inv_obj X2).obj Y
     := by
      by_cases hY: Y.unop.len=0
      ·  exact (eqToHom (augmented'_inv_obj_obj_eq0 X1 hY)) ≫ f.right ≫
             (eqToHom (augmented'_inv_obj_obj_eq0 X2 hY).symm)
      · exact (eqToHom (augmented'_inv_obj_obj_ne0 X1 hY).symm)≫  f.left.app (op [Y.unop.len-1])
         ≫  (eqToHom (augmented'_inv_obj_obj_ne0 X2 hY))


def augmented'_inv_map  {X1 X2: SimplicialObject.Augmented C}  (f :X1 ⟶ X2):
    augmented'_inv_obj X1 ⟶ augmented'_inv_obj X2 where
    app Y :=by
           by_cases  hY: Y.unop.len=0
           ·  exact (eqToHom (augmented'_inv_obj_obj_eq0 X1 hY)) ≫ f.right ≫
             (eqToHom (augmented'_inv_obj_obj_eq0 X2 hY).symm)
           · exact (eqToHom (augmented'_inv_obj_obj_ne0 X1 hY).symm)≫  f.left.app (op [Y.unop.len-1])
         ≫  (eqToHom (augmented'_inv_obj_obj_ne0 X2 hY))
    naturality := by {
      intro Y Z g
      dsimp
      unfold augmented'_inv_obj augmented'_inv_obj_map
      dsimp
      by_cases hZ : Z.unop.len =0
      · unfold augmented'_inv_obj_map'
        rw [dif_pos hZ,dif_pos hZ,dif_pos hZ]
        by_cases hY : Y.unop.len=0
        · rw [dif_pos hY,dif_pos hY,dif_pos hY]
          simp only [eqToHom_trans, eqToHom_trans_assoc, Category.assoc]
        · rw [dif_neg hY,dif_neg hY,dif_neg hY]
          simp
          rw [← Category.assoc,← Category.assoc, Category.assoc _ _ f.right]
          have h1:=f.w
          apply congrArg NatTrans.app at h1
          have h2 := congrFun h1 (op [AugmentedSimplexCategory.len Y.unop - 1])
          rw [NatTrans.comp_app,NatTrans.comp_app,show ((const C).map f.right).app
            (op [AugmentedSimplexCategory.len Y.unop - 1]) = f.right from rfl] at h2
          rw [← h2]
          simp only [Functor.id_obj, Functor.const_obj_obj, Functor.id_map, Category.assoc]
      · rw [dif_neg hZ,dif_neg hZ,dif_neg hZ, dif_neg (sourceInNA g.unop hZ )]
        simp
        rw [← Category.assoc,← Category.assoc,← Category.assoc,← Category.assoc]
        rw [Category.assoc _ _ (X2.left.map _)]
        change _=(eqToHom _ ≫ f.left.app (op (toNAObj Y.unop)) ≫ X2.left.map (toNAMap g.unop hZ).op) ≫
    eqToHom _
        rw [← f.left.naturality,Category.assoc,Category.assoc,Category.assoc,Category.assoc]
        congr
    }


def augmented'_inv : SimplicialObject.Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)  where
   obj := augmented'_inv_obj
   map := augmented'_inv_map
   map_id := by {
    intro X
    apply NatTrans.ext
    funext Y
    unfold augmented'_inv_map
    dsimp only [Functor.id_obj, instCategoryAugmented_id_right, instCategoryAugmented_id_left_app,
      NatTrans.id_app]
    split
    all_goals simp only [ Category.id_comp, eqToHom_trans, eqToHom_refl]
   }
   map_comp := by {
    intro X1 X2 X3 F G
    apply NatTrans.ext
    funext Y
    unfold augmented'_inv_map
    dsimp
    by_cases hY: Y.unop.len=0
    · rw [dif_pos hY,dif_pos hY,dif_pos hY]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · rw [dif_neg hY,dif_neg hY,dif_neg hY]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
   }

lemma unitIso_equiv (X : (AugmentedSimplexCategoryᵒᵖ ⥤ C)) : (augmented' ⋙ augmented'_inv ).obj X =X
  :=by
    rw [Functor.comp_obj]
    apply Functor.ext
    case h_obj => {
      intro Y
      by_cases hY :Y.unop.len=0
      · unfold augmented'_inv augmented'_inv_obj augmented'_inv_obj_obj
        dsimp
        rw [if_pos hY]
        unfold augmented' augmented'_obj
        dsimp
        congr
        all_goals exact id hY.symm
      · change _=X.obj (op ( Y.unop))
        rw [←  (toNAObj_self hY)]
        change _ =( simplexCategoryToAugmentedSimplexCategory.op ⋙ X).obj  (op (toNAObj Y.unop))
        rw [← augmented'_obj_left]
        unfold augmented'_inv augmented'_inv_obj augmented'_inv_obj_obj
        dsimp
        rw [if_neg hY]
        rfl
    }
    case h_map => {
      intro Y Z f
      by_cases hZ : Z.unop.len =0
      · unfold augmented'_inv augmented'_inv_obj augmented'_inv_obj_map
        dsimp
        rw [dif_pos hZ]
        by_cases hY : Y.unop.len =0
        · unfold augmented'_inv_obj_map'
          rw [dif_pos hY]
          have ht : Y=Z := by
            change op (Y.unop)=op (Z.unop)
            apply congrArg
            apply AugmentedSimplexCategory.ext
            rw [hZ,hY]
          have hf: (f)= (eqToHom ht):= by
             change (f.unop).op= (eqToHom ht).unop.op
             apply congrArg
             apply IsInitial.hom_ext (AugmentedSimplexCategory.len_zero_isInitial hZ)
          rw [hf,eqToHom_map X]
          simp only [eqToHom_trans]
        · unfold augmented'_inv_obj_map'
          rw [dif_neg hY]
          unfold augmented' augmented'_obj
          dsimp
          simp
          let g:= AugmentedSimplexCategory.map_from_initial   (simplexCategoryToAugmentedSimplexCategory.obj [Y.unop.len-1]).len
          change eqToHom _ ≫ X.map g.op ≫ _ =_
          have hsour : op [(simplexCategoryToAugmentedSimplexCategory.obj [ Y.unop.len - 1]).len]ₐ = Y  := by
            change _= op (Y.unop)
            congr
            apply AugmentedSimplexCategory.ext
            unfold simplexCategoryToAugmentedSimplexCategory
            exact Nat.succ_pred hY
          have htar: Z = (op [0]ₐ):= by
            change op (Z.unop)= _
            apply congrArg
            apply AugmentedSimplexCategory.ext
            exact hZ
          have hgt : g = (eqToHom (hsour) ≫ f ≫ eqToHom (htar)).unop:= by
            apply IsInitial.hom_ext AugmentedSimplexCategory.zero_isInitial
          rw [hgt]
          change _ ≫ X.map (eqToHom (hsour) ≫ f ≫ eqToHom (htar)) ≫ _=_
          rw [ X.map_comp,X.map_comp,eqToHom_map X,eqToHom_map X]
          simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      · change _=_ ≫ X.map (f.unop).op ≫ _
        rw [←  (toNAMap_self f.unop hZ)]
        rw [op_comp, op_comp, X.map_comp, X.map_comp]
        rw [eqToHom_op,eqToHom_op,eqToHom_map X,eqToHom_map X]
        rw [Category.assoc,Category.assoc,eqToHom_trans]
        rw [← Category.assoc,← Category.assoc,eqToHom_trans,Category.assoc]
        change _=_≫ (augmented'_obj X).left.map (toNAMap f.unop hZ).op
           ≫ _
        unfold augmented'_inv augmented'_inv_obj augmented'_inv_obj_map
        dsimp
        rw [dif_neg hZ]
        rfl

    }
--The aim is to use isoMake
-- augmented'_obj_left
lemma counitIso_equiv_left   (X : Augmented C) :
    ((augmented'_inv⋙ augmented' ).obj X).left = X.left:= by
    rw [Functor.comp_obj]
    unfold augmented'
    dsimp
    rw [augmented'_obj_left]
    exact augmented'_inv_obj_left X

lemma counitIso_equiv_right   (X : Augmented C) :
 ((augmented'_inv⋙ augmented' ).obj X).right = X.right :=
   rfl

def counitIso_obj (X : Augmented C) : ((augmented'_inv⋙ augmented' ).obj X) ≅ X:= by
    refine Comma.isoMk (CategoryTheory.eqToIso (counitIso_equiv_left X))
     (CategoryTheory.eqToIso (counitIso_equiv_right X)) (?_)
    simp
    apply NatTrans.ext
    funext d
    unfold augmented' augmented'_inv  augmented'_obj augmented'_inv_obj augmented'_inv_obj_obj
      augmented'_inv_obj_map augmented'_inv_obj_map'
    dsimp
    have h0 : AugmentedSimplexCategory.len [0]ₐ = 0 := rfl
    rw [dif_pos h0]
    rw [dif_neg (imagSC_ne_zero d.unop )]
    simp
    congr
    change _= X.hom.app (op [d.unop.len+1-1])
    have hd : op ([d.unop.len+1-1] : SimplexCategory) = d :=rfl
    simp [hd]
    have hde : ((augmented'_inv ⋙ augmented').obj X).left.obj d = X.left.obj d := by
      rfl
    have hx : (eqToHom (counitIso_equiv_left X)).app d = eqToHom hde := by
        apply eqToHom_app
    rw [hx]
    simp
    exact Category.id_comp (X.hom.app d)

lemma unitIso_nat (X1 X2 : AugmentedSimplexCategoryᵒᵖ ⥤ C)  (F :X1⟶ X2):
(𝟭 (AugmentedSimplexCategoryᵒᵖ ⥤ C)).map F ≫ eqToHom (unitIso_equiv X2).symm
= eqToHom (unitIso_equiv X1).symm  ≫ (augmented' ⋙ augmented'_inv).map F:= by
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
  apply NatTrans.ext
  funext d
  unfold augmented'  augmented'_inv  augmented'_inv_map
  simp
  by_cases hd: d.unop.len=0
  · rw [dif_pos hd]
    simp only [comp_eqToHom_iff,eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
    exact dcongr_arg F.app (unop_eq_iff_eq_op.mp hd)
  · rw [dif_neg hd]
    unfold augmented'_map
    simp only [Functor.id_obj, whiskerLeft_app, Functor.op_obj, unop_op, eqToHom_trans_assoc,
      comp_eqToHom_iff, Category.assoc, eqToHom_trans]
    have hD: d=op (simplexCategoryToAugmentedSimplexCategory.obj [d.unop.len - 1]) := by
      change op d.unop =_
      apply congrArg
      exact (toNAObj_self hd).symm
    exact dcongr_arg F.app hD

def unitIso' : 𝟭 (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≅ augmented' ⋙ augmented'_inv where
  hom := {
    app := by
      intro X
      exact eqToHom (unitIso_equiv X).symm
    naturality := by
       intro X1 X2 F
       exact unitIso_nat X1 X2 F
  }
  inv := {
    app := by
        intro X
        exact eqToHom (unitIso_equiv X)
    naturality := by
      intro X1 X2 F
      rw [← eqToHom_comp_iff]
      symm
      rw [← Category.assoc,← comp_eqToHom_iff]
      exact unitIso_nat X1 X2 F
  }

def counitIso'   : augmented'_inv ⋙  augmented' ≅ 𝟭 (Augmented C) where
  hom := {
    app := by
      intro X
      exact (counitIso_obj X).hom
    naturality := by
      intro X1 X2 F
      simp
      apply Comma.hom_ext
      · rw [Comma.comp_left,Comma.comp_left]
        unfold augmented' augmented'_map counitIso_obj augmented'_inv augmented'_inv_map
        apply NatTrans.ext
        funext d
        dsimp
        rw [dif_neg (imagSC_ne_zero d.unop)]
        simp
        rw [eqToHom_app,eqToHom_app]
        exact eqToHom_naturality F.left.app (by rfl)
      · rw [Comma.comp_right,Comma.comp_right]
        unfold augmented' augmented'_map counitIso_obj augmented'_inv augmented'_inv_map
        dsimp
        rw [dif_pos (by rfl)]
        simp
        have ht: 𝟙 (augmented'.obj (augmented'_inv_obj X1)).right ≫ F.right = F.right :=
          Category.id_comp F.right
        rw [ht]
        exact Category.comp_id F.right
  }
  inv := {
    app := by
      intro X
      exact (counitIso_obj X).inv
    naturality := by
        intro X1 X2 F
        simp
        apply Comma.hom_ext
        · rw [Comma.comp_left,Comma.comp_left]
          unfold augmented' augmented'_map counitIso_obj augmented'_inv augmented'_inv_map
          apply NatTrans.ext
          funext d
          dsimp
          rw [dif_neg (imagSC_ne_zero d.unop)]
          simp
          rw [eqToHom_app,eqToHom_app]
          exact eqToHom_naturality F.left.app rfl
        · rw [Comma.comp_right,Comma.comp_right]
          unfold augmented' augmented'_map counitIso_obj augmented'_inv augmented'_inv_map
          dsimp
          rw [dif_pos (by rfl)]
          simp
          have ht: 𝟙 (augmented'.obj (augmented'_inv_obj X1)).right ≫ F.right =F.right :=
             Category.id_comp F.right
          rw [ht]
          exact Category.comp_id F.right
  }


def equiv :(AugmentedSimplexCategoryᵒᵖ ⥤ C)  ≌ (Augmented C) where
   functor :=  augmented'
   inverse := augmented'_inv
   unitIso := unitIso'
   counitIso := counitIso'
   functor_unitIso_comp := by
      intro X1
      unfold  unitIso' counitIso' counitIso_obj  Comma.isoMk
      dsimp
      apply Comma.hom_ext
      · rw [eqToHom_map,Comma.comp_left,Comma.eqToHom_left,Comma.id_left,eqToHom_trans,eqToHom_refl]
      · rw [eqToHom_map,Comma.comp_right,Comma.eqToHom_right,eqToHom_refl,Category.comp_id
         ,Comma.id_right]







end SimplicialObject

-- porting note: removed @[nolint has_nonempty_instance]
/-- Cosimplicial objects. -/
def CosimplicialObject :=
  SimplexCategory ⥤ C
#align category_theory.cosimplicial_object CategoryTheory.CosimplicialObject

@[simps!]
instance : Category (CosimplicialObject C) := by
  dsimp only [CosimplicialObject]
  infer_instance

namespace CosimplicialObject

-- mathport name: cosimplicial_object.at
set_option quotPrecheck false in
/-- `X _[n]` denotes the `n`th-term of the cosimplicial object X -/
scoped[Simplicial]
  notation:1000 X " _[" n "]" =>
    (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  infer_instance

instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y)
    (h : ∀ (n : SimplexCategory), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)

variable (X : CosimplicialObject C)

open Simplicial

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.δ i)
#align category_theory.cosimplicial_object.δ CategoryTheory.CosimplicialObject.δ

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.σ i)
#align category_theory.cosimplicial_object.σ CategoryTheory.CosimplicialObject.σ

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (CategoryTheory.eqToIso (by rw [h]))
#align category_theory.cosimplicial_object.eq_to_iso CategoryTheory.CosimplicialObject.eqToIso

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  simp [eqToIso]
#align category_theory.cosimplicial_object.eq_to_iso_refl CategoryTheory.CosimplicialObject.eqToIso_refl

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.cosimplicial_object.δ_comp_δ CategoryTheory.CosimplicialObject.δ_comp_δ

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred fun (hj : j = 0) => by simp only [hj, Fin.not_lt_zero] at H) ≫
        X.δ (Fin.castSucc i) := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.cosimplicial_object.δ_comp_δ' CategoryTheory.CosimplicialObject.δ_comp_δ'

@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.cosimplicial_object.δ_comp_δ'' CategoryTheory.CosimplicialObject.δ_comp_δ''

/-- The special case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ i ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self CategoryTheory.CosimplicialObject.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by
  subst H
  rw [δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self' CategoryTheory.CosimplicialObject.δ_comp_δ_self'

/-- The second cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.δ (Fin.castSucc i) ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_le CategoryTheory.CosimplicialObject.δ_comp_σ_of_le

/-- The first part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_self CategoryTheory.CosimplicialObject.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_self]
#align category_theory.cosimplicial_object.δ_comp_σ_self' CategoryTheory.CosimplicialObject.δ_comp_σ_self'

/-- The second part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_succ CategoryTheory.CosimplicialObject.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  rw [δ_comp_σ_succ]
#align category_theory.cosimplicial_object.δ_comp_σ_succ' CategoryTheory.CosimplicialObject.δ_comp_σ_succ'

/-- The fourth cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.δ i.succ ≫ X.σ (Fin.castSucc j) = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
        X.δ (i.pred <|
          fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt' CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt'

/-- The fifth cosimplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ (Fin.castSucc i) ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.cosimplicial_object.σ_comp_σ CategoryTheory.CosimplicialObject.σ_comp_σ

@[reassoc (attr := simp)]
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (SimplexCategory.mk (n + 1)) = f.app (SimplexCategory.mk n) ≫ X'.δ i :=
  f.naturality _
#align category_theory.cosimplicial_object.δ_naturality CategoryTheory.CosimplicialObject.δ_naturality

@[reassoc (attr := simp)]
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (SimplexCategory.mk n) = f.app (SimplexCategory.mk (n + 1)) ≫ X'.σ i :=
  f.naturality _
#align category_theory.cosimplicial_object.σ_naturality CategoryTheory.CosimplicialObject.σ_naturality

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps!]
def whiskering (D : Type*) [Category D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _
#align category_theory.cosimplicial_object.whiskering CategoryTheory.CosimplicialObject.whiskering

-- porting note: removed @[nolint has_nonempty_instance]
/-- Truncated cosimplicial objects. -/
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C
#align category_theory.cosimplicial_object.truncated CategoryTheory.CosimplicialObject.Truncated

instance : Category (Truncated C n) := by
  dsimp [Truncated]
  infer_instance

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps!]
def whiskering {n} (D : Type*) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _
#align category_theory.cosimplicial_object.truncated.whiskering CategoryTheory.CosimplicialObject.Truncated.whiskering

variable {C}

end Truncated

section Skeleton

/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion
#align category_theory.cosimplicial_object.sk CategoryTheory.CosimplicialObject.sk

end Skeleton

variable (C)

/-- The constant cosimplicial object. -/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _
#align category_theory.cosimplicial_object.const CategoryTheory.CosimplicialObject.const

-- porting note: removed @[nolint has_nonempty_instance]
/-- Augmented cosimplicial objects. -/
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))
#align category_theory.cosimplicial_object.augmented CategoryTheory.CosimplicialObject.Augmented

@[simps!]
instance : Category (Augmented C) := by
  dsimp only [Augmented]
  infer_instance

variable {C}

namespace Augmented

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : Augmented C} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  Comma.hom_ext _ _ h₁ h₂

/-- Drop the augmentation. -/
@[simps!]
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _
#align category_theory.cosimplicial_object.augmented.drop CategoryTheory.CosimplicialObject.Augmented.drop

/-- The point of the augmentation. -/
@[simps!]
def point : Augmented C ⥤ C :=
  Comma.fst _ _
#align category_theory.cosimplicial_object.augmented.point CategoryTheory.CosimplicialObject.Augmented.point

/-- The functor from augmented objects to arrows. -/
@[simps!]
def toArrow : Augmented C ⥤ Arrow C where
  obj X :=
    { left := point.obj X
      right := drop.obj X _[0]
      hom := X.hom.app _ }
  map η :=
    { left := point.map η
      right := (drop.map η).app _
      w := by
        dsimp
        rw [← NatTrans.comp_app]
        erw [← η.w]
        rfl }
#align category_theory.cosimplicial_object.augmented.to_arrow CategoryTheory.CosimplicialObject.Augmented.toArrow

variable (C)

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskeringObj (D : Type*) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj X :=
    { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.hom F }
  map η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w := by
        ext
        dsimp
        rw [Category.id_comp, Category.id_comp, ← F.map_comp, ← F.map_comp, ← NatTrans.comp_app]
        erw [← η.w]
        rfl }
#align category_theory.cosimplicial_object.augmented.whiskering_obj CategoryTheory.CosimplicialObject.Augmented.whiskeringObj

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map η :=
    { app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w := by
            ext n
            dsimp
            rw [Category.id_comp, Category.id_comp, η.naturality] }
      naturality := fun _ _ f => by ext <;> dsimp <;> simp }
#align category_theory.cosimplicial_object.augmented.whiskering CategoryTheory.CosimplicialObject.Augmented.whiskering

variable {C}

end Augmented

open Simplicial

/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0])
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : ([0] : SimplexCategory) ⟶ i),
      f ≫ X.map g₁ = f ≫ X.map g₂) : CosimplicialObject.Augmented C where
  left := X₀
  right := X
  hom :=
    { app := fun i => f ≫ X.map (SimplexCategory.const i 0)
      naturality := by
        intro i j g
        dsimp
        simpa [← X.map_comp] using w _ _ _ }
#align category_theory.cosimplicial_object.augment CategoryTheory.CosimplicialObject.augment

-- porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
    (X.augment X₀ f w).hom.app [0] = f := by
  dsimp
  rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, Category.comp_id]
#align category_theory.cosimplicial_object.augment_hom_zero CategoryTheory.CosimplicialObject.augment_hom_zero

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps!]
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _
#align category_theory.simplicial_cosimplicial_equiv CategoryTheory.simplicialCosimplicialEquiv

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps!]
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _
#align category_theory.cosimplicial_simplicial_equiv CategoryTheory.cosimplicialSimplicialEquiv

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps!]
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) :
    CosimplicialObject.Augmented Cᵒᵖ where
  left := Opposite.op X.right
  right := X.left.rightOp
  hom := NatTrans.rightOp X.hom
#align category_theory.simplicial_object.augmented.right_op CategoryTheory.SimplicialObject.Augmented.rightOp

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps!]
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) :
    SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  hom := NatTrans.leftOp X.hom
#align category_theory.cosimplicial_object.augmented.left_op CategoryTheory.CosimplicialObject.Augmented.leftOp

/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps!]
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) :
    X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso (CategoryTheory.eqToIso <| by aesop_cat)
#align category_theory.simplicial_object.augmented.right_op_left_op_iso CategoryTheory.SimplicialObject.Augmented.rightOpLeftOpIso

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps!]
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso
#align category_theory.cosimplicial_object.augmented.left_op_right_op_iso CategoryTheory.CosimplicialObject.Augmented.leftOpRightOpIso

variable (C)

/-- A functorial version of `SimplicialObject.Augmented.rightOp`. -/
@[simps]
def simplicialToCosimplicialAugmented :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ where
  obj X := X.unop.rightOp
  map f :=
    { left := f.unop.right.op
      right := NatTrans.rightOp f.unop.left
      w := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }
#align category_theory.simplicial_to_cosimplicial_augmented CategoryTheory.simplicialToCosimplicialAugmented

/-- A functorial version of `Cosimplicial_object.Augmented.leftOp`. -/
@[simps]
def cosimplicialToSimplicialAugmented :
    CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ where
  obj X := Opposite.op X.leftOp
  map f :=
    Quiver.Hom.op <|
      { left := NatTrans.leftOp f.right
        right := f.left.unop
        w := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w (unop x)).symm }
#align category_theory.cosimplicial_to_simplicial_augmented CategoryTheory.cosimplicialToSimplicialAugmented

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps! functor inverse]
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ :=
  Equivalence.mk (simplicialToCosimplicialAugmented _) (cosimplicialToSimplicialAugmented _)
    (NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      rw [← f.op_unop]
      simp_rw [← op_comp]
      congr 1
      aesop_cat)
    (NatIso.ofComponents fun X => X.leftOpRightOpIso)
#align category_theory.simplicial_cosimplicial_augmented_equiv CategoryTheory.simplicialCosimplicialAugmentedEquiv

end CategoryTheory
