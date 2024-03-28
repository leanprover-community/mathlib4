/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.AlgebraicTopology.AugmentedSimplexCategory
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Opposites

#align_import algebraic_topology.simplicial_object from "leanprover-community/mathlib"@"5ed51dc37c6b891b79314ee11a50adc2b1df6fd6"

/-!
# Simplicial objects in a category.

A simplicial object in a category `C` is a `C`-valued presheaf on `SimplexCategory`.
(Similarly a cosimplicial object is functor `SimplexCategory ⥤ C`.)

Use the notation `X _[n]` in the `Simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

Define augmented simplicial objects via the comma category construction, and show that this is
equivalent to functors `AugmentedSimplexCategoryᵒᵖ ⥤ C`.

-/

open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

-- porting note (#10927): removed @[nolint has_nonempty_instance]
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

-- Porting note (#10688): added to ease automation
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

-- porting note (#10927): removed @[nolint has_nonempty_instance]
/-- Truncated simplicial objects. -/
def Truncated (n : ℕ) :=
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C
#align category_theory.simplicial_object.truncated CategoryTheory.SimplicialObject.Truncated

instance {n : ℕ} : Category (Truncated C n) := by
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

-- porting note (#10927): removed @[nolint has_nonempty_instance]
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

-- Porting note (#10688): added to ease automation
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
    { app := fun i => X.map (SimplexCategory.const _ _ 0).op ≫ f
      naturality := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }
#align category_theory.simplicial_object.augment CategoryTheory.SimplicialObject.augment

-- Porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op [0]) = f := by simp
#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zero




namespace augFuncEquiv
open AugmentedSimplexCategory
namespace functor'
/--The object map for the functor
`(AugmentedSimplexCategoryᵒᵖ ⥤ C) ⥤ Augmented C`-/
def obj' (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) :
    SimplicialObject.Augmented C where
    left := SimplexCategory.augment.op ⋙ X
    right := X.obj (op [0]ₐ)
    hom :=
    {
      app := fun d => X.map (map_from_initial (SimplexCategory.augment.obj d.unop).len ).op
      naturality := by
        intros
        simp only [Functor.id_obj, Functor.comp_obj, Functor.op_obj, Functor.const_obj_obj,
          Functor.comp_map, Functor.op_map, ← X.map_comp, ← op_comp, smallCategory_comp, Hom.comp,
          Functor.const_obj_map, Category.comp_id]
        apply congrArg X.map ∘ congrArg op
        apply IsInitial.hom_ext zeroIsInitial
    }
/--The morphism map for the functor
 `(AugmentedSimplexCategoryᵒᵖ ⥤ C) ⥤ Augmented C` -/
def map' {X  Y : AugmentedSimplexCategoryᵒᵖ ⥤ C} (f : X⟶ Y) : obj' X ⟶ obj' Y where
  left := whiskerLeft SimplexCategory.augment.op f
  right := f.app  (op [0]ₐ)
  w := by
       ext
       rw [Functor.id_map,NatTrans.comp_app,NatTrans.comp_app]
       simp only [Functor.id_obj, Functor.const_obj_obj, whiskerLeft_app, Functor.op_obj,
         Functor.const_map_app,obj',Functor.id_obj, Functor.op_obj, Functor.comp_obj,
          NatTrans.naturality]

end functor'

/--The functor `(AugmentedSimplexCategoryᵒᵖ ⥤ C)⥤ Augmented C`-/
def functor' : (AugmentedSimplexCategoryᵒᵖ ⥤ C)⥤ SimplicialObject.Augmented C  where
  obj := functor'.obj'
  map := functor'.map'

namespace inverse'
namespace obj'
/--The object map for the functor which is the image of `X ∈ Augmented C` under the functor
`Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def obj'' (X: SimplicialObject.Augmented C) (Y : AugmentedSimplexCategoryᵒᵖ  ): C :=
    if Y.unop.len=0 then X.right else X.left.obj (op [Y.unop.len-1])

/--Part of the morphism map for the functor which is the image of `X ∈ Augmented C`
 under the functor  `Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def mapTargetZero' (X: SimplicialObject.Augmented C) (Y : AugmentedSimplexCategoryᵒᵖ  ) :
    obj'.obj'' X Y ⟶ X.right :=  by
    by_cases hY : Y.unop.len=0
    · exact eqToHom (if_pos hY )
    · exact (eqToHom (if_neg hY )) ≫  X.hom.app (op [Y.unop.len-1])

/--The morphism map for the functor which is the image of `X ∈ Augmented C`
 under the functor  `Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def map'' (X: SimplicialObject.Augmented C) {Y Z: AugmentedSimplexCategoryᵒᵖ} (f: Y ⟶ Z) :
    obj'.obj'' X Y ⟶ obj'.obj'' X Z :=  by
    by_cases hZ : Z.unop.len =0
    · exact  (mapTargetZero' X Y)≫ (eqToHom (if_pos hZ).symm)
    · exact eqToHom (if_neg (strict_initial' f.unop hZ))
       ≫ X.left.map (unaugment.map f.unop hZ).op  ≫ eqToHom (if_neg hZ).symm

end obj'
/--The object map for the functor
`Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def obj' (X: SimplicialObject.Augmented C) : (AugmentedSimplexCategoryᵒᵖ ⥤ C) where
  obj := obj'.obj'' X
  map := obj'.map'' X
  map_id := by
    simp only
    intro Y
    unfold obj'.map'' inverse'.obj'.mapTargetZero'
    by_cases hY: Y.unop.len=0
    ·  rw [dif_pos hY,dif_pos hY,eqToHom_trans,eqToHom_refl]
    ·  rw [dif_neg hY,unop_id,unaugment.map_id,show
       (𝟙 (SimplexCategory.mk (Y.unop.len - 1))).op = 𝟙 (op (SimplexCategory.mk (Y.unop.len - 1)))
       from rfl,X.left.map_id,← eqToHom_refl,← eqToHom_refl,← eqToHom_refl,eqToHom_trans,
       eqToHom_trans]
       all_goals rfl
  map_comp := by
    intro Y Z W f g
    unfold inverse'.obj'.map'' inverse'.obj'.mapTargetZero'
    dsimp only
    by_cases hW : W.unop.len=0
    · rw [dif_pos hW,dif_pos hW]
      by_cases hZ : Z.unop.len=0
      · rw [dif_pos hZ,dif_pos hZ]
        simp only [Functor.id_obj, eqToHom_trans, Category.assoc]
      · have hx:= X.hom.naturality (unaugment.map f.unop hZ).op
        unfold unaugment.obj at hx
        rw [dif_neg hZ,dif_neg hZ,dif_neg (strict_initial' f.unop hZ),← Category.assoc,
        ← Category.assoc,← Category.assoc,Category.assoc _ (eqToHom _) (eqToHom _),eqToHom_trans,
        eqToHom_refl,Category.comp_id,Category.assoc (eqToHom _) (X.left.map _) _,show
        X.left.map (unaugment.map f.unop hZ).op = ((𝟭 (SimplicialObject C)).obj X.left).map
        (unaugment.map f.unop hZ).op from rfl, hx]
        simp only [Functor.id_obj, Category.assoc, Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id]
    · rw [dif_neg hW,dif_neg hW,dif_neg (strict_initial' g.unop hW),unop_comp,unaugment.map_comp,
      op_comp,X.left.map_comp]
      simp only [Functor.id_obj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
/--The morphism map for the functor
`Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def map'  {X1 X2: SimplicialObject.Augmented C}  (f :X1 ⟶ X2): obj' X1 ⟶ obj' X2 where
  app Y :=by
      by_cases  hY: Y.unop.len=0
      · exact eqToHom (if_pos hY) ≫ f.right ≫ eqToHom (if_pos hY).symm
      · exact eqToHom (if_neg hY) ≫ f.left.app (op [Y.unop.len-1]) ≫ eqToHom (if_neg hY).symm
  naturality := by
      intro Y Z g
      dsimp
      unfold obj' inverse'.obj'.map''
      dsimp
      by_cases hZ : Z.unop.len =0
      · unfold inverse'.obj'.mapTargetZero'
        rw [dif_pos hZ,dif_pos hZ,dif_pos hZ]
        by_cases hY : Y.unop.len=0
        · simp only [dif_pos hY,eqToHom_trans, eqToHom_trans_assoc, Category.assoc]
        · simp only [dif_neg hY,Functor.id_obj, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp]
          rw [← Category.assoc,← Category.assoc, Category.assoc _ _ f.right]
          have h2 := congrFun (congrArg NatTrans.app f.w) (op [Y.unop.len - 1])
          rw [NatTrans.comp_app,NatTrans.comp_app,show ((const C).map f.right).app
            (op [Y.unop.len - 1]) = f.right from rfl] at h2
          simp only [← h2,Functor.id_obj, Functor.const_obj_obj, Functor.id_map, Category.assoc]
      · rw [dif_neg hZ,dif_neg hZ,dif_neg hZ,dif_neg (strict_initial' g.unop hZ )]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc,← Category.assoc,← Category.assoc,← Category.assoc,
        Category.assoc _ _ (X2.left.map _),← f.left.naturality,Category.assoc,Category.assoc,
        Category.assoc,Category.assoc]
        congr

end inverse'
/--The functor
`Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def inverse' : SimplicialObject.Augmented C ⥤ (AugmentedSimplexCategoryᵒᵖ ⥤ C)  where
  obj := inverse'.obj'
  map := inverse'.map'
  map_id := by
    intros
    apply NatTrans.ext
    funext
    simp only [inverse'.map', instCategoryAugmented_id_right, Category.id_comp, eqToHom_trans,
      eqToHom_refl, Functor.id_obj, instCategoryAugmented_id_left_app, dite_eq_ite, ite_self,
      NatTrans.id_app]
  map_comp := by
    intros
    apply NatTrans.ext
    funext Y
    by_cases h: Y.unop.len=0
    · simp only [inverse'.map',Functor.id_obj, instCategoryAugmented_comp_right, Category.assoc,
      instCategoryAugmented_comp_left_app, dif_pos h, NatTrans.comp_app, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    · simp only [inverse'.map',Functor.id_obj, instCategoryAugmented_comp_right, Category.assoc,
      instCategoryAugmented_comp_left_app, dif_neg h, NatTrans.comp_app, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]


namespace unitIso'

lemma app' (X : AugmentedSimplexCategoryᵒᵖ ⥤ C) : (functor' ⋙ inverse' ).obj X =X :=by
    rw [Functor.comp_obj]
    apply Functor.ext
    case h_obj =>
      intro Y
      unfold inverse' inverse'.obj' inverse'.obj'.obj'' functor' functor'.obj'
      by_cases hY :Y.unop.len=0
      · simp only [Functor.comp_obj, Functor.op_obj, unop_op,if_pos hY,congrArg X.obj]
        exact congrArg X.obj (congrArg op hY.symm)
      · nth_rewrite 2 [← (op_unop Y)]
        rw [← unaugment_augment_obj hY]
        exact if_neg hY
    case h_map =>
      intro Y Z f
      unfold inverse' inverse'.obj' inverse'.obj'.map'' inverse'.obj'.mapTargetZero'
      by_cases hZ : Z.unop.len =0
      · dsimp
        rw [dif_pos hZ]
        by_cases hY : Y.unop.len =0
        · let hx:= congrArg X.map
            (congrArg Quiver.Hom.op (map_into_initial_eqToHom (lenZeroIsInitial hY) f.unop))
          rw [eqToHom_op,eqToHom_map X,Quiver.Hom.op_unop] at hx
          simp only [dif_pos hY,eqToHom_trans, hx, op_unop]
        · unfold functor' functor'.obj'
          simp only [dif_neg hY,Functor.id_obj,Functor.op_obj, Functor.comp_obj, unop_op]
          rw [show map_from_initial (SimplexCategory.augment.obj [Y.unop.len-1]).len
           =(eqToHom (congrArg op (unaugment_augment_obj hY)) ≫f≫eqToHom (congrArg op hZ)).unop by
           apply IsInitial.hom_ext zeroIsInitial,Quiver.Hom.op_unop,X.map_comp,X.map_comp,
           eqToHom_map X,eqToHom_map X,eqToHom_trans_assoc,Category.assoc,Category.assoc,
           eqToHom_trans]
      · nth_rewrite 2 [← (Quiver.Hom.op_unop f)]
        rw [← unaugment_augment_map f.unop hZ,op_comp, op_comp,X.map_comp,X.map_comp,eqToHom_op,
        eqToHom_op,eqToHom_map X,eqToHom_map X,Category.assoc,Category.assoc,eqToHom_trans,
        eqToHom_trans_assoc]
        exact dif_neg hZ


lemma nat' (X1 X2 : AugmentedSimplexCategoryᵒᵖ ⥤ C)  (F :X1⟶ X2):
    (𝟭 (AugmentedSimplexCategoryᵒᵖ ⥤ C)).map F ≫ eqToHom (app' X2).symm
    = eqToHom (app' X1).symm  ≫ (functor' ⋙ inverse').map F:= by
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
  apply NatTrans.ext
  funext d
  unfold functor'  inverse'  inverse'.map'
  simp
  by_cases hd: d.unop.len=0
  · rw [dif_pos hd]
    simp only [comp_eqToHom_iff,eqToHom_trans_assoc, Category.assoc, eqToHom_trans]
    exact dcongr_arg F.app (unop_eq_iff_eq_op.mp hd)
  · rw [dif_neg hd]
    unfold functor'.map'
    simp only [Functor.id_obj, whiskerLeft_app, Functor.op_obj, unop_op, eqToHom_trans_assoc,
      comp_eqToHom_iff, Category.assoc, eqToHom_trans]
    refine  dcongr_arg F.app ?_
    change op d.unop =_
    apply congrArg
    exact (AugmentedSimplexCategory.unaugment_augment_obj hd).symm

end unitIso'
/--The unit of the equivalance between
`Augmented C` and `(AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def unitIso' : 𝟭 (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≅ functor' ⋙ inverse' where
  hom := {
    app := fun X => eqToHom (unitIso'.app' X).symm
    naturality := fun ⦃X Y⦄ f ↦ unitIso'.nat' X Y f
  }
  inv := {
    app := fun X => eqToHom (unitIso'.app' X)
    naturality := by
      intros
      rw [← eqToHom_comp_iff,← Category.assoc, comp_eqToHom_iff]
      exact (unitIso'.nat' _ _ _).symm
  }

namespace counitIso'
/--Part of the data of the app map for the counit of the equivalance between
`Augmented C` and `(AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def app' (X : Augmented C) : ((inverse'⋙ functor' ).obj X) ≅ X:= by
    refine Comma.isoMk (CategoryTheory.eqToIso ?_) (CategoryTheory.eqToIso (by rfl)) ?_
    change  SimplexCategory.augment.op ⋙ inverse'.obj' X = X.left
    apply Functor.ext
    intro Y Z f
    simp only [inverse'.obj', Functor.comp_obj, Functor.op_obj, Functor.comp_map,
      inverse'.obj'.map'', unop_op, Functor.id_obj, eqToHom_refl, Functor.op_map,
      Quiver.Hom.unop_op, Category.comp_id, Category.id_comp,
      dif_neg (SimplexCategory.augment_len Z.unop)]
    exact congrArg X.left.map (congrArg op (SimplexCategory.augment_unaugment_map f.unop))
    intros
    rfl
    apply NatTrans.ext
    funext d
    unfold functor' inverse'  functor'.obj' inverse'.obj' inverse'.obj'.obj''
      inverse'.obj'.map'' inverse'.obj'.mapTargetZero'
    simp only [Functor.id_obj, Functor.op_obj, Functor.comp_obj, unop_op, eqToHom_refl,
      Quiver.Hom.unop_op, Functor.const_obj_obj, eqToIso.hom, Functor.id_map,
      instCategorySimplicialObject_comp_app, Category.id_comp, Category.comp_id,
      CategoryTheory.eqToIso_refl, Iso.refl_hom, Functor.map_id]
    rw [dif_pos (by rfl),eqToHom_app,eqToHom_refl]
    exact Category.id_comp (X.hom.app d)
end counitIso'
/--The counit of the equivalance between
`Augmented C` and `(AugmentedSimplexCategoryᵒᵖ ⥤ C)`-/
def counitIso'   : inverse' ⋙  functor' ≅ 𝟭 (Augmented C) where
  hom := {
    app := fun X => (augFuncEquiv.counitIso'.app' X).hom
    naturality := by
      intro X1 X2 F
      unfold functor' functor'.map' augFuncEquiv.counitIso'.app' inverse' inverse'.map'
      apply Comma.hom_ext
      · apply NatTrans.ext
        funext d
        simp [Comma.comp_left]
        rw [dif_neg (SimplexCategory.augment_len d.unop),eqToHom_app,eqToHom_app]
        exact eqToHom_naturality F.left.app (by rfl)
      · simp [Comma.comp_right]
        rw [dif_pos (by rfl),show 𝟙 (functor'.obj (inverse'.obj' X1)).right≫F.right=F.right
         from Category.id_comp F.right]
        exact Category.comp_id F.right
  }
  inv := {
    app := fun X => (augFuncEquiv.counitIso'.app' X).inv
    naturality := by
        intro X1 X2 F
        unfold functor' functor'.map' augFuncEquiv.counitIso'.app' inverse' inverse'.map'
        apply Comma.hom_ext
        · apply NatTrans.ext
          funext d
          simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, CategoryTheory.eqToIso_refl,
            instCategoryAugmented_comp_left_app, Comma.isoMk_inv_left, eqToIso.inv,
            Functor.comp_map, unop_op, eqToHom_refl, Category.comp_id, Category.id_comp,
            whiskerLeft_app, Functor.op_obj]
          rw [dif_neg (SimplexCategory.augment_len d.unop),eqToHom_app,eqToHom_app]
          exact eqToHom_naturality F.left.app rfl
        · simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, CategoryTheory.eqToIso_refl,
          instCategoryAugmented_comp_right, Comma.isoMk_inv_right, Iso.refl_inv, Functor.comp_map,
          unop_op, eqToHom_refl, Category.comp_id, Category.id_comp]
          rw [dif_pos (by rfl), show 𝟙 (functor'.obj (inverse'.obj' X1)).right ≫ F.right =F.right
           from  Category.id_comp F.right]
          exact Category.comp_id F.right
  }
end augFuncEquiv
open augFuncEquiv in
/--The equivelence between `Augmented C` and `AugmentedSimplexCategoryᵒᵖ ⥤ C`-/
def augFuncEquiv : AugmentedSimplexCategoryᵒᵖ ⥤ C  ≌ (Augmented C) where
  functor := functor'
  inverse := inverse'
  unitIso := unitIso'
  counitIso := counitIso'
  functor_unitIso_comp := by
      intros
      unfold  unitIso' counitIso' counitIso'.app'  Comma.isoMk
      dsimp
      apply Comma.hom_ext
      · rw [eqToHom_map,Comma.comp_left,Comma.eqToHom_left,Comma.id_left,eqToHom_trans,eqToHom_refl]
      · rw [eqToHom_map,Comma.comp_right,Comma.eqToHom_right,eqToHom_refl,Category.comp_id
         ,Comma.id_right]
end SimplicialObject

-- porting note (#10927): removed @[nolint has_nonempty_instance]
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

-- Porting note (#10688): added to ease automation
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

-- porting note (#10927): removed @[nolint has_nonempty_instance]
/-- Truncated cosimplicial objects. -/
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C
#align category_theory.cosimplicial_object.truncated CategoryTheory.CosimplicialObject.Truncated

instance {n : ℕ} : Category (Truncated C n) := by
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

-- porting note (#10927): removed @[nolint has_nonempty_instance]
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

-- Porting note (#10688): added to ease automation
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
    { app := fun i => f ≫ X.map (SimplexCategory.const _ _ 0)
      naturality := by
        intro i j g
        dsimp
        rw [Category.id_comp, Category.assoc, ← X.map_comp, w] }
#align category_theory.cosimplicial_object.augment CategoryTheory.CosimplicialObject.augment

-- Porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
    (X.augment X₀ f w).hom.app [0] = f := by simp
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
