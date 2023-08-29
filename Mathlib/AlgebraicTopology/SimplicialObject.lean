/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathlib.AlgebraicTopology.SimplexCategory
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
  -- ⊢ Category.{?u.61, max u v} (SimplexCategoryᵒᵖ ⥤ C)
  infer_instance
  -- 🎉 no goals

namespace SimplicialObject

set_option quotPrecheck false in
/-- `X _[n]` denotes the `n`th-term of the simplicial object X -/
scoped[Simplicial]
  notation:1000 X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

open Simplicial

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  -- ⊢ HasLimitsOfShape J (SimplexCategoryᵒᵖ ⥤ C)
  infer_instance
  -- 🎉 no goals

instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [SimplicialObject]
  -- ⊢ HasColimitsOfShape J (SimplexCategoryᵒᵖ ⥤ C)
  infer_instance
  -- 🎉 no goals

instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : SimplicialObject C} (f g : X ⟶ Y)
  (h : ∀ (n : SimplexCategoryᵒᵖ), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)
                       -- ⊢ NatTrans.app f x✝ = NatTrans.app g x✝
                            -- 🎉 no goals

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
                                       -- 🎉 no goals
#align category_theory.simplicial_object.eq_to_iso CategoryTheory.SimplicialObject.eqToIso

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  -- ⊢ (eqToIso X h).hom = (Iso.refl (X.obj (op [n]))).hom
  simp [eqToIso]
  -- 🎉 no goals
#align category_theory.simplicial_object.eq_to_iso_refl CategoryTheory.SimplicialObject.eqToIso_refl

/-- The generic case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ (Fin.castSucc i) ≫ X.δ j := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.succ j)).op ≫ X.map (SimplexCategory.δ i).op = …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_δ CategoryTheory.SimplicialObject.δ_comp_δ

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ j ≫ X.δ i =
      X.δ (Fin.castSucc i) ≫
        X.δ (j.pred <| fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) := by
                                              -- 🎉 no goals
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ j).op ≫ X.map (SimplexCategory.δ i).op = X.map (Sim …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_δ' CategoryTheory.SimplicialObject.δ_comp_δ'
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ j.succ ≫ X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.succ j)).op ≫ X.map (SimplexCategory.δ (Fin.ca …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_δ'' CategoryTheory.SimplicialObject.δ_comp_δ''

/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ (Fin.castSucc i) ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.castSucc i)).op ≫ X.map (SimplexCategory.δ i). …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_δ_self CategoryTheory.SimplicialObject.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  subst H
  -- ⊢ δ X (Fin.castSucc i) ≫ δ X i = δ X (Fin.succ i) ≫ δ X i
  rw [δ_comp_δ_self]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_δ_self' CategoryTheory.SimplicialObject.δ_comp_δ_self'

/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.σ j.succ ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ (Fin.succ j)).op ≫ X.map (SimplexCategory.δ (Fin.ca …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_of_le CategoryTheory.SimplicialObject.δ_comp_σ_of_le

/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ (Fin.castSucc i) = 𝟙 _ := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ i).op ≫ X.map (SimplexCategory.δ (Fin.castSucc i)). …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_self CategoryTheory.SimplicialObject.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  -- ⊢ σ X i ≫ δ X (Fin.castSucc i) = 𝟙 (X.obj (op [n]))
  rw [δ_comp_σ_self]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_self' CategoryTheory.SimplicialObject.δ_comp_σ_self'

/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ i).op ≫ X.map (SimplexCategory.δ (Fin.succ i)).op = …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_succ CategoryTheory.SimplicialObject.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by
  subst H
  -- ⊢ σ X i ≫ δ X (Fin.succ i) = 𝟙 (X.obj (op [n]))
  rw [δ_comp_σ_succ]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_succ' CategoryTheory.SimplicialObject.δ_comp_σ_succ'

/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.σ (Fin.castSucc j) ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ (Fin.castSucc j)).op ≫ X.map (SimplexCategory.δ (Fi …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_of_gt CategoryTheory.SimplicialObject.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred <| fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) ≫
                                            -- 🎉 no goals
        X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ j).op ≫ X.map (SimplexCategory.δ i).op = X.map (Sim …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
  -- 🎉 no goals
#align category_theory.simplicial_object.δ_comp_σ_of_gt' CategoryTheory.SimplicialObject.δ_comp_σ_of_gt'

/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ (Fin.castSucc i) = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ j).op ≫ X.map (SimplexCategory.σ (Fin.castSucc i)). …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]
  -- 🎉 no goals
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
  -- ⊢ Category.{?u.68325, max u v} ((SimplexCategory.Truncated n)ᵒᵖ ⥤ C)
  infer_instance
  -- 🎉 no goals

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  -- ⊢ HasLimitsOfShape J ((SimplexCategory.Truncated n)ᵒᵖ ⥤ C)
  infer_instance
  -- 🎉 no goals

instance {n} [HasLimits C] : HasLimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  -- ⊢ HasColimitsOfShape J ((SimplexCategory.Truncated n)ᵒᵖ ⥤ C)
  infer_instance
  -- 🎉 no goals

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
  -- ⊢ Category.{?u.76503, max u v} (Comma (𝟭 (SimplicialObject C)) (const C))
  infer_instance
  -- 🎉 no goals

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
        -- ⊢ NatTrans.app η.left (op [0]) ≫ NatTrans.app Y✝.hom (op [0]) = NatTrans.app X …
        rw [← NatTrans.comp_app]
        -- ⊢ NatTrans.app (η.left ≫ Y✝.hom) (op [0]) = NatTrans.app X✝.hom (op [0]) ≫ η.r …
        erw [η.w]
        -- ⊢ NatTrans.app (X✝.hom ≫ (const C).map η.right) (op [0]) = NatTrans.app X✝.hom …
        rfl }
        -- 🎉 no goals
#align category_theory.simplicial_object.augmented.to_arrow CategoryTheory.SimplicialObject.Augmented.toArrow

/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    (Augmented.drop.map f).app (op (SimplexCategory.mk 0)) ≫ Y.hom.app (op (SimplexCategory.mk 0)) =
      X.hom.app (op (SimplexCategory.mk 0)) ≫ Augmented.point.map f :=
  by convert congr_app f.w (op (SimplexCategory.mk 0))
     -- 🎉 no goals
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
        -- ⊢ NatTrans.app ((𝟭 (SimplicialObject D)).map (whiskerRight η.left F) ≫ ((fun X …
        dsimp [whiskerRight]
        -- ⊢ F.map (NatTrans.app η.left n✝) ≫ F.map (NatTrans.app Y✝.hom n✝) ≫ 𝟙 (F.obj Y …
        simp only [Category.comp_id, ← F.map_comp, ← NatTrans.comp_app]
        -- ⊢ F.map (NatTrans.app (η.left ≫ Y✝.hom) n✝) = F.map (NatTrans.app X✝.hom n✝ ≫  …
        erw [η.w]
        -- ⊢ F.map (NatTrans.app (X✝.hom ≫ (const C).map η.right) n✝) = F.map (NatTrans.a …
        rfl }
        -- 🎉 no goals
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
            -- ⊢ NatTrans.app ((𝟭 (SimplicialObject D)).map (whiskerLeft (drop.obj A) η) ≫ (( …
            dsimp
            -- ⊢ NatTrans.app η (A.left.obj n) ≫ Y✝.map (NatTrans.app A.hom n) ≫ 𝟙 (Y✝.obj A. …
            rw [Category.comp_id, Category.comp_id, η.naturality] } }
            -- 🎉 no goals
  map_comp := fun _ _ => by ext <;> rfl
                            -- ⊢ NatTrans.app (NatTrans.app ({ obj := whiskeringObj C D, map := fun {X Y} η = …
                                    -- 🎉 no goals
                                    -- 🎉 no goals
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
        -- ⊢ ((𝟭 (SimplicialObject C)).obj X).map g ≫ (fun i => X.map (SimplexCategory.co …
        dsimp
        -- ⊢ X.map g ≫ X.map (SimplexCategory.const j.unop 0).op ≫ f = (X.map (SimplexCat …
        rw [← g.op_unop]
        -- ⊢ X.map g.unop.op ≫ X.map (SimplexCategory.const j.unop 0).op ≫ f = (X.map (Si …
        simpa only [← X.map_comp, ← Category.assoc, Category.comp_id, ← op_comp] using w _ _ _ }
        -- 🎉 no goals
#align category_theory.simplicial_object.augment CategoryTheory.SimplicialObject.augment

-- porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
    (X.augment X₀ f w).hom.app (op [0]) = f := by
  dsimp
  -- ⊢ X.map (SimplexCategory.const [0] 0).op ≫ f = f
  rw [SimplexCategory.hom_zero_zero ([0].const 0), op_id, X.map_id, Category.id_comp]
  -- 🎉 no goals
#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zero

end SimplicialObject

-- porting note: removed @[nolint has_nonempty_instance]
/-- Cosimplicial objects. -/
def CosimplicialObject :=
  SimplexCategory ⥤ C
#align category_theory.cosimplicial_object CategoryTheory.CosimplicialObject

@[simps!]
instance : Category (CosimplicialObject C) := by
  dsimp only [CosimplicialObject]
  -- ⊢ Category.{?u.208707, max u v} (SimplexCategory ⥤ C)
  infer_instance
  -- 🎉 no goals

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
  -- ⊢ HasLimitsOfShape J (SimplexCategory ⥤ C)
  infer_instance
  -- 🎉 no goals

instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [CosimplicialObject]
  -- ⊢ HasColimitsOfShape J (SimplexCategory ⥤ C)
  infer_instance
  -- 🎉 no goals

instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C}

-- porting note: added to ease automation
@[ext]
lemma hom_ext {X Y : CosimplicialObject C} (f g : X ⟶ Y)
  (h : ∀ (n : SimplexCategory), f.app n = g.app n) : f = g :=
  NatTrans.ext _ _ (by ext; apply h)
                       -- ⊢ NatTrans.app f x✝ = NatTrans.app g x✝
                            -- 🎉 no goals

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
                                       -- 🎉 no goals
#align category_theory.cosimplicial_object.eq_to_iso CategoryTheory.CosimplicialObject.eqToIso

@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  -- ⊢ (eqToIso X h).hom = (Iso.refl (X.obj [n])).hom
  simp [eqToIso]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.eq_to_iso_refl CategoryTheory.CosimplicialObject.eqToIso_refl

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ (Fin.castSucc i) := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ i) ≫ X.map (SimplexCategory.δ (Fin.succ j)) = X.map …
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_δ CategoryTheory.CosimplicialObject.δ_comp_δ

@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred <| fun (hj : j = 0) => by simp only [hj, Fin.not_lt_zero] at H) ≫
                                            -- 🎉 no goals
        X.δ (Fin.castSucc i) := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ i) ≫ X.map (SimplexCategory.δ j) = X.map (SimplexCa …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_δ' CategoryTheory.CosimplicialObject.δ_comp_δ'

@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j) :
    X.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.castLT i (_ : ↑i < n + 2))) ≫ X.map (SimplexCa …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_δ'' CategoryTheory.CosimplicialObject.δ_comp_δ''

/-- The special case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} :
    X.δ i ≫ X.δ (Fin.castSucc i) = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  -- ⊢ X.map (SimplexCategory.δ i) ≫ X.map (SimplexCategory.δ (Fin.castSucc i)) = X …
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_δ_self CategoryTheory.CosimplicialObject.δ_comp_δ_self

@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by
  subst H
  -- ⊢ δ X i ≫ δ X (Fin.castSucc i) = δ X i ≫ δ X (Fin.succ i)
  rw [δ_comp_δ_self]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_δ_self' CategoryTheory.CosimplicialObject.δ_comp_δ_self'

/-- The second cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j) :
    X.δ (Fin.castSucc i) ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.castSucc i)) ≫ X.map (SimplexCategory.σ (Fin.s …
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_of_le CategoryTheory.CosimplicialObject.δ_comp_σ_of_le

/-- The first part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ (Fin.castSucc i) ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.castSucc i)) ≫ X.map (SimplexCategory.σ i) = 𝟙 …
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_self CategoryTheory.CosimplicialObject.δ_comp_σ_self

@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  -- ⊢ δ X (Fin.castSucc i) ≫ σ X i = 𝟙 (X.obj [n])
  rw [δ_comp_σ_self]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_self' CategoryTheory.CosimplicialObject.δ_comp_σ_self'

/-- The second part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.succ i)) ≫ X.map (SimplexCategory.σ i) = 𝟙 (X. …
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_succ CategoryTheory.CosimplicialObject.δ_comp_σ_succ

@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by
  subst H
  -- ⊢ δ X (Fin.succ i) ≫ σ X i = 𝟙 (X.obj [n])
  rw [δ_comp_σ_succ]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_succ' CategoryTheory.CosimplicialObject.δ_comp_σ_succ'

/-- The fourth cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i) :
    X.δ i.succ ≫ X.σ (Fin.castSucc j) = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.δ (Fin.succ i)) ≫ X.map (SimplexCategory.σ (Fin.castS …
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt

@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
        X.δ (i.pred <|
          fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) := by
                                 -- 🎉 no goals
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.δ i) ≫ X.map (SimplexCategory.σ j) = X.map (SimplexCa …
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
  -- 🎉 no goals
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt' CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt'

/-- The fifth cosimplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ (Fin.castSucc i) ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  -- ⊢ X.map (SimplexCategory.σ (Fin.castSucc i)) ≫ X.map (SimplexCategory.σ j) = X …
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]
  -- 🎉 no goals
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
  -- ⊢ Category.{?u.295628, max u v} (SimplexCategory.Truncated n ⥤ C)
  infer_instance
  -- 🎉 no goals

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  -- ⊢ HasLimitsOfShape J (SimplexCategory.Truncated n ⥤ C)
  infer_instance
  -- 🎉 no goals

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [Truncated]
  -- ⊢ HasColimitsOfShape J (SimplexCategory.Truncated n ⥤ C)
  infer_instance
  -- 🎉 no goals

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
  -- ⊢ Category.{?u.303800, max u v} (Comma (const C) (𝟭 (CosimplicialObject C)))
  infer_instance
  -- 🎉 no goals

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
        -- ⊢ η.left ≫ NatTrans.app Y✝.hom [0] = NatTrans.app X✝.hom [0] ≫ NatTrans.app η. …
        rw [← NatTrans.comp_app]
        -- ⊢ η.left ≫ NatTrans.app Y✝.hom [0] = NatTrans.app (X✝.hom ≫ η.right) [0]
        erw [← η.w]
        -- ⊢ η.left ≫ NatTrans.app Y✝.hom [0] = NatTrans.app ((const C).map η.left ≫ Y✝.h …
        rfl }
        -- 🎉 no goals
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
        -- ⊢ NatTrans.app ((const D).map (F.map η.left) ≫ ((fun X => { left := F.obj (poi …
        dsimp
        -- ⊢ F.map η.left ≫ 𝟙 (F.obj Y✝.left) ≫ F.map (NatTrans.app Y✝.hom n✝) = (𝟙 (F.ob …
        rw [Category.id_comp, Category.id_comp, ← F.map_comp, ← F.map_comp, ← NatTrans.comp_app]
        -- ⊢ F.map (η.left ≫ NatTrans.app Y✝.hom n✝) = F.map (NatTrans.app (X✝.hom ≫ η.ri …
        erw [← η.w]
        -- ⊢ F.map (η.left ≫ NatTrans.app Y✝.hom n✝) = F.map (NatTrans.app ((const C).map …
        rfl }
        -- 🎉 no goals
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
            -- ⊢ NatTrans.app ((const D).map (NatTrans.app η (point.obj A)) ≫ ((whiskeringObj …
            dsimp
            -- ⊢ NatTrans.app η A.left ≫ 𝟙 (Y✝.obj A.left) ≫ Y✝.map (NatTrans.app A.hom n) =  …
            rw [Category.id_comp, Category.id_comp, η.naturality] }
            -- 🎉 no goals
      naturality := fun _ _ f => by ext <;> dsimp <;> simp }
                                    -- ⊢ ((whiskeringObj C D X✝).map f ≫ (fun A => CommaMorphism.mk (NatTrans.app η ( …
                                            -- ⊢ X✝.map f.left ≫ NatTrans.app η x✝.left = NatTrans.app η x✝¹.left ≫ Y✝.map f. …
                                            -- ⊢ X✝.map (NatTrans.app f.right n✝) ≫ NatTrans.app η (x✝.right.obj n✝) = NatTra …
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
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
        -- ⊢ ((const C).obj X₀).map g ≫ (fun i => f ≫ X.map (SimplexCategory.const i 0))  …
        dsimp
        -- ⊢ 𝟙 X₀ ≫ f ≫ X.map (SimplexCategory.const j 0) = (f ≫ X.map (SimplexCategory.c …
        simpa [← X.map_comp] using w _ _ _ }
        -- 🎉 no goals
#align category_theory.cosimplicial_object.augment CategoryTheory.CosimplicialObject.augment

-- porting note: removed @[simp] as the linter complains
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
    (X.augment X₀ f w).hom.app [0] = f := by
  dsimp
  -- ⊢ f ≫ X.map (SimplexCategory.const [0] 0) = f
  rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, Category.comp_id]
  -- 🎉 no goals
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
                                                                    -- 🎉 no goals
#align category_theory.simplicial_object.augmented.right_op_left_op_iso CategoryTheory.SimplicialObject.Augmented.rightOpLeftOpIso

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps!]
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (CategoryTheory.eqToIso <| by simp) X.right.leftOpRightOpIso
                                            -- 🎉 no goals
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
        -- ⊢ NatTrans.app ((CosimplicialObject.const Cᵒᵖ).map f.unop.right.op ≫ ((fun X = …
        dsimp
        -- ⊢ f.unop.right.op ≫ (NatTrans.app Y✝.unop.hom (op x)).op = (NatTrans.app X✝.un …
        simp_rw [← op_comp]
        -- ⊢ (NatTrans.app Y✝.unop.hom (op x) ≫ f.unop.right).op = (NatTrans.app f.unop.l …
        congr 1
        -- ⊢ NatTrans.app Y✝.unop.hom (op x) ≫ f.unop.right = NatTrans.app f.unop.left (o …
        exact (congr_app f.unop.w (op x)).symm }
        -- 🎉 no goals
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
          -- ⊢ NatTrans.app ((𝟭 (SimplicialObject C)).map (NatTrans.leftOp f.right) ≫ (Cosi …
          dsimp
          -- ⊢ (NatTrans.app f.right x.unop).unop ≫ (NatTrans.app X✝.hom x.unop).unop = (Na …
          simp_rw [← unop_comp]
          -- ⊢ (NatTrans.app X✝.hom x.unop ≫ NatTrans.app f.right x.unop).unop = (f.left ≫  …
          congr 1
          -- ⊢ NatTrans.app X✝.hom x.unop ≫ NatTrans.app f.right x.unop = f.left ≫ NatTrans …
          exact (congr_app f.w (unop x)).symm }
          -- 🎉 no goals
#align category_theory.cosimplicial_to_simplicial_augmented CategoryTheory.cosimplicialToSimplicialAugmented

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps! functor inverse]
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ :=
  Equivalence.mk (simplicialToCosimplicialAugmented _) (cosimplicialToSimplicialAugmented _)
    (NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun f => by
      dsimp
      -- ⊢ f ≫ (SimplicialObject.Augmented.rightOpLeftOpIso Y✝.unop).hom.op = (Simplici …
      rw [← f.op_unop]
      -- ⊢ f.unop.op ≫ (SimplicialObject.Augmented.rightOpLeftOpIso Y✝.unop).hom.op = ( …
      simp_rw [← op_comp]
      -- ⊢ ((SimplicialObject.Augmented.rightOpLeftOpIso Y✝.unop).hom ≫ f.unop).op = (C …
      congr 1
      -- ⊢ (SimplicialObject.Augmented.rightOpLeftOpIso Y✝.unop).hom ≫ f.unop = CommaMo …
      aesop_cat)
      -- 🎉 no goals
    (NatIso.ofComponents fun X => X.leftOpRightOpIso)
#align category_theory.simplicial_cosimplicial_augmented_equiv CategoryTheory.simplicialCosimplicialAugmentedEquiv

end CategoryTheory
