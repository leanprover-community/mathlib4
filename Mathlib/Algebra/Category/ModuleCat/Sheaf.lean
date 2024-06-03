/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Sheaves of modules over a sheaf of rings

In this file, we define the category `SheafOfModules R` when `R : Sheaf J RingCat`
is a sheaf of rings on a category `C` equipped with a Grothendieck topology `J`.

## TODO
* construct the associated sheaf: more precisely, given a morphism of `α : P ⟶ R.val`
where `P` is a presheaf of rings and `R` a sheaf of rings such that `α` identifies
`R` to the associated sheaf of `P`, then construct a sheafification functor
`PresheafOfModules P ⥤ SheafOfModules R`.

-/

universe v v₁ u₁ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- A sheaf of modules is a presheaf of modules such that the underlying presheaf
of abelian groups is a sheaf. -/
structure SheafOfModules where
  /-- the underlying presheaf of modules of a sheaf of modules -/
  val : PresheafOfModules.{v} R.val
  isSheaf : Presheaf.IsSheaf J val.presheaf

namespace SheafOfModules

variable {R}

/-- A morphism between sheaves of modules is a morphism between the underlying
presheaves of modules. -/
@[ext]
structure Hom (X Y : SheafOfModules.{v} R) where
  /-- a morphism between the underlying presheaves of modules -/
  val : X.val ⟶ Y.val

instance : Category (SheafOfModules.{v} R) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩

@[ext]
lemma hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Hom.ext _ _ h

@[simp]
lemma id_val (X : SheafOfModules.{v} R) : Hom.val (𝟙 X) = 𝟙 X.val := rfl

@[simp, reassoc]
lemma comp_val {X Y Z : SheafOfModules.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val := rfl

variable (R)
/-- The forgetful functor `SheafOfModules.{v} R ⥤ PresheafOfModules R.val`. -/
@[simps]
def forget : SheafOfModules.{v} R ⥤ PresheafOfModules R.val where
  obj F := F.val
  map φ := φ.val

/-- The forget functor `SheafOfModules R ⥤ PresheafOfModules R.val` is fully faithful. -/
@[simps]
def fullyFaithfulForget : (forget.{v} R).FullyFaithful where
  preimage φ := ⟨φ⟩

instance : (forget.{v} R).Faithful := (fullyFaithfulForget R).faithful

instance : (forget.{v} R).Full := (fullyFaithfulForget R).full

/-- Evaluation on an object `X` gives a functor
`SheafOfModules R ⥤ ModuleCat (R.val.obj X)`. -/
def evaluation (X : Cᵒᵖ) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.val.obj X) :=
  forget _ ⋙ PresheafOfModules.evaluation _ X

/-- The type of sections of a sheaf of modules. -/
abbrev sections (M : SheafOfModules.{v} R) : Type _ := M.val.sections

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGroupCat.{u})]

/-- The obvious free sheaf of modules of rank `1`. -/
@[simps]
def unit : SheafOfModules R where
  val := PresheafOfModules.unit R.val
  isSheaf := ((sheafCompose J (forget₂ RingCat.{u} AddCommGroupCat.{u})).obj R).cond

variable {R}

/-- The bijection `(unit R ⟶ M) ≃ M.sections` for `M : SheafOfModules R`. -/
def unitHomEquiv (M : SheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections :=
  (fullyFaithfulForget R).homEquiv.trans M.val.unitHomEquiv

@[simp]
lemma unitHomEquiv_apply_coe (M : SheafOfModules R) (f : unit R ⟶ M) (X : Cᵒᵖ) :
    (M.unitHomEquiv f).val X = f.val.app X (1 : R.val.obj X) := rfl

end SheafOfModules
