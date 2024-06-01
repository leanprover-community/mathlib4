/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

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
def fullyFaithfulForget : (forget R).FullyFaithful where
  preimage φ := ⟨φ⟩

instance : (forget R).Faithful := (fullyFaithfulForget R).faithful

instance : (forget R).Full := (fullyFaithfulForget R).full

/-- Evaluation on an object `X` gives a functor
`SheafOfModules R ⥤ ModuleCat (R.val.obj X)`. -/
def evaluation (X : Cᵒᵖ) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.val.obj X) :=
  forget _ ⋙ PresheafOfModules.evaluation _ X

end SheafOfModules

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M₁ M₂ : PresheafOfModules.{v} R}
    (f : M₁ ⟶ M₂) {N : PresheafOfModules.{v} R}
    (hN : Presheaf.IsSheaf J N.presheaf)
    [J.WEqualsLocallyBijective AddCommGroupCat.{v}]
    [Presheaf.IsLocallySurjective J f.hom]
    [Presheaf.IsLocallyInjective J f.hom]

/-- The bijection `(M₂ ⟶ N) ≃ (M₁ ⟶ N)` induced by a locally bijective morphism
`f : M₁ ⟶ M₂` of presheaves of modules, when `N` is a sheaf. -/
@[simps]
noncomputable def homEquivOfIsLocallyBijective : (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  toFun φ := f ≫ φ
  invFun ψ :=
    { hom := ((J.W_of_isLocallyBijective f.hom).homEquiv _ hN).symm ψ.hom
      map_smul := by
        obtain ⟨φ, hφ⟩ := ((J.W_of_isLocallyBijective f.hom).homEquiv _ hN).surjective ψ.hom
        simp only [← hφ, Equiv.symm_apply_apply]
        dsimp at hφ
        intro X r y
        apply hN.isSeparated _ _ (Presheaf.imageSieve_mem J f.hom y)
        rintro Y p ⟨x, hx⟩
        have eq := ψ.map_smul _ (R.map p.op r) x
        simp only [← hφ] at eq
        dsimp at eq
        erw [← NatTrans.naturality_apply φ p.op (r • y), N.map_smul, M₂.map_smul,
          ← NatTrans.naturality_apply φ p.op y, ← hx, ← eq, f.map_smul]
        rfl }
  left_inv φ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective f.hom).homEquiv _ hN).left_inv φ.hom)
  right_inv ψ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective f.hom).homEquiv _ hN).right_inv ψ.hom)

end PresheafOfModules
