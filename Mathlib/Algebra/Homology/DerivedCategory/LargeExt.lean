/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Shift.ShiftedHom

/-!
# Ext groups in abelian categories

If `C` is an abelian category, we define types `LargeExt X Y n`
for objects `X` and `Y` in `C` and `n : ℕ` as a single-field structure
containing a shifted morphism in the derived category of `C`.
Then, we need to introduce an auxiliary universe `w` and the
assumption `HasDerivedCategory.{w} C` so that `LargeExt X Y n : Type w`.
(When using the constructed localized category, we may use `w := max u v`.)

## TODO

* construct the equivalence `LargeExt X Y 0 ≃ (X ⟶ Y)`
* construct the long exact sequences of `Ext`
* shrink the types `LargeExt X Y n` in order to define `SmallExt X Y n : Type w'`
when we know that the `Ext`-groups are `w'`-small, and redefine
`Ext := SmallExt.{v}` (which will work when `C` has enough projectives
or enough injectives).


-/

universe w v u

namespace CategoryTheory

open DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

namespace Abelian

variable (X Y Z T : C) (n : ℕ)

/-- The Ext-groups in an abelian category `C`, define as `Type w` when
`[HasDerivedCategory.{w} C]`. -/
@[ext]
structure LargeExt : Type w where
  /-- a shifted hom in the derived category -/
  hom : ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ)

namespace LargeExt

/-- The bijection between `LargeExt X Y n` and shifted homs in the derived category. -/
@[simps]
def equiv :
    LargeExt X Y n ≃
      ShiftedHom ((singleFunctor C 0).obj X) ((singleFunctor C 0).obj Y) (n : ℤ) where
  toFun := hom
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (LargeExt X Y n) := (equiv X Y n).addCommGroup

@[simp]
lemma add_hom (x y : LargeExt X Y n) : (x + y).hom = x.hom + y.hom := rfl

@[simp]
lemma sub_hom (x y : LargeExt X Y n) : (x - y).hom = x.hom - y.hom := rfl

@[simp]
lemma neg_hom (x : LargeExt X Y n) : (-x).hom = -x.hom := rfl

@[simp]
lemma zero_hom (X Y : C) (n : ℕ) : (0 : LargeExt X Y n).hom = 0 := rfl

@[simp]
lemma zsmul_hom (a : ℤ) (x : LargeExt X Y n) :
    (a • x).hom = a • x.hom := rfl

variable {X Y Z T}

/-- The canonical map `(X ⟶ Y) → LargeExt X Y 0`: -/
@[simps]
noncomputable def ofHom (f : X ⟶ Y) : LargeExt X Y 0 :=
  mk (ShiftedHom.mk₀ ((0 : ℕ) : ℤ) rfl ((singleFunctor C 0).map f))

/-- The composition on `Ext`-groups. -/
@[simps]
noncomputable def comp {a b c : ℕ} (α : LargeExt X Y a) (β : LargeExt Y Z b) (h : a + b = c) :
    LargeExt X Z c where
  hom := α.hom.comp β.hom (by omega)

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ}
    (α : LargeExt X Y a₁) (β : LargeExt Y Z a₂) (γ : LargeExt Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show _ = a by omega) =
      α.comp (β.comp γ h₂₃) (by omega) := by
  ext
  dsimp
  apply ShiftedHom.comp_assoc
  omega

@[simp]
lemma comp_add {a b c : ℕ} (α : LargeExt X Y a) (β₁ β₂ : LargeExt Y Z b) (h : a + b = c) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by aesop

@[simp]
lemma add_comp {a b c : ℕ} (α₁ α₂ : LargeExt X Y a) (β : LargeExt Y Z b) (h : a + b = c) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by aesop

@[simp]
lemma ofHom_id_comp {a : ℕ} (α : LargeExt X Y a) :
    (ofHom (𝟙 X)).comp α (zero_add a) = α := by aesop

@[simp]
lemma comp_ofHom_id {a : ℕ} (α : LargeExt X Y a) :
    α.comp (ofHom (𝟙 Y)) (add_zero a) = α := by aesop

lemma ofHom_comp_ofHom (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (add_zero _) := by
  ext
  dsimp
  rw [Functor.map_comp]
  symm
  apply ShiftedHom.mk₀_comp_mk₀

/-- Auxiliary definition for `LargeExtFunctor`. -/
noncomputable def LargeExtFunctor.obj (n : ℕ) (X : C) : C ⥤ Ab where
  obj := fun Y => AddCommGroupCat.of (LargeExt X Y n)
  map := fun g => AddCommGroupCat.ofHom (AddMonoidHom.mk'
    (fun α ↦ α.comp (ofHom g) (add_zero n)) (by aesop))
  map_comp _ _ := by
    ext
    dsimp
    simp only [ofHom_comp_ofHom]
    symm
    apply comp_assoc
    all_goals omega

variable (C)

/-- The `Ext`-groups in degree `n : ℕ`, as a bifunctor `Cᵒᵖ ⥤ C ⥤ Ab.{w}`. -/
noncomputable def LargeExtFunctor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ Ab.{w} where
  obj X := LargeExtFunctor.obj n X.unop
  map {X₁ X₂} f :=
    { app := fun Y => AddCommGroupCat.ofHom (AddMonoidHom.mk'
        (fun β ↦ (ofHom f.unop).comp β (zero_add n)) (by aesop))
      naturality := by
        intros
        ext
        symm
        dsimp [LargeExtFunctor.obj]
        apply comp_assoc
        all_goals omega }
  map_comp _ _ := by
    ext
    dsimp [LargeExtFunctor.obj]
    simp only [ofHom_comp_ofHom]
    apply comp_assoc
    all_goals omega

end LargeExt

end Abelian

end CategoryTheory
