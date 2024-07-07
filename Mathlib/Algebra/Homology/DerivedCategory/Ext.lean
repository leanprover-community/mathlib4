/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.SmallShiftedHom

/-!
# Ext groups in abelian categories

Let `C` be an abelian category (with `C : Type u` and `Category.{v} C`).
In this file, we introduce the assumption `HasExt.{w} C` which asserts
that morphisms between single complexes in arbitrary degrees in
the derived category of `C` are `w`-small. Under this assumption,
we define `Ext.{w} X Y n : Type w` as shrunk versions of suitable
types of morphisms in the derived category. In particular, when `C` has
enough projectives or enough injectives, the property `HasExt.{v} C`
shall hold (TODO).

Note: in certain situations, `w := v` shall be the preferred
choice of universe (e.g. if `C := ModuleCat.{v} R` with `R : Type v`).
However, in the development of the API for Ext-groups, it is important
to keep a larger degree of generality for universes, as `w < v`
may happen in certain situations. Indeed, if `X : Scheme.{u}`,
then the underlying category of the étale site of `X` shall be a large
category. However, the category `Sheaf X.Etale AddCommGroupCat.{u}`
shall have good properties (because there is a small category of affine
schemes with the same category of sheaves), and even though the type of
morphisms in `Sheaf X.Etale AddCommGroupCat.{u}` shall be
in `Type (u + 1)`, these types are going to be `u`-small.
Then, for `C := Sheaf X.etale AddCommGroupCat.{u}`, we will have
`Category.{u + 1} C`, but `HasExt.{u} C` will hold
(as `C` has enough injectives). Then, the `Ext` groups between étale
sheaves over `X` shall be in `Type u`.

## TODO
* construct the additive structure on `Ext`
* compute `Ext X Y 0`
* define the class in `Ext S.X₃ S.X₁ 1` of a short exact short complex `S`
* construct the long exact sequences of `Ext`.

-/

universe w' w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

open Localization Limits

/-- The property that morphisms between single complexes in arbitrary degrees are `w`-small
in the derived category. -/
abbrev HasExt : Prop :=
  ∀ (X Y : C), HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ
    ((CochainComplex.singleFunctor C 0).obj X) ((CochainComplex.singleFunctor C 0).obj Y)

-- TODO: when the canonical t-structure is formalized, replace `n : ℤ` by `n : ℕ`
lemma hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ), Small.{w}
      ((DerivedCategory.singleFunctor C 0).obj X ⟶
        (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ DerivedCategory.Q]
  constructor
  · intro h X Y n
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((DerivedCategory.singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    refine (small_congr ?_).1 (h X Y (b - a))
    exact (Functor.FullyFaithful.ofFullyFaithful
      (shiftFunctor _ a)).homEquiv.trans
      ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv

lemma hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [hasExt_iff.{w}]
  infer_instance

variable {C}

variable [HasExt.{w} C]

namespace Abelian

/-- A Ext-group in an abelian category `C`, defined as a `Type w` when `[HasExt.{w} C]`. -/
def Ext (X Y : C) (n : ℕ) : Type w :=
  SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((CochainComplex.singleFunctor C 0).obj X)
    ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)

namespace Ext

variable {X Y Z T : C}

/-- The composition of `Ext`. -/
noncomputable def comp {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    Ext X Z c :=
  SmallShiftedHom.comp α β (by omega)

lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : ℕ} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃)
    (h₁₂ : a₁ + a₂ = a₁₂) (h₂₃ : a₂ + a₃ = a₂₃) (h : a₁ + a₂ + a₃ = a) :
    (α.comp β h₁₂).comp γ (show a₁₂ + a₃ = a by omega) =
      α.comp (β.comp γ h₂₃) (by omega) :=
  SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by omega)

section

variable [HasDerivedCategory.{w'} C]

/-- When an instance of `[HasDerivedCategory.{w'} C]` is available, this is the bijection
between `Ext.{w} X Y n` and a type of morphisms in the derived category. -/
noncomputable def homEquiv {n : ℕ} :
    Ext.{w} X Y n ≃ ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
      ((DerivedCategory.singleFunctor C 0).obj Y) (n : ℤ) :=
  SmallShiftedHom.equiv (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) DerivedCategory.Q

/-- The morphism in the derived category which corresponds to an element in `Ext X Y a`. -/
noncomputable abbrev hom {a : ℕ} (α : Ext X Y a) :
    ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
      ((DerivedCategory.singleFunctor C 0).obj Y) (a : ℤ) :=
  homEquiv α

@[simp]
lemma comp_hom {a b : ℕ} (α : Ext X Y a) (β : Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by omega) := by
  apply SmallShiftedHom.equiv_comp

@[ext]
lemma ext {n : ℕ} {α β : Ext X Y n} (h : α.hom = β.hom) : α = β :=
  homEquiv.injective h

lemma ext_iff {n : ℕ} {α β : Ext X Y n} : α = β ↔ α.hom = β.hom :=
  ⟨fun h ↦ by rw [h], ext⟩

end

noncomputable def mk₀ (f : X ⟶ Y) : Ext X Y 0 := SmallShiftedHom.mk₀ _ _ (by simp)
  ((CochainComplex.singleFunctor C 0).map f)

@[simp]
lemma mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((DerivedCategory.singleFunctor C 0).map f) :=
  sorry

section

variable {n : ℕ} {X₁ X₂ : C}

instance [HasDerivedCategory C] :
    PreservesBinaryBiproduct X₁ X₂ (DerivedCategory.singleFunctor C 0) :=
  sorry

lemma biprod_ext {α β : Ext (X₁ ⊞ X₂) Y n}
    (h₁ : (mk₀ biprod.inl).comp α (zero_add n) = (mk₀ biprod.inl).comp β (zero_add n))
    (h₂ : (mk₀ biprod.inr).comp α (zero_add n) = (mk₀ biprod.inr).comp β (zero_add n)) :
    α = β := by
  letI := HasDerivedCategory.standard C
  rw [ext_iff] at h₁ h₂ ⊢
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (DerivedCategory.singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

variable (α₁ : Ext X₁ Y n) (α₂ : Ext X₂ Y n)

noncomputable def descBiprod : Ext (X₁ ⊞ X₂) Y n := by
  letI := HasDerivedCategory.standard C
  exact homEquiv.symm (Cofan.IsColimit.desc
    (isBinaryBilimitOfPreserves (DerivedCategory.singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit (by
        rintro ⟨_|_⟩
        · exact α₁.hom
        · exact α₂.hom))

@[simp]
lemma inl_descBiprod : (mk₀ biprod.inl).comp (descBiprod α₁ α₂) (zero_add n) = α₁ := by
  letI := HasDerivedCategory.standard C
  ext
  dsimp [descBiprod]
  simp only [comp_hom, Int.Nat.cast_ofNat_Int, mk₀_hom, Equiv.apply_symm_apply,
    ShiftedHom.mk₀_comp]
  exact Cofan.IsColimit.fac
    (isBinaryBilimitOfPreserves (DerivedCategory.singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit _ WalkingPair.left

@[simp]
lemma inr_descBiprod : (mk₀ biprod.inr).comp (descBiprod α₁ α₂) (zero_add n) = α₂ := by
  letI := HasDerivedCategory.standard C
  ext
  dsimp [descBiprod]
  simp only [comp_hom, Int.Nat.cast_ofNat_Int, mk₀_hom, Equiv.apply_symm_apply,
    ShiftedHom.mk₀_comp]
  exact Cofan.IsColimit.fac
    (isBinaryBilimitOfPreserves (DerivedCategory.singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit _ WalkingPair.right

end

noncomputable instance {n : ℕ} : Add (Ext X Y n) where
  add α₁ α₂ := (mk₀ (biprod.lift (𝟙 X) (𝟙 X))).comp (descBiprod α₁ α₂) (zero_add n)

lemma add_hom [HasDerivedCategory.{w'} C] {n : ℕ} (α₁ α₂ : Ext X Y n) :
    (α₁ + α₂).hom = α₁.hom + α₂.hom :=
  sorry

end Ext

end Abelian

end CategoryTheory
