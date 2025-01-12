/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# Cylinders

-/

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

structure Precylinder [CategoryWithWeakEquivalences C] (A : C) where
  I : C
  i₀ : A ⟶ I
  i₁ : A ⟶ I
  σ : I ⟶ A
  i₀_σ : i₀ ≫ σ = 𝟙 A := by aesop_cat
  i₁_σ : i₁ ≫ σ = 𝟙 A := by aesop_cat
  weakEquivalence_σ : WeakEquivalence σ := by infer_instance

namespace Precylinder

attribute [instance] weakEquivalence_σ
attribute [reassoc (attr := simp)] i₀_σ i₁_σ

variable [CategoryWithWeakEquivalences C]
  {A : C} (P : Precylinder A)

section

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  [(weakEquivalences C).ContainsIdentities]

instance : WeakEquivalence P.i₀ :=
  weakEquivalence_of_postcomp_of_fac (P.i₀_σ)

instance : WeakEquivalence P.i₁ :=
  weakEquivalence_of_postcomp_of_fac (P.i₁_σ)

end

variable [HasBinaryCoproduct A A]

noncomputable def i : A ⨿ A ⟶ P.I := coprod.desc P.i₀ P.i₁

@[reassoc (attr := simp)]
lemma inl_i : coprod.inl ≫ P.i = P.i₀ := by simp [i]

@[reassoc (attr := simp)]
lemma inr_i : coprod.inr ≫ P.i = P.i₁ := by simp [i]

def symm : Precylinder A where
  I := P.I
  i₀ := P.i₁
  i₁ := P.i₀
  σ := P.σ

end Precylinder

structure Cylinder [CategoryWithWeakEquivalences C]
    [CategoryWithCofibrations C] (A : C)
    [HasBinaryCoproduct A A] extends Precylinder A where
  cofibration_i : Cofibration toPrecylinder.i := by infer_instance

namespace Cylinder

attribute [instance] cofibration_i

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] {A : C}

section

variable [CategoryWithFibrations C] [HasBinaryCoproduct A A]

variable (h : MorphismProperty.MapFactorizationData (cofibrations C) (trivialFibrations C)
    (coprod.desc (𝟙 A) (𝟙 A)))

@[simps]
noncomputable def ofFactorizationData : Cylinder A where
  I := h.Z
  i₀ := coprod.inl ≫ h.i
  i₁ := coprod.inr ≫ h.i
  σ := h.p
  cofibration_i := by
    convert inferInstanceAs (Cofibration h.i)
    aesop_cat

@[simp]
lemma ofFactorizationData_i : (ofFactorizationData h).i = h.i := by aesop_cat

@[simp]
lemma ofFactorizationData_p : (ofFactorizationData h).σ = h.p := rfl

instance : Fibration (ofFactorizationData h).σ := by
  dsimp
  infer_instance

end

end Cylinder

end HomotopicalAlgebra
