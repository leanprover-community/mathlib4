/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke
-/

module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Ring.Associator
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Category algebra of a linear category
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Linear

open DirectSum
open CategoryTheory.Preadditive

def CategoryAlgebra (R : Type w) [CommSemiring R] (C : Type u) [Category.{v} C] [Preadditive C]
  [Linear R C] := ⨁ (p : C × C), p.1 ⟶ p.2

namespace CategoryAlgebra

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [DecidableEq C]

instance inhabited : Inhabited (CategoryAlgebra R C) :=
  inferInstanceAs (Inhabited (⨁ (p : C × C), p.1 ⟶ p.2))

instance addCommMonoid : AddCommMonoid (CategoryAlgebra R C) :=
  inferInstanceAs (AddCommMonoid (⨁ (p : C × C), p.1 ⟶ p.2))

instance instIsCancelAdd [IsCancelAdd R] : IsCancelAdd (CategoryAlgebra R C) :=
  inferInstanceAs (IsCancelAdd (⨁ (p : C × C), p.1 ⟶ p.2))

instance instModule : Module R (CategoryAlgebra R C) :=
  inferInstanceAs (Module R (⨁ (p : C × C), p.1 ⟶ p.2))

protected def of (a b : C) : (a ⟶ b) →+ CategoryAlgebra R C :=
  DirectSum.of (fun (p : C × C) ↦ p.1 ⟶ p.2) (a,b)

theorem addHom_ext {γ : Type w'} [AddZeroClass γ] ⦃f g : CategoryAlgebra R C →+ γ⦄
    (H : ∀ (X Y : C) (y : X ⟶ Y), f (CategoryAlgebra.of X Y y) = g (CategoryAlgebra.of X Y y)) :
    f = g := DFinsupp.addHom_ext (fun p => H p.1 p.2)

theorem of_eq_single (a b : C) (f : a ⟶ b) :
    (CategoryAlgebra.of a b f : CategoryAlgebra R C) =
    DFinsupp.single (a,b) f := by rfl

def compEq (X Y Z W : C) (h : Y = Z) : (X ⟶ Y) →+ (Z ⟶ W) →+ (X ⟶ W) where
  toFun f := compHom (f ≫ eqToHom h)
  map_add' := by
    intros
    ext
    simp
  map_zero' := by
    ext
    simp

def comp₀ (X Y Z W : C) : (X ⟶ Y) →+ (Z ⟶ W) →+ (X ⟶ W) :=
  if h : Y = Z then compEq X Y Z W h else 0

theorem comp₀_assoc (X₁ Y₁ X₂ Y₂ X₃ Y₃ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((comp₀ X₁ Y₂ X₃ Y₃) (((comp₀ X₁ Y₁ X₂ Y₂) f) g)) h =
    ((comp₀ X₁ Y₁ X₂ Y₃) f) (((comp₀ X₂ Y₂ X₃ Y₃) g) h)
    := by
  by_cases h₁₂ : Y₁ = X₂ <;> by_cases h₂₃ : Y₂ = X₃ <;>
  simp [comp₀, compEq, h₁₂, h₂₃, compHom, Preadditive.leftComp]

@[irreducible] def mul' : CategoryAlgebra R C →+ CategoryAlgebra R C →+ CategoryAlgebra R C :=
  DFinsupp.sumAddHom₂ (fun q p ↦ AddMonoidHom.compr₂
    (comp₀ q.1 q.2 p.1 p.2) (CategoryAlgebra.of q.1 p.2))

instance instMul : Mul (CategoryAlgebra R C) := ⟨fun f g => mul' f g⟩

theorem mul_def (f g : CategoryAlgebra R C) :
    f * g = DFinsupp.sumAddHom₂ (fun q p ↦ AddMonoidHom.compr₂
    (comp₀ q.1 q.2 p.1 p.2) (CategoryAlgebra.of q.1 p.2)) f g := by
  with_unfolding_all rfl

instance : NonUnitalNonAssocSemiring (CategoryAlgebra R C) where
  left_distrib := fun a b c => by simp [mul_def]
  right_distrib := fun a b c => by simp [mul_def]
  zero_mul := fun a => by simp [mul_def]
  mul_zero := fun a => by simp [mul_def]

theorem mul_of (X₁ Y₁ X₂ Y₂ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (CategoryAlgebra.of X₁ Y₁ f) * (CategoryAlgebra.of X₂ Y₂ g : (CategoryAlgebra R C)) =
    CategoryAlgebra.of X₁ Y₂ (comp₀ X₁ Y₁ X₂ Y₂ f g) := by
  simp [mul_def, CategoryAlgebra.of_eq_single, DFinsupp.sumAddHom₂_single]

theorem mul_assoc' :
    AddMonoidHom.mulLeft₃ (R := (CategoryAlgebra R C)) = AddMonoidHom.mulRight₃ := by
  apply CategoryAlgebra.addHom_ext
  rintro X₁ Y₁ f
  apply CategoryAlgebra.addHom_ext
  rintro X₂ Y₂ g
  apply CategoryAlgebra.addHom_ext
  rintro X₃ Y₃ h
  simp only [AddMonoidHom.mulLeft₃, AddMonoidHom.mul, AddMonoidHom.mulLeft, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, AddMonoidHom.coe_comp, Function.comp_apply, mul_of, AddMonoidHom.mulRight₃,
    AddMonoidHom.compr₂, AddMonoidHom.compHom_apply_apply]
  apply congrArg
  apply comp₀_assoc

instance : NonUnitalSemiring (CategoryAlgebra R C) where
  mul_assoc a b c := by
    have : AddMonoidHom.mulLeft₃ a b c = AddMonoidHom.mulRight₃ a b c := by simp [mul_assoc']
    simpa


section Unital

variable [Fintype C]

def one' : CategoryAlgebra R C :=  ∑ i : C, (CategoryAlgebra.of i i (𝟙 i))

instance : One (CategoryAlgebra R C) := ⟨one'⟩

theorem one_def : (1 : CategoryAlgebra R C) = ∑ i : C, (CategoryAlgebra.of i i (𝟙 i)) := rfl

instance [Fintype C] : Semiring (CategoryAlgebra R C) where
  one_mul := by
    have H : (AddMonoidHom.mulLeft (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      apply CategoryAlgebra.addHom_ext
      rintro X₁ Y₁ f
      simp only [AddMonoidHom.mulLeft, one_def, Finset.sum_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        mul_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single_of_mem X₁ (Finset.mem_univ _)]
      · simp [comp₀, compEq, compHom, Preadditive.leftComp]
      · intro b _ h
        simp [comp₀, h]
    apply DFunLike.congr_fun (h₁ := H)
  mul_one := by
    have H : (AddMonoidHom.mulRight (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      apply CategoryAlgebra.addHom_ext
      rintro X₁ Y₁ f
      simp only [AddMonoidHom.mulRight, one_def, Finset.mul_sum, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, mul_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single_of_mem Y₁ (Finset.mem_univ _)]
      · simp [comp₀, compEq, compHom, Preadditive.leftComp]
      · intro b _ h
        simp [comp₀, h.symm]
    apply DFunLike.congr_fun (h₁ := H)

end Unital
end CategoryAlgebra
end CategoryTheory.Linear
