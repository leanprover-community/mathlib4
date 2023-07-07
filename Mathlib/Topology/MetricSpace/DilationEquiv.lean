/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.MetricSpace.Dilation

/-!
# Dilation equivalence
-/

open scoped NNReal ENNReal
open Function Set
open Dilation (ratio ratio_ne_zero ratio_pos edist_eq)

section Class

variable (F : Type _) (X Y : outParam (Type _)) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

class DilationEquivClass extends EquivLike F X Y where
  edist_eq' : ∀ f : F, ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : X, edist (f x) (f y) = r * edist x y

instance (priority := 100) [DilationEquivClass F X Y] : DilationClass F X Y :=
  { inferInstanceAs (FunLike F X fun _ ↦ Y), ‹DilationEquivClass F X Y› with }

end Class

structure DilationEquiv (X Y : Type _) [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    extends X ≃ Y, Dilation X Y

infixl:25 " ≃ᵈ " => DilationEquiv

namespace DilationEquiv

section PseudoEMetricSpace

variable {X Y Z : Type _} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

instance : DilationEquivClass (X ≃ᵈ Y) X Y where
  coe f := f.1
  inv f := f.1.symm
  left_inv f := f.left_inv'
  right_inv f := f.right_inv'
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h -; congr; exact FunLike.ext' h
  edist_eq' f := f.edist_eq'

instance : CoeFun (X ≃ᵈ Y) fun _ ↦ (X → Y) where
  coe f := f

@[simp] theorem coe_toEquiv (e : X ≃ᵈ Y) : ⇑e.toEquiv = e := rfl

@[ext]
protected theorem ext {e e' : X ≃ᵈ Y} (h : ∀ x, e x = e' x) : e = e' :=
  FunLike.ext _ _ h

def symm (e : X ≃ᵈ Y) : Y ≃ᵈ X where
  toEquiv := e.1.symm
  edist_eq' := by
    refine ⟨(ratio e)⁻¹, inv_ne_zero <| ratio_ne_zero e, e.surjective.forall₂.2 fun x y ↦ ?_⟩
    simp_rw [Equiv.toFun_as_coe, Equiv.symm_apply_apply, coe_toEquiv, edist_eq]
    rw [← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel (ratio_ne_zero e),
      ENNReal.coe_one, one_mul]

@[simp] theorem symm_symm (e : X ≃ᵈ Y) : e.symm.symm = e := rfl
@[simp] theorem apply_symm_apply (e : X ≃ᵈ Y) (x : Y) : e (e.symm x) = x := e.right_inv x
@[simp] theorem symm_apply_apply (e : X ≃ᵈ Y) (x : X) : e.symm (e x) = x := e.left_inv x

def Simps.symm_apply (e : X ≃ᵈ Y) : Y → X := e.symm

initialize_simps_projections DilationEquiv (toFun → apply, invFun → symm_apply)

@[simps! (config := .asFn) apply]
def refl (X : Type _) [PseudoEMetricSpace X] : X ≃ᵈ X where
  toEquiv := .refl X
  edist_eq' := ⟨1, one_ne_zero, fun _ _ ↦ by simp⟩

@[simp] theorem refl_symm : (refl X).symm = refl X := rfl
@[simp] theorem ratio_refl : ratio (refl X) = 1 := Dilation.ratio_id

@[simps! (config := .asFn) apply]
def trans (e₁ : X ≃ᵈ Y) (e₂ : Y ≃ᵈ Z) : X ≃ᵈ Z where
  toEquiv := e₁.1.trans e₂.1
  __ := e₂.toDilation.comp e₁.toDilation

@[simp] theorem refl_trans (e : X ≃ᵈ Y) : (refl X).trans e = e := rfl
@[simp] theorem trans_refl (e : X ≃ᵈ Y) : e.trans (refl Y) = e := rfl

@[simp] theorem symm_trans_self (e : X ≃ᵈ Y) : e.symm.trans e = refl Y :=
  DilationEquiv.ext e.apply_symm_apply

@[simp] theorem self_trans_symm (e : X ≃ᵈ Y) : e.trans e.symm = refl X :=
  DilationEquiv.ext e.symm_apply_apply

protected theorem surjective (e : X ≃ᵈ Y) : Surjective e := e.1.surjective
protected theorem bijective (e : X ≃ᵈ Y) : Bijective e := e.1.bijective
protected theorem injective (e : X ≃ᵈ Y) : Injective e := e.1.injective

@[simp]
theorem ratio_trans (e : X ≃ᵈ Y) (e' : Y ≃ᵈ Z) : ratio (e.trans e') = ratio e * ratio e' := by
  -- If `X` is trivial, then so is `Y`, otherwise we apply `Dilation.ratio_comp'`
  by_cases hX : ∀ x y : X, edist x y = 0 ∨ edist x y = ∞
  · have hY : ∀ x y : Y, edist x y = 0 ∨ edist x y = ∞ := e.surjective.forall₂.2 fun x y ↦ by
      refine (hX x y).imp (fun h ↦ ?_) fun h ↦ ?_ <;> simp [*, Dilation.ratio_ne_zero]
    simp [Dilation.ratio_of_trivial, *]
  push_neg at hX
  exact (Dilation.ratio_comp' (g := e'.toDilation) (f := e.toDilation) hX).trans (mul_comm _ _)

instance : Group (X ≃ᵈ X) where
  mul e e' := e'.trans e
  mul_assoc _ _ _ := rfl
  one := refl _
  one_mul _ := rfl
  mul_one _ := rfl
  inv := symm
  mul_left_inv := self_trans_symm

theorem mul_def (e e' : X ≃ᵈ X) : e * e' = e'.trans e := rfl
theorem one_def : (1 : X ≃ᵈ X) = refl X := rfl
theorem inv_def (e : X ≃ᵈ X) : e⁻¹ = e.symm := rfl

@[simp] theorem coe_mul (e e' : X ≃ᵈ X) : ⇑(e * e') = e ∘ e' := rfl
@[simp] theorem coe_one : ⇑(1 : X ≃ᵈ X) = id := rfl
theorem coe_inv (e : X ≃ᵈ X) : ⇑(e⁻¹) = e.symm := rfl

/-- Dilation.ratio as a mo-/
noncomputable def ratioHom : (X ≃ᵈ X) →* ℝ≥0 where
  toFun := Dilation.ratio
  map_one' := ratio_refl
  map_mul' _ _ := (ratio_trans _ _).trans (mul_comm _ _)

@[simp]
theorem ratio_pow (e : X ≃ᵈ X) (n : ℕ) : ratio (e ^ n) = ratio e ^ n :=
  ratioHom.map_pow _ _

@[simp]
theorem ratio_zpow (e : X ≃ᵈ X) (n : ℤ) : ratio (e ^ n) = ratio e ^ n :=
  ratioHom.map_zpow _ _

@[simps]
def toPerm : (X ≃ᵈ X) →* Equiv.Perm X where
  toFun e := e.1
  map_mul' _ _ := rfl
  map_one' := rfl

@[norm_cast]
theorem coe_pow (e : X ≃ᵈ X) (n : ℕ) : ⇑(e ^ n) = e^[n] := by
  rw [← coe_toEquiv, ← toPerm_apply, map_pow, Equiv.Perm.coe_pow]; rfl

end PseudoEMetricSpace

end DilationEquiv
