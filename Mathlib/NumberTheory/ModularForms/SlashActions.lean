/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.AdaptationNote

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a given group
parametrized by some Type. This is modeled on the slash action of `GLPos (Fin 2) ℝ` on the space
of modular forms.

## Notation

In the `ModularForm` locale, this provides

* `f ∣[k;γ] A`: the `k`th `γ`-compatible slash action by `A` on `f`
* `f ∣[k] A`: the `k`th `ℂ`-compatible slash action by `A` on `f`; a shorthand for `f ∣[k;ℂ] A`
-/


open Complex UpperHalfPlane ModularGroup

open scoped MatrixGroups

/-- A general version of the slash action of the space of modular forms. -/
class SlashAction (β G α γ : Type*) [Group G] [AddMonoid α] [SMul γ α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  slash_mul : ∀ (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
  smul_slash : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • map k g a
  add_slash : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

scoped[ModularForm] notation:100 f " ∣[" k ";" γ "] " a:100 => SlashAction.map γ k a f

scoped[ModularForm] notation:100 f " ∣[" k "] " a:100 => SlashAction.map ℂ k a f

open scoped ModularForm

@[simp]
theorem SlashAction.neg_slash {β G α γ : Type*} [Group G] [AddGroup α] [SMul γ α]
    [SlashAction β G α γ] (k : β) (g : G) (a : α) : (-a) ∣[k;γ] g = -a ∣[k;γ] g :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← SlashAction.add_slash, neg_add_cancel, SlashAction.zero_slash]

@[simp]
theorem SlashAction.smul_slash_of_tower {R β G α : Type*} (γ : Type*) [Group G] [AddGroup α]
    [Monoid γ] [MulAction γ α] [SMul R γ] [SMul R α] [IsScalarTower R γ α] [SlashAction β G α γ]
    (k : β) (g : G) (a : α) (r : R) : (r • a) ∣[k;γ] g = r • a ∣[k;γ] g := by
  rw [← smul_one_smul γ r a, SlashAction.smul_slash, smul_one_smul]

attribute [simp] SlashAction.zero_slash SlashAction.slash_one SlashAction.smul_slash
  SlashAction.add_slash

/-- Slash_action induced by a monoid homomorphism. -/
def monoidHomSlashAction {β G H α γ : Type*} [Group G] [AddMonoid α] [SMul γ α] [Group H]
    [SlashAction β G α γ] (h : H →* G) : SlashAction β H α γ where
  map k g := SlashAction.map γ k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  smul_slash _ _ := SlashAction.smul_slash _ _
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _

namespace ModularForm

noncomputable section

/-- The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
  f (γ • x) * (↑(↑ₘ[ℝ] γ).det : ℂ) ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)

variable {k : ℤ} (f : ℍ → ℂ)

section

-- temporary notation until the instance is built
local notation:100 f " ∣[" k "]" γ:100 => ModularForm.slash k γ f

private theorem slash_mul (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ) :
    f ∣[k] (A * B) = (f ∣[k] A) ∣[k] B := by
  ext1 x
  simp only [slash, UpperHalfPlane.denom_cocycle A B x]
  simp only [mul_smul, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul, ofReal_mul, denom, smulAux,
    smulAux', num, coe_mk, UpperHalfPlane.coe_smul]
  rw [mul_zpow, mul_right_comm _ _ (((↑ₘ[ℝ] B).det : ℂ) ^ (k - 1)),
    ← mul_assoc, mul_zpow, ← mul_assoc]

private theorem add_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
    (f + g) ∣[k]A = f ∣[k]A + g ∣[k]A := by
  ext1
  simp only [slash, Pi.add_apply, denom, zpow_neg]
  ring

private theorem slash_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k]1 = f :=
  funext <| by simp [slash, denom]

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

private theorem smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : α) :
    (c • f) ∣[k]A = c • f ∣[k]A := by
  simp_rw [← smul_one_smul ℂ c f, ← smul_one_smul ℂ c (f ∣[k]A)]
  ext1
  simp_rw [slash]
  simp only [slash, Algebra.id.smul_eq_mul, Matrix.GeneralLinearGroup.val_det_apply, Pi.smul_apply]
  ring

private theorem zero_slash (k : ℤ) (A : GL(2, ℝ)⁺) : (0 : ℍ → ℂ) ∣[k]A = 0 :=
  funext fun _ => by simp only [slash, Pi.zero_apply, zero_mul]

instance : SlashAction ℤ GL(2, ℝ)⁺ (ℍ → ℂ) ℂ where
  map := slash
  zero_slash := zero_slash
  slash_one := slash_one
  slash_mul := slash_mul
  smul_slash := smul_slash
  add_slash := add_slash

end

theorem slash_def (A : GL(2, ℝ)⁺) : f ∣[k] A = slash k A f :=
  rfl

instance SLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))

@[simp]
theorem SL_slash (γ : SL(2, ℤ)) : f ∣[k] γ = f ∣[k] (γ : GL(2, ℝ)⁺) :=
  rfl

theorem is_invariant_const (A : SL(2, ℤ)) (x : ℂ) :
    Function.const ℍ x ∣[(0 : ℤ)] A = Function.const ℍ x := by
  funext
  simp only [SL_slash, slash_def, slash, Function.const_apply, det_coe, ofReal_one, zero_sub,
    zpow_neg, zpow_one, inv_one, mul_one, neg_zero, zpow_zero]

/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
theorem is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] A = (1 : ℍ → ℂ) :=
  is_invariant_const _ _

/-- Variant of `is_invariant_one` with the left hand side in simp normal form. -/
@[simp]
theorem is_invariant_one' (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] (A : GL(2, ℝ)⁺) = 1 := by
  simpa using is_invariant_one A

/-- A function `f : ℍ → ℂ` is slash-invariant, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
theorem slash_action_eq'_iff (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    (f ∣[k] γ) z = f z ↔ f (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ k * f z := by
  simp only [SL_slash, slash_def, ModularForm.slash]
  convert inv_mul_eq_iff_eq_mul₀ (G₀ := ℂ) _ using 2
  · rw [mul_comm]
    simp only [denom, zpow_neg, det_coe, ofReal_one, one_zpow, mul_one,
      sl_moeb]
    rfl
  · convert zpow_ne_zero k (denom_ne_zero γ z)

theorem mul_slash (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = ((↑ₘA).det : ℝ) • f ∣[k1] A * g ∣[k2] A := by
  ext1 x
  simp only [slash_def, slash, Matrix.GeneralLinearGroup.val_det_apply,
    Pi.mul_apply, Pi.smul_apply, Algebra.smul_mul_assoc, real_smul]
  set d : ℂ := ↑(↑ₘ[ℝ] A).det
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
    have : d ≠ 0 := by
      dsimp only [d]
      exact_mod_cast Matrix.GLPos.det_ne_zero A
    rw [← zpow_one_add₀ this, ← zpow_add₀ this]
    congr; ring
  have h22 : denom A x ^ (-(k1 + k2)) = denom A x ^ (-k1) * denom A x ^ (-k2) := by
    rw [Int.neg_add, zpow_add₀]
    exact UpperHalfPlane.denom_ne_zero A x
  rw [h1, h22]
  ring

theorem mul_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A :=
  calc
    (f * g) ∣[k1 + k2] (A : GL(2, ℝ)⁺) =
        ((↑ₘA).det : ℝ) • f ∣[k1] A * g ∣[k2] A := by
      apply mul_slash
    _ = (1 : ℝ) • f ∣[k1] A * g ∣[k2] A := by rw [det_coe]
    _ = f ∣[k1] A * g ∣[k2] A := by rw [one_smul]

end

end ModularForm
