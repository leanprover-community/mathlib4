/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

#align_import number_theory.modular_forms.slash_actions from "leanprover-community/mathlib"@"738054fa93d43512da144ec45ce799d18fd44248"

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


open Complex UpperHalfPlane

open scoped UpperHalfPlane

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)
-- like `↑ₘ`, but allows the user to specify the ring `R`. Useful to help Lean elaborate.
local notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

/-- A general version of the slash action of the space of modular forms.-/
class SlashAction (β G α γ : Type*) [Group G] [AddMonoid α] [SMul γ α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  slash_mul : ∀ (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
  smul_slash : ∀ (k : β) (g : G) (a : α) (z : γ), map k g (z • a) = z • map k g a
  add_slash : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b
#align slash_action SlashAction

scoped[ModularForm] notation:100 f " ∣[" k ";" γ "] " a:100 => SlashAction.map γ k a f

scoped[ModularForm] notation:100 f " ∣[" k "] " a:100 => SlashAction.map ℂ k a f

open scoped ModularForm

@[simp]
theorem SlashAction.neg_slash {β G α γ : Type*} [Group G] [AddGroup α] [SMul γ α]
    [SlashAction β G α γ] (k : β) (g : G) (a : α) : (-a) ∣[k;γ] g = -a ∣[k;γ] g :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← SlashAction.add_slash, add_left_neg, SlashAction.zero_slash]
    -- 🎉 no goals
#align slash_action.neg_slash SlashAction.neg_slash

@[simp]
theorem SlashAction.smul_slash_of_tower {R β G α : Type*} (γ : Type*) [Group G] [AddGroup α]
    [Monoid γ] [MulAction γ α] [SMul R γ] [SMul R α] [IsScalarTower R γ α] [SlashAction β G α γ]
    (k : β) (g : G) (a : α) (r : R) : (r • a) ∣[k;γ] g = r • a ∣[k;γ] g := by
  rw [← smul_one_smul γ r a, SlashAction.smul_slash, smul_one_smul]
  -- 🎉 no goals
#align slash_action.smul_slash_of_tower SlashAction.smul_slash_of_tower

attribute [simp] SlashAction.zero_slash SlashAction.slash_one SlashAction.smul_slash
  SlashAction.add_slash

/-- Slash_action induced by a monoid homomorphism.-/
def monoidHomSlashAction {β G H α γ : Type*} [Group G] [AddMonoid α] [SMul γ α] [Group H]
    [SlashAction β G α γ] (h : H →* G) : SlashAction β H α γ where
  map k g := SlashAction.map γ k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
                      -- 🎉 no goals
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
                           -- 🎉 no goals
  smul_slash _ _ := SlashAction.smul_slash _ _
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _
#align monoid_hom_slash_action monoidHomSlashAction

namespace ModularForm

noncomputable section

/-- The weight `k` action of `GL(2, ℝ)⁺` on functions `f : ℍ → ℂ`. -/
def slash (k : ℤ) (γ : GL(2, ℝ)⁺) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
  f (γ • x) * (((↑ₘγ).det : ℝ) : ℂ) ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)
#align modular_form.slash ModularForm.slash

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ℍ → ℂ)

section

-- temporary notation until the instance is built
local notation:100 f " ∣[" k "]" γ:100 => ModularForm.slash k γ f

private theorem slash_mul (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ) :
    f ∣[k](A * B) = (f ∣[k]A) ∣[k]B := by
  ext1 x
  -- ⊢ (f ∣[k](A * B)) x = ((f ∣[k]A) ∣[k]B) x
  simp_rw [slash, UpperHalfPlane.denom_cocycle A B x]
  -- ⊢ f ((A * B) • x) * ↑(Matrix.det ↑↑(A * B)) ^ (k - 1) * (denom A (smulAux B x) …
  have e3 : (A * B) • x = A • B • x := by convert UpperHalfPlane.mul_smul' A B x
  -- ⊢ f ((A * B) • x) * ↑(Matrix.det ↑↑(A * B)) ^ (k - 1) * (denom A (smulAux B x) …
  rw [e3]
  -- ⊢ f (A • B • x) * ↑(Matrix.det ↑↑(A * B)) ^ (k - 1) * (denom A (smulAux B x) * …
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, ofReal_mul, Subgroup.coe_mul,
    UpperHalfPlane.coe_smul, Units.val_mul, Matrix.det_mul,
    UpperHalfPlane.smulAux, UpperHalfPlane.smulAux', UpperHalfPlane.coe_mk] at *
  field_simp
  -- ⊢ f (A • B • x) * (↑(Matrix.det ↑↑A) * ↑(Matrix.det ↑↑B)) ^ (k - 1) / ((↑(↑↑A  …
  have : (((↑(↑A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((↑(↑B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ)) ^ (k - 1) =
      ((↑(↑A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 1) *
        ((↑(↑B : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ (k - 1) := by
    simp_rw [← mul_zpow]
  simp_rw [this, ← mul_assoc, ← mul_zpow]
  -- 🎉 no goals

private theorem add_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
    (f + g) ∣[k]A = f ∣[k]A + g ∣[k]A := by
  ext1
  -- ⊢ ((f + g) ∣[k]A) x✝ = (f ∣[k]A + g ∣[k]A) x✝
  simp only [slash, Pi.add_apply, denom, zpow_neg]
  -- ⊢ (f (A • x✝) + g (A • x✝)) * ↑(Matrix.det ↑↑A) ^ (k - 1) * ((↑(↑↑A 1 0) * ↑x✝ …
  ring
  -- 🎉 no goals

private theorem slash_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k]1 = f :=
  funext <| by simp [slash, denom]
               -- 🎉 no goals

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

private theorem smul_slash (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : α) :
    (c • f) ∣[k]A = c • f ∣[k]A := by
  simp_rw [← smul_one_smul ℂ c f, ← smul_one_smul ℂ c (f ∣[k]A)]
  -- ⊢ ((c • 1) • f) ∣[k]A = (c • 1) • f ∣[k]A
  ext1
  -- ⊢ (((c • 1) • f) ∣[k]A) x✝ = ((c • 1) • f ∣[k]A) x✝
  simp_rw [slash]
  -- ⊢ ((c • 1) • f) (A • x✝) * ↑(Matrix.det ↑↑A) ^ (k - 1) * denom A x✝ ^ (-k) = ( …
  simp only [slash, Algebra.id.smul_eq_mul, Matrix.GeneralLinearGroup.val_det_apply, Pi.smul_apply]
  -- ⊢ c • 1 * f (A • x✝) * ↑(Matrix.det ↑↑A) ^ (k - 1) * denom A x✝ ^ (-k) = c • 1 …
  ring
  -- 🎉 no goals

private theorem zero_slash (k : ℤ) (A : GL(2, ℝ)⁺) : (0 : ℍ → ℂ) ∣[k]A = 0 :=
  funext fun _ => by simp only [slash, Pi.zero_apply, zero_mul]
                     -- 🎉 no goals

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
#align modular_form.slash_def ModularForm.slash_def

instance subgroupAction (Γ : Subgroup SL(2, ℤ)) : SlashAction ℤ Γ (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
      (MonoidHom.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) (Subgroup.subtype Γ)))
#align modular_form.subgroup_action ModularForm.subgroupAction

@[simp]
theorem subgroup_slash (Γ : Subgroup SL(2, ℤ)) (γ : Γ) : f ∣[k] γ = f ∣[k] (γ : GL(2, ℝ)⁺) :=
  rfl
#align modular_form.subgroup_slash ModularForm.subgroup_slash

instance SLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) ℂ :=
  monoidHomSlashAction
    (MonoidHom.comp Matrix.SpecialLinearGroup.toGLPos
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)))
set_option linter.uppercaseLean3 false in
#align modular_form.SL_action ModularForm.SLAction

@[simp]
theorem SL_slash (γ : SL(2, ℤ)) : f ∣[k] γ = f ∣[k] (γ : GL(2, ℝ)⁺) :=
  rfl
set_option linter.uppercaseLean3 false in
#align modular_form.SL_slash ModularForm.SL_slash

/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
-- @[simp] -- Porting note: simpNF says LHS simplifies to something more complex
theorem is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] A = (1 : ℍ → ℂ) := by
  have : ((↑ₘ(A : GL(2, ℝ)⁺)).det : ℝ) = 1 := det_coe'
  -- ⊢ 1 ∣[0] A = 1
  funext
  -- ⊢ (1 ∣[0] A) x✝ = OfNat.ofNat 1 x✝
  rw [SL_slash, slash_def, slash, zero_sub, this]
  -- ⊢ OfNat.ofNat 1 (↑A • x✝) * ↑1 ^ (-1) * denom (↑A) x✝ ^ (-0) = OfNat.ofNat 1 x✝
  simp
  -- 🎉 no goals
#align modular_form.is_invariant_one ModularForm.is_invariant_one

/-- A function `f : ℍ → ℂ` is slash-invariant, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
theorem slash_action_eq'_iff (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (f : ℍ → ℂ) (γ : Γ) (z : ℍ) :
    (f ∣[k] γ) z = f z ↔ f (γ • z) = ((↑ₘ[ℤ] γ 1 0 : ℂ) * z + (↑ₘ[ℤ] γ 1 1 : ℂ)) ^ k * f z := by
  simp only [subgroup_slash, slash_def, ModularForm.slash]
  -- ⊢ f (↑↑γ • z) * ↑(Matrix.det ↑↑↑↑γ) ^ (k - 1) * denom (↑↑γ) z ^ (-k) = f z ↔ f …
  convert inv_mul_eq_iff_eq_mul₀ (G₀ := ℂ) _ using 2
  -- ⊢ f (↑↑γ • z) * ↑(Matrix.det ↑↑↑↑γ) ^ (k - 1) * denom (↑↑γ) z ^ (-k) = ((↑(↑↑↑ …
  · rw [mul_comm]
    -- ⊢ denom (↑↑γ) z ^ (-k) * (f (↑↑γ • z) * ↑(Matrix.det ↑↑↑↑γ) ^ (k - 1)) = ((↑(↑ …
    simp only [denom, zpow_neg, det_coe', ofReal_one, one_zpow, mul_one, subgroup_to_sl_moeb,
      sl_moeb]
    rfl
    -- 🎉 no goals
  · convert zpow_ne_zero k (denom_ne_zero γ z)
    -- 🎉 no goals
#align modular_form.slash_action_eq'_iff ModularForm.slash_action_eq'_iff

theorem mul_slash (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = ((↑ₘA).det : ℝ) • f ∣[k1] A * g ∣[k2] A := by
  ext1 x
  -- ⊢ ((f * g) ∣[k1 + k2] A) x = (Matrix.det ↑↑A • f ∣[k1] A * g ∣[k2] A) x
  simp only [slash_def, slash, Matrix.GeneralLinearGroup.val_det_apply,
    Pi.mul_apply, Pi.smul_apply, Algebra.smul_mul_assoc, real_smul]
  set d : ℂ := ↑((↑ₘA).det : ℝ)
  -- ⊢ f (A • x) * g (A • x) * d ^ (k1 + k2 - 1) * denom A x ^ (-(k1 + k2)) = d * ( …
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
    have : d ≠ 0 := by
      dsimp
      norm_cast
      exact Matrix.GLPos.det_ne_zero A
    rw [← zpow_one_add₀ this, ← zpow_add₀ this]
    congr; ring
  have h22 : denom A x ^ (-(k1 + k2)) = denom A x ^ (-k1) * denom A x ^ (-k2) := by
    rw [Int.neg_add, zpow_add₀]
    exact UpperHalfPlane.denom_ne_zero A x
  rw [h1, h22]
  -- ⊢ f (A • x) * g (A • x) * (d * d ^ (k1 - 1) * d ^ (k2 - 1)) * (denom A x ^ (-k …
  ring
  -- 🎉 no goals
#align modular_form.mul_slash ModularForm.mul_slash

set_option maxHeartbeats 1000000 in
-- @[simp] -- Porting note: simpNF says LHS simplifies to something more complex
theorem mul_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A :=
  calc
    (f * g) ∣[k1 + k2] (A : GL(2, ℝ)⁺) =
        ((↑ₘA).det : ℝ) • f ∣[k1] A * g ∣[k2] A := by
      apply mul_slash
      -- 🎉 no goals
    _ = (1 : ℝ) • f ∣[k1] A * g ∣[k2] A := by rw [det_coe']
                                              -- 🎉 no goals
    _ = f ∣[k1] A * g ∣[k2] A := by rw [one_smul]
                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align modular_form.mul_slash_SL2 ModularForm.mul_slash_SL2

theorem mul_slash_subgroup (k1 k2 : ℤ) (Γ : Subgroup SL(2, ℤ)) (A : Γ) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A :=
  mul_slash_SL2 k1 k2 A f g
#align modular_form.mul_slash_subgroup ModularForm.mul_slash_subgroup

end

end ModularForm
