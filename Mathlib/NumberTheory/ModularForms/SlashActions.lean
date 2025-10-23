/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.AdaptationNote

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a group on an a
additive monoid, parametrized by some index type. This is modeled on the slash action of
`GL (Fin 2) ℝ` on the space of modular forms.

## Notation

Scoped in the `ModularForm` namespace, this file defines

* `f ∣[k] A`: the `k`th slash action by `A` on `f`
-/


open Complex UpperHalfPlane ModularGroup

open scoped MatrixGroups

/-- A general version of the slash action of the space of modular forms. This is the same data as a
family of `DistribMulAction Gᵒᵖ α` indexed by `k`. -/
class SlashAction (β G α : Type*) [Monoid G] [AddMonoid α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  slash_mul : ∀ (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
  add_slash : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

scoped[ModularForm] notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

open scoped ModularForm

@[simp]
theorem SlashAction.neg_slash {β G α : Type*} [Monoid G] [AddGroup α]
    [SlashAction β G α] (k : β) (g : G) (a : α) : (-a) ∣[k] g = -a ∣[k] g :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← add_slash, neg_add_cancel, zero_slash]

attribute [simp] SlashAction.zero_slash SlashAction.slash_one SlashAction.add_slash

/-- Slash_action induced by a monoid homomorphism. -/
def monoidHomSlashAction {β G H α : Type*} [Monoid G] [AddMonoid α] [Monoid H]
    [SlashAction β G α] (h : H →* G) : SlashAction β H α where
  map k g := SlashAction.map k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _

namespace ModularForm

noncomputable section

variable {k : ℤ} (f : ℍ → ℂ)

section privateSlash

/-- The weight `k` action of `GL (Fin 2) ℝ` on functions `f : ℍ → ℂ`. Invoking this directly is
deprecated; it should always be used via the `SlashAction` instance. -/
private def privateSlash (k : ℤ) (γ : GL (Fin 2) ℝ) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
  σ γ (f (γ • x)) * |γ.det.val| ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)

-- Why is `noncomputable` flag needed here, when we're in a noncomputable section already?
@[deprecated (since := "2025-09-19")] noncomputable alias slash := privateSlash

-- temporary notation until the instance is built
local notation:100 f " ∣[" k "] " γ:100 => ModularForm.privateSlash k γ f

private theorem slash_mul (k : ℤ) (A B : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    f ∣[k] (A * B) = (f ∣[k] A) ∣[k] B := by
  ext1 τ
  calc σ (A * B) (f ((A * B) • τ)) * |(A * B).det.val| ^ (k - 1) * denom (A * B) τ ^ (-k)
  _ = σ B (σ A (f (A • B • τ))) * (|A.det.val| ^ (k - 1) * |B.det.val| ^ (k - 1)) *
      (((σ B) (denom A ↑(B • τ) ^ (-k))) * denom B τ ^ (-k)) := by
    rw [σ_mul_comm, σ_mul, denom_cocycle_σ, mul_zpow, mul_smul, map_mul, Units.val_mul,
      abs_mul, ofReal_mul, mul_zpow, map_zpow₀]
  _ = σ B (σ A (f (A • B • τ)) * |A.det.val| ^ (k - 1) * (denom A ↑(B • τ) ^ (-k)))
        * |B.det.val| ^ (k - 1) * denom B τ ^ (-k) := by
     rw [map_mul, map_zpow₀, map_mul, map_zpow₀, σ_ofReal]
     ring
  _ = ((f ∣[k] A) ∣[k] B) τ := rfl

private theorem add_slash (k : ℤ) (A : GL (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f + g) ∣[k] A = f ∣[k] A + g ∣[k] A := by
  ext1 τ
  simp [privateSlash, add_mul]

private theorem slash_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k] 1 = f :=
  funext <| by simp [privateSlash, σ, denom]

private theorem zero_slash (k : ℤ) (A : GL (Fin 2) ℝ) : (0 : ℍ → ℂ) ∣[k] A = 0 :=
  funext fun _ => by simp [privateSlash]

/-- The weight `k` action of `GL (Fin 2) ℝ` on functions `f : ℍ → ℂ`. -/
instance : SlashAction ℤ (GL (Fin 2) ℝ) (ℍ → ℂ) where
  map := privateSlash
  zero_slash := zero_slash
  slash_one := slash_one
  slash_mul := slash_mul
  add_slash := add_slash

end privateSlash

theorem slash_def (g : GL (Fin 2) ℝ) :
    f ∣[k] g = fun τ ↦ σ g (f (g • τ)) * |g.det.val| ^ (k - 1) * denom g τ ^ (-k) :=
  rfl

theorem slash_apply (g : GL (Fin 2) ℝ) (τ : ℍ) :
    (f ∣[k] g) τ = σ g (f (g • τ)) * |g.det.val| ^ (k - 1) * denom g τ ^ (-k) :=
  rfl

theorem smul_slash (k : ℤ) (A : GL (Fin 2) ℝ) (f : ℍ → ℂ) (c : ℂ) :
    (c • f) ∣[k] A = σ A c • f ∣[k] A := by
  ext τ : 1
  simp only [slash_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

instance SLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) :=
  monoidHomSlashAction (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem SL_slash (γ : SL(2, ℤ)) : f ∣[k] γ = f ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

theorem SL_slash_def (γ : SL(2, ℤ)) :
    f ∣[k] γ = fun τ ↦ f (γ • τ) * denom γ τ ^ (-k) := by
  simp [SL_slash, slash_def, σ]

theorem SL_slash_apply (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k) := by
  simp [SL_slash, slash_def, σ]

@[simp]
theorem SL_smul_slash {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]
    (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) (c : α) :
    (c • f) ∣[k] A = c • f ∣[k] A := by
  ext τ : 1
  simp [SL_slash_apply, Pi.smul_apply, smul_mul_assoc]

theorem is_invariant_const (A : SL(2, ℤ)) (x : ℂ) :
    Function.const ℍ x ∣[(0 : ℤ)] A = Function.const ℍ x := by
  funext
  simp [SL_slash, slash_def, σ, zero_lt_one]

/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
theorem is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] A = (1 : ℍ → ℂ) :=
  is_invariant_const _ _

/-- Variant of `is_invariant_one` with the left-hand side in simp normal form. -/
@[simp]
theorem is_invariant_one' (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] (A : GL (Fin 2) ℝ) = 1 := by
  simpa using is_invariant_one A

/-- A function `f : ℍ → ℂ` is slash-invariant, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
theorem slash_action_eq'_iff (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    (f ∣[k] γ) z = f z ↔ f (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ k * f z := by
  simp only [SL_slash_apply]
  convert inv_mul_eq_iff_eq_mul₀ (G₀ := ℂ) _ using 2
  · simp only [mul_comm (f _), denom, zpow_neg]
    rfl
  · exact zpow_ne_zero k (denom_ne_zero γ z)

theorem mul_slash (k1 k2 : ℤ) (A : GL (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = |(A.det : ℝ)| • (f ∣[k1] A * g ∣[k2] A) := by
  ext1 x
  simp only [slash_apply, Pi.mul_apply, Pi.smul_apply, real_smul, map_mul, neg_add,
    zpow_add₀ (denom_ne_zero _ x)]
  set d := (↑|A.det.val| : ℂ)
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
    have : d ≠ 0 := ofReal_ne_zero.mpr <| abs_ne_zero.mpr <| NeZero.ne _
    rw [← zpow_one_add₀ this, ← zpow_add₀ this]
    ring_nf
  rw [h1]
  ring

theorem mul_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A := by
  simp [SL_slash, mul_slash]

end

end ModularForm
