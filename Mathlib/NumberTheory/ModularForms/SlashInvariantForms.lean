/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.SlashActions

#align_import number_theory.modular_forms.slash_invariant_forms from "leanprover-community/mathlib"@"738054fa93d43512da144ec45ce799d18fd44248"

/-!
# Slash invariant forms

This file defines functions that are invariant under a `SlashAction` which forms the basis for
defining `ModularForm` and `CuspForm`. We prove several instances for such spaces, in particular
that they form a module.
-/


open Complex UpperHalfPlane

open scoped UpperHalfPlane ModularForm

noncomputable section

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

local notation:1024 "↑ₘ" A:1024 =>
  (((A : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) _)
-- like `↑ₘ`, but allows the user to specify the ring `R`. Useful to help Lean elaborate.
local notation:1024 "↑ₘ[" R "]" A:1024 =>
  ((A : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)

section SlashInvariantForms

open ModularForm

variable (F : Type*) (Γ : outParam <| Subgroup SL(2, ℤ)) (k : outParam ℤ)

/-- Functions `ℍ → ℂ` that are invariant under the `SlashAction`. -/
structure SlashInvariantForm where
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ : Γ, toFun ∣[k] γ = toFun
#align slash_invariant_form SlashInvariantForm

/-- `SlashInvariantFormClass F Γ k` asserts `F` is a type of bundled functions that are invariant
under the `SlashAction`. -/
class SlashInvariantFormClass extends FunLike F ℍ fun _ => ℂ where
  slash_action_eq : ∀ (f : F) (γ : Γ), (f : ℍ → ℂ) ∣[k] γ = f
#align slash_invariant_form_class SlashInvariantFormClass

instance (priority := 100) SlashInvariantFormClass.slashInvariantForm :
    SlashInvariantFormClass (SlashInvariantForm Γ k) Γ k where
  coe := SlashInvariantForm.toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, slash_action_eq' := slash_action_eq'✝ } = g
                                      -- ⊢ { toFun := toFun✝¹, slash_action_eq' := slash_action_eq'✝¹ } = { toFun := to …
                                               -- 🎉 no goals
  slash_action_eq := SlashInvariantForm.slash_action_eq'
#align slash_invariant_form_class.slash_invariant_form SlashInvariantFormClass.slashInvariantForm

variable {F Γ k}

instance : CoeFun (SlashInvariantForm Γ k) fun _ => ℍ → ℂ :=
  FunLike.hasCoeToFun

@[simp]
theorem SlashInvariantForm.toFun_eq_coe {f : SlashInvariantForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align slash_invariant_form_to_fun_eq_coe SlashInvariantForm.toFun_eq_coe

@[simp]
theorem SlashInvariantForm.coe_mk (f : ℍ → ℂ) (hf : ∀ γ : Γ, f ∣[k] γ = f) : ⇑(mk f hf) = f := rfl

@[ext]
theorem SlashInvariantForm.ext {f g : SlashInvariantForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align slash_invariant_form_ext SlashInvariantForm.ext

/-- Copy of a `SlashInvariantForm` with a new `toFun` equal to the old one.
Useful to fix definitional equalities. -/
protected def SlashInvariantForm.copy (f : SlashInvariantForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    SlashInvariantForm Γ k where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
#align slash_invariant_form.copy SlashInvariantForm.copy

end SlashInvariantForms

namespace SlashInvariantForm

open SlashInvariantForm

variable {F : Type*} {Γ : outParam <| Subgroup SL(2, ℤ)} {k : outParam ℤ}

instance (priority := 100) SlashInvariantFormClass.coeToFun [SlashInvariantFormClass F Γ k] :
    CoeFun F fun _ => ℍ → ℂ :=
  FunLike.hasCoeToFun
#align slash_invariant_form.slash_invariant_form_class.coe_to_fun SlashInvariantForm.SlashInvariantFormClass.coeToFun

-- @[simp] -- Porting note: simpNF says LHS simplifies to something more complex
theorem slash_action_eqn [SlashInvariantFormClass F Γ k] (f : F) (γ : Γ) : ↑f ∣[k] γ = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f γ
#align slash_invariant_form.slash_action_eqn SlashInvariantForm.slash_action_eqn

theorem slash_action_eqn' (k : ℤ) (Γ : Subgroup SL(2, ℤ)) [SlashInvariantFormClass F Γ k] (f : F)
    (γ : Γ) (z : ℍ) : f (γ • z) = ((↑ₘ[ℤ] γ 1 0 : ℂ) * z + (↑ₘ[ℤ] γ 1 1 : ℂ)) ^ k * f z := by
  rw [← ModularForm.slash_action_eq'_iff, slash_action_eqn]
  -- 🎉 no goals
#align slash_invariant_form.slash_action_eqn' SlashInvariantForm.slash_action_eqn'

instance [SlashInvariantFormClass F Γ k] : CoeTC F (SlashInvariantForm Γ k) :=
  ⟨fun f =>
    { toFun := f
      slash_action_eq' := slash_action_eqn f }⟩

@[simp]
theorem SlashInvariantFormClass.coe_coe [SlashInvariantFormClass F Γ k] (f : F) :
    ((f : SlashInvariantForm Γ k) : ℍ → ℂ) = f :=
  rfl
#align slash_invariant_form.slash_invariant_form_class.coe_coe SlashInvariantForm.SlashInvariantFormClass.coe_coe

instance instAdd : Add (SlashInvariantForm Γ k) :=
  ⟨fun f g =>
    { toFun := f + g
      slash_action_eq' := fun γ => by
        rw [SlashAction.add_slash, slash_action_eqn, slash_action_eqn] }⟩
        -- 🎉 no goals
#align slash_invariant_form.has_add SlashInvariantForm.instAdd

@[simp]
theorem coe_add (f g : SlashInvariantForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align slash_invariant_form.coe_add SlashInvariantForm.coe_add

@[simp]
theorem add_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align slash_invariant_form.add_apply SlashInvariantForm.add_apply

instance instZero : Zero (SlashInvariantForm Γ k) :=
  ⟨{toFun := 0
    slash_action_eq' := SlashAction.zero_slash _}⟩
#align slash_invariant_form.has_zero SlashInvariantForm.instZero

@[simp]
theorem coe_zero : ⇑(0 : SlashInvariantForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align slash_invariant_form.coe_zero SlashInvariantForm.coe_zero

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

instance instSMul : SMul α (SlashInvariantForm Γ k) :=
  ⟨fun c f =>
    { toFun := c • ↑f
      slash_action_eq' := fun γ => by rw [SlashAction.smul_slash_of_tower, slash_action_eqn] }⟩
                                      -- 🎉 no goals
#align slash_invariant_form.has_smul SlashInvariantForm.instSMul

@[simp]
theorem coe_smul (f : SlashInvariantForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl
#align slash_invariant_form.coe_smul SlashInvariantForm.coe_smul

@[simp]
theorem smul_apply (f : SlashInvariantForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl
#align slash_invariant_form.smul_apply SlashInvariantForm.smul_apply

end

instance instNeg : Neg (SlashInvariantForm Γ k) :=
  ⟨fun f =>
    { toFun := -f
      slash_action_eq' := fun γ => by rw [SlashAction.neg_slash, slash_action_eqn] }⟩
                                      -- 🎉 no goals
#align slash_invariant_form.has_neg SlashInvariantForm.instNeg

@[simp]
theorem coe_neg (f : SlashInvariantForm Γ k) : ⇑(-f) = -f :=
  rfl
#align slash_invariant_form.coe_neg SlashInvariantForm.coe_neg

@[simp]
theorem neg_apply (f : SlashInvariantForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align slash_invariant_form.neg_apply SlashInvariantForm.neg_apply

instance instSub : Sub (SlashInvariantForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align slash_invariant_form.has_sub SlashInvariantForm.instSub

@[simp]
theorem coe_sub (f g : SlashInvariantForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align slash_invariant_form.coe_sub SlashInvariantForm.coe_sub

@[simp]
theorem sub_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align slash_invariant_form.sub_apply SlashInvariantForm.sub_apply

instance : AddCommGroup (SlashInvariantForm Γ k) :=
  FunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `SlashInvariantForm` to `ℍ → ℂ`.-/
def coeHom : SlashInvariantForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl
#align slash_invariant_form.coe_hom SlashInvariantForm.coeHom

theorem coeHom_injective : Function.Injective (@coeHom Γ k) :=
  FunLike.coe_injective
#align slash_invariant_form.coe_hom_injective SlashInvariantForm.coeHom_injective

instance : Module ℂ (SlashInvariantForm Γ k) :=
  coeHom_injective.module ℂ coeHom fun _ _ => rfl

instance : One (SlashInvariantForm Γ 0) :=
  ⟨{toFun := 1
    slash_action_eq' := fun A => ModularForm.is_invariant_one A }⟩

@[simp]
theorem one_coe_eq_one : ((1 : SlashInvariantForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl
#align slash_invariant_form.one_coe_eq_one SlashInvariantForm.one_coe_eq_one

instance : Inhabited (SlashInvariantForm Γ k) :=
  ⟨0⟩

/-- The slash invariant form of weight `k₁ + k₂` given by the product of two modular forms of
weights `k₁` and `k₂`. -/
def mul {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : SlashInvariantForm Γ (k₁ + k₂) where
  toFun := f * g
  slash_action_eq' A := by
    simp_rw [ModularForm.mul_slash_subgroup, SlashInvariantFormClass.slash_action_eq]
    -- 🎉 no goals

@[simp]
theorem coe_mul {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : ⇑(f.mul g) = ⇑f * ⇑g :=
  rfl

end SlashInvariantForm
