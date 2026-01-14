/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Slash invariant forms

This file defines functions that are invariant under a `SlashAction` which forms the basis for
defining `ModularForm` and `CuspForm`. We prove several instances for such spaces, in particular
that they form a module over `ℝ`, and over `ℂ` if the group is contained in `SL(2, ℝ)`.
-/

open Complex UpperHalfPlane ModularForm

open scoped MatrixGroups

noncomputable section

section SlashInvariantForms

open ModularForm

variable (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)

/-- Functions `ℍ → ℂ` that are invariant under the `SlashAction`. -/
structure SlashInvariantForm where
  /-- The underlying function `ℍ → ℂ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ ∈ Γ, toFun ∣[k] γ = toFun

/-- `SlashInvariantFormClass F Γ k` asserts `F` is a type of bundled functions that are invariant
under the `SlashAction`. -/
class SlashInvariantFormClass [FunLike F ℍ ℂ] : Prop where
  slash_action_eq : ∀ (f : F), ∀ γ ∈ Γ, (f : ℍ → ℂ) ∣[k] γ = f

instance (priority := 100) SlashInvariantForm.funLike :
    FunLike (SlashInvariantForm Γ k) ℍ ℂ where
  coe := SlashInvariantForm.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance (priority := 100) SlashInvariantFormClass.slashInvariantForm :
    SlashInvariantFormClass (SlashInvariantForm Γ k) Γ k where
  slash_action_eq := SlashInvariantForm.slash_action_eq'

variable {F Γ k}

@[simp]
theorem SlashInvariantForm.toFun_eq_coe {f : SlashInvariantForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
theorem SlashInvariantForm.coe_mk (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ, f ∣[k] γ = f) : ⇑(mk f hf) = f := rfl

@[ext]
theorem SlashInvariantForm.ext {f g : SlashInvariantForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SlashInvariantForm` with a new `toFun` equal to the old one.
Useful to fix definitional equalities. -/
protected def SlashInvariantForm.copy (f : SlashInvariantForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    SlashInvariantForm Γ k where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'

end SlashInvariantForms

namespace SlashInvariantForm

variable {F : Type*} {Γ : Subgroup <| GL (Fin 2) ℝ} {k : ℤ} [FunLike F ℍ ℂ]

theorem slash_action_eqn [SlashInvariantFormClass F Γ k] (f : F) (γ) (hγ : γ ∈ Γ) :
    ↑f ∣[k] γ = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f γ hγ

theorem slash_action_eqn' {k : ℤ} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) = (γ 1 0 * z + γ 1 1) ^ k * f z := by
  have : f (γ • z) = f z * denom γ z ^ k := by
    simpa [slash_def, σ, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero _ _)),
      Subgroup.HasDetOne.det_eq hγ] using congr_fun (slash_action_eqn f γ hγ) z
  rw [this, denom, mul_comm]

/-- Every `SlashInvariantForm` `f` satisfies ` f (γ • z) = (denom γ z) ^ k * f z`. -/
theorem slash_action_eqn'' {k : ℤ} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn' f hγ z

/-- Every `SlashInvariantForm` `f` satisfies ` f (γ • z) = (denom γ z) ^ k * f z`. -/
theorem slash_action_eqn_SL'' {k : ℤ} {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn' f (by simpa using hγ) z


instance [SlashInvariantFormClass F Γ k] : CoeTC F (SlashInvariantForm Γ k) :=
  ⟨fun f ↦ { slash_action_eq' := slash_action_eqn f, .. }⟩

instance instAdd : Add (SlashInvariantForm Γ k) :=
  ⟨fun f g ↦
    { toFun := f + g
      slash_action_eq' := fun γ hγ ↦ by
        rw [SlashAction.add_slash, slash_action_eqn f γ hγ, slash_action_eqn g γ hγ] }⟩

@[simp]
theorem coe_add (f g : SlashInvariantForm Γ k) : ⇑(f + g) = f + g :=
  rfl

@[simp]
theorem add_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl

instance instZero : Zero (SlashInvariantForm Γ k) :=
  ⟨{toFun := 0
    slash_action_eq' := fun _ _ ↦ SlashAction.zero_slash _ _}⟩

@[simp]
theorem coe_zero : ⇑(0 : SlashInvariantForm Γ k) = (0 : ℍ → ℂ) :=
  rfl

section smul

variable [Γ.HasDetOne] {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

/-- Scalar multiplication by `ℂ`, assuming that `Γ ⊆ SL(2, ℝ)`. -/
instance instSMul : SMul α (SlashInvariantForm Γ k) where
  smul c f :=
  { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul ℂ]
      simp [-smul_assoc, smul_slash, slash_action_eqn _ _ hγ, σ, Subgroup.HasDetOne.det_eq hγ] }

@[simp]
theorem coe_smul (f : SlashInvariantForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem smul_apply (f : SlashInvariantForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl

end smul

section smulℝ

variable {α : Type*} [SMul α ℂ] [SMul α ℝ] [IsScalarTower α ℝ ℂ]

/-- Scalar multiplication by `ℝ`, valid without restrictions on the determinant. -/
instance instSMulℝ : SMul α (SlashInvariantForm Γ k) where
  smul c f :=
  { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul ℝ, ← smul_one_smul ℂ, smul_slash,
        Complex.real_smul, mul_one, σ_ofReal, slash_action_eqn _ _ hγ] }

@[simp]
theorem coe_smulℝ (f : SlashInvariantForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem smul_applyℝ (f : SlashInvariantForm Γ k) (n : α) (z : ℍ) :
    (n • f) z = n • f z :=
  rfl

end smulℝ

instance instNeg : Neg (SlashInvariantForm Γ k) :=
  ⟨fun f =>
    { toFun := -f
      slash_action_eq' := fun γ hγ => by rw [SlashAction.neg_slash, slash_action_eqn f γ hγ] }⟩

@[simp]
theorem coe_neg (f : SlashInvariantForm Γ k) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem neg_apply (f : SlashInvariantForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl

instance instSub : Sub (SlashInvariantForm Γ k) :=
  ⟨fun f g => f + -g⟩

@[simp]
theorem coe_sub (f g : SlashInvariantForm Γ k) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem sub_apply (f g : SlashInvariantForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl

instance : AddCommGroup (SlashInvariantForm Γ k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smulℝ coe_smulℝ

/-- Additive coercion from `SlashInvariantForm` to `ℍ → ℂ`. -/
def coeHom : SlashInvariantForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeHom_injective : Function.Injective (@coeHom Γ k) :=
  DFunLike.coe_injective

instance instModuleComplex [Γ.HasDetOne] {α : Type*} [Semiring α] [Module α ℂ]
    [IsScalarTower α ℂ ℂ] : Module α (SlashInvariantForm Γ k) :=
  coeHom_injective.module α _ (fun _ _ ↦ rfl)

instance instModuleReal {α : Type*} [Semiring α] [Module α ℝ] [Module α ℂ] [IsScalarTower α ℝ ℂ] :
    Module α (SlashInvariantForm Γ k) :=
  coeHom_injective.module α _ (fun _ _ ↦ rfl)

/-- The `SlashInvariantForm` corresponding to `Function.const _ x`. -/
@[simps -fullyApplied]
def const [Γ.HasDetOne] (x : ℂ) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' g hg := by ext; simp [slash_def, σ, Subgroup.HasDetOne.det_eq hg]

/-- The `SlashInvariantForm` corresponding to `Function.const _ x`. -/
@[simps -fullyApplied]
def constℝ [Γ.HasDetPlusMinusOne] (x : ℝ) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' g hg := funext fun τ ↦ by simp [slash_apply,
    Subgroup.HasDetPlusMinusOne.abs_det hg, -Matrix.GeneralLinearGroup.val_det_apply]

instance [Γ.HasDetPlusMinusOne] : One (SlashInvariantForm Γ 0) where
  one := { constℝ 1 with toFun := 1 }

@[simp]
theorem one_coe_eq_one [Γ.HasDetPlusMinusOne] : ((1 : SlashInvariantForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl

instance : Inhabited (SlashInvariantForm Γ k) :=
  ⟨0⟩

/-- The slash invariant form of weight `k₁ + k₂` given by the product of two slash-invariant forms
of weights `k₁` and `k₂`. -/
def mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : SlashInvariantForm Γ (k₁ + k₂) where
  toFun := f * g
  slash_action_eq' A hA := by simp [mul_slash, Subgroup.HasDetPlusMinusOne.abs_det hA,
    -Matrix.GeneralLinearGroup.val_det_apply, slash_action_eqn f A hA, slash_action_eqn g A hA]

@[simp]
theorem coe_mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : ⇑(f.mul g) = ⇑f * ⇑g :=
  rfl

instance [Γ.HasDetPlusMinusOne] : NatCast (SlashInvariantForm Γ 0) where
  natCast n := constℝ n

@[simp, norm_cast]
theorem coe_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) : ⇑(n : SlashInvariantForm Γ 0) = n := rfl

instance [Γ.HasDetPlusMinusOne] : IntCast (SlashInvariantForm Γ 0) where
  intCast z := constℝ z

@[simp, norm_cast]
theorem coe_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) : ⇑(z : SlashInvariantForm Γ 0) = z := rfl

open ConjAct Pointwise in
/-- Translating a `SlashInvariantForm` by `g : GL (Fin 2) ℝ`, to obtain a new
`SlashInvariantForm` of level `g⁻¹ Γ g`. -/
noncomputable def translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) ℝ) :
    SlashInvariantForm (toConjAct g⁻¹ • Γ) k where
  toFun := f ∣[k] g
  slash_action_eq' j hj := by
    rw [map_inv, Γ.mem_inv_pointwise_smul_iff, toConjAct_smul] at hj
    simpa [← SlashAction.slash_mul] using congr_arg (· ∣[k] g) (slash_action_eqn f _ hj)

@[simp]
lemma coe_translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) ℝ) :
    translate f g = ⇑f ∣[k] g :=
  rfl

@[deprecated (since := "2025-08-15")] alias translateGL := translate
@[deprecated (since := "2025-08-15")] alias coe_translateGL := coe_translate
@[deprecated (since := "2025-05-15")] alias translateGLPos := translate
@[deprecated (since := "2025-05-15")] alias coe_translateGLPos := coe_translate

end SlashInvariantForm
