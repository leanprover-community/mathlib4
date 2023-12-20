/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

#align_import number_theory.modular_forms.basic from "leanprover-community/mathlib"@"57f9349f2fe19d2de7207e99b0341808d977cdcf"

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them. Including constructing
the graded ring of modular forms.

We begin by defining modular forms and cusp forms as extension of `SlashInvariantForm`s then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

open Complex UpperHalfPlane

open scoped Topology Manifold UpperHalfPlane

noncomputable section

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

section ModularForm

open ModularForm

variable (F : Type*) (Γ : Subgroup SL(2, ℤ)) (k : ℤ)

open scoped ModularForm

/-- These are `SlashInvariantForm`'s that are holomophic and bounded at infinity. -/
structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_infty' : ∀ A : SL(2, ℤ), IsBoundedAtImInfty (toSlashInvariantForm ∣[k] A)
#align modular_form ModularForm

/-- The `SlashInvariantForm` associated to a `ModularForm`. -/
add_decl_doc ModularForm.toSlashInvariantForm

/-- These are `SlashInvariantForm`s that are holomophic and zero at infinity. -/
structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (toSlashInvariantForm : ℍ → ℂ)
  zero_at_infty' : ∀ A : SL(2, ℤ), IsZeroAtImInfty (toSlashInvariantForm ∣[k] A)
#align cusp_form CuspForm

/-- The `SlashInvariantForm` associated to a `CuspForm`. -/
add_decl_doc CuspForm.toSlashInvariantForm

/-- `ModularFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and bounded
at infinity. -/
class ModularFormClass (F : Type*) (Γ : outParam <| Subgroup (SL(2, ℤ))) (k : outParam ℤ)
    extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ)
  bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), IsBoundedAtImInfty (f ∣[k] A)
#align modular_form_class ModularFormClass

/-- `CuspFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and zero
at infinity. -/
class CuspFormClass (F : Type*) (Γ : outParam <| Subgroup (SL(2, ℤ))) (k : outParam ℤ)
    extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ)
  zero_at_infty : ∀ (f : F) (A : SL(2, ℤ)), IsZeroAtImInfty (f ∣[k] A)
#align cusp_form_class CuspFormClass

instance (priority := 100) ModularFormClass.modularForm :
    ModularFormClass (ModularForm Γ k) Γ k where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact FunLike.ext' h
  slash_action_eq f := f.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_infty := ModularForm.bdd_at_infty'
#align modular_form_class.modular_form ModularFormClass.modularForm

instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact FunLike.ext' h
  slash_action_eq f := f.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_infty := CuspForm.zero_at_infty'
#align cusp_form_class.cusp_form CuspFormClass.cuspForm

variable {F Γ k}

theorem ModularForm.toFun_eq_coe (f : ModularForm Γ k) : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align modular_form_to_fun_eq_coe ModularForm.toFun_eq_coe

@[simp]
theorem ModularForm.toSlashInvariantForm_coe (f : ModularForm Γ k) : ⇑f.1 = f :=
  rfl

theorem CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl
#align cusp_form_to_fun_eq_coe CuspForm.toFun_eq_coe

@[simp]
theorem CuspForm.toSlashInvariantForm_coe (f : CuspForm Γ k) : ⇑f.1 = f := rfl

@[ext]
theorem ModularForm.ext {f g : ModularForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align modular_form.ext ModularForm.ext

@[ext]
theorem CuspForm.ext {f g : CuspForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align cusp_form.ext CuspForm.ext

/-- Copy of a `ModularForm` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    ModularForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  bdd_at_infty' A := h.symm ▸ f.bdd_at_infty' A
#align modular_form.copy ModularForm.copy

/-- Copy of a `CuspForm` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def CuspForm.copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : CuspForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  zero_at_infty' A := h.symm ▸ f.zero_at_infty' A
#align cusp_form.copy CuspForm.copy

end ModularForm

namespace ModularForm

open SlashInvariantForm

variable {F : Type*} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

instance add : Add (ModularForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).add (g.bdd_at_infty' A) }⟩
#align modular_form.has_add ModularForm.add

@[simp]
theorem coe_add (f g : ModularForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align modular_form.coe_add ModularForm.coe_add

@[simp]
theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align modular_form.add_apply ModularForm.add_apply

instance instZero : Zero (ModularForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by simpa using zero_form_isBoundedAtImInfty } ⟩
#align modular_form.has_zero ModularForm.instZero

@[simp]
theorem coe_zero : ⇑(0 : ModularForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align modular_form.coe_zero ModularForm.coe_zero

@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm Γ k) z = 0 :=
  rfl
#align modular_form.zero_apply ModularForm.zero_apply

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

instance instSMul : SMul α (ModularForm Γ k) :=
  ⟨fun c f =>
    { toSlashInvariantForm := c • f.1
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).const_smul_left (c • (1 : ℂ)) }⟩
#align modular_form.has_smul ModularForm.instSMul

@[simp]
theorem coe_smul (f : ModularForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl
#align modular_form.coe_smul ModularForm.coe_smul

@[simp]
theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl
#align modular_form.smul_apply ModularForm.smul_apply

end

instance instNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_infty' := fun A => by simpa using (f.bdd_at_infty' A).neg }⟩
#align modular_form.has_neg ModularForm.instNeg

@[simp]
theorem coe_neg (f : ModularForm Γ k) : ⇑(-f) = -f :=
  rfl
#align modular_form.coe_neg ModularForm.coe_neg

@[simp]
theorem neg_apply (f : ModularForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align modular_form.neg_apply ModularForm.neg_apply

instance instSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align modular_form.has_sub ModularForm.instSub

@[simp]
theorem coe_sub (f g : ModularForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align modular_form.coe_sub ModularForm.coe_sub

@[simp]
theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align modular_form.sub_apply ModularForm.sub_apply

instance : AddCommGroup (ModularForm Γ k) :=
  FunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `ModularForm` to `ℍ → ℂ`. -/
@[simps]
def coeHom : ModularForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl
#align modular_form.coe_hom ModularForm.coeHom

instance : Module ℂ (ModularForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

/-- The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
def mul {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_infty' A := by
    -- porting note: was `by simpa using ...`
    -- `mul_slash_SL2` is no longer a `simp` and `simpa only [mul_slash_SL2] using ...` failed
    rw [SlashInvariantForm.coe_mul, mul_slash_SL2]
    exact (f.bdd_at_infty' A).mul (g.bdd_at_infty' A)
#align modular_form.mul ModularForm.mul

@[simp]
theorem mul_coe {k_1 k_2 : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k_1)
    (g : ModularForm Γ k_2) : (f.mul g : ℍ → ℂ) = f * g :=
  rfl
#align modular_form.mul_coe ModularForm.mul_coe

instance : One (ModularForm Γ 0) :=
  ⟨ { toSlashInvariantForm := 1
      holo' := fun x => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      bdd_at_infty' := fun A => by
        simpa only [SlashInvariantForm.one_coe_eq_one,
          ModularForm.is_invariant_one] using atImInfty.const_boundedAtFilter (1 : ℂ) }⟩

@[simp]
theorem one_coe_eq_one : ((1 : ModularForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl
#align modular_form.one_coe_eq_one ModularForm.one_coe_eq_one

end ModularForm

namespace CuspForm

open ModularForm

variable {F : Type*} {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).add (g.zero_at_infty' A) }⟩
#align cusp_form.has_add CuspForm.hasAdd

@[simp]
theorem coe_add (f g : CuspForm Γ k) : ⇑(f + g) = f + g :=
  rfl
#align cusp_form.coe_add CuspForm.coe_add

@[simp]
theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl
#align cusp_form.add_apply CuspForm.add_apply

instance instZero : Zero (CuspForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      zero_at_infty' := by simpa using Filter.zero_zeroAtFilter _ } ⟩
#align cusp_form.has_zero CuspForm.instZero

@[simp]
theorem coe_zero : ⇑(0 : CuspForm Γ k) = (0 : ℍ → ℂ) :=
  rfl
#align cusp_form.coe_zero CuspForm.coe_zero

@[simp]
theorem zero_apply (z : ℍ) : (0 : CuspForm Γ k) z = 0 :=
  rfl
#align cusp_form.zero_apply CuspForm.zero_apply

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

instance instSMul : SMul α (CuspForm Γ k) :=
  ⟨fun c f =>
    { toSlashInvariantForm := c • f.1
      holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).smul (c • (1 : ℂ)) }⟩
#align cusp_form.has_smul CuspForm.instSMul

@[simp]
theorem coe_smul (f : CuspForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl
#align cusp_form.coe_smul CuspForm.coe_smul

@[simp]
theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
  rfl
#align cusp_form.smul_apply CuspForm.smul_apply

end

instance instNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_infty' := fun A => by simpa using (f.zero_at_infty' A).neg }⟩
#align cusp_form.has_neg CuspForm.instNeg

@[simp]
theorem coe_neg (f : CuspForm Γ k) : ⇑(-f) = -f :=
  rfl
#align cusp_form.coe_neg CuspForm.coe_neg

@[simp]
theorem neg_apply (f : CuspForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl
#align cusp_form.neg_apply CuspForm.neg_apply

instance instSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩
#align cusp_form.has_sub CuspForm.instSub

@[simp]
theorem coe_sub (f g : CuspForm Γ k) : ⇑(f - g) = f - g :=
  rfl
#align cusp_form.coe_sub CuspForm.coe_sub

@[simp]
theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl
#align cusp_form.sub_apply CuspForm.sub_apply

instance : AddCommGroup (CuspForm Γ k) :=
  FunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `CuspForm` to `ℍ → ℂ`. -/
@[simps]
def coeHom : CuspForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := CuspForm.coe_zero
  map_add' _ _ := rfl
#align cusp_form.coe_hom CuspForm.coeHom

instance : Module ℂ (CuspForm Γ k) :=
  Function.Injective.module ℂ coeHom FunLike.coe_injective fun _ _ => rfl

instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩

instance (priority := 99) [CuspFormClass F Γ k] : ModularFormClass F Γ k where
  coe := FunLike.coe
  coe_injective' := FunLike.coe_injective'
  slash_action_eq := SlashInvariantFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_infty _ _ := (CuspFormClass.zero_at_infty _ _).boundedAtFilter

end CuspForm

namespace ModularForm

section GradedRing

/--cast for modular forms, which is useful for removing `heq`'s.-/
def mcast {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) : ModularForm Γ b
    where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' := by intro A; have := f.slash_action_eq' A; convert this; exact h.symm
  holo' := f.holo'
  bdd_at_infty' := by intro A; convert f.bdd_at_infty' A <;> exact h.symm

theorem type_eq {a b : ℤ} (Γ : Subgroup SL(2, ℤ)) (h : a = b) :
    ModularForm Γ a = ModularForm Γ b := by
  induction h
  rfl

theorem cast_eq_mcast {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) :
    cast (type_eq Γ h) f = mcast h f := by
  induction h
  ext1
  rfl

theorem hEq_one_mul (k : ℤ) {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k) :
    HEq ((1 : ModularForm Γ 0).mul f) f := by
  apply heq_of_cast_eq (type_eq Γ (zero_add k).symm).symm
  funext
  rw [cast_eq_mcast, mcast]
  simp only [mul_coe, one_coe_eq_one, one_mul]
  ext1
  rfl
  simp only [zero_add]

theorem hEq_mul_one (k : ℤ) {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ k) :
    HEq (f.mul (1 : ModularForm Γ 0)) f := by
  apply heq_of_cast_eq (type_eq Γ (add_zero k).symm).symm
  funext
  rw [cast_eq_mcast, mcast]
  simp only [mul_coe, one_coe_eq_one, mul_one]
  ext1
  rfl
  simp only [add_zero]

theorem hEq_mul_assoc {a b c : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ a)
    (g : ModularForm Γ b) (h : ModularForm Γ c) : HEq ((f.mul g).mul h) (f.mul (g.mul h)) := by
  apply heq_of_cast_eq (type_eq Γ (add_assoc a b c))
  rw [cast_eq_mcast, mcast]
  ext1
  simp only [mul_coe, Pi.mul_apply, ← mul_assoc]
  rfl
  apply add_assoc

theorem hEq_mul_comm {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    HEq (f.mul g) (g.mul f) := by
  apply heq_of_cast_eq (type_eq Γ (add_comm a b))
  rw [cast_eq_mcast, mcast]
  ext1
  simp only [mul_coe, Pi.mul_apply, mul_comm]
  rfl
  apply add_comm

variable (ι : Type _) (A : ι → Type _) [Zero ι] [GradedMonoid.GOne A]

@[simp]
theorem one_fst : (1 : GradedMonoid A).fst = 0 :=
  rfl

@[simp]
theorem one_snd : (1 : GradedMonoid A).snd = 1 :=
  rfl

instance (Γ : Subgroup SL(2, ℤ)) : GradedMonoid.GOne fun k => ModularForm Γ k
    where
  one := 1

instance (Γ : Subgroup SL(2, ℤ)) : GradedMonoid.GMul fun k => ModularForm Γ k
    where
  mul f g := f.mul g

instance gradedModRing (Γ : Subgroup SL(2, ℤ)) : DirectSum.GCommRing fun k => ModularForm Γ k
    where
  mul f g := f.mul g
  one := 1
  one_mul f := by
    rw [GradedMonoid.GOne.toOne, GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · simp only [(· * ·), one_fst, zero_add]
    · simp only [(· * ·), one_fst, one_snd, Submodule.coe_mk, one_mul, hEq_one_mul]
  mul_one f := by
    rw [GradedMonoid.GOne.toOne, GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · simp only [(· * ·), one_fst, add_zero]
    · simp only [(· * ·), one_fst, one_snd, Submodule.coe_mk, mul_one, hEq_mul_one]
  mul_assoc f g h := by
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · apply add_assoc
    · simp only [(· * ·), Submodule.coe_mk, hEq_mul_assoc]
  mul_zero {i j} f := by ext1; simp
  zero_mul {i j} f := by ext1; simp
  mul_add {i j} f g h := by
    ext1
    simp only [Pi.mul_apply, mul_add, mul_coe, add_apply]
  add_mul {i j} f g h := by
    ext1
    simp only [add_mul, mul_coe, Pi.mul_apply, add_apply]
  mul_comm f g := by
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext
    · apply add_comm
    · apply hEq_mul_comm
  gnpow_zero' := by
    intro f
    apply Sigma.ext <;> rw [GradedMonoid.GMonoid.gnpowRec_zero]
  gnpow_succ' := by
    intro n f
    rw [GradedMonoid.GMul.toMul]
    apply Sigma.ext <;> rw [GradedMonoid.GMonoid.gnpowRec_succ]
  natCast n := n • (1 : ModularForm Γ 0)
  natCast_zero := by simp only [zero_smul]
  natCast_succ n := by simp only [add_smul, one_nsmul, add_right_inj]
  intCast n := n • (1 : ModularForm Γ 0)
  intCast_ofNat := by simp only [coe_nat_zsmul, forall_const]
  intCast_negSucc_ofNat n := by simp only [Int.negSucc_coe]; apply _root_.neg_smul
