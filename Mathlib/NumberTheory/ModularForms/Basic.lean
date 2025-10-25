/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them. Including constructing
the graded ring of modular forms.

We begin by defining modular forms and cusp forms as extension of `SlashInvariantForm`s then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

@[expose] public section

open Complex UpperHalfPlane Matrix.SpecialLinearGroup

open scoped Topology Manifold MatrixGroups ComplexConjugate

noncomputable section

namespace UpperHalfPlane

/-- The matrix `[-1, 0; 0, 1]`, which defines an anti-holomorphic involution of `ℍ` via
`τ ↦ -conj τ`. -/
def J : GL (Fin 2) ℝ := .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

lemma coe_J_smul (τ : ℍ) : (↑(J • τ) : ℂ) = -conj ↑τ := by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : ℝ) < 0 by simp, num, denom]

lemma J_smul (τ : ℍ) : J • τ = ofComplex (-(conj ↑τ)) := by
  ext
  rw [coe_J_smul, ofComplex_apply_of_im_pos (by simpa using τ.im_pos), coe_mk_subtype]

@[simp] lemma val_J : J.val = !![-1, 0; 0, 1] := rfl

@[simp] lemma J_sq : J ^ 2 = 1 := by ext; simp [J, sq, Matrix.one_fin_two]

@[simp] lemma det_J : J.det = -1 := by ext; simp [J]

@[simp] lemma sigma_J : σ J = starRingEnd ℂ := by simp [σ, J]

@[simp] lemma denom_J (τ : ℍ) : denom J τ = 1 := by simp [J, denom]

end UpperHalfPlane

section ModularForm

open ModularForm

/-- The weight `k` slash action of `GL(2, ℝ)⁺` preserves holomorphic functions. This is private,
since it is a step towards the proof of `MDifferentiable.slash` which is more general. -/
private lemma MDifferentiable.slash_of_pos {f : ℍ → ℂ} (hf : MDiff f)
    (k : ℤ) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    MDiff (f ∣[k] g) := by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using hf.comp (mdifferentiable_smul hg)

private lemma slash_J (f : ℍ → ℂ) (k : ℤ) :
    f ∣[k] J = fun τ : ℍ ↦ conj (f <| ofComplex <| -(conj ↑τ)) := by
  simp [slash_def, J_smul]

/-- The weight `k` slash action of the negative-determinant matrix `J` preserves holomorphic
functions. -/
private lemma MDifferentiable.slashJ {f : ℍ → ℂ} (hf : MDiff f) (k : ℤ) :
    MDiff (f ∣[k] J) := by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x ↦ conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x ↦ conj (f <| ofComplex <| -conj x)) := fun z h ↦ by simp [ofComplex_apply_of_im_pos h]
  refine .congr (fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_) this
  have : 0 < (-conj z).im := by simpa using hz
  have := hf.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds this)
  simpa using (this.comp _ differentiable_neg.differentiableAt).star_star.neg

/-- The weight `k` slash action of `GL(2, ℝ)` preserves holomorphic functions. -/
lemma MDifferentiable.slash {f : ℍ → ℂ} (hf : MDiff f)
    (k : ℤ) (g : GL (Fin 2) ℝ) : MDiff (f ∣[k] g) := by
  refine g.det_ne_zero.lt_or_gt.elim (fun hg ↦ ?_) (hf.slash_of_pos k)
  rw [show g = J * (J * g) by simp [← mul_assoc, ← sq], SlashAction.slash_mul]
  exact (hf.slashJ k).slash_of_pos _ (by simpa using hg)

variable (F : Type*) (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)

open scoped ModularForm

/-- These are `SlashInvariantForm`'s that are holomorphic and bounded at infinity. -/
structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt toFun k

/-- The `SlashInvariantForm` associated to a `ModularForm`. -/
add_decl_doc ModularForm.toSlashInvariantForm

/-- These are `SlashInvariantForm`s that are holomorphic and zero at infinity. -/
structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  zero_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt toFun k

/-- The `SlashInvariantForm` associated to a `CuspForm`. -/
add_decl_doc CuspForm.toSlashInvariantForm

/-- `ModularFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and bounded
at all cusps. -/
class ModularFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDiff (f : ℍ → ℂ)
  bdd_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt f k

/-- `CuspFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and zero
at all cusps. -/
class CuspFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDiff (f : ℍ → ℂ)
  zero_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt f k

instance (priority := 100) ModularForm.funLike :
    FunLike (ModularForm Γ k) ℍ ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (priority := 100) ModularFormClass.modularForm :
    ModularFormClass (ModularForm Γ k) Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_cusps := ModularForm.bdd_at_cusps'

@[fun_prop]
lemma ModularFormClass.continuous {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    Continuous f :=
  (ModularFormClass.holo f).continuous

instance (priority := 100) CuspForm.funLike : FunLike (CuspForm Γ k) ℍ ℂ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_cusps := CuspForm.zero_at_cusps'

initialize_simps_projections ModularForm (toFun → coe, as_prefix coe)

initialize_simps_projections CuspForm (toFun → coe, as_prefix coe)

variable {F Γ k}

theorem ModularForm.toFun_eq_coe (f : ModularForm Γ k) : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
theorem ModularForm.toSlashInvariantForm_coe (f : ModularForm Γ k) : ⇑f.1 = f :=
  rfl

theorem CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
theorem CuspForm.toSlashInvariantForm_coe (f : CuspForm Γ k) : ⇑f.1 = f := rfl

@[ext]
theorem ModularForm.ext {f g : ModularForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[ext]
theorem CuspForm.ext {f g : CuspForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `ModularForm` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def ModularForm.copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    ModularForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  bdd_at_cusps' A := h.symm ▸ f.bdd_at_cusps' A

/-- Copy of a `CuspForm` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def CuspForm.copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) : CuspForm Γ k where
  toSlashInvariantForm := f.1.copy f' h
  holo' := h.symm ▸ f.holo'
  zero_at_cusps' A := h.symm ▸ f.zero_at_cusps' A

end ModularForm

namespace ModularForm

open SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

instance add : Add (ModularForm Γ k) where add f g :=
  { toSlashInvariantForm := f + g
    holo' := f.holo'.add g.holo'
    bdd_at_cusps' hc := by simpa using (f.bdd_at_cusps' hc).add (g.bdd_at_cusps' hc) }

@[simp]
theorem coe_add (f g : ModularForm Γ k) : ⇑(f + g) = f + g :=
  rfl

@[simp]
theorem add_apply (f g : ModularForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl

instance instZero : Zero (ModularForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      bdd_at_cusps' hc g hg := by
        simp only [SlashInvariantForm.toFun_eq_coe, coe_zero, SlashAction.zero_slash]
        exact zero_form_isBoundedAtImInfty } ⟩

@[simp]
theorem coe_zero : ⇑(0 : ModularForm Γ k) = (0 : ℍ → ℂ) :=
  rfl

@[simp]
theorem zero_apply (z : ℍ) : (0 : ModularForm Γ k) z = 0 :=
  rfl

@[simp] lemma coe_eq_zero_iff (f : ModularForm Γ k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  rw [← coe_zero, DFunLike.coe_fn_eq]

section
-- scalar multiplication by real types (no assumption on `Γ`)

variable {α : Type*} [SMul α ℝ] [SMul α ℂ] [IsScalarTower α ℝ ℂ]

local instance : IsScalarTower α ℂ ℂ where
  smul_assoc a y z := by simpa using smul_assoc (a • (1 : ℝ)) y z

instance instSMulℝ : SMul α (ModularForm Γ k) where
  smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    bdd_at_cusps' := fun hc g hg ↦ by
      simpa only [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        SlashInvariantForm.coe_smulℝ, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f, smul_slash]
        using (f.bdd_at_cusps' hc g hg).const_smul_left _ }

@[simp]
theorem coe_smul (f : ModularForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl

end

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ] [Γ.HasDetOne]

instance instSMulℂ : SMul α (ModularForm Γ k) where
  smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    bdd_at_cusps' := fun hc g hg ↦ by
      simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        SlashInvariantForm.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f, smul_slash]
      exact (f.bdd_at_cusps' hc g hg).const_smul_left (σ g (c • (1 : ℂ))) }

@[simp]
theorem IsGLPos.coe_smul (f : ModularForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem IsGLPos.smul_apply (f : ModularForm Γ k) (n : α) (z : ℍ) : (n • f) z = n • f z :=
  rfl

end

instance instNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_cusps' := fun hc g hg => by simpa using (f.bdd_at_cusps' hc g hg).neg }⟩

@[simp]
theorem coe_neg (f : ModularForm Γ k) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem neg_apply (f : ModularForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl

instance instSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩

@[simp]
theorem coe_sub (f g : ModularForm Γ k) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem sub_apply (f g : ModularForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl

instance : AddCommGroup (ModularForm Γ k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `ModularForm` to `ℍ → ℂ`. -/
@[simps]
def coeHom : ModularForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

instance : Module ℝ (ModularForm Γ k) :=
  Function.Injective.module ℝ coeHom DFunLike.coe_injective fun _ _ => rfl

instance [Γ.HasDetOne] : Module ℂ (ModularForm Γ k) :=
  Function.Injective.module ℂ coeHom DFunLike.coe_injective fun _ _ => rfl

instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

/-- The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
@[simps! -fullyApplied coe]
def mul {k_1 k_2 : ℤ} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_cusps' hc γ hγ := by
    simpa [mul_slash] using ((f.bdd_at_cusps' hc γ hγ).mul (g.bdd_at_cusps' hc γ hγ)).smul _

@[deprecated (since := "2025-12-06")] alias mul_coe := coe_mul

/-- The constant function with value `x : ℂ` as a modular form of weight 0 and any level. -/
@[simps! -fullyApplied] def const (x : ℂ) [Γ.HasDetOne] : ModularForm Γ 0 where
  toSlashInvariantForm := .const x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_const, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using atImInfty.const_boundedAtFilter _

@[deprecated (since := "2025-12-06")] alias const_toFun := coe_const

@[simp]
lemma const_apply [Γ.HasDetOne] (x : ℂ) (τ : ℍ) : (const x : ModularForm Γ 0) τ = x := rfl

/-- The constant function with value `x : ℂ` as a modular form of weight 0 and any level. -/
@[simps! -fullyApplied coe] def constℝ (x : ℝ) [Γ.HasDetPlusMinusOne] : ModularForm Γ 0 where
  toSlashInvariantForm := .constℝ x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_constℝ, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using atImInfty.const_boundedAtFilter _

@[deprecated (since := "2025-12-06")] alias constℝ_toFun := coe_constℝ

@[simp]
lemma constℝ_apply [Γ.HasDetPlusMinusOne] (x : ℝ) (τ : ℍ) :
    (constℝ x : ModularForm Γ 0) τ = x :=
  rfl

instance [Γ.HasDetPlusMinusOne] : One (ModularForm Γ 0) where
  one := { constℝ 1 with toSlashInvariantForm := 1 }

@[simp]
theorem one_coe_eq_one [Γ.HasDetPlusMinusOne] : ⇑(1 : ModularForm Γ 0) = 1 :=
  rfl

instance [Γ.HasDetPlusMinusOne] : NatCast (ModularForm Γ 0) where
  natCast n := constℝ n

@[simp, norm_cast]
lemma coe_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    ⇑(n : ModularForm Γ 0) = n := rfl

lemma toSlashInvariantForm_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    (n : ModularForm Γ 0).toSlashInvariantForm = n := rfl

instance [Γ.HasDetPlusMinusOne] : IntCast (ModularForm Γ 0) where
  intCast z := constℝ z

@[simp, norm_cast]
lemma coe_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) :
    ⇑(z : ModularForm Γ 0) = z := rfl

lemma toSlashInvariantForm_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) :
    (z : ModularForm Γ 0).toSlashInvariantForm = z := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_cusps' := fun A => by simpa using (f.zero_at_cusps' A).add (g.zero_at_cusps' A) }⟩

@[simp]
theorem coe_add (f g : CuspForm Γ k) : ⇑(f + g) = f + g :=
  rfl

@[simp]
theorem add_apply (f g : CuspForm Γ k) (z : ℍ) : (f + g) z = f z + g z :=
  rfl

instance instZero : Zero (CuspForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      zero_at_cusps' hc g hg := by simpa using Filter.zero_zeroAtFilter _ } ⟩

@[simp]
theorem coe_zero : ⇑(0 : CuspForm Γ k) = (0 : ℍ → ℂ) :=
  rfl

@[simp]
theorem zero_apply (z : ℍ) : (0 : CuspForm Γ k) z = 0 :=
  rfl

section
-- scalar multiplication by real types (no assumption on `Γ`)

variable {α : Type*} [SMul α ℝ] [SMul α ℂ] [IsScalarTower α ℝ ℂ]

local instance : IsScalarTower α ℂ ℂ where
  smul_assoc a y z := by simpa using smul_assoc (a • (1 : ℝ)) y z

instance instSMul : SMul α (CuspForm Γ k) where smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        SlashInvariantForm.coe_smulℝ, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f, smul_slash]
      exact (f.zero_at_cusps' hc g hg).smul _ }

@[simp]
theorem coe_smul (f : CuspForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
  rfl

end

section
-- scalar multiplication by complex types (assuming `IsGLPos Γ`)

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ] [Γ.HasDetOne]

instance IsGLPos.instSMul : SMul α (CuspForm Γ k) where smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        SlashInvariantForm.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f,
        smul_slash]
      exact (f.zero_at_cusps' hc g hg).smul _ }

@[simp]
theorem IsGLPos.coe_smul (f : CuspForm Γ k) (n : α) : ⇑(n • f) = n • ⇑f :=
  rfl

@[simp]
theorem IsGLPos.smul_apply (f : CuspForm Γ k) (n : α) {z : ℍ} : (n • f) z = n • f z :=
  rfl

end

instance instNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_cusps' hc g hg := by simpa using (f.zero_at_cusps' hc g hg).neg }⟩

@[simp]
theorem coe_neg (f : CuspForm Γ k) : ⇑(-f) = -f :=
  rfl

@[simp]
theorem neg_apply (f : CuspForm Γ k) (z : ℍ) : (-f) z = -f z :=
  rfl

instance instSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩

@[simp]
theorem coe_sub (f g : CuspForm Γ k) : ⇑(f - g) = f - g :=
  rfl

@[simp]
theorem sub_apply (f g : CuspForm Γ k) (z : ℍ) : (f - g) z = f z - g z :=
  rfl

instance : AddCommGroup (CuspForm Γ k) :=
  DFunLike.coe_injective.addCommGroup _ rfl coe_add coe_neg coe_sub coe_smul coe_smul

/-- Additive coercion from `CuspForm` to `ℍ → ℂ`. -/
@[simps]
def coeHom : CuspForm Γ k →+ ℍ → ℂ where
  toFun f := f
  map_zero' := CuspForm.coe_zero
  map_add' _ _ := rfl

instance : Module ℝ (CuspForm Γ k) :=
  Function.Injective.module ℝ coeHom DFunLike.coe_injective fun _ _ => rfl

instance [Γ.HasDetOne] : Module ℂ (CuspForm Γ k) :=
  Function.Injective.module ℂ coeHom DFunLike.coe_injective fun _ _ => rfl

instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩

instance (priority := 99) [FunLike F ℍ ℂ] [CuspFormClass F Γ k] : ModularFormClass F Γ k where
  slash_action_eq := SlashInvariantFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_cusps f _ hc g hg := (CuspFormClass.zero_at_cusps f hc g hg).boundedAtFilter

end CuspForm

namespace ModularForm

section GradedRing

/-- Cast for modular forms, which is useful for avoiding `Heq`s. -/
def mcast {a b : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (h : a = b) (f : ModularForm Γ a) :
    ModularForm Γ b where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' A := h ▸ f.slash_action_eq' A
  holo' := f.holo'
  bdd_at_cusps' A := h ▸ f.bdd_at_cusps' A

@[ext (iff := false)]
theorem gradedMonoid_eq_of_cast {Γ : Subgroup (GL (Fin 2) ℝ)} {a b : GradedMonoid (ModularForm Γ)}
    (h : a.fst = b.fst) (h2 : mcast h a.snd = b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

instance (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] :
    GradedMonoid.GOne (ModularForm Γ) where
  one := 1

instance (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] :
    GradedMonoid.GMul (ModularForm Γ) where
  mul f g := f.mul g

instance instGCommRing (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] :
    DirectSum.GCommRing (ModularForm Γ) where
  one_mul _ := gradedMonoid_eq_of_cast (zero_add _) (ext fun _ => one_mul _)
  mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext fun _ => mul_one _)
  mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext fun _ => mul_assoc _ _ _)
  mul_zero {_ _} _ := ext fun _ => mul_zero _
  zero_mul {_ _} _ := ext fun _ => zero_mul _
  mul_add {_ _} _ _ _ := ext fun _ => mul_add _ _ _
  add_mul {_ _} _ _ _ := ext fun _ => add_mul _ _ _
  mul_comm _ _ := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  natCast := Nat.cast
  natCast_zero := ext fun _ => Nat.cast_zero
  natCast_succ _ := ext fun _ => Nat.cast_succ _
  intCast := Int.cast
  intCast_ofNat _ := ext fun _ => AddGroupWithOne.intCast_ofNat _
  intCast_negSucc_ofNat _ := ext fun _ => AddGroupWithOne.intCast_negSucc _

instance instGAlgebra (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] :
    DirectSum.GAlgebra ℂ (ModularForm Γ) where
  toFun := { toFun z := const z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_one := rfl
  map_mul _x _y := rfl
  commutes _c _x := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  smul_def _x _x := gradedMonoid_eq_of_cast (zero_add _).symm (ext fun _ => rfl)

open scoped DirectSum in
example (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] : Algebra ℂ (⨁ i, ModularForm Γ i) :=
inferInstance

end GradedRing

end ModularForm

section translate

open ModularForm OnePoint

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)

open ConjAct Pointwise in
/-- Translating a `ModularForm` by `GL(2, ℝ)`, to obtain a new `ModularForm`. -/
noncomputable def ModularForm.translate [ModularFormClass F Γ k] (g : GL (Fin 2) ℝ) :
    ModularForm (toConjAct g⁻¹ • Γ) k where
  __ := SlashInvariantForm.translate f g
  bdd_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe, SlashInvariantForm.coe_translate,
      ← SlashAction.slash_mul, ← isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
    apply ModularFormClass.bdd_at_cusps f
    simpa [mul_smul, hγ] using hc.smul g
  holo' := (ModularFormClass.holo f).slash k g

@[simp]
lemma ModularForm.coe_translate [ModularFormClass F Γ k] (g : GL (Fin 2) ℝ) :
    translate f g = ⇑f ∣[k] g :=
  rfl

open ConjAct Pointwise in
/-- Translating a `CuspForm` by `SL(2, ℤ)`, to obtain a new `CuspForm`. -/
noncomputable def CuspForm.translate [CuspFormClass F Γ k] (g : GL (Fin 2) ℝ) :
    CuspForm (toConjAct g⁻¹ • Γ) k where
  __ := ModularForm.translate f g
  zero_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe,
      ModularForm.coe_translate, ← SlashAction.slash_mul, ← isZeroAt_infty_iff,
      ← OnePoint.IsZeroAt.smul_iff]
    apply CuspFormClass.zero_at_cusps f
    simpa [mul_smul, hγ] using hc.smul g

@[simp]
lemma CuspForm.coe_translate [CuspFormClass F Γ k] (g : SL(2, ℤ)) :
    translate f g = ⇑f ∣[k] g :=
  rfl

end translate

section SL2Z

open ModularForm CuspForm OnePoint

variable {k F} {Γ : Subgroup (GL (Fin 2) ℝ)} [FunLike F ℍ ℂ] (f : F)

instance [Γ.IsArithmetic] : Fact (IsCusp ∞ Γ) :=
  ⟨by simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩⟩

lemma ModularFormClass.bdd_at_infty [ModularFormClass F Γ k] [Fact (IsCusp ∞ Γ)] :
    IsBoundedAtImInfty f :=
  isBoundedAt_infty_iff.mp <| bdd_at_cusps f Fact.out

lemma CuspFormClass.zero_at_infty [CuspFormClass F Γ k] [Fact (IsCusp ∞ Γ)] :
    IsZeroAtImInfty f :=
  isZeroAt_infty_iff.mp <| zero_at_cusps f Fact.out

variable [Γ.IsArithmetic] (g : SL(2, ℤ))

lemma ModularFormClass.bdd_at_infty_slash [ModularFormClass F Γ k] :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [← OnePoint.isBoundedAt_infty_iff, SL_slash, ← OnePoint.IsBoundedAt.smul_iff]
  apply bdd_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

lemma CuspFormClass.zero_at_infty_slash [CuspFormClass F Γ k] :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [← OnePoint.isZeroAt_infty_iff, SL_slash, ← OnePoint.IsZeroAt.smul_iff]
  apply zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

end SL2Z
