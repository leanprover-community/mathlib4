/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Q-expansions of modular forms
-/

open ModularForm Complex Filter Asymptotics UpperHalfPlane

open scoped Real Topology Manifold

noncomputable section

/-!
## Extending functions from `ℍ` to `ℂ`
-/

local notation "I∞" => comap Complex.im atTop

namespace UpperHalfPlane

@[simp] lemma coe_mk_subtype (z : ℂ) (hz : 0 < z.im) :
    UpperHalfPlane.coe ⟨z, hz⟩ = z := by
  rfl

/-- DOCSTRING -/
lemma ofComplex_apply' {z : ℂ} (hz : 0 < z.im) :
    ofComplex z = ⟨z, hz⟩ :=
  by simpa only [coe_mk_subtype] using ofComplex_apply ⟨z, hz⟩

lemma eventuallyEq_coe_comp_ofComplex (z : ℂ) (hz : 0 < z.im) :
    UpperHalfPlane.coe ∘ ofComplex =ᶠ[𝓝 z] id := by
  refine eventually_of_mem
    ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz) (fun x hx ↦ ?_)
  simp only [Function.comp_apply, ofComplex_apply' hx, id_eq, coe_mk_subtype]

lemma im_pos_mem_comap_im_atTop : {z | 0 < z.im} ∈ I∞ :=
  mem_comap_atTop_iff_exists_forall_lt.mpr ⟨0, fun _ ↦ by tauto⟩

lemma tendsto_comap_im_ofComplex :
    Tendsto ofComplex I∞ atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  refine tendsto_comap.congr' ?_
  filter_upwards [im_pos_mem_comap_im_atTop] with z hz
  simp only [ofComplex_apply' hz, ← UpperHalfPlane.coe_im, coe_mk_subtype]

lemma tendsto_coe_atImInfty :
    Tendsto UpperHalfPlane.coe atImInfty I∞ := by
  simpa only [atImInfty, tendsto_comap_iff, Function.comp_def,
    funext UpperHalfPlane.coe_im] using tendsto_comap

lemma mdifferentiableAt_ofComplex (z : ℂ) (hz : 0 < z.im) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ofComplex z := by
  rw [mdifferentiableAt_iff]
  constructor
  · rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex z hz).symm ?_
    simpa only [UpperHalfPlane.ofComplex_apply' hz, Subtype.coe_mk] using tendsto_id
  · simp only [writtenInExtChartAt, extChartAt, PartialHomeomorph.extend,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
      PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
      PartialHomeomorph.singletonChartedSpace_chartAt_eq, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, CompTriple.comp_eq, modelWithCornersSelf_coe, Set.range_id, id_eq,
      differentiableWithinAt_univ]
    exact differentiableAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex z hz)

end UpperHalfPlane

local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R

section ModformEquivs

variable {k : ℤ}

theorem modform_bounded_atIInfty
    {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    BoundedAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, ModularForm.toSlashInvariantForm_coe]
    using IsBigO.comp_tendsto (ModularFormClass.bdd_at_infty f 1) tendsto_comap_im_ofComplex

theorem cuspform_zero_atIInfty {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F Γ k] (f : F) : ZeroAtFilter I∞ (f ∘ ofComplex) := by
  simpa only [SlashAction.slash_one, CuspForm.toSlashInvariantForm_coe]
    using (CuspFormClass.zero_at_infty f 1).comp tendsto_comap_im_ofComplex

theorem modform_periodic {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (CongruenceSubgroup.Gamma 1) k] (f : F) (w : ℂ) :
    (f ∘ ofComplex) (w + 1) = (f ∘ ofComplex) w := by
  by_cases hw : 0 < im w
  · have : 0 < im (w + 1) := by simp only [add_im, one_im, add_zero, hw]
    simp only [Function.comp_apply, ofComplex_apply' hw, ofComplex_apply' this]
    convert SlashInvariantForm.vAdd_width_periodic 1 k 1 f ⟨w, hw⟩ using 2
    simp only [Nat.cast_one, Int.cast_one, mul_one, UpperHalfPlane.ext_iff, coe_mk_subtype,
      coe_vadd, ofReal_one, add_comm]
  · have : ¬0 < im (w + 1) := by simp only [add_im, one_im, add_zero, hw, not_false_eq_true]
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hw),
      ofComplex_apply_of_im_nonpos (not_lt.mp this)]

theorem modform_hol {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k]
    (f : F) {z : ℂ} (hz : 0 < im z) :
    DifferentiableAt ℂ (f ∘ ofComplex) z := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact (ModularFormClass.holo f _).comp z (mdifferentiableAt_ofComplex z hz)

theorem modform_hol_infty
    {Γ : Subgroup SL(2, ℤ)} {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    ∀ᶠ z : ℂ in I∞, DifferentiableAt ℂ (f ∘ ofComplex) z :=
  eventually_of_mem im_pos_mem_comap_im_atTop (fun _ hz ↦ modform_hol f hz)

end ModformEquivs

section Modforms

theorem z_in_H {q : ℂ} (hq : Complex.abs q < 1) (hq_ne : q ≠ 0) : 0 < im (invQParam 1 q) := by
  rw [im_invQParam]
  apply mul_pos_of_neg_of_neg
  · exact div_neg_of_neg_of_pos (neg_lt_zero.mpr zero_lt_one) Real.two_pi_pos
  rwa [Real.log_neg_iff (Complex.abs.pos hq_ne)]

/-- The analytic function `F` such that `f τ = F (exp (2 * π * I * τ))`. -/
def cuspFcnH (f : ℍ → ℂ) : ℂ → ℂ := cuspFcn 1 (f ∘ ofComplex)

variable {k : ℤ}

local notation  "Γ(" n ")"  => CongruenceSubgroup.Gamma n

theorem eq_cuspFcnH {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ(1) k] (f : F) (z : ℍ) :
    cuspFcnH f (qParam 1 z) = f z := by
  convert eq_cuspFcn one_ne_zero (modform_periodic f) z
  simp only [Function.comp_apply, ofComplex_apply]

theorem cusp_fcn_diff {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ(1) k] (f : F)
    {q : ℂ} (hq : Complex.abs q < 1) :
    DifferentiableAt ℂ (cuspFcnH f) q := by
  rcases eq_or_ne q 0 with rfl | hq'
  · exact differentiableAt_cuspFcn_zero zero_lt_one (modform_periodic f) (modform_hol_infty f)
      (modform_bounded_atIInfty f)
  · exact qParam_right_inv one_ne_zero hq' ▸
      (differentiableAt_cuspFcn one_ne_zero (modform_periodic f) (modform_hol f <| z_in_H hq hq'))

theorem cusp_fcn_vanish {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ(1) k] (f : F) :
    cuspFcnH f 0 = 0 :=
  cuspFcn_zero_of_zero_at_inf zero_lt_one (cuspform_zero_atIInfty f)

theorem exp_decay_of_cuspform {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F Γ(1) k] (f : F) :
    IsBigO atImInfty f fun z ↦ Real.exp (-2 * π * z.im) := by
  have := exp_decay_of_zero_at_inf zero_lt_one (modform_periodic f)
    (modform_hol_infty f) (cuspform_zero_atIInfty f)
  simp only [div_one] at this
  convert this.comp_tendsto tendsto_coe_atImInfty using 1
  ext τ
  simp only [Function.comp_apply, ofComplex_apply]

end Modforms

end
