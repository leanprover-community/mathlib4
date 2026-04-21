/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# `L¹` space

In this file we establish an API between `Integrable` and the space `L¹` of equivalence
classes of integrable functions, already defined as a special case of `L^p` spaces for `p = 1`.

## Notation

* `α →₁[μ] β` is the type of `L¹` space, where `α` is a `MeasureSpace` and `β` is a
  `NormedAddCommGroup`. `f : α →ₘ β` is a "function" in `L¹`.
  In comments, `[f]` is also used to denote an `L¹` function.

  `₁` can be typed as `\1`.

## Tags

function space, l1

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open EMetric ENNReal Filter MeasureTheory NNReal Set

variable {α β ε ε' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}
variable [NormedAddCommGroup β] [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

namespace MeasureTheory

namespace AEEqFun

section

/-- A class of almost everywhere equal functions is `Integrable` if its function representative
is integrable. -/
def Integrable (f : α →ₘ[μ] ε) : Prop :=
  MeasureTheory.Integrable f μ

theorem integrable_mk {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (mk f hf : α →ₘ[μ] ε) ↔ MeasureTheory.Integrable f μ := by
  simp only [Integrable]
  apply integrable_congr
  exact coeFn_mk f hf

theorem integrable_coeFn {f : α →ₘ[μ] ε} : MeasureTheory.Integrable f μ ↔ Integrable f := by
  rw [← integrable_mk f.aestronglyMeasurable, mk_coeFn]

theorem integrable_zero : Integrable (0 : α →ₘ[μ] ε') :=
  (MeasureTheory.integrable_zero α ε' μ).congr (coeFn_mk _ _).symm

end

section

theorem Integrable.neg {f : α →ₘ[μ] β} : Integrable f → Integrable (-f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 ((integrable_mk hfm).1 hfi).neg

section

theorem integrable_iff_mem_L1 {f : α →ₘ[μ] β} : Integrable f ↔ f ∈ (α →₁[μ] β) := by
  rw [← integrable_coeFn, ← memLp_one_iff_integrable, Lp.mem_Lp_iff_memLp]

-- TODO: generalise these lemmas to `ENormedSpace` or similar
theorem Integrable.add {f g : α →ₘ[μ] β} : Integrable f → Integrable g → Integrable (f + g) := by
  refine induction_on₂ f g fun f hf g hg hfi hgi => ?_
  simp only [integrable_mk, mk_add_mk] at hfi hgi ⊢
  exact hfi.add hgi

theorem Integrable.sub {f g : α →ₘ[μ] β} (hf : Integrable f) (hg : Integrable g) :
    Integrable (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

end

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

theorem Integrable.smul {c : 𝕜} {f : α →ₘ[μ] β} : Integrable f → Integrable (c • f) :=
  induction_on f fun _f hfm hfi => (integrable_mk _).2 <|
    by simpa using ((integrable_mk hfm).1 hfi).smul c

end IsBoundedSMul

end

end AEEqFun

namespace L1


theorem integrable_coeFn (f : α →₁[μ] β) : Integrable f μ := by
  rw [← memLp_one_iff_integrable]
  exact Lp.memLp f

theorem hasFiniteIntegral_coeFn (f : α →₁[μ] β) : HasFiniteIntegral f μ :=
  (integrable_coeFn f).hasFiniteIntegral

@[fun_prop]
theorem stronglyMeasurable_coeFn (f : α →₁[μ] β) : StronglyMeasurable f :=
  Lp.stronglyMeasurable f

@[fun_prop]
theorem measurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α →₁[μ] β) : Measurable f :=
  (Lp.stronglyMeasurable f).measurable

@[fun_prop]
theorem aestronglyMeasurable_coeFn (f : α →₁[μ] β) : AEStronglyMeasurable f μ :=
  Lp.aestronglyMeasurable f

@[fun_prop]
theorem aemeasurable_coeFn [MeasurableSpace β] [BorelSpace β] (f : α →₁[μ] β) : AEMeasurable f μ :=
  (Lp.stronglyMeasurable f).measurable.aemeasurable

theorem edist_def (f g : α →₁[μ] β) : edist f g = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [Lp.edist_def, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm, Pi.sub_apply,
    toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

theorem dist_def (f g : α →₁[μ] β) : dist f g = (∫⁻ a, edist (f a) (g a) ∂μ).toReal := by
  simp_rw [dist_edist, edist_def]

theorem norm_def (f : α →₁[μ] β) : ‖f‖ = (∫⁻ a, ‖f a‖ₑ ∂μ).toReal := by
  simp [Lp.norm_def, eLpNorm, eLpNorm'_eq_lintegral_enorm]

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `norm_def` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem norm_sub_eq_lintegral (f g : α →₁[μ] β) : ‖f - g‖ = (∫⁻ x, ‖f x - g x‖ₑ ∂μ).toReal := by
  rw [norm_def]
  congr 1
  rw [lintegral_congr_ae]
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

theorem ofReal_norm_eq_lintegral (f : α →₁[μ] β) : ENNReal.ofReal ‖f‖ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  rw [norm_def, ENNReal.ofReal_toReal]
  exact ne_of_lt (hasFiniteIntegral_coeFn f)

/-- Computing the norm of a difference between two L¹-functions. Note that this is not a
  special case of `ofReal_norm_eq_lintegral` since `(f - g) x` and `f x - g x` are not equal
  (but only a.e.-equal). -/
theorem ofReal_norm_sub_eq_lintegral (f g : α →₁[μ] β) :
    ENNReal.ofReal ‖f - g‖ = ∫⁻ x, ‖f x - g x‖ₑ ∂μ := by
  simp_rw [ofReal_norm_eq_lintegral, ← edist_zero_right]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with _ ha
  simp only [ha, Pi.sub_apply]

end L1

namespace Integrable


/-- Construct the equivalence class `[f]` of an integrable function `f`, as a member of the
space `Lp β 1 μ`. -/
def toL1 (f : α → β) (hf : Integrable f μ) : α →₁[μ] β :=
  (memLp_one_iff_integrable.2 hf).toLp f

@[simp]
theorem toL1_coeFn (f : α →₁[μ] β) (hf : Integrable f μ) : hf.toL1 f = f := by
  simp [Integrable.toL1]

theorem coeFn_toL1 {f : α → β} (hf : Integrable f μ) : hf.toL1 f =ᵐ[μ] f :=
  AEEqFun.coeFn_mk _ _

@[simp]
theorem toL1_zero (h : Integrable (0 : α → β) μ) : h.toL1 0 = 0 :=
  rfl

@[simp]
theorem toL1_eq_mk (f : α → β) (hf : Integrable f μ) :
    (hf.toL1 f : α →ₘ[μ] β) = AEEqFun.mk f hf.aestronglyMeasurable :=
  rfl

@[simp]
theorem toL1_eq_toL1_iff (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 f hf = toL1 g hg ↔ f =ᵐ[μ] g :=
  MemLp.toLp_eq_toLp_iff _ _

theorem toL1_add (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f + g) (hf.add hg) = toL1 f hf + toL1 g hg :=
  rfl

theorem toL1_neg (f : α → β) (hf : Integrable f μ) : toL1 (-f) (Integrable.neg hf) = -toL1 f hf :=
  rfl

theorem toL1_sub (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    toL1 (f - g) (hf.sub hg) = toL1 f hf - toL1 g hg :=
  rfl

theorem norm_toL1 (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = (∫⁻ a, edist (f a) 0 ∂μ).toReal := by
  simp [toL1, Lp.norm_toLp, eLpNorm, eLpNorm'_eq_lintegral_enorm]

theorem enorm_toL1 {f : α → β} (hf : Integrable f μ) : ‖hf.toL1 f‖ₑ = ∫⁻ a, ‖f a‖ₑ ∂μ := by
  simp only [Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  simp [eLpNorm, eLpNorm']

theorem norm_toL1_eq_lintegral_norm (f : α → β) (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  rw [norm_toL1, lintegral_norm_eq_lintegral_edist]

@[simp]
theorem edist_toL1_toL1 (f g : α → β) (hf : Integrable f μ) (hg : Integrable g μ) :
    edist (hf.toL1 f) (hg.toL1 g) = ∫⁻ a, edist (f a) (g a) ∂μ := by
  simp only [toL1, Lp.edist_toLp_toLp, eLpNorm, one_ne_zero, eLpNorm'_eq_lintegral_enorm,
    Pi.sub_apply, toReal_one, ENNReal.rpow_one, ne_eq, not_false_eq_true, div_self, ite_false]
  simp [edist_eq_enorm_sub]

theorem edist_toL1_zero (f : α → β) (hf : Integrable f μ) :
    edist (hf.toL1 f) 0 = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [edist_zero_right, Lp.enorm_def, toL1_eq_mk, eLpNorm_aeeqFun]
  apply eLpNorm_one_eq_lintegral_enorm

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

theorem toL1_smul (f : α → β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (fun a => k • f a) (hf.smul k) = k • toL1 f hf :=
  rfl

theorem toL1_smul' (f : α → β) (hf : Integrable f μ) (k : 𝕜) :
    toL1 (k • f) (hf.smul k) = k • toL1 f hf :=
  rfl

end Integrable

end MeasureTheory
