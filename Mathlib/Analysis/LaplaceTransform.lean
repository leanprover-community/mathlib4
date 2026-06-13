/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Laplace transform

This file defines the one-sided Laplace transform

`laplace f s = ∫ t in Ioi 0, exp (-s * t) • f t`

of a function `f : ℝ → E`. The convergence predicate only needs a normed additive group with a
complex scalar action; the transform itself needs the real normed-space structure required by the
Bochner integral. The definitions take an optional measure argument, defaulting to Lebesgue measure
restricted to `Ioi 0`.

## Main definitions

* `LaplaceConvergent f s`: the predicate that the Laplace integral is defined at `s`.
* `laplace f s`: the Laplace transform of `f` at `s`.
* `HasLaplace f s m`: shorthand asserting convergence and value of the Laplace transform.
* `LaplaceConvergent.of_re_le`/`LaplaceConvergent.of_re_lt`: half-plane monotonicity
  of convergence in `s.re`.
* `laplaceConvergent_of_isBigO_exp`: exponential-order convergence for `s.re` larger
  than the growth rate.
* `laplace_indicator_comp_sub`: the time-shift rule for the one-sided Laplace transform.
* `hasLaplace_const`/`hasLaplace_one`/`hasLaplace_cexp`: basic transform values.

Derivative, integration, holomorphy, and convolution rules are in
`Mathlib.Analysis.LaplaceTransformDeriv`.

## Design notes

As for `mellin`, the transform is a total function. If the integrand is not integrable, the
Bochner integral convention makes the value `0`; use `LaplaceConvergent` or `HasLaplace` to record
the meaningful cases.

Scalar multiplication hypotheses are kept at `IsBoundedSMul` when boundedness suffices for
integrability. Some proofs locally derive `NormSMulClass` from `IsBoundedSMul` and a normed
division ring scalar, because exact norm and integral identities such as `norm_smul` and
`integral_smul` are stated with the equality-form typeclass.

-/

@[expose] public section

open MeasureTheory Set Asymptotics Filter
open Complex hiding exp
open scoped Topology

noncomputable section

variable {E : Type*}

section Defs

variable [NormedAddCommGroup E] [SMul ℂ E]

/-- Predicate on `f` and `s` asserting that the Laplace integral is well-defined.

The optional measure argument defaults to Lebesgue measure restricted to `(0, ∞)`, giving the
classical one-sided Laplace transform. -/
def LaplaceConvergent (f : ℝ → E) (s : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t) μ

/-- Unfold convergence of a Laplace integral with an arbitrary measure. -/
theorem laplaceConvergent_iff_integrable (f : ℝ → E) (s : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    LaplaceConvergent f s μ ↔
      Integrable (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t) μ :=
  Iff.rfl

/-- Unfold convergence of a one-sided Laplace integral with respect to a base measure. -/
theorem laplaceConvergent_iff_integrableOn (f : ℝ → E) (s : ℂ)
    (μ : Measure ℝ := volume) :
    LaplaceConvergent f s (μ.restrict (Ioi 0)) ↔
      IntegrableOn (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t) (Ioi 0) μ :=
  Iff.rfl

theorem LaplaceConvergent.congr_ae {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hfg : f =ᵐ[μ] g) : LaplaceConvergent g s μ := by
  exact hf.congr <| hfg.mono fun _ ht => by simp [ht]

theorem laplaceConvergent_congr_ae {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hfg : f =ᵐ[μ] g) : LaplaceConvergent f s μ ↔ LaplaceConvergent g s μ :=
  ⟨fun hf => hf.congr_ae hfg, fun hg => hg.congr_ae hfg.symm⟩

theorem LaplaceConvergent.const_smul {μ : Measure ℝ} {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    LaplaceConvergent (fun t => c • f t) s μ := by
  exact (hf.smul c).congr <| ae_of_all _ fun _ => by simp only [Pi.smul_apply, smul_comm]

end Defs

section Transform

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]

/-- The Laplace transform of `f`, at the complex parameter `s`.

The optional measure argument defaults to Lebesgue measure restricted to `(0, ∞)`, giving the
classical one-sided Laplace transform. -/
def laplace (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) : E :=
  ∫ t : ℝ, Complex.exp ((-s) * (t : ℂ)) • f t ∂μ

/-- Predicate standing for "the Laplace transform of `f` is defined at `s` and equal to `m`". -/
def HasLaplace (f : ℝ → E) (s : ℂ) (m : E)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  LaplaceConvergent f s μ ∧ laplace f s μ = m

theorem laplace_eq_integral_Ioi (f : ℝ → E) (s : ℂ) :
    laplace f s = ∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ)) • f t := rfl

theorem laplace_congr_ae {μ : Measure ℝ} {f g : ℝ → E} (s : ℂ) (hfg : f =ᵐ[μ] g) :
    laplace f s μ = laplace g s μ := by
  exact integral_congr_ae <| hfg.mono fun _ ht => by simp [ht]

theorem HasLaplace.congr_ae {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m μ) (hfg : f =ᵐ[μ] g) : HasLaplace g s m μ :=
  ⟨hf.1.congr_ae hfg, by rw [← laplace_congr_ae s hfg, hf.2]⟩

end Transform

section Add

variable [NormedAddCommGroup E]

@[simp]
theorem laplace_zero [NormedSpace ℝ E] [SMulZeroClass ℂ E] (s : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (fun _ : ℝ => (0 : E)) s μ = 0 := by
  simp [laplace]

@[simp]
theorem laplace_neg [NormedSpace ℝ E] [DistribSMul ℂ E] (f : ℝ → E) (s : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (fun t => -f t) s μ = -laplace f s μ := by
  simp [laplace, integral_neg]

theorem LaplaceConvergent.add [DistribSMul ℂ E] {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (fun t => f t + g t) s μ := by
  exact (Integrable.add hf hg).congr <| ae_of_all _ fun _ => (smul_add _ _ _).symm

theorem LaplaceConvergent.sub [DistribSMul ℂ E] {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (fun t => f t - g t) s μ := by
  exact (Integrable.sub hf hg).congr <| ae_of_all _ fun _ => (smul_sub _ _ _).symm

theorem hasLaplace_add [NormedSpace ℝ E] [DistribSMul ℂ E]
    {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    HasLaplace (fun t => f t + g t) s (laplace f s μ + laplace g s μ) μ :=
  ⟨hf.add hg, by
    simpa only [laplace, smul_add] using integral_add hf hg⟩

theorem hasLaplace_sub [NormedSpace ℝ E] [DistribSMul ℂ E]
    {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    HasLaplace (fun t => f t - g t) s (laplace f s μ - laplace g s μ) μ :=
  ⟨hf.sub hg, by
    simpa only [laplace, smul_sub] using integral_sub hf hg⟩

theorem HasLaplace.add [NormedSpace ℝ E] [DistribSMul ℂ E]
    {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplace f s m μ) (hg : HasLaplace g s n μ) :
    HasLaplace (fun t => f t + g t) s (m + n) μ := by
  simpa [hf.2, hg.2] using hasLaplace_add hf.1 hg.1

theorem HasLaplace.sub [NormedSpace ℝ E] [DistribSMul ℂ E]
    {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplace f s m μ) (hg : HasLaplace g s n μ) :
    HasLaplace (fun t => f t - g t) s (m - n) μ := by
  simpa [hf.2, hg.2] using hasLaplace_sub hf.1 hg.1

end Add

section ConstSMul

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [SMul ℂ E]

/-- Compatibility with scalar multiplication by a normed division ring. For scalar multiplication by
more general rings assuming *a priori* convergence, see `hasLaplace_const_smul`. -/
theorem laplace_const_smul (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0))
    {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    laplace (fun t => c • f t) s μ = c • laplace f s μ := by
  letI : NormSMulClass 𝕜 E := NormedDivisionRing.toNormSMulClass
  simp only [laplace, smul_comm, integral_smul]

theorem laplace_div_const (f : ℝ → ℂ) (s a : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (fun t => f t / a) s μ = laplace f s μ / a := by
  simp_rw [laplace, smul_eq_mul, ← mul_div_assoc, integral_div]

theorem hasLaplace_const_smul {μ : Measure ℝ} {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) {R : Type*} [NormedRing R] [Module R E]
    [IsBoundedSMul R E] [SMulCommClass ℝ R E] [SMulCommClass ℂ R E] (c : R) :
    HasLaplace (fun t => c • f t) s (c • laplace f s μ) μ :=
  ⟨hf.const_smul c, by
    simpa [laplace, smul_comm] using hf.integral_smul c⟩

theorem HasLaplace.const_smul {μ : Measure ℝ} {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m μ) {R : Type*} [NormedRing R] [Module R E]
    [IsBoundedSMul R E] [SMulCommClass ℝ R E] [SMulCommClass ℂ R E] (c : R) :
    HasLaplace (fun t => c • f t) s (c • m) μ := by
  simpa [hf.2] using hasLaplace_const_smul hf.1 c

end ConstSMul

section Norm

/-- The norm of the Laplace kernel. -/
theorem norm_laplaceKernel (s : ℂ) (t : ℝ) :
    ‖Complex.exp ((-s) * (t : ℂ))‖ = Real.exp (-s.re * t) := by
  simp [Complex.norm_exp, mul_comm]

variable [NormedAddCommGroup E] [MulActionWithZero ℂ E] [IsBoundedSMul ℂ E]

/-- A convergent Laplace integrand has an a.e. strongly measurable unweighted function. -/
theorem LaplaceConvergent.aestronglyMeasurable {μ : Measure ℝ} {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) : AEStronglyMeasurable f μ := by
  refine (aestronglyMeasurable_smul_iff₀
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) μ)
    (ae_of_all _ fun _ => Complex.exp_ne_zero _)).1 ?_
  exact (show Integrable (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t) μ from hf)
    |>.aestronglyMeasurable

local instance : NormSMulClass ℂ E :=
  NormedDivisionRing.toNormSMulClass

/-- Auxiliary lemma reducing convergence of vector-valued Laplace integrals to real-valued
integrability of the norm. -/
theorem laplaceConvergent_iff_norm {μ : Measure ℝ} {f : ℝ → E} {s : ℂ}
    (hf : AEStronglyMeasurable f μ) :
    LaplaceConvergent f s μ ↔
      Integrable (fun t : ℝ => Real.exp (-s.re * t) * ‖f t‖) μ := by
  rw [LaplaceConvergent, ← integrable_norm_iff
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp ((-s) * (t : ℂ)))
      |>.aestronglyMeasurable.smul hf)]
  refine integrable_congr <| ae_of_all _ fun t => ?_
  dsimp only
  rw [norm_smul]
  simp [Complex.norm_exp, mul_comm]

/-- A convenient sufficient condition for convergence of a Laplace integral. -/
theorem laplaceConvergent_of_integrable_norm {μ : Measure ℝ} {f : ℝ → E} {s : ℂ}
    (hf : AEStronglyMeasurable f μ)
    (h : Integrable (fun t : ℝ => Real.exp (-s.re * t) * ‖f t‖) μ) :
    LaplaceConvergent f s μ :=
  (laplaceConvergent_iff_norm hf).2 h

/-- Exponential-order convergence criterion for the Laplace transform.

If `f` is locally integrable on `[0, ∞)` and `f t = O(exp (a * t))` as `t → ∞`,
then its Laplace transform converges on the half-plane `a < s.re`. -/
theorem laplaceConvergent_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    (hfc : LocallyIntegrableOn f (Ici 0))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    LaplaceConvergent f s := by
  exact laplaceConvergent_of_integrable_norm
    (AEStronglyMeasurable.mono_set Ioi_subset_Ici_self hfc.aestronglyMeasurable)
    (integrableOn_exp_neg_mul_norm_of_isBigO_exp hfc hf_top hs)

end Norm

section Monotonicity

variable [NormedAddCommGroup E] [MulActionWithZero ℂ E] [IsBoundedSMul ℂ E]

local instance : NormSMulClass ℂ E :=
  NormedDivisionRing.toNormSMulClass

/-- Monotonicity of Laplace convergence in the real part of the parameter, for measures supported
on the nonnegative reals. -/
theorem LaplaceConvergent.of_re_le_of_ae_nonneg {μ : Measure ℝ} {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀ μ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hs : s₀.re ≤ s.re) :
    LaplaceConvergent f s μ := by
  have hf_meas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  rw [laplaceConvergent_iff_norm hf_meas] at hf ⊢
  refine hf.mono' ((by fun_prop : Continuous fun t : ℝ => Real.exp (-s.re * t))
    |>.aestronglyMeasurable.mul hf_meas.norm) ?_
  filter_upwards [hμ] with t ht_nonneg
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  gcongr

/-- Half-plane monotonicity of convergence for the one-sided Laplace transform. If `f` has a
Laplace transform at `s₀`, then it has a Laplace transform at every `s` with
`s₀.re ≤ s.re`. -/
theorem LaplaceConvergent.of_re_le {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re ≤ s.re) : LaplaceConvergent f s :=
  hf.of_re_le_of_ae_nonneg ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht => le_of_lt ht) hs

/-- Strict half-plane version of `LaplaceConvergent.of_re_le`. -/
theorem LaplaceConvergent.of_re_lt {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re < s.re) : LaplaceConvergent f s :=
  hf.of_re_le hs.le

/-- Laplace convergence only depends on the real part of the parameter. -/
theorem laplaceConvergent_congr_re {μ : Measure ℝ} {f : ℝ → E} {s₀ s : ℂ}
    (hs : s₀.re = s.re) :
    LaplaceConvergent f s₀ μ ↔ LaplaceConvergent f s μ := by
  by_cases hf_meas : AEStronglyMeasurable f μ
  · rw [laplaceConvergent_iff_norm hf_meas, laplaceConvergent_iff_norm hf_meas]
    simp [hs]
  · constructor <;> intro hf <;> exact (hf_meas hf.aestronglyMeasurable).elim

/-- Transfer one-sided Laplace convergence between parameters with the same real part. -/
theorem LaplaceConvergent.congr_re {μ : Measure ℝ} {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀ μ) (hs : s₀.re = s.re) :
    LaplaceConvergent f s μ :=
  (laplaceConvergent_congr_re hs).1 hf

end Monotonicity

section NormBound

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MulActionWithZero ℂ E]
  [IsBoundedSMul ℂ E]

local instance : NormSMulClass ℂ E :=
  NormedDivisionRing.toNormSMulClass

/-- The norm of a Laplace transform is bounded by the integral of the norm of its integrand. -/
theorem norm_laplace_le_integral_norm (f : ℝ → E) (s : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    ‖laplace f s μ‖ ≤ ∫ t : ℝ, Real.exp (-s.re * t) * ‖f t‖ ∂μ := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr with t
  rw [norm_smul]
  simp [Complex.norm_exp, mul_comm]

end NormBound

section Shift

variable [NormedAddCommGroup E]

theorem LaplaceConvergent.cexp_smul [MulAction ℂ E]
    {μ : Measure ℝ} {f : ℝ → E} {s a : ℂ} :
    LaplaceConvergent (fun t : ℝ => Complex.exp (a * (t : ℂ)) • f t) s μ ↔
      LaplaceConvergent f (s - a) μ := by
  refine integrable_congr <| ae_of_all _ fun t => ?_
  dsimp only
  rw [← mul_smul, ← Complex.exp_add]
  congr 1
  ring_nf

/-- Multiplying the original function by an exponential translates the Laplace transform. -/
theorem laplace_cexp_smul [NormedSpace ℝ E] [MulAction ℂ E] (f : ℝ → E) (s a : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (fun t : ℝ => Complex.exp (a * (t : ℂ)) • f t) s μ =
      laplace f (s - a) μ := by
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_smul, ← Complex.exp_add]
  congr 1
  ring_nf

end Shift

section TimeShift

variable [NormedAddCommGroup E]

/-- Time-shift convergence rule for the one-sided Laplace transform.

For `0 ≤ a`, shifting a function to the right by `a` and cutting it off on `(a, ∞)` preserves
convergence of its Laplace transform. -/
theorem LaplaceConvergent.indicator_comp_sub [MulActionWithZero ℂ E] [IsBoundedSMul ℂ E]
    {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 ≤ a) :
    LaplaceConvergent ((Ioi a).indicator fun t : ℝ => f (t - a)) s ↔
      LaplaceConvergent f s := by
  let g : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • f t
  let τ : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight a
  change Integrable (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) •
      (Ioi a).indicator (fun t : ℝ => f (t - a)) t) (volume.restrict (Ioi 0)) ↔
    Integrable g (volume.restrict (Ioi 0))
  rw [← Set.indicator_smul, integrable_indicator_iff measurableSet_Ioi, IntegrableOn]
  rw [Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_left.mpr ha,
    ← (show Measure.map τ (volume.restrict (Ioi 0)) = volume.restrict (Ioi a) by
      simpa [τ, preimage_add_const_Ioi] using
        map_add_right_restrict volume a (s := Ioi a) measurableSet_Ioi),
    integrable_map_equiv τ]
  rw [show ((fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f (t - a)) ∘ τ) =
      Complex.exp ((-s) * (a : ℂ)) • g by
    ext u
    simp only [Function.comp_apply, τ, MeasurableEquiv.coe_addRight, g, Pi.smul_apply,
      add_sub_cancel_right, ← mul_smul, ← Complex.exp_add,
      ← mul_add, ← Complex.ofReal_add, add_comm a u],
    integrable_smul_iff (Complex.exp_ne_zero _) g]

/-- Time-shift rule for the one-sided Laplace transform:
`ℒ(t ↦ f (t - a) 𝟙_{a < t})(s) = exp (-s * a) • ℒ(f)(s)`. -/
theorem laplace_indicator_comp_sub [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
    [SMulCommClass ℝ ℂ E] (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    laplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s =
      Complex.exp ((-s) * (a : ℂ)) • laplace f s := by
  letI : NormSMulClass ℂ E := NormedDivisionRing.toNormSMulClass
  let h : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • f (t - a)
  let τ : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight a
  calc
    laplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s
        = ∫ u : ℝ in Ioi 0, h (u + a) := by
          rw [laplace_eq_integral_Ioi, ← Set.indicator_smul,
            setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr ha,
            ← (show Measure.map τ (volume.restrict (Ioi 0)) = volume.restrict (Ioi a) by
              simpa [τ, preimage_add_const_Ioi] using
                map_add_right_restrict volume a (s := Ioi a) measurableSet_Ioi)]
          exact τ.measurableEmbedding.integral_map h
    _ = Complex.exp ((-s) * (a : ℂ)) • laplace f s := by
          rw [laplace_eq_integral_Ioi, ← integral_smul]
          refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
          simp only [h, add_sub_cancel_right, ← mul_smul, ← Complex.exp_add, ← mul_add,
            ← Complex.ofReal_add, add_comm a u]

theorem hasLaplace_indicator_comp_sub [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
    [SMulCommClass ℝ ℂ E] {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ}
    (ha : 0 ≤ a) (hf : HasLaplace f s m) :
    HasLaplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s
      (Complex.exp ((-s) * (a : ℂ)) • m) := by
  exact ⟨(LaplaceConvergent.indicator_comp_sub (f := f) (s := s) ha).2 hf.1, by
    rw [laplace_indicator_comp_sub f s ha, hf.2]⟩

end TimeShift

section RealScaling

variable [NormedAddCommGroup E]

/-- Compatibility of convergence of the one-sided Laplace transform with positive dilation of the
input. -/
theorem LaplaceConvergent.comp_mul_left [SMul ℂ E] {f : ℝ → E} {s : ℂ} {a : ℝ}
    (ha : 0 < a) :
    LaplaceConvergent (fun t : ℝ => f (a * t)) s ↔ LaplaceConvergent f (s / a) := by
  let g : ℝ → E := fun u => Complex.exp ((-(s / a)) * (u : ℂ)) • f u
  have h₁ : EqOn (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f (a * t))
      (fun t : ℝ => g (a * t)) (Ioi 0) := fun t ht => by
    dsimp [g]
    congr 1
    rw [ofReal_mul]
    field_simp [ha.ne']
  rw [laplaceConvergent_iff_integrableOn, laplaceConvergent_iff_integrableOn,
    integrableOn_congr_fun h₁ measurableSet_Ioi]
  simpa [g, mul_zero] using integrableOn_Ioi_comp_mul_left_iff g 0 ha

/-- Compatibility of convergence of the one-sided Laplace transform with positive dilation of the
input. -/
theorem LaplaceConvergent.comp_mul_right [SMul ℂ E] {f : ℝ → E} {s : ℂ} {a : ℝ}
    (ha : 0 < a) :
    LaplaceConvergent (fun t : ℝ => f (t * a)) s ↔ LaplaceConvergent f (s / a) := by
  simpa only [mul_comm] using LaplaceConvergent.comp_mul_left (f := f) (s := s) ha

/-- Compatibility of the one-sided Laplace transform with positive dilation of the input. -/
theorem laplace_comp_mul_left [NormedSpace ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    laplace (fun t : ℝ => f (a * t)) s = (a : ℂ)⁻¹ • laplace f (s / a) := by
  let g : ℝ → E := fun u => Complex.exp ((-(s / a)) * (u : ℂ)) • f u
  calc
    laplace (fun t : ℝ => f (a * t)) s = ∫ t : ℝ in Ioi 0, g (a * t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      dsimp [g, laplace]
      congr 1
      rw [ofReal_mul]
      field_simp [ha.ne']
    _ = (a : ℝ)⁻¹ • ∫ u : ℝ in Ioi 0, g u := by
      rw [integral_comp_mul_left_Ioi g 0 ha, mul_zero]
    _ = (a : ℂ)⁻¹ • laplace f (s / a) := by
      dsimp [g, laplace]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simp

/-- Compatibility of the one-sided Laplace transform with positive dilation of the input. -/
theorem laplace_comp_mul_right [NormedSpace ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    laplace (fun t : ℝ => f (t * a)) s = (a : ℂ)⁻¹ • laplace f (s / a) := by
  simpa only [mul_comm] using laplace_comp_mul_left f s ha

end RealScaling

section Values

section Const

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The Laplace transform of a constant vector. -/
theorem hasLaplace_const [CompleteSpace E] {s : ℂ} (hs : 0 < s.re) (c : E) :
    HasLaplace (fun _ : ℝ => c) s (s⁻¹ • c) := by
  have hscalar := integrableOn_exp_mul_complex_Ioi (a := -s)
    (by simpa using neg_lt_neg hs) 0
  refine ⟨hscalar.smul_const c, ?_⟩
  rw [laplace_eq_integral_Ioi]
  calc
    (∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ)) • c)
        = (∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ))) • c := by
          simpa using ((1 : ℂ →L[ℝ] ℂ).smulRight c).integral_comp_comm hscalar
    _ = s⁻¹ • c := by
          simpa using congrArg (fun z : ℂ => z • c)
            (integral_exp_mul_complex_Ioi (a := -s) (by simpa using neg_lt_neg hs) 0)

end Const

/-- The Laplace transform of the constant function `1`. -/
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ => (1 : ℂ)) s (1 / s) := by
  simpa [div_eq_mul_inv, smul_eq_mul] using hasLaplace_const hs (1 : ℂ)

/-- The Laplace transform of a complex exponential. -/
theorem hasLaplace_cexp {a s : ℂ} (h : a.re < s.re) :
    HasLaplace (fun t : ℝ => Complex.exp (a * (t : ℂ))) s (1 / (s - a)) := by
  have h1 := hasLaplace_one (s := s - a) (by simpa [sub_re] using sub_pos.mpr h)
  refine ⟨?_, ?_⟩
  · simpa [smul_eq_mul] using
      (LaplaceConvergent.cexp_smul (f := fun _ : ℝ => (1 : ℂ)) (s := s) (a := a)).2 h1.1
  · simpa [smul_eq_mul] using
      (laplace_cexp_smul (fun _ : ℝ => (1 : ℂ)) s a).trans h1.2

end Values

end
