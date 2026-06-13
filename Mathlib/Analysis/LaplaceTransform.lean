/-
Copyright (c) 2026 Daniel Dennis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Dennis
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convolution

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
* `laplace_differentiableAt_of_isBigO_exp`: holomorphy on a right half-plane for functions
  of exponential order.
* `laplace_ofReal_smul_eq_neg_deriv_of_isBigO_exp`: multiplication by `t` corresponds to
  negating the derivative with respect to the Laplace parameter.
* `laplace_intervalIntegral_zero`: the integration rule
  `ℒ(t ↦ ∫ x in 0..t, f x) s = s⁻¹ • ℒ(f) s`.
* `laplace_posConvolution`/`laplace_posConvolution_mul`: convolution theorems for the
  one-sided convolution.
* `laplace_deriv`: the derivative rule `ℒ(f') s = s • ℒ(f) s - f 0`.

## Design notes

As for `mellin`, the transform is a total function. If the integrand is not integrable, the
Bochner integral convention makes the value `0`; use `LaplaceConvergent` or `HasLaplace` to record
the meaningful cases.

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

theorem laplaceConvergent_iff_integrableOn (f : ℝ → E) (s : ℂ) :
    LaplaceConvergent f s ↔
      IntegrableOn (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t) (Ioi 0) :=
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

variable [NormedAddCommGroup E] [DistribSMul ℂ E]

theorem LaplaceConvergent.add {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (fun t => f t + g t) s μ := by
  exact (Integrable.add hf hg).congr <| ae_of_all _ fun _ => (smul_add _ _ _).symm

theorem LaplaceConvergent.sub {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (fun t => f t - g t) s μ := by
  exact (Integrable.sub hf hg).congr <| ae_of_all _ fun _ => (smul_sub _ _ _).symm

end Add

section HasLaplaceAdd

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [DistribSMul ℂ E]

theorem hasLaplace_add {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    HasLaplace (fun t => f t + g t) s (laplace f s μ + laplace g s μ) μ :=
  ⟨hf.add hg, by
    simpa only [laplace, smul_add] using integral_add hf hg⟩

theorem hasLaplace_sub {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    HasLaplace (fun t => f t - g t) s (laplace f s μ - laplace g s μ) μ :=
  ⟨hf.sub hg, by
    simpa only [laplace, smul_sub] using integral_sub hf hg⟩

theorem HasLaplace.add {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplace f s m μ) (hg : HasLaplace g s n μ) :
    HasLaplace (fun t => f t + g t) s (m + n) μ := by
  simpa [hf.2, hg.2] using hasLaplace_add hf.1 hg.1

theorem HasLaplace.sub {μ : Measure ℝ} {f g : ℝ → E} {s : ℂ} {m n : E}
    (hf : HasLaplace f s m μ) (hg : HasLaplace g s n μ) :
    HasLaplace (fun t => f t - g t) s (m - n) μ := by
  simpa [hf.2, hg.2] using hasLaplace_sub hf.1 hg.1

end HasLaplaceAdd

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
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
    exact (hfc.mono_set Ioi_subset_Ici_self).aestronglyMeasurable
  rw [laplaceConvergent_iff_norm hf_meas]
  change IntegrableOn (fun t : ℝ => Real.exp (-s.re * t) * ‖f t‖) (Ioi (0 : ℝ))
  obtain ⟨C, _hCpos, hC⟩ := hf_top.exists_pos
  obtain ⟨B, hB⟩ := (eventually_atTop.1 hC.bound)
  let c := max B 1
  have hc_pos : 0 < c :=
    lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have hc_subset : Ioi c ⊆ Ici (0 : ℝ) := fun t ht => le_of_lt (hc_pos.trans ht)
  have h_exp_cont : ContinuousOn (fun t : ℝ => Real.exp (-s.re * t)) (Ici (0 : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-s.re * t)).continuousOn
  have hlocal_mul : IntegrableOn (fun t : ℝ => ‖f t‖ * Real.exp (-s.re * t)) (Ioc 0 c) := by
    have hloc : LocallyIntegrableOn (fun t : ℝ => ‖f t‖ * Real.exp (-s.re * t)) (Ici 0) := by
      exact hfc.norm.mul_continuousOn h_exp_cont isClosed_Ici.isLocallyClosed
    have hIcc : IntegrableOn (fun t : ℝ => ‖f t‖ * Real.exp (-s.re * t)) (Icc 0 c) := by
      exact hloc.integrableOn_compact_subset (fun t ht => ht.1) isCompact_Icc
    exact hIcc.mono_set fun _ ht => ⟨le_of_lt ht.1, ht.2⟩
  have hlocal : IntegrableOn (fun t : ℝ => Real.exp (-s.re * t) * ‖f t‖) (Ioc 0 c) := by
    simpa [mul_comm] using hlocal_mul
  have htail_exp : IntegrableOn (fun t : ℝ => C * Real.exp ((a - s.re) * t)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (a := a - s.re) (sub_neg.mpr hs) c).const_mul C
  have htail_meas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-s.re * t) * ‖f t‖)
      (volume.restrict (Ioi c)) := by
    simpa [mul_comm] using
      ((hfc.norm.mono_set hc_subset).mul_continuousOn
        ((by fun_prop : Continuous fun t : ℝ => Real.exp (-s.re * t)).continuousOn)
        isOpen_Ioi.isLocallyClosed).aestronglyMeasurable
  have htail : IntegrableOn (fun t : ℝ => Real.exp (-s.re * t) * ‖f t‖) (Ioi c) := by
    refine Integrable.mono' htail_exp htail_meas ?_
    refine ae_restrict_iff' measurableSet_Ioi |>.mpr (Eventually.of_forall fun t ht => ?_)
    have htB : B ≤ t := (le_max_left B 1).trans (le_of_lt ht)
    have hf_bound : ‖f t‖ ≤ C * Real.exp (a * t) := by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hB t htB
    have hnonneg : 0 ≤ Real.exp (-s.re * t) * ‖f t‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    calc
      ‖Real.exp (-s.re * t) * ‖f t‖‖ = Real.exp (-s.re * t) * ‖f t‖ :=
        Real.norm_of_nonneg hnonneg
      _ ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) := by
        gcongr
      _ = C * Real.exp ((a - s.re) * t) := by
        calc
          Real.exp (-s.re * t) * (C * Real.exp (a * t))
              = C * (Real.exp (-s.re * t) * Real.exp (a * t)) := by ring
          _ = C * Real.exp ((a - s.re) * t) := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hdecomp : Ioi (0 : ℝ) = Ioc 0 c ∪ Ioi c := by
    rw [Ioc_union_Ioi (le_max_right (0 : ℝ) c), min_eq_left hc_pos.le]
  rw [hdecomp, integrableOn_union]
  exact ⟨hlocal, htail⟩

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
  have hkernel_meas : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp ((-s₀) * (t : ℂ)) • f t) μ :=
    hf.aestronglyMeasurable
  have hf_meas : AEStronglyMeasurable f μ := by
    have h : AEStronglyMeasurable
        (fun t : ℝ => Complex.exp (s₀ * (t : ℂ)) •
          (Complex.exp ((-s₀) * (t : ℂ)) • f t)) μ := by
      exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (s₀ * (t : ℂ)))
        |>.aestronglyMeasurable.smul hkernel_meas
    refine h.congr (ae_of_all _ fun t => ?_)
    dsimp only
    rw [smul_smul, ← Complex.exp_add]
    simp only [← add_mul, add_neg_cancel, zero_mul, Complex.exp_zero, one_smul]
  rw [laplaceConvergent_iff_norm hf_meas] at hf ⊢
  refine Integrable.mono' hf ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-s.re * t))
      |>.aestronglyMeasurable.mul hf_meas.norm
  · filter_upwards [hμ] with t ht_nonneg
    have hle_exp : Real.exp (-s.re * t) ≤ Real.exp (-s₀.re * t) := by
      exact Real.exp_le_exp.mpr (by nlinarith)
    have htarget_nonneg : 0 ≤ Real.exp (-s.re * t) * ‖f t‖ :=
      mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    calc
      ‖Real.exp (-s.re * t) * ‖f t‖‖ = Real.exp (-s.re * t) * ‖f t‖ :=
        Real.norm_of_nonneg htarget_nonneg
      _ ≤ Real.exp (-s₀.re * t) * ‖f t‖ := by
        gcongr

/-- Strict half-plane monotonicity of Laplace convergence for measures supported on the
nonnegative reals. -/
theorem LaplaceConvergent.of_re_lt_of_ae_nonneg {μ : Measure ℝ} {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀ μ) (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hs : s₀.re < s.re) :
    LaplaceConvergent f s μ :=
  hf.of_re_le_of_ae_nonneg hμ hs.le

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

/-- For the one-sided Laplace transform, convergence only depends on the real part of `s`. -/
theorem laplaceConvergent_congr_re {f : ℝ → E} {s₀ s : ℂ} (hs : s₀.re = s.re) :
    LaplaceConvergent f s₀ ↔ LaplaceConvergent f s :=
  ⟨fun hf => hf.of_re_le hs.le, fun hf => hf.of_re_le hs.ge⟩

/-- Transfer one-sided Laplace convergence between parameters with the same real part. -/
theorem LaplaceConvergent.congr_re {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re = s.re) : LaplaceConvergent f s :=
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

section LaplaceDiff

variable [NormedAddCommGroup E]

/-- Multiplying by the independent variable preserves exponential order, after increasing the
exponential rate. -/
theorem isBigO_ofReal_smul_of_isBigO_exp [Module ℂ E] [IsBoundedSMul ℂ E]
    {a b : ℝ} {f : ℝ → E} (hab : a < b)
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) :
    (fun t : ℝ => (t : ℂ) • f t) =O[atTop] fun t : ℝ => Real.exp (b * t) := by
  have ht : (fun t : ℝ => (t : ℂ)) =O[atTop] (fun t : ℝ => t) := by
    refine isBigO_iff.2 ⟨1, Eventually.of_forall fun t => ?_⟩
    simp [Real.norm_eq_abs]
  exact (ht.smul hf_top).trans <| by
    simpa [smul_eq_mul, Real.rpow_one, mul_comm] using
      (isLittleO_exp_mul_rpow_of_lt 1 hab).isBigO

/-- Derivative of the Laplace kernel with respect to the Laplace parameter. -/
theorem hasDerivAt_laplaceKernel_param (s : ℂ) (t : ℝ) :
    HasDerivAt (fun z : ℂ => Complex.exp ((-z) * (t : ℂ)))
      (-(t : ℂ) * Complex.exp ((-s) * (t : ℂ))) s := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id s).neg.const_mul (t : ℂ)).cexp)

/-- If `f` is locally integrable on `[0, ∞)` and has exponential order `a`, then the
Laplace transform is complex differentiable at every `s` with `a < s.re`. Its derivative is
`-ℒ(t • f)(s)`. -/
theorem laplace_hasDerivAt_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    LaplaceConvergent (fun t : ℝ => (t : ℂ) • f t) s ∧
      HasDerivAt (laplace f) (-laplace (fun t : ℝ => (t : ℂ) • f t) s) s := by
  let tf : ℝ → E := fun t => (t : ℂ) • f t
  have htf_loc : LocallyIntegrableOn tf (Ici (0 : ℝ)) := by
    refine LocallyIntegrableOn.continuousOn_smul isClosed_Ici.isLocallyClosed hfc ?_
    exact (by fun_prop : ContinuousOn (fun t : ℝ => (t : ℂ)) (Ici (0 : ℝ)))
  obtain ⟨b, hab, hbs⟩ := exists_between hs
  have htf_top : tf =O[atTop] fun t : ℝ => Real.exp (b * t) :=
    isBigO_ofReal_smul_of_isBigO_exp hab hf_top
  have htf_conv : LaplaceConvergent tf s :=
    laplaceConvergent_of_isBigO_exp htf_loc htf_top hbs
  refine ⟨htf_conv, ?_⟩
  set F : ℂ → ℝ → E := fun z t => Complex.exp ((-z) * (t : ℂ)) • f t
  set F' : ℂ → ℝ → E := fun z t => -(Complex.exp ((-z) * (t : ℂ)) • ((t : ℂ) • f t))
  obtain ⟨v, hv0, hvlt⟩ : ∃ v : ℝ, 0 < v ∧ v < s.re - b :=
    exists_between (sub_pos.mpr hbs)
  have hball_sub : b < (s - (v : ℂ)).re := by
    rw [sub_re, ofReal_re]
    linarith
  have hbound_conv : LaplaceConvergent tf (s - (v : ℂ)) :=
    laplaceConvergent_of_isBigO_exp htf_loc htf_top hball_sub
  have h1 : ∀ᶠ z : ℂ in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict <| Ioi 0) := by
    refine Eventually.of_forall fun z => ?_
    have hmeas_f : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
      AEStronglyMeasurable.mono_set Ioi_subset_Ici_self hfc.aestronglyMeasurable
    exact ((by fun_prop : Continuous fun t : ℝ => Complex.exp ((-z) * (t : ℂ)))
      |>.aestronglyMeasurable).smul hmeas_f
  have h2 : Integrable (F s) (volume.restrict <| Ioi (0 : ℝ)) := by
    simpa [F, LaplaceConvergent] using laplaceConvergent_of_isBigO_exp hfc hf_top hs
  have h3 : AEStronglyMeasurable (F' s) (volume.restrict <| Ioi (0 : ℝ)) := by
    have hmeas := htf_conv.aestronglyMeasurable.neg
    refine hmeas.congr (Eventually.of_forall fun t => ?_)
    rfl
  let bound : ℝ → ℝ := fun t => Real.exp (-(s.re - v) * t) * (t * ‖f t‖)
  have h4 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ z : ℂ, z ∈ Metric.ball s v → ‖F' z t‖ ≤ bound t := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    have hz_re : s.re - v ≤ z.re := by
      rw [mem_ball_iff_norm'] at hz
      have hz' := (re_le_norm (s - z)).trans hz.le
      rwa [sub_re, sub_le_iff_le_add, ← sub_le_iff_le_add'] at hz'
    have hexp_le : Real.exp (-z.re * t) ≤ Real.exp (-(s.re - v) * t) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right (neg_le_neg hz_re) (le_of_lt ht)
    have hnorm_eq : ‖F' z t‖ = Real.exp (-z.re * t) * (t * ‖f t‖) := by
      change ‖-(Complex.exp ((-z) * (t : ℂ)) • ((t : ℂ) • f t))‖ =
        Real.exp (-z.re * t) * (t * ‖f t‖)
      rw [norm_neg, norm_smul, norm_laplaceKernel, norm_smul, norm_real,
        Real.norm_of_nonneg ht.le]
    rw [hnorm_eq]
    exact mul_le_mul_of_nonneg_right hexp_le (mul_nonneg ht.le (norm_nonneg _))
  have h5 : Integrable bound (volume.restrict <| Ioi (0 : ℝ)) := by
    have hnorm := (laplaceConvergent_iff_norm (f := tf) (s := s - (v : ℂ))
      (AEStronglyMeasurable.mono_set Ioi_subset_Ici_self htf_loc.aestronglyMeasurable)).1
      hbound_conv
    refine hnorm.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [bound, tf, sub_re, ofReal_re, norm_smul, Real.norm_of_nonneg ht.le,
      mul_comm, mul_assoc]
  have h6 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ y : ℂ, y ∈ Metric.ball s v → HasDerivAt (fun z : ℂ => F z t) (F' y t) y := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t _ht y _hy => ?_
    have hker : HasDerivAt (fun z : ℂ => Complex.exp ((-z) * (t : ℂ)))
        (-(t : ℂ) * Complex.exp ((-y) * (t : ℂ))) y :=
      hasDerivAt_laplaceKernel_param y t
    convert hker.smul_const (f t) using 1
    change -(Complex.exp ((-y) * (t : ℂ)) • ((t : ℂ) • f t)) =
      ((-(t : ℂ)) * Complex.exp ((-y) * (t : ℂ))) • f t
    rw [smul_smul, ← neg_smul]
    congr 1
    ring
  have main := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hv0) h1 h2 h3 h4 h5 h6
  simpa [F, F', tf, laplace, integral_neg] using main.2

/-- If `f` is locally integrable on `[0, ∞)` and has exponential order `a`, then the derivative
of its Laplace transform is `-ℒ(t • f)(s)` for every `s` with `a < s.re`. -/
theorem hasDerivAt_laplace_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    HasDerivAt (laplace f) (-laplace (fun t : ℝ => (t : ℂ) • f t) s) s :=
  (laplace_hasDerivAt_of_isBigO_exp hfc hf_top hs).2

/-- Multiplication by the independent variable corresponds to negating the derivative with respect
to the Laplace parameter:
`d/ds ℒ(f)(s) = -ℒ(t • f)(s)`. -/
theorem deriv_laplace_eq_neg_laplace_ofReal_smul_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    deriv (laplace f) s = -laplace (fun t : ℝ => (t : ℂ) • f t) s :=
  (hasDerivAt_laplace_of_isBigO_exp hfc hf_top hs).deriv

/-- Multiplication by the independent variable corresponds to negating the derivative with respect
to the Laplace parameter:
`ℒ(t • f)(s) = - d/ds ℒ(f)(s)`. -/
theorem laplace_ofReal_smul_eq_neg_deriv_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    laplace (fun t : ℝ => (t : ℂ) • f t) s = -deriv (laplace f) s := by
  rw [deriv_laplace_eq_neg_laplace_ofReal_smul_of_isBigO_exp hfc hf_top hs]
  simp

/-- `HasLaplace` form of `laplace_ofReal_smul_eq_neg_deriv_of_isBigO_exp`. -/
theorem hasLaplace_ofReal_smul_eq_neg_deriv_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    HasLaplace (fun t : ℝ => (t : ℂ) • f t) s (-deriv (laplace f) s) := by
  exact ⟨(laplace_hasDerivAt_of_isBigO_exp hfc hf_top hs).1,
    laplace_ofReal_smul_eq_neg_deriv_of_isBigO_exp hfc hf_top hs⟩

/-- If `f` is locally integrable on `[0, ∞)` and has exponential order `a`, then the
Laplace transform is holomorphic at every `s` with `a < s.re`. -/
theorem laplace_differentiableAt_of_isBigO_exp {a : ℝ} {f : ℝ → E} {s : ℂ}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) (hs : a < s.re) :
    DifferentiableAt ℂ (laplace f) s :=
  (laplace_hasDerivAt_of_isBigO_exp hfc hf_top hs).2.differentiableAt

/-- If `f` is locally integrable on `[0, ∞)` and has exponential order `a`, then the
Laplace transform is holomorphic on the half-plane `a < s.re`. -/
theorem laplace_differentiableOn_of_isBigO_exp {a : ℝ} {f : ℝ → E}
    [NormedSpace ℂ E]
    (hfc : LocallyIntegrableOn f (Ici (0 : ℝ)))
    (hf_top : f =O[atTop] fun t : ℝ => Real.exp (a * t)) :
    DifferentiableOn ℂ (laplace f) {s : ℂ | a < s.re} := by
  intro s hs
  exact (laplace_differentiableAt_of_isBigO_exp hfc hf_top hs).differentiableWithinAt

end LaplaceDiff

section Shift

variable [NormedAddCommGroup E] [MulAction ℂ E]

theorem LaplaceConvergent.cexp_smul {μ : Measure ℝ} {f : ℝ → E} {s a : ℂ} :
    LaplaceConvergent (fun t : ℝ => Complex.exp (a * (t : ℂ)) • f t) s μ ↔
      LaplaceConvergent f (s - a) μ := by
  refine integrable_congr <| ae_of_all _ fun t => ?_
  dsimp only
  rw [← mul_smul, ← Complex.exp_add]
  congr 1
  ring_nf

end Shift

section TransformShift

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MulAction ℂ E]

/-- Multiplying the original function by an exponential translates the Laplace transform. -/
theorem laplace_cexp_smul (f : ℝ → E) (s a : ℂ)
    (μ : Measure ℝ := volume.restrict (Ioi 0)) :
    laplace (fun t : ℝ => Complex.exp (a * (t : ℂ)) • f t) s μ =
      laplace f (s - a) μ := by
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_smul, ← Complex.exp_add]
  congr 1
  ring_nf

end TransformShift

section TimeShift

private theorem map_add_right_volume_restrict_Ioi (a : ℝ) :
    Measure.map (fun t : ℝ => t + a) (volume.restrict (Ioi 0)) =
      volume.restrict (Ioi a) := by
  calc
    Measure.map (fun t : ℝ => t + a) (volume.restrict (Ioi 0))
        = (Measure.map (fun t : ℝ => t + a) volume).restrict (Ioi a) := by
          rw [Measure.restrict_map (by fun_prop : Measurable fun t : ℝ => t + a)
            measurableSet_Ioi]
          simp [preimage_add_const_Ioi]
    _ = volume.restrict (Ioi a) := by
          rw [map_add_right_eq_self volume a]

private theorem laplace_timeShift_integrand_comp {E : Type*} [MulAction ℂ E]
    (f : ℝ → E) (s : ℂ) (a u : ℝ) :
    Complex.exp ((-s) * (u + a : ℂ)) • f (u + a - a) =
      Complex.exp ((-s) * (a : ℂ)) • (Complex.exp ((-s) * (u : ℂ)) • f u) := by
  rw [add_sub_cancel_right, ← mul_smul, ← Complex.exp_add]
  congr 1
  ring_nf

section Convergence

variable [NormedAddCommGroup E] [MulActionWithZero ℂ E] [IsBoundedSMul ℂ E]

/-- Time-shift convergence rule for the one-sided Laplace transform.

For `0 ≤ a`, shifting a function to the right by `a` and cutting it off on `(a, ∞)` preserves
convergence of its Laplace transform. -/
theorem LaplaceConvergent.indicator_comp_sub {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 ≤ a) :
    LaplaceConvergent ((Ioi a).indicator fun t : ℝ => f (t - a)) s ↔
      LaplaceConvergent f s := by
  let h : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • f (t - a)
  let g : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • f t
  let c : ℂ := Complex.exp ((-s) * (a : ℂ))
  let τ : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight a
  have hmap : Measure.map τ (volume.restrict (Ioi 0)) = volume.restrict (Ioi a) := by
    simpa [τ] using map_add_right_volume_restrict_Ioi a
  rw [LaplaceConvergent]
  change Integrable (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) •
      (Ioi a).indicator (fun t : ℝ => f (t - a)) t) (volume.restrict (Ioi 0)) ↔
    Integrable g (volume.restrict (Ioi 0))
  rw [show (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) •
        (Ioi a).indicator (fun t : ℝ => f (t - a)) t) = (Ioi a).indicator h by
      funext t
      by_cases ht : t ∈ Ioi a <;> simp [h, ht]]
  rw [integrable_indicator_iff measurableSet_Ioi]
  change Integrable h ((volume.restrict (Ioi 0)).restrict (Ioi a)) ↔
    Integrable g (volume.restrict (Ioi 0))
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hinter : Ioi a ∩ Ioi (0 : ℝ) = Ioi a := by
    rw [Ioi_inter_Ioi, sup_eq_left.mpr ha]
  rw [hinter, ← hmap, τ.measurableEmbedding.integrable_map_iff]
  change Integrable (fun u : ℝ => h (u + a)) (volume.restrict (Ioi 0)) ↔
    Integrable g (volume.restrict (Ioi 0))
  have hcomp : (fun u : ℝ => h (u + a)) = fun u : ℝ => c • g u := by
    funext u
    simpa [h, g, c] using laplace_timeShift_integrand_comp f s a u
  rw [hcomp]
  exact integrable_smul_iff (Complex.exp_ne_zero _) g

end Convergence

section Transform

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
  [SMulCommClass ℝ ℂ E]

local instance : NormSMulClass ℂ E :=
  NormedDivisionRing.toNormSMulClass

/-- Time-shift rule for the one-sided Laplace transform:
`ℒ(t ↦ f (t - a) 𝟙_{a < t})(s) = exp (-s * a) • ℒ(f)(s)`. -/
theorem laplace_indicator_comp_sub (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 ≤ a) :
    laplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s =
      Complex.exp ((-s) * (a : ℂ)) • laplace f s := by
  let h : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • f (t - a)
  let g : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • f t
  let c : ℂ := Complex.exp ((-s) * (a : ℂ))
  let τ : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight a
  have hmap : Measure.map τ (volume.restrict (Ioi 0)) = volume.restrict (Ioi a) := by
    simpa [τ] using map_add_right_volume_restrict_Ioi a
  have hinter : Ioi (0 : ℝ) ∩ Ioi a = Ioi a := by
    rw [Ioi_inter_Ioi, sup_eq_right.mpr ha]
  have hcomp : (fun u : ℝ => h (u + a)) = fun u : ℝ => c • g u := by
    funext u
    simpa [h, g, c] using laplace_timeShift_integrand_comp f s a u
  calc
    laplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s
        = ∫ t : ℝ in Ioi 0, (Ioi a).indicator h t := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          by_cases hta : t ∈ Ioi a <;> simp [h, hta]
    _ = ∫ t : ℝ in Ioi a, h t := by
          rw [setIntegral_indicator measurableSet_Ioi, hinter]
    _ = ∫ u : ℝ in Ioi 0, h (u + a) := by
          rw [← hmap]
          exact τ.measurableEmbedding.integral_map h
    _ = ∫ u : ℝ in Ioi 0, c • g u := by
          rw [hcomp]
    _ = c • ∫ u : ℝ in Ioi 0, g u := by
          rw [integral_smul]
    _ = Complex.exp ((-s) * (a : ℂ)) • laplace f s := rfl

theorem hasLaplace_indicator_comp_sub {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ}
    (ha : 0 ≤ a) (hf : HasLaplace f s m) :
    HasLaplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s
      (Complex.exp ((-s) * (a : ℂ)) • m) := by
  exact ⟨(LaplaceConvergent.indicator_comp_sub (f := f) (s := s) ha).2 hf.1, by
    rw [laplace_indicator_comp_sub f s ha, hf.2]⟩

theorem HasLaplace.indicator_comp_sub {f : ℝ → E} {s : ℂ} {m : E} {a : ℝ}
    (hf : HasLaplace f s m) (ha : 0 ≤ a) :
    HasLaplace ((Ioi a).indicator fun t : ℝ => f (t - a)) s
      (Complex.exp ((-s) * (a : ℂ)) • m) :=
  hasLaplace_indicator_comp_sub ha hf

end Transform

end TimeShift

section RealScaling

variable [NormedAddCommGroup E] [SMul ℂ E]

/-- Compatibility of convergence of the one-sided Laplace transform with positive dilation of the
input. -/
theorem LaplaceConvergent.comp_mul_left {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
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
theorem LaplaceConvergent.comp_mul_right {f : ℝ → E} {s : ℂ} {a : ℝ} (ha : 0 < a) :
    LaplaceConvergent (fun t : ℝ => f (t * a)) s ↔ LaplaceConvergent f (s / a) := by
  simpa only [mul_comm] using LaplaceConvergent.comp_mul_left (f := f) (s := s) ha

end RealScaling

section RealScalingTransform

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]

/-- Compatibility of the one-sided Laplace transform with positive dilation of the input. -/
theorem laplace_comp_mul_left (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    laplace (fun t : ℝ => f (a * t)) s = (a : ℂ)⁻¹ • laplace f (s / a) := by
  let g : ℝ → E := fun u => Complex.exp ((-(s / a)) * (u : ℂ)) • f u
  have h₁ : laplace (fun t : ℝ => f (a * t)) s = ∫ t : ℝ in Ioi 0, g (a * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    dsimp [g, laplace]
    congr 1
    rw [ofReal_mul]
    field_simp [ha.ne']
  rw [h₁, integral_comp_mul_left_Ioi g 0 ha, mul_zero]
  dsimp [g, laplace]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp

/-- Compatibility of the one-sided Laplace transform with positive dilation of the input. -/
theorem laplace_comp_mul_right (f : ℝ → E) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    laplace (fun t : ℝ => f (t * a)) s = (a : ℂ)⁻¹ • laplace f (s / a) := by
  simpa only [mul_comm] using laplace_comp_mul_left f s ha

end RealScalingTransform

section PosConvolution

variable {E₁ E₂ F : Type*}
variable [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
variable [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem laplace_posConvolution_integrand (B : E₁ →L[ℂ] E₂ →L[ℂ] F)
    (f : ℝ → E₁) (g : ℝ → E₂) (s : ℂ) {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    Complex.exp ((-s) * (x : ℂ)) •
        (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) x =
      (MeasureTheory.posConvolution
        (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
        (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • g t)
        (B.bilinearRestrictScalars ℝ)) x := by
  simp only [MeasureTheory.posConvolution, indicator_of_mem hx,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply]
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hxexp : Complex.exp ((-s) * (x : ℂ)) =
      Complex.exp ((-s) * (t : ℂ)) * Complex.exp ((-s) * ((x - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hxexp]
  simp [smul_smul, mul_comm]

/-- Convergence of the one-sided convolution under a complex bilinear map.

If the Laplace transforms of `f` and `g` converge at `s`, then the Laplace transform of their
forward convolution through `B` converges at `s`. The convolution is formed with
`B.bilinearRestrictScalars ℝ`, since `MeasureTheory.posConvolution` is stated for real bilinear
maps. -/
theorem LaplaceConvergent.posConvolution {f : ℝ → E₁} {g : ℝ → E₂} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s)
    (B : E₁ →L[ℂ] E₂ →L[ℂ] F) :
    LaplaceConvergent (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) s := by
  let F₁ : ℝ → E₁ := fun t => Complex.exp ((-s) * (t : ℂ)) • f t
  let F₂ : ℝ → E₂ := fun t => Complex.exp ((-s) * (t : ℂ)) • g t
  have hF₁ : IntegrableOn F₁ (Ioi (0 : ℝ)) := by
    simpa [F₁] using (laplaceConvergent_iff_integrableOn f s).1 hf
  have hF₂ : IntegrableOn F₂ (Ioi (0 : ℝ)) := by
    simpa [F₂] using (laplaceConvergent_iff_integrableOn g s).1 hg
  have hconv_int : Integrable (MeasureTheory.posConvolution F₁ F₂
      (B.bilinearRestrictScalars ℝ)) volume :=
    MeasureTheory.integrable_posConvolution hF₁ hF₂ (B.bilinearRestrictScalars ℝ)
  rw [laplaceConvergent_iff_integrableOn]
  refine hconv_int.integrableOn.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simpa [F₁, F₂] using (laplace_posConvolution_integrand B f g s hx).symm

variable [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace F]

/-- The convolution theorem for the one-sided Laplace transform, complex bilinear version.

For `B : E₁ →L[ℂ] E₂ →L[ℂ] F`, the Laplace transform of the forward convolution through
`B.bilinearRestrictScalars ℝ` is `B (ℒ f s) (ℒ g s)`. -/
theorem laplace_posConvolution {f : ℝ → E₁} {g : ℝ → E₂} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s)
    (B : E₁ →L[ℂ] E₂ →L[ℂ] F) :
    laplace (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) s =
      B (laplace f s) (laplace g s) := by
  let F₁ : ℝ → E₁ := fun t => Complex.exp ((-s) * (t : ℂ)) • f t
  let F₂ : ℝ → E₂ := fun t => Complex.exp ((-s) * (t : ℂ)) • g t
  have hF₁ : IntegrableOn F₁ (Ioi (0 : ℝ)) := by
    simpa [F₁] using (laplaceConvergent_iff_integrableOn f s).1 hf
  have hF₂ : IntegrableOn F₂ (Ioi (0 : ℝ)) := by
    simpa [F₂] using (laplaceConvergent_iff_integrableOn g s).1 hg
  have hconv := MeasureTheory.integral_posConvolution (μ := volume) (ν := volume)
    hF₁ hF₂ (B.bilinearRestrictScalars ℝ)
  have hleft : laplace (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) s =
      ∫ x : ℝ in Ioi 0, ∫ t in 0..x, B (F₁ t) (F₂ (x - t)) := by
    rw [laplace_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [laplace_posConvolution_integrand B f g s hx]
    simp [MeasureTheory.posConvolution, F₁, F₂, hx]
  calc
    laplace (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) s
        = ∫ x : ℝ in Ioi 0, ∫ t in 0..x, B (F₁ t) (F₂ (x - t)) := hleft
    _ = (B.bilinearRestrictScalars ℝ) (∫ x : ℝ in Ioi 0, F₁ x)
        (∫ x : ℝ in Ioi 0, F₂ x) := hconv
    _ = B (laplace f s) (laplace g s) := by
        simp [F₁, F₂, laplace]

/-- `HasLaplace` form of `laplace_posConvolution`. -/
theorem hasLaplace_posConvolution {f : ℝ → E₁} {g : ℝ → E₂} {s : ℂ}
    {m : E₁} {n : E₂} (hf : HasLaplace f s m) (hg : HasLaplace g s n)
    (B : E₁ →L[ℂ] E₂ →L[ℂ] F) :
    HasLaplace (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) s (B m n) := by
  exact ⟨hf.1.posConvolution hg.1 B, by
    rw [laplace_posConvolution hf.1 hg.1 B, hf.2, hg.2]⟩

/-- `HasLaplace` method form of `hasLaplace_posConvolution`. -/
theorem HasLaplace.posConvolution {f : ℝ → E₁} {g : ℝ → E₂} {s : ℂ}
    {m : E₁} {n : E₂} (hf : HasLaplace f s m) (hg : HasLaplace g s n)
    (B : E₁ →L[ℂ] E₂ →L[ℂ] F) :
    HasLaplace (MeasureTheory.posConvolution f g (B.bilinearRestrictScalars ℝ)) s (B m n) :=
  hasLaplace_posConvolution hf hg B

end PosConvolution

section PosConvolutionLsmul

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
  [IsScalarTower ℝ ℂ E] [SMulCommClass ℝ ℂ E]

local instance : NormSMulClass ℂ E :=
  NormedDivisionRing.toNormSMulClass

private theorem laplace_posConvolution_lsmul_integrand (f : ℝ → ℂ) (g : ℝ → E) (s : ℂ)
    {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    Complex.exp ((-s) * (x : ℂ)) •
        (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) x =
      (MeasureTheory.posConvolution
        (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) * f t)
        (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • g t)
        (ContinuousLinearMap.lsmul ℝ ℂ)) x := by
  simp only [MeasureTheory.posConvolution, indicator_of_mem hx,
    ContinuousLinearMap.lsmul_apply]
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hxexp : Complex.exp ((-s) * (x : ℂ)) =
      Complex.exp ((-s) * (t : ℂ)) * Complex.exp ((-s) * ((x - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hxexp]
  simp [smul_smul, mul_assoc, mul_comm]

/-- Convergence of the one-sided convolution under scalar multiplication.

If the Laplace transforms of `f : ℝ → ℂ` and `g : ℝ → E` converge at `s`, then the
Laplace transform of their forward convolution converges at `s`. -/
theorem LaplaceConvergent.posConvolution_lsmul {f : ℝ → ℂ} {g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    LaplaceConvergent (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) s := by
  let F : ℝ → ℂ := fun t => Complex.exp ((-s) * (t : ℂ)) * f t
  let G : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • g t
  have hF : IntegrableOn F (Ioi (0 : ℝ)) := by
    simpa [F, smul_eq_mul] using (laplaceConvergent_iff_integrableOn f s).1 hf
  have hG : IntegrableOn G (Ioi (0 : ℝ)) := by
    simpa [G] using (laplaceConvergent_iff_integrableOn g s).1 hg
  have hconv_int : Integrable (MeasureTheory.posConvolution F G
      (ContinuousLinearMap.lsmul ℝ ℂ (E := E))) volume :=
    MeasureTheory.integrable_posConvolution hF hG (ContinuousLinearMap.lsmul ℝ ℂ (E := E))
  rw [laplaceConvergent_iff_integrableOn]
  refine hconv_int.integrableOn.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simpa [F, G] using (laplace_posConvolution_lsmul_integrand (E := E) f g s hx).symm

variable [CompleteSpace E]

/-- The convolution theorem for the one-sided Laplace transform, scalar-multiplication version.

For `f : ℝ → ℂ` and `g : ℝ → E`, the Laplace transform of the forward convolution is
`ℒ(f)(s) • ℒ(g)(s)`. This uses `MeasureTheory.posConvolution`, i.e. the one-sided convolution
`x ↦ 𝟙_{0 < x} ∫ t in 0..x, f t • g (x - t)`. -/
theorem laplace_posConvolution_lsmul {f : ℝ → ℂ} {g : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) s =
      laplace f s • laplace g s := by
  let F : ℝ → ℂ := fun t => Complex.exp ((-s) * (t : ℂ)) * f t
  let G : ℝ → E := fun t => Complex.exp ((-s) * (t : ℂ)) • g t
  have hF : IntegrableOn F (Ioi (0 : ℝ)) := by
    simpa [F, smul_eq_mul] using (laplaceConvergent_iff_integrableOn f s).1 hf
  have hG : IntegrableOn G (Ioi (0 : ℝ)) := by
    simpa [G] using (laplaceConvergent_iff_integrableOn g s).1 hg
  have hconv := MeasureTheory.integral_posConvolution (μ := volume) (ν := volume)
    hF hG (ContinuousLinearMap.lsmul ℝ ℂ (E := E))
  have hleft : laplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) s =
      ∫ x : ℝ in Ioi 0, ∫ t in 0..x, ContinuousLinearMap.lsmul ℝ ℂ (F t) (G (x - t)) := by
    rw [laplace_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [laplace_posConvolution_lsmul_integrand (E := E) f g s hx]
    simp [MeasureTheory.posConvolution, F, G, hx]
  calc
    laplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) s
        = ∫ x : ℝ in Ioi 0, ∫ t in 0..x,
            ContinuousLinearMap.lsmul ℝ ℂ (F t) (G (x - t)) := hleft
    _ = ContinuousLinearMap.lsmul ℝ ℂ (∫ x : ℝ in Ioi 0, F x)
        (∫ x : ℝ in Ioi 0, G x) := hconv
    _ = laplace f s • laplace g s := by
        simp [F, G, laplace, smul_eq_mul]

/-- `HasLaplace` form of `laplace_posConvolution_lsmul`. -/
theorem hasLaplace_posConvolution_lsmul {f : ℝ → ℂ} {g : ℝ → E} {s m : ℂ} {n : E}
    (hf : HasLaplace f s m) (hg : HasLaplace g s n) :
    HasLaplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) s
      (m • n) := by
  exact ⟨hf.1.posConvolution_lsmul hg.1, by
    rw [laplace_posConvolution_lsmul hf.1 hg.1, hf.2, hg.2]⟩

/-- `HasLaplace` method form of `hasLaplace_posConvolution_lsmul`. -/
theorem HasLaplace.posConvolution_lsmul {f : ℝ → ℂ} {g : ℝ → E} {s m : ℂ} {n : E}
    (hf : HasLaplace f s m) (hg : HasLaplace g s n) :
    HasLaplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.lsmul ℝ ℂ)) s (m • n) :=
  hasLaplace_posConvolution_lsmul hf hg

end PosConvolutionLsmul

section PosConvolutionMul

/-- Convergence of the one-sided convolution under multiplication. -/
theorem LaplaceConvergent.posConvolution_mul {f g : ℝ → ℂ} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    LaplaceConvergent (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℂ)) s := by
  simpa [MeasureTheory.posConvolution, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (LaplaceConvergent.posConvolution_lsmul (E := ℂ) hf hg)

/-- The convolution theorem for the one-sided Laplace transform, complex multiplication version.

For complex-valued functions, the Laplace transform of the forward convolution is the product of
the individual Laplace transforms. -/
theorem laplace_posConvolution_mul {f g : ℝ → ℂ} {s : ℂ}
    (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℂ)) s =
      laplace f s * laplace g s := by
  simpa [MeasureTheory.posConvolution, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (laplace_posConvolution_lsmul (E := ℂ) hf hg)

/-- `HasLaplace` form of `laplace_posConvolution_mul`. -/
theorem hasLaplace_posConvolution_mul {f g : ℝ → ℂ} {s m n : ℂ}
    (hf : HasLaplace f s m) (hg : HasLaplace g s n) :
    HasLaplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℂ)) s (m * n) := by
  simpa [MeasureTheory.posConvolution, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    (hasLaplace_posConvolution_lsmul (E := ℂ) hf hg)

/-- `HasLaplace` method form of `hasLaplace_posConvolution_mul`. -/
theorem HasLaplace.posConvolution_mul {f g : ℝ → ℂ} {s m n : ℂ}
    (hf : HasLaplace f s m) (hg : HasLaplace g s n) :
    HasLaplace (MeasureTheory.posConvolution f g (ContinuousLinearMap.mul ℝ ℂ)) s (m * n) :=
  hasLaplace_posConvolution_mul hf hg

end PosConvolutionMul

section Deriv

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
  [SMulCommClass ℝ ℂ E] [CompleteSpace E]

local instance : NormSMulClass ℂ E :=
  NormedDivisionRing.toNormSMulClass

/-- The derivative of the Laplace kernel. -/
theorem hasDerivAt_laplaceKernel (s : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp ((-s) * (u : ℂ)))
      ((-s) * Complex.exp ((-s) * (t : ℂ))) t := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (((ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp)

/-- The derivative rule for the Laplace transform with an explicit right-boundary value at `0`.

If `exp (-s t) • f t` tends to `m` as `t → 0+` and tends to `0` at `∞`, then
`ℒ(f') s = s • ℒ(f) s - m`. See `laplace_deriv` for the common version where `m = f 0`
follows from differentiability at `0`. -/
theorem laplace_deriv_of_tendsto {f f' : ℝ → E} {s : ℂ} {m : E}
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : LaplaceConvergent f s) (hf' : LaplaceConvergent f' s)
    (h_zero : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      (𝓝[>] (0 : ℝ)) (𝓝 m))
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    laplace f' s = s • laplace f s - m := by
  let u : ℝ → ℂ := fun t => Complex.exp ((-s) * (t : ℂ))
  let g : ℝ → E := u • f
  let sf : ℝ → E := s • fun t => u t • f t
  let nsf : ℝ → E := -sf
  let df : ℝ → E := fun t => u t • f' t
  let g' : ℝ → E := df + nsf
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u ((-s) * u t) t := by
    intro t ht
    simpa [u] using hasDerivAt_laplaceKernel s t
  have hgderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (g' t) t := by
    intro t ht
    simpa [g, g', df, nsf, sf, smul_smul, neg_smul, mul_comm, mul_left_comm, mul_assoc]
      using (hu t ht).smul (hderiv t ht)
  have hf_int : IntegrableOn (fun t : ℝ => u t • f t) (Ioi 0) := by
    simpa [u] using (laplaceConvergent_iff_integrableOn f s).1 hf
  have hnsf : IntegrableOn nsf (Ioi 0) := (hf_int.smul s).neg
  have hdf : IntegrableOn df (Ioi 0) := by
    simpa [df, u] using (laplaceConvergent_iff_integrableOn f' s).1 hf'
  have hg'int : IntegrableOn g' (Ioi 0) := by
    simpa [g'] using hdf.add hnsf
  rw [← Ici_sdiff_left] at h_zero
  have h_zero_g : Tendsto g (𝓝[Ici 0 \ {0}] (0 : ℝ)) (𝓝 m) := by
    apply h_zero.congr'
    filter_upwards with t
    simp [g, u]
  let G : ℝ → E := Function.update g 0 m
  have hGcont : ContinuousWithinAt G (Ici 0) 0 :=
    continuousWithinAt_update_same.mpr h_zero_g
  have hGderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt G (g' t) t := by
    intro t ht
    apply (hgderiv t ht).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht.ne'] with y hy
    exact Function.update_of_ne hy m g
  have h_infty_g : Tendsto g atTop (𝓝 0) := by
    apply h_infty.congr'
    filter_upwards with t
    simp [g, u]
  have hGtop : Tendsto G atTop (𝓝 0) := by
    apply h_infty_g.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    exact (Function.update_of_ne hx m g).symm
  have hftc : ∫ t : ℝ in Ioi 0, g' t = (0 : E) - m := by
    simpa [G] using
      integral_Ioi_of_hasDerivAt_of_tendsto hGcont hGderiv hg'int hGtop
  have hsum : (∫ t : ℝ in Ioi 0, df t) + ∫ t : ℝ in Ioi 0, nsf t = -m := by
    calc
      (∫ t : ℝ in Ioi 0, df t) + ∫ t : ℝ in Ioi 0, nsf t
          = ∫ t : ℝ in Ioi 0, g' t := by
            simpa [g'] using (integral_add hdf hnsf).symm
      _ = -m := by simpa using hftc
  have hmain : laplace f' s + -(s • laplace f s) = -m := by
    simpa [laplace, u, df, nsf, sf, integral_smul, integral_neg] using hsum
  calc
    laplace f' s
        = (laplace f' s + -(s • laplace f s)) + s • laplace f s := by
          abel
    _ = -m + s • laplace f s := by rw [hmain]
    _ = s • laplace f s - m := by abel

/-- The derivative rule for the Laplace transform:
`ℒ(f') s = s • ℒ(f) s - f 0`.

The function only needs to be continuous from the right at `0` and differentiable on `(0, ∞)`.
The boundary condition at infinity is stated explicitly as `exp (-s t) • f t → 0`; convergence
of the two Laplace integrals supplies the integrability needed for integration by parts. -/
theorem laplace_deriv {f f' : ℝ → E} {s : ℂ}
    (hcont : ContinuousWithinAt f (Ici (0 : ℝ)) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : LaplaceConvergent f s) (hf' : LaplaceConvergent f' s)
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    laplace f' s = s • laplace f s - f 0 := by
  refine laplace_deriv_of_tendsto hderiv hf hf' ?_ h_infty
  simpa using ((by fun_prop : ContinuousAt
    (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) 0)
      |>.tendsto.mono_left nhdsWithin_le_nhds).smul
        (continuousWithinAt_Ioi_iff_Ici.mpr hcont)

/-- A convenience version of `laplace_deriv` where differentiability is assumed on `[0, ∞)`. -/
theorem laplace_deriv' {f f' : ℝ → E} {s : ℂ}
    (hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : LaplaceConvergent f s) (hf' : LaplaceConvergent f' s)
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    laplace f' s = s • laplace f s - f 0 :=
  laplace_deriv ((hderiv 0 (by simp)).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (le_of_lt (mem_Ioi.mp ht))) hf hf' h_infty

theorem hasLaplace_deriv_of_tendsto {f f' : ℝ → E} {s : ℂ} {m m₀ : E}
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s m) (hf' : LaplaceConvergent f' s)
    (h_zero : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    HasLaplace f' s (s • m - m₀) :=
  ⟨hf', by rw [laplace_deriv_of_tendsto hderiv hf.1 hf' h_zero h_infty, hf.2]⟩

theorem HasLaplace.deriv_of_tendsto {f f' : ℝ → E} {s : ℂ} {m m₀ : E}
    (hf : HasLaplace f s m)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf' : LaplaceConvergent f' s)
    (h_zero : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    HasLaplace f' s (s • m - m₀) :=
  hasLaplace_deriv_of_tendsto hderiv hf hf' h_zero h_infty

theorem hasLaplace_deriv {f f' : ℝ → E} {s : ℂ} {m : E}
    (hcont : ContinuousWithinAt f (Ici (0 : ℝ)) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s m) (hf' : LaplaceConvergent f' s)
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    HasLaplace f' s (s • m - f 0) :=
  ⟨hf', by rw [laplace_deriv hcont hderiv hf.1 hf' h_infty, hf.2]⟩

theorem HasLaplace.deriv {f f' : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m)
    (hcont : ContinuousWithinAt f (Ici (0 : ℝ)) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf' : LaplaceConvergent f' s)
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    HasLaplace f' s (s • m - f 0) :=
  hasLaplace_deriv hcont hderiv hf hf' h_infty

theorem hasLaplace_deriv' {f f' : ℝ → E} {s : ℂ} {m : E}
    (hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s m) (hf' : LaplaceConvergent f' s)
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    HasLaplace f' s (s • m - f 0) :=
  ⟨hf', by rw [laplace_deriv' hderiv hf.1 hf' h_infty, hf.2]⟩

theorem HasLaplace.deriv' {f f' : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m)
    (hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt f (f' t) t)
    (hf' : LaplaceConvergent f' s)
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • f t)
      atTop (𝓝 0)) :
    HasLaplace f' s (s • m - f 0) :=
  hasLaplace_deriv' hderiv hf hf' h_infty

/-- Integration rule for the Laplace transform, stated for an antiderivative.

If `F' = f`, the lower boundary term of `exp (-s t) • F t` at `0+` is zero, and the upper
boundary term at infinity is zero, then `ℒ(F) s = s⁻¹ • ℒ(f) s`. -/
theorem laplace_antideriv_of_tendsto {F f : ℝ → E} {s : ℂ} (hs : s ≠ 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (f t) t)
    (hF : LaplaceConvergent F s) (hf : LaplaceConvergent f s)
    (h_zero : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • F t)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • F t)
      atTop (𝓝 0)) :
    laplace F s = s⁻¹ • laplace f s := by
  have h := laplace_deriv_of_tendsto hderiv hF hf h_zero h_infty
  have h' : laplace f s = s • laplace F s := by simpa using h
  rw [h', smul_smul]
  simp [hs]

theorem hasLaplace_antideriv_of_tendsto {F f : ℝ → E} {s : ℂ} {m : E} (hs : s ≠ 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (f t) t)
    (hF : LaplaceConvergent F s) (hf : HasLaplace f s m)
    (h_zero : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • F t)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h_infty : Tendsto (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • F t)
      atTop (𝓝 0)) :
    HasLaplace F s (s⁻¹ • m) :=
  ⟨hF, by rw [laplace_antideriv_of_tendsto hs hderiv hF hf.1 h_zero h_infty, hf.2]⟩

/-- Integration rule for the one-sided Laplace transform:
`ℒ(t ↦ ∫ x in 0..t, f x) s = s⁻¹ • ℒ(f) s`.

The hypotheses follow the derivative-rule style in this file: convergence and the boundary term at
infinity are explicit, and the zero boundary term at `0+` is stated as a limit. -/
theorem laplace_intervalIntegral_zero_of_tendsto {f : ℝ → E} {s : ℂ} (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : LaplaceConvergent f s)
    (h_zero : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    laplace (fun t : ℝ => ∫ x in 0..t, f x) s = s⁻¹ • laplace f s := by
  refine laplace_antideriv_of_tendsto hs ?_ hF hf h_zero h_infty
  intro t ht
  exact intervalIntegral.integral_hasDerivAt_right (hfi t ht)
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi t ht)
    (hcont.continuousAt (isOpen_Ioi.mem_nhds ht))

theorem hasLaplace_intervalIntegral_zero_of_tendsto {f : ℝ → E} {s : ℂ} {m : E}
    (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : HasLaplace f s m)
    (h_zero : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (s⁻¹ • m) :=
  ⟨hF, by
    rw [laplace_intervalIntegral_zero_of_tendsto hs hfi hcont hF hf.1 h_zero h_infty, hf.2]⟩

theorem HasLaplace.intervalIntegral_zero_of_tendsto {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m) (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (h_zero : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (s⁻¹ • m) :=
  hasLaplace_intervalIntegral_zero_of_tendsto hs hfi hcont hF hf h_zero h_infty

/-- Integration rule for the one-sided Laplace transform:
`ℒ(t ↦ ∫ x in 0..t, f x) s = s⁻¹ • ℒ(f) s`.

This version derives the lower boundary term at `0+` from interval integrability near `0`.
Convergence of the Laplace transform of the primitive, and the boundary term at infinity, are kept
explicit. -/
theorem laplace_intervalIntegral_zero {f : ℝ → E} {s : ℂ} (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : LaplaceConvergent f s)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    laplace (fun t : ℝ => ∫ x in 0..t, f x) s = s⁻¹ • laplace f s := by
  refine laplace_intervalIntegral_zero_of_tendsto hs hfi hcont hF hf ?_ h_infty
  let F : ℝ → E := fun t => ∫ x in 0..t, f x
  have hF_cont_right : ContinuousWithinAt F (Ioi (0 : ℝ)) 0 := by
    have h_int : IntervalIntegrable f volume (min (0 : ℝ) 0) (max (0 : ℝ) (1 : ℝ)) := by
      simpa only [min_self, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using
        hfi (1 : ℝ) (show (1 : ℝ) ∈ Ioi 0 by exact (zero_lt_one : (0 : ℝ) < 1))
    have hFcontIcc : ContinuousWithinAt F (Icc (0 : ℝ) (1 : ℝ)) 0 := by
      simpa [F] using intervalIntegral.continuousWithinAt_primitive (a := (0 : ℝ))
        (b₀ := (0 : ℝ)) (b₁ := (0 : ℝ)) (b₂ := (1 : ℝ)) (f := f) (μ := volume)
        (by simp) h_int
    change Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 (F 0))
    rw [← nhdsWithin_inter_of_mem (t := Ioi (0 : ℝ))
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one))]
    exact hFcontIcc.mono fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩
  have hF_tendsto : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [ContinuousWithinAt, F] using hF_cont_right
  simpa [F] using ((by fun_prop : ContinuousAt
    (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) 0)
      |>.tendsto.mono_left nhdsWithin_le_nhds).smul hF_tendsto

theorem hasLaplace_intervalIntegral_zero {f : ℝ → E} {s : ℂ} {m : E} (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : HasLaplace f s m)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (s⁻¹ • m) :=
  ⟨hF, by rw [laplace_intervalIntegral_zero hs hfi hcont hF hf.1 h_infty, hf.2]⟩

theorem HasLaplace.intervalIntegral_zero {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m) (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (s⁻¹ • m) :=
  hasLaplace_intervalIntegral_zero hs hfi hcont hF hf h_infty

/-- Convenience version of `laplace_intervalIntegral_zero` for a continuous function on
`[0, ∞)`. -/
theorem laplace_intervalIntegral_zero_of_continuousOn {f : ℝ → E} {s : ℂ} (hs : s ≠ 0)
    (hcont : ContinuousOn f (Ici (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : LaplaceConvergent f s)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    laplace (fun t : ℝ => ∫ x in 0..t, f x) s = s⁻¹ • laplace f s := by
  have hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t := by
    intro t ht
    exact (hcont.mono (by rw [uIcc_of_le ht.le]; exact Icc_subset_Ici_self)).intervalIntegrable
  exact laplace_intervalIntegral_zero hs hfi (hcont.mono Ioi_subset_Ici_self) hF hf h_infty

theorem hasLaplace_intervalIntegral_zero_of_continuousOn {f : ℝ → E} {s : ℂ} {m : E}
    (hs : s ≠ 0)
    (hcont : ContinuousOn f (Ici (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : HasLaplace f s m)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (s⁻¹ • m) :=
  ⟨hF, by rw [laplace_intervalIntegral_zero_of_continuousOn hs hcont hF hf.1 h_infty, hf.2]⟩

theorem HasLaplace.intervalIntegral_zero_of_continuousOn {f : ℝ → E} {s : ℂ} {m : E}
    (hf : HasLaplace f s m) (hs : s ≠ 0) (hcont : ContinuousOn f (Ici (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (s⁻¹ • m) :=
  hasLaplace_intervalIntegral_zero_of_continuousOn hs hcont hF hf h_infty

/-- Complex-valued form of the integration rule, using division by the Laplace parameter. -/
theorem laplace_intervalIntegral_zero_eq_div {f : ℝ → ℂ} {s : ℂ} (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : LaplaceConvergent f s)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    laplace (fun t : ℝ => ∫ x in 0..t, f x) s = laplace f s / s := by
  rw [laplace_intervalIntegral_zero hs hfi hcont hF hf h_infty]
  simp [div_eq_mul_inv, smul_eq_mul, mul_comm]

theorem hasLaplace_intervalIntegral_zero_div {f : ℝ → ℂ} {s m : ℂ} (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (hf : HasLaplace f s m)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (m / s) := by
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using
    hasLaplace_intervalIntegral_zero hs hfi hcont hF hf h_infty

theorem HasLaplace.intervalIntegral_zero_div {f : ℝ → ℂ} {s m : ℂ}
    (hf : HasLaplace f s m) (hs : s ≠ 0)
    (hfi : ∀ t ∈ Ioi (0 : ℝ), IntervalIntegrable f volume 0 t)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hF : LaplaceConvergent (fun t : ℝ => ∫ x in 0..t, f x) s)
    (h_infty : Tendsto
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)) • (∫ x in 0..t, f x))
      atTop (𝓝 0)) :
    HasLaplace (fun t : ℝ => ∫ x in 0..t, f x) s (m / s) :=
  hasLaplace_intervalIntegral_zero_div hs hfi hcont hF hf h_infty

end Deriv

section Values

/-- The Laplace transform of the constant function `1`. -/
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ => (1 : ℂ)) s (1 / s) := by
  have hs' : (-s).re < 0 := by simpa using neg_lt_zero.mpr hs
  refine ⟨?_, ?_⟩
  · simpa [IntegrableOn, LaplaceConvergent, smul_eq_mul] using
      (integrableOn_exp_mul_complex_Ioi (a := -s) hs' 0)
  · calc
      laplace (fun _ : ℝ => (1 : ℂ)) s
          = ∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ)) := by
            simp [laplace, smul_eq_mul]
      _ = -Complex.exp ((-s) * (0 : ℝ)) / (-s) := by
            simpa using integral_exp_mul_complex_Ioi (a := -s) hs' 0
      _ = 1 / s := by
            simp

section Const

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℂ E] [IsBoundedSMul ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The Laplace transform of a constant vector. -/
theorem hasLaplace_const [CompleteSpace E] {s : ℂ} (hs : 0 < s.re) (c : E) :
    HasLaplace (fun _ : ℝ => c) s (s⁻¹ • c) := by
  have hs' : (-s).re < 0 := by simpa using neg_lt_zero.mpr hs
  have hscalar : IntegrableOn (fun t : ℝ => Complex.exp ((-s) * (t : ℂ))) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (a := -s) hs' 0
  refine ⟨hscalar.smul_const c, ?_⟩
  calc
    laplace (fun _ : ℝ => c) s
        = ∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ)) • c := rfl
    _ = (∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ))) • c := by
          let L : ℂ →L[ℝ] E := (1 : ℂ →L[ℝ] ℂ).smulRight c
          change ∫ t : ℝ in Ioi 0, L (Complex.exp ((-s) * (t : ℂ))) =
            L (∫ t : ℝ in Ioi 0, Complex.exp ((-s) * (t : ℂ)))
          exact L.integral_comp_comm hscalar
    _ = s⁻¹ • c := by
          rw [integral_exp_mul_complex_Ioi (a := -s) hs' 0]
          congr 1
          simp

end Const

/-- The Laplace transform of a complex exponential. -/
theorem hasLaplace_cexp {a s : ℂ} (h : a.re < s.re) :
    HasLaplace (fun t : ℝ => Complex.exp (a * (t : ℂ))) s (1 / (s - a)) := by
  have hsa : (a - s).re < 0 := by simpa [sub_re] using sub_neg.mpr h
  refine ⟨?_, ?_⟩
  · refine (integrableOn_exp_mul_complex_Ioi (a := a - s) hsa 0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    symm
    change Complex.exp ((-s) * (t : ℂ)) * Complex.exp (a * (t : ℂ)) =
      Complex.exp ((a - s) * (t : ℂ))
    rw [← Complex.exp_add]
    congr 1
    ring
  · calc
      laplace (fun t : ℝ => Complex.exp (a * (t : ℂ))) s
          = ∫ t : ℝ in Ioi 0, Complex.exp ((a - s) * (t : ℂ)) := by
            refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
            dsimp [laplace]
            rw [← Complex.exp_add]
            congr 1
            ring
      _ = -Complex.exp ((a - s) * (0 : ℝ)) / (a - s) := by
            simpa using integral_exp_mul_complex_Ioi (a := a - s) hsa 0
      _ = 1 / (s - a) := by
            have h_ne : s - a ≠ 0 := fun hzero => by
              have : s.re - a.re = 0 := by
                simpa using congr_arg Complex.re hzero
              linarith
            have h_ne' : a - s ≠ 0 := by
              intro hzero
              apply h_ne
              rw [sub_eq_zero] at hzero ⊢
              exact hzero.symm
            simp
            field_simp [h_ne, h_ne']
            ring

end Values

end
