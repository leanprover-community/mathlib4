/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Bounding of integrals by asymptotics

We establish integrability of `f` from `f = O(g)`.

## Main results

* `Asymptotics.IsBigO.integrableAtFilter`: If `f = O[l] g` on measurably generated `l`,
  `f` is strongly measurable at `l`, and `g` is integrable at `l`, then `f` is integrable at `l`.
-/

open Asymptotics MeasureTheory Set Filter

variable {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : α → E} {g : α → F} {a b : α} {μ : Measure α} {l : Filter α}

/-- If `f = O[l] g` on measurably generated `l`, `f` is strongly measurable at `l`,
and `g` is integrable at `l`, then `f` is integrable at `l`. -/
theorem _root_.Asymptotics.IsBigO.integrableAtFilter [IsMeasurablyGenerated l]
    (hf : f =O[l] g) (hfm : StronglyMeasurableAtFilter f l μ) (hg : IntegrableAtFilter g l μ) :
    IntegrableAtFilter f l μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨s, hsl, hsm, hfg, hf, hg⟩ :=
    (hC.smallSets.and <| hfm.eventually.and hg.eventually).exists_measurable_mem_of_smallSets
  refine ⟨s, hsl, (hg.norm.const_mul C).mono hf ?_⟩
  refine (ae_restrict_mem hsm).mono fun x hx ↦ ?_
  exact (hfg x hx).trans (le_abs_self _)

/-- Variant of `MeasureTheory.Integrable.mono` taking `f =O[⊤] (g)` instead of `‖f(x)‖ ≤ ‖g(x)‖` -/
theorem _root_.Asymptotics.IsBigO.integrable (hfm : AEStronglyMeasurable f μ)
    (hf : f =O[⊤] g) (hg : Integrable g μ) : Integrable f μ := by
  rewrite [← integrableAtFilter_top] at *
  exact hf.integrableAtFilter ⟨univ, univ_mem, hfm.restrict⟩ hg

namespace Asymptotics

section Uniform

variable {ι : Type*} [MeasurableSpace ι] {f : ι × α → E} {s : Set ι} {μ : Measure ι}

/-- Let `f : X x Y → Z`. If as y → l, f(x, y) = O(g(y)) uniformly on `s : Set X` of finite measure,
then f is eventually (as y → l) integrable along `s`. -/
theorem IsBigO.eventually_integrableOn [Norm F]
    (hf : f =O[𝓟 s ×ˢ l] fun (_i, x) ↦ g x)
    (hfm : ∀ᶠ x in l, AEStronglyMeasurable (fun i ↦ f (i, x)) (μ.restrict s))
    (hs : MeasurableSet s) (hμ : μ s < ⊤) :
    ∀ᶠ x in l, IntegrableOn (fun i ↦ f (i, x)) s μ := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  obtain ⟨w, hwl, hw⟩ := hfm.exists_mem
  refine eventually_iff_exists_mem.mpr ⟨w ∩ v, inter_mem hwl hv, fun x hx ↦ ?_⟩
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ s]; exact hμ⟩
  refine Integrable.mono' (integrable_const (C * ‖g x‖)) (hw x hx.1) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  intro y hy
  exact ht (y, x) <| huv ⟨hu hy, hx.2⟩

variable [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let `f : X x Y → Z`. If as y → l, f(x, y) = O(g(y)) uniformly on `s : Set X` of finite measure,
then the integral of f along s is O(g(y)). -/
theorem IsBigO.set_integral_isBigO
    (hf : f =O[𝓟 s ×ˢ l] fun (_i, x) ↦ g x) (hs : MeasurableSet s) (hμ : μ s < ⊤)  :
    (fun x ↦ ∫ i in s, f (i, x) ∂μ) =O[l] g := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C * (μ s).toReal, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx ↦ ?_⟩⟩
  rewrite [mul_assoc, ← smul_eq_mul (a' := ‖g x‖), ← MeasureTheory.Measure.restrict_apply_univ,
    ← integral_const, mul_comm, ← smul_eq_mul, ← integral_smul_const]
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ s]; exact hμ⟩
  refine (norm_integral_le_integral_norm _).trans <|
    integral_mono_of_nonneg (univ_mem' fun _ ↦ norm_nonneg _) (integrable_const _) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  intro y hy
  rewrite [smul_eq_mul, mul_comm]
  exact ht (y, x) <| huv ⟨hu hy, hx⟩

end Uniform

end Asymptotics
