/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inv

#align_import analysis.calculus.dslope from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/


open scoped Classical Topology Filter

open Function Set Filter

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and
`deriv f a` for `a = b`. -/
noncomputable def dslope (f : 𝕜 → E) (a : 𝕜) : 𝕜 → E :=
  update (slope f a) a (deriv f a)
#align dslope dslope

@[simp]
theorem dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a :=
  update_same _ _ _
#align dslope_same dslope_same

variable {f : 𝕜 → E} {a b : 𝕜} {s : Set 𝕜}

theorem dslope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a b = slope f a b :=
  update_noteq h _ _
#align dslope_of_ne dslope_of_ne

theorem ContinuousLinearMap.dslope_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (g : 𝕜 → E) (a b : 𝕜) (H : a = b → DifferentiableAt 𝕜 g a) :
    dslope (f ∘ g) a b = f (dslope g a b) := by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using f.toLinearMap.slope_comp g a b
#align continuous_linear_map.dslope_comp ContinuousLinearMap.dslope_comp

theorem eqOn_dslope_slope (f : 𝕜 → E) (a : 𝕜) : EqOn (dslope f a) (slope f a) {a}ᶜ := fun _ =>
  dslope_of_ne f
#align eq_on_dslope_slope eqOn_dslope_slope

theorem dslope_eventuallyEq_slope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a =ᶠ[𝓝 b] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem (isOpen_ne.mem_nhds h)
#align dslope_eventually_eq_slope_of_ne dslope_eventuallyEq_slope_of_ne

theorem dslope_eventuallyEq_slope_punctured_nhds (f : 𝕜 → E) : dslope f a =ᶠ[𝓝[≠] a] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem self_mem_nhdsWithin
#align dslope_eventually_eq_slope_punctured_nhds dslope_eventuallyEq_slope_punctured_nhds

@[simp]
theorem sub_smul_dslope (f : 𝕜 → E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f a := by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]
#align sub_smul_dslope sub_smul_dslope

theorem dslope_sub_smul_of_ne (f : 𝕜 → E) (h : b ≠ a) :
    dslope (fun x => (x - a) • f x) a b = f b := by
  rw [dslope_of_ne _ h, slope_sub_smul _ h.symm]
#align dslope_sub_smul_of_ne dslope_sub_smul_of_ne

theorem eqOn_dslope_sub_smul (f : 𝕜 → E) (a : 𝕜) :
    EqOn (dslope (fun x => (x - a) • f x) a) f {a}ᶜ := fun _ => dslope_sub_smul_of_ne f
#align eq_on_dslope_sub_smul eqOn_dslope_sub_smul

theorem dslope_sub_smul [DecidableEq 𝕜] (f : 𝕜 → E) (a : 𝕜) :
    dslope (fun x => (x - a) • f x) a = update f a (deriv (fun x => (x - a) • f x) a) :=
  eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩
#align dslope_sub_smul dslope_sub_smul

@[simp]
theorem continuousAt_dslope_same : ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a := by
  simp only [dslope, continuousAt_update_same, ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope]
#align continuous_at_dslope_same continuousAt_dslope_same

theorem ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) :
    ContinuousWithinAt f s b := by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this
#align continuous_within_at.of_dslope ContinuousWithinAt.of_dslope

theorem ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f b :=
  (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope
#align continuous_at.of_dslope ContinuousAt.of_dslope

theorem ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f s := fun x hx =>
  (h x hx).of_dslope
#align continuous_on.of_dslope ContinuousOn.of_dslope

theorem continuousWithinAt_dslope_of_ne (h : b ≠ a) :
    ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b := by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  simp only [dslope, continuousWithinAt_update_of_ne h]
  exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 h)).smul
    (hc.sub continuousWithinAt_const)
#align continuous_within_at_dslope_of_ne continuousWithinAt_dslope_of_ne

theorem continuousAt_dslope_of_ne (h : b ≠ a) : ContinuousAt (dslope f a) b ↔ ContinuousAt f b := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]
#align continuous_at_dslope_of_ne continuousAt_dslope_of_ne

theorem continuousOn_dslope (h : s ∈ 𝓝 a) :
    ContinuousOn (dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a := by
  refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 <| hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]
#align continuous_on_dslope continuousOn_dslope

theorem DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt 𝕜 (dslope f a) s b) :
    DifferentiableWithinAt 𝕜 f s b := by
  simpa only [id, sub_smul_dslope f a, sub_add_cancel] using
    ((differentiableWithinAt_id.sub_const a).smul h).add_const (f a)
#align differentiable_within_at.of_dslope DifferentiableWithinAt.of_dslope

theorem DifferentiableAt.of_dslope (h : DifferentiableAt 𝕜 (dslope f a) b) :
    DifferentiableAt 𝕜 f b :=
  differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope
#align differentiable_at.of_dslope DifferentiableAt.of_dslope

theorem DifferentiableOn.of_dslope (h : DifferentiableOn 𝕜 (dslope f a) s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).of_dslope
#align differentiable_on.of_dslope DifferentiableOn.of_dslope

theorem differentiableWithinAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithinAt 𝕜 f s b := by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  refine (((differentiableWithinAt_id.sub_const a).inv (sub_ne_zero.2 h)).smul
    (hd.sub_const (f a))).congr_of_eventuallyEq ?_ (dslope_of_ne _ h)
  refine (eqOn_dslope_slope _ _).eventuallyEq_of_mem ?_
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)
#align differentiable_within_at_dslope_of_ne differentiableWithinAt_dslope_of_ne

theorem differentiableOn_dslope_of_nmem (h : a ∉ s) :
    DifferentiableOn 𝕜 (dslope f a) s ↔ DifferentiableOn 𝕜 f s :=
  forall_congr' fun _ =>
    forall_congr' fun hx => differentiableWithinAt_dslope_of_ne <| ne_of_mem_of_not_mem hx h
#align differentiable_on_dslope_of_nmem differentiableOn_dslope_of_nmem

theorem differentiableAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableAt 𝕜 (dslope f a) b ↔ DifferentiableAt 𝕜 f b := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]
#align differentiable_at_dslope_of_ne differentiableAt_dslope_of_ne
