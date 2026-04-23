/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Piecewise

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/

@[expose] public section

open scoped Topology Filter

open Function Set Filter

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Classical in
/-- `dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and
`deriv f a` for `a = b`. -/
noncomputable def dslope (f : 𝕜 → E) (a : 𝕜) : 𝕜 → E :=
  update (slope f a) a (deriv f a)

@[simp]
theorem dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a := by
  classical
  exact update_self ..

variable {f : 𝕜 → E} {a b : 𝕜} {s : Set 𝕜}

theorem dslope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a b = slope f a b := by
  classical
  exact update_of_ne h ..

theorem ContinuousLinearMap.dslope_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (g : 𝕜 → E) (a b : 𝕜) (H : a = b → DifferentiableAt 𝕜 g a) :
    dslope (f ∘ g) a b = f (dslope g a b) := by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using f.toLinearMap.slope_comp g a b

theorem eqOn_dslope_slope (f : 𝕜 → E) (a : 𝕜) : EqOn (dslope f a) (slope f a) {a}ᶜ := fun _ =>
  dslope_of_ne f

theorem dslope_eventuallyEq_slope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a =ᶠ[𝓝 b] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem (isOpen_ne.mem_nhds h)

theorem dslope_eventuallyEq_slope_nhdsNE (f : 𝕜 → E) : dslope f a =ᶠ[𝓝[≠] a] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem self_mem_nhdsWithin

@[simp]
theorem sub_smul_dslope (f : 𝕜 → E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f a := by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]

theorem dslope_sub_smul_of_ne (f : 𝕜 → E) (h : b ≠ a) :
    dslope (fun x => (x - a) • f x) a b = f b := by
  rw [dslope_of_ne _ h, slope_sub_smul _ h.symm]

theorem eqOn_dslope_sub_smul (f : 𝕜 → E) (a : 𝕜) :
    EqOn (dslope (fun x => (x - a) • f x) a) f {a}ᶜ := fun _ => dslope_sub_smul_of_ne f

theorem dslope_sub_smul [DecidableEq 𝕜] (f : 𝕜 → E) (a : 𝕜) :
    dslope (fun x => (x - a) • f x) a = update f a (deriv (fun x => (x - a) • f x) a) :=
  eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩

@[simp]
theorem continuousAt_dslope_same : ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a := by
  simp only [dslope, continuousAt_update_same, ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope]

theorem ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) :
    ContinuousWithinAt f s b := by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this

theorem ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f b :=
  (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope

theorem ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f s := fun x hx =>
  (h x hx).of_dslope

theorem continuousWithinAt_dslope_of_ne (h : b ≠ a) :
    ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b := by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  classical
  simp only [dslope, continuousWithinAt_update_of_ne h]
  exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 h)).smul
    (hc.sub continuousWithinAt_const)

theorem continuousAt_dslope_of_ne (h : b ≠ a) : ContinuousAt (dslope f a) b ↔ ContinuousAt f b := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]

theorem continuousOn_dslope (h : s ∈ 𝓝 a) :
    ContinuousOn (dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a := by
  refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 <| hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]

theorem DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt 𝕜 (dslope f a) s b) :
    DifferentiableWithinAt 𝕜 f s b := by
  simpa only [id, sub_smul_dslope f a, sub_add_cancel] using
    ((differentiableWithinAt_id.sub_const a).fun_smul h).add_const (f a)

theorem DifferentiableAt.of_dslope (h : DifferentiableAt 𝕜 (dslope f a) b) :
    DifferentiableAt 𝕜 f b :=
  differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope

theorem DifferentiableOn.of_dslope (h : DifferentiableOn 𝕜 (dslope f a) s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).of_dslope

theorem differentiableWithinAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithinAt 𝕜 f s b := by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  refine (((differentiableWithinAt_id.sub_const a).inv (sub_ne_zero.2 h)).smul
    (hd.sub_const (f a))).congr_of_eventuallyEq ?_ (dslope_of_ne _ h)
  refine (eqOn_dslope_slope _ _).eventuallyEq_of_mem ?_
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)

theorem differentiableOn_dslope_of_notMem (h : a ∉ s) :
    DifferentiableOn 𝕜 (dslope f a) s ↔ DifferentiableOn 𝕜 f s :=
  forall_congr' fun _ =>
    forall_congr' fun hx => differentiableWithinAt_dslope_of_ne <| ne_of_mem_of_not_mem hx h

theorem differentiableAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableAt 𝕜 (dslope f a) b ↔ DifferentiableAt 𝕜 f b := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]
