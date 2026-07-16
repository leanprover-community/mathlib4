/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Almost everywhere differentiability of functions with locally bounded variation

In this file we show that a bounded variation function is differentiable almost everywhere.
This implies that Lipschitz functions from the real line into finite-dimensional vector spaces
are also differentiable almost everywhere.

## Main definitions and results

* `LocallyBoundedVariationOn.ae_differentiableWithinAt` shows that a bounded variation
  function on a subset of ℝ into a finite-dimensional real vector space is differentiable almost
  everywhere, with `DifferentiableWithinAt` in its conclusion.
* `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` shows that a bounded variation function on
  an interval of ℝ into a finite-dimensional real vector space is differentiable almost everywhere,
  with `DifferentiableAt` in its conclusion.
* `LipschitzOnWith.ae_differentiableWithinAt` is the same result for Lipschitz functions.

We also give several variations around these results.

-/

public section

open scoped NNReal Topology ENNReal
open Set MeasureTheory Filter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section

open Finset

variable {α : Type*} [LinearOrder α] {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {s : Set α} {f : α → E} {g : α → F} {C D : ℝ≥0∞} {B : E →L[ℝ] F →L[ℝ] G}

lemma eVariationOn_bilinear_comp_le (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D)
    (B : E →L[ℝ] F →L[ℝ] G) :
    eVariationOn (fun x ↦ B (f x) (g x) : α → G) s ≤
      ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by
  apply iSup_le
  rintro ⟨n, ⟨u, u_mono, u_mem⟩⟩
  calc ∑ i ∈ range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u i)))
  _ ≤ ∑ i ∈ range n, edist (B (f (u (i + 1))) (g (u (i + 1)))) (B (f (u i)) (g (u (i + 1)))) +
      ∑ i ∈ range n, edist (B (f (u i)) (g (u (i + 1)))) (B (f (u i)) (g (u i))) := by
    rw [← Finset.sum_add_distrib]
    gcongr with i hi
    apply edist_triangle
  _ = ∑ i ∈ range n, ‖B (f (u (i + 1)) - f (u i)) (g (u (i + 1)))‖ₑ +
      ∑ i ∈ range n, ‖B (f (u i)) (g (u (i + 1)) - g (u i))‖ₑ := by simp [edist_eq_enorm_sub]
  _ ≤ ∑ i ∈ range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * ‖g (u (i + 1))‖ₑ +
      ∑ i ∈ range n, ‖B‖ₑ * ‖f (u i)‖ₑ * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply ContinuousLinearMap.le_opENorm₂
    · apply ContinuousLinearMap.le_opENorm₂
  _ ≤ ∑ i ∈ range n, ‖B‖ₑ * ‖f (u (i + 1)) - f (u i)‖ₑ * D +
      ∑ i ∈ range n, ‖B‖ₑ * C * ‖g (u (i + 1)) - g (u i)‖ₑ := by
    gcongr with i hi i hi
    · apply hg _ (u_mem _)
    · apply hf _ (u_mem _)
  _ = ‖B‖ₑ * D * ∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖ₑ +
      ‖B‖ₑ * C * ∑ i ∈ range n, ‖g (u (i + 1)) - g (u i)‖ₑ := by
    simp only [← sum_mul, ← mul_sum]
    ring
  _ ≤ ‖B‖ₑ * D * eVariationOn f s + ‖B‖ₑ * C * eVariationOn g s := by
    simp only [← edist_eq_enorm_sub]
    gcongr
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi ↦ u_mem i)
    · exact eVariationOn.sum_le_of_monotoneOn_Iic (u_mono.monotoneOn _) (fun i hi ↦ u_mem i)
  _ = ‖B‖ₑ * (C * eVariationOn g s + D * eVariationOn f s) := by ring

@[to_fun eVariationOn_fun_smul_le]
lemma eVariationOn_smul_le {𝕜 : Type*} {f : α → 𝕜} {g : α → F}
    [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    {C D : ℝ≥0∞} {s : Set α} (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D) :
    eVariationOn (f • g) s ≤ C * eVariationOn g s + D * eVariationOn f s := by
  apply (eVariationOn_bilinear_comp_le hf hg (B := ContinuousLinearMap.lsmul ℝ 𝕜)).trans
  grw [ContinuousLinearMap.opENorm_lsmul_le, one_mul]

@[to_fun eVariationOn_fun_mul_le]
lemma eVariation_mul_le {f g : α → ℝ}
    {C D : ℝ≥0∞} {s : Set α} (hf : ∀ x ∈ s, ‖f x‖ₑ ≤ C) (hg : ∀ x ∈ s, ‖g x‖ₑ ≤ D) :
    eVariationOn (f * g) s ≤ C * eVariationOn g s + D * eVariationOn f s := by
  simpa using eVariationOn_smul_le hf hg

lemma BoundedVariationOn.bilinear_comp
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) (B : E →L[ℝ] F →L[ℝ] G) :
    BoundedVariationOn (fun x ↦ B (f x) (g x)) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨⟨x, hx⟩⟩
  · simp
  suffices eVariationOn (fun x ↦ (B (f x)) (g x)) s < ∞ from ne_of_lt this
  have A (y) (hy : y ∈ s) : ‖f y‖ₑ ≤ ‖f x‖ₑ + eVariationOn f s := by
    grw [show f y = f x + (f y - f x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  have A' (y) (hy : y ∈ s) : ‖g y‖ₑ ≤ ‖g x‖ₑ + eVariationOn g s := by
    grw [show g y = g x + (g y - g x) by abel, enorm_add_le, ← edist_eq_enorm_sub,
      eVariationOn.edist_le _ hy hx]
  grw [eVariationOn_bilinear_comp_le A A']
  simp [mul_add, ENNReal.mul_lt_top_iff, hf.lt_top, hg.lt_top]

@[to_fun]
lemma BoundedVariationOn.smul {𝕜 : Type*} {f : α → 𝕜} {g : α → F}
    [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    {s : Set α} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f • g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ 𝕜)

@[to_fun]
lemma BoundedVariationOn.mul {f g : α → ℝ} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f * g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ ℝ)

lemma LocallyBoundedVariationOn.bilinear_comp (hf : LocallyBoundedVariationOn f s)
    (hg : LocallyBoundedVariationOn g s) (B : E →L[ℝ] F →L[ℝ] G) :
    LocallyBoundedVariationOn (fun x ↦ B (f x) (g x)) s :=
  fun a b ha hb ↦ (hf a b ha hb).bilinear_comp (hg a b ha hb) B

@[to_fun]
lemma LocallyBoundedVariationOn.smul {𝕜 : Type*} {f : α → 𝕜} {g : α → F}
    [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [IsScalarTower ℝ 𝕜 F]
    {s : Set α} (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f • g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ 𝕜)

@[to_fun]
lemma LocallyBoundedVariationOn.mul {f g : α → ℝ} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f * g) s :=
  hf.bilinear_comp hg (B := ContinuousLinearMap.lsmul ℝ ℝ)

end

namespace LocallyBoundedVariationOn

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiableWithinAt_of_mem`. -/
theorem ae_differentiableWithinAt_of_mem_real {f : ℝ → ℝ} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨p, q, hp, hq, rfl⟩ : ∃ p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q :=
    h.exists_monotoneOn_sub_monotoneOn
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem] with
    x hxp hxq xs
  exact (hxp xs).sub (hxq xs)

/-- A bounded variation function into a finite-dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiableWithinAt_of_mem`. -/
theorem ae_differentiableWithinAt_of_mem_pi {ι : Type*} [Fintype ι] {f : ℝ → ι → ℝ} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 fun x : ι → ℝ => x i := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (fun x : ℝ => f x i) s x := fun i ↦ by
    apply ae_differentiableWithinAt_of_mem_real
    exact LipschitzWith.comp_locallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 fun i => hx i xs

/-- A real function into a finite-dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiableWithinAt_of_mem {f : ℝ → V} {s : Set ℝ}
    (h : LocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let A := (Module.Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    exact (ContinuousLinearEquiv.comp_differentiableWithinAt_iff _).mp (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_locallyBoundedVariationOn h

/-- A real function into a finite-dimensional real vector space with bounded variation on an
interval is differentiable almost everywhere in this interval. This one differs from
`LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem` by using `DifferentiableAt` instead of
`DifferentiableWithinAt` in its conclusion. -/
theorem _root_.BoundedVariationOn.ae_differentiableAt_of_mem_uIcc {f : ℝ → V} {a b : ℝ}
    (h : BoundedVariationOn f (uIcc a b)) : ∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x := by
  have h₁ : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem, h₁, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc, mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt
    (Icc_mem_nhds (lt_of_le_of_ne hx₄.left hx₂.symm) (lt_of_le_of_ne hx₄.right hx₃))

/-- A real function into a finite-dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiableWithinAt {f : ℝ → V} {s : Set ℝ} (h : LocallyBoundedVariationOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiableWithinAt_of_mem

/-- A real function into a finite-dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiableAt {f : ℝ → V} (h : LocallyBoundedVariationOn f univ) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with x hx
  rw [differentiableWithinAt_univ] at hx
  exact hx (mem_univ _)

end LocallyBoundedVariationOn

/-- A real function into a finite-dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzOnWith.ae_differentiableWithinAt_of_mem`.
-/
theorem LipschitzOnWith.ae_differentiableWithinAt_of_mem_real {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x :=
  h.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

/-- A real function into a finite-dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzOnWith.ae_differentiableWithinAt`. -/
theorem LipschitzOnWith.ae_differentiableWithinAt_real {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x :=
  h.locallyBoundedVariationOn.ae_differentiableWithinAt hs

/-- A real Lipschitz function into a finite-dimensional real vector space is differentiable
almost everywhere. For the general Rademacher theorem assuming
that the source space is finite dimensional, see `LipschitzWith.ae_differentiableAt`. -/
theorem LipschitzWith.ae_differentiableAt_real {C : ℝ≥0} {f : ℝ → V} (h : LipschitzWith C f) :
    ∀ᵐ x, DifferentiableAt ℝ f x :=
  (h.locallyBoundedVariationOn univ).ae_differentiableAt
