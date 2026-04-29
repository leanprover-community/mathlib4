/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.Homotopy.Affine

/-!
# Poincaré lemma for 1-forms

In this file we prove Poincaré lemma for 1-forms for convex sets.
Namely, we show that a closed 1-form on a convex subset of a normed space is exact.

We also prove that the integrals of a closed 1-form
along 2 curves that are joined by a `C²`-smooth homotopy are equal.
In the future, this will allow us to prove Poincaré lemma for simply connected open sets
and, more generally, for simply connected locally convex sets.

## Implementation notes

In this file, we represent a 1-form as `ω : E → E →L[𝕜] F`, where `𝕜` is `ℝ` or `ℂ`,
not as `ω : E → E [⋀^Fin 1]→L[𝕜] F`.
A 1-form represented this way is closed
iff its Fréchet derivative `dω : E → E →L[𝕜] E →L[𝕜] F` is symmetric, `dω a x y = dω a y x`.
-/

public section

open scoped unitInterval Interval Pointwise Topology
open AffineMap Filter Function MeasureTheory Set

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace ContinuousMap.Homotopy

variable [NormedSpace ℝ E] [NormedSpace ℝ F] {a b c d : E}
    {γ₁ : Path a b} {γ₂ : Path c d} {s : Set (I × I)} {t : Set E}

set_option backward.isDefEq.respectTransparency false in
private theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))) (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  -- The overall plan of the proof is to pullback the 1-form to the unit square along the homotopy,
  -- prove that it's a closed 1-form, then apply the divergence theorem.
  -- Let `U` be the interior of the unit square
  -- Warning: throughout the proof, we sometimes have `0` or `1` in product spaces,
  -- not only in `I` or `ℝ`, so, e.g., `Icc 0 1` may refer to the unit square
  -- in `ℝ × ℝ`.
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hinterior : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq]
    simp [Prod.mk_zero_zero, Prod.mk_one_one]
  have hunique : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUopen : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hU_subset : U ⊆ Icc 0 1 := hinterior ▸ interior_subset
  have hclosure : closure U = Icc 0 1 := by
    simp [hU, closure_prod_eq, Prod.mk_zero_zero, Prod.mk_one_one]
  -- Extend the homotopy `φ` to a continuous map  `ψ : ℝ × ℝ → E`
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2 with hψ
  have hψφ : ∀ a b : I, ψ (a, b) = φ (a, b) := by simp [ψ]
  have hψ_cont : Continuous ψ := by fun_prop
  have hψUt : MapsTo ψ U t := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    lift a to I using Ioo_subset_Icc_self ha
    lift b to I using Ioo_subset_Icc_self hb
    simpa [hψφ] using hφt a ha b hb
  -- Let `dψ` be its derivative.
  set dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fderivWithin ℝ ψ (Icc 0 1)
  -- Let `s'` be the set `s` interpreted as a set in `ℝ × ℝ`
  set s' : Set (ℝ × ℝ) := Prod.map (↑) (↑) '' s with hs'
  have hmem_s' (x y : I) : (↑x, ↑y) ∈ s' ↔ (x, y) ∈ s := by
    rw [hs', ← Prod.map_apply, Injective.mem_set_image]
    apply Injective.prodMap <;> apply Subtype.val_injective
  have hs'c : s'.Countable := hs.image _
  have hdψ : ∀ a ∈ U, HasFDerivAt ψ (dψ a) a := by
    rintro a haU
    refine hcontdiff.differentiableOn (by decide) a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Let `d2ψ` be its second derivative
  set d2ψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] E := fderivWithin ℝ dψ (Icc 0 1)
  have hd2ψ : ∀ a ∈ U, HasFDerivAt dψ (d2ψ a) a := by
    rintro a haU
    refine hcontdiff.fderivWithin hunique (by decide) |>.differentiableOn_one a (hU_subset haU)
      |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    rwa [← mem_interior_iff_mem_nhds, hinterior]
  -- Note that `d2ψ` is symmetric
  have hd2ψ_symm : ∀ a ∈ Icc 0 1, ∀ x y, d2ψ a x y = d2ψ a y x := by
    intro a ha
    exact (hcontdiff a ha).isSymmSndFDerivWithinAt (by simp) hunique
      (by simp [hinterior, hclosure, ha]) ha
  -- Consider `η a = ω (ψ a) ∘L dψ a`.
  set η : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ω (ψ a) ∘L dψ a
  -- Put `f a = η a (0, 1)`, `g a = -η a (1, 0)`.
  set f : ℝ × ℝ → F := fun a ↦ η a (0, 1)
  have hf : ∀ a ∈ Icc 0 1, f a = ω (ψ a) (derivWithin (ψ ∘ (a.1, ·)) I a.2) := by
    intro a ha
    simp only [f, η, dψ, ContinuousLinearMap.comp_apply]
    congr 1
    have : HasDerivWithinAt (a.1, ·) (0, 1) I a.2 :=
      .prodMk (hasDerivWithinAt_const ..) (hasDerivWithinAt_id ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ha.1.1, ht.1⟩, ⟨ha.2.1, ht.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.2, ha.2.2⟩
  set g : ℝ × ℝ → F := fun a ↦ -η a (1, 0)
  have hg : ∀ a ∈ Icc 0 1, g a = ω (ψ a) (-derivWithin (ψ ∘ (·, a.2)) I a.1) := by
    intro a ha
    simp only [g, η, dψ, ContinuousLinearMap.comp_apply, map_neg]
    congr 2
    have : HasDerivWithinAt (·, a.2) (1, 0) I a.1 :=
      .prodMk (hasDerivWithinAt_id ..) (hasDerivWithinAt_const ..)
    refine DifferentiableWithinAt.hasFDerivWithinAt ?_ |>.comp_hasDerivWithinAt _ this ?_
      |>.derivWithin ?_ |>.symm
    · exact hcontdiff.differentiableOn (by decide) _ ha
    · exact fun t ht ↦ ⟨⟨ht.1, ha.1.2⟩, ⟨ht.2, ha.2.2⟩⟩
    · exact uniqueDiffOn_Icc_zero_one _ ⟨ha.1.1, ha.2.1⟩
  -- Then our goal is to prove that the integral of `η`
  -- along the boundary of the unit square is zero.
  suffices (((∫ x in 0..1, g (x, 1)) - ∫ x in 0..1, g (x, 0)) +
      ∫ y in 0..1, f (1, y)) - ∫ y in 0..1, f (0, y) = 0 by
    have hfi (s : I) :
        ∫ t in 0..1, f (s, t) = ∫ᶜ x in ⟨φ.curry s, rfl, rfl⟩, ω x := by
      simp only [curveIntegral_def, curveIntegralFun_def]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro t ht
      simp [Path.extend, hf (s, t), Prod.le_def, s.2.1, s.2.2, ht.1, ht.2, Function.comp_def, hψ]
    have hf₀ : ∫ t in 0..1, f (0, t) = ∫ᶜ x in γ₁, ω x := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 0
    have hf₁ : ∫ t in 0..1, f (1, t) = curveIntegral ω γ₂ := by
      simpa [curveIntegral_def, curveIntegralFun_def, Path.extend] using hfi 1
    have hgi (t : I) : ∫ᶜ x in φ.evalAt t, ω x = -∫ s in 0..1, g (s, t) := by
      simp only [curveIntegral_def, curveIntegralFun_def, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le zero_le_one]
      intro s hs
      simp only [hs, Path.extend_apply, φ.evalAt_apply]
      simp [hg (s, t), Prod.le_def, hs.1, hs.2, t.2.1, t.2.2, Function.comp_def, hψ]
    rw [← hf₀, ← hf₁, hgi, hgi]
    linear_combination (norm := {dsimp; abel}) -this
  -- Write a formula for the derivative of `η`.
  set dη : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] F := fun a ↦
    .compL ℝ (ℝ × ℝ) E F (ω (ψ a)) ∘L d2ψ a + (dω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hdη : ∀ a ∈ U \ s', HasFDerivAt η (dη a) a := by
    rintro a ⟨haU, has⟩
    refine HasFDerivWithinAt.comp_hasFDerivAt (t := t) a ?_ ?_ ?_ |>.clm_comp (hd2ψ a haU)
    · rcases a with ⟨x, y⟩
      lift x to I using Ioo_subset_Icc_self haU.1
      lift y to I using Ioo_subset_Icc_self haU.2
      apply hω
      · simpa using haU.1
      · simpa using haU.2
      · simpa [hmem_s'] using has
    · exact hdψ a haU
    · filter_upwards [hUopen.mem_nhds haU] using hψUt
  have hdη_symm : ∀ a ∈ U \ s', ∀ u v, dη a u v = dη a v u := by
    rintro ⟨a, b⟩ ⟨hU, hs'⟩ u v
    lift a to I using Ioo_subset_Icc_self hU.1
    lift b to I using Ioo_subset_Icc_self hU.2
    have hdψ_mem (u) : dψ (a, b) u ∈ tangentConeAt ℝ t (φ (a, b)) := by
      refine tangentConeAt_mono hψUt.image_subset ?_
      rw [← hψφ]
      refine (hdψ _ hU).hasFDerivWithinAt.mapsTo_tangent_cone ?_
      simp [tangentConeAt_of_mem_nhds (hUopen.mem_nhds hU)]
    have := hdω_symm a hU.1 b hU.2 (by simpa [hmem_s'] using hs') _ (hdψ_mem u) _ (hdψ_mem v)
    simp [dη, hψφ, this, hd2ψ_symm _ (hU_subset hU)]
  -- It gives formulas for the derivatives of `f` and `g`
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  have hf' : ∀ a ∈ U \ s', HasFDerivAt f (f' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a (hdη a ha)
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)
  have hg' : ∀ a ∈ U \ s', HasFDerivAt g (g' a) a := by
    intro a ha
    exact (ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp a (hdη a ha) |>.neg
  -- Note that the divergence of `(f, g)` is a.e. zero.
  have hf'g' : (fun a ↦ f' a (1, 0) + g' a (0, 1)) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    rw [Icc_prod_eq, Measure.volume_eq_prod,
      Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo), hs'c.ae_notMem _]
      with a hU hs
    simp [f', g', hdη_symm a ⟨hU, hs⟩ (0, 1)]
  suffices ∫ a : ℝ × ℝ in Icc 0 1, f' a (1, 0) + g' a (0, 1) = 0 by
    have hηc : ContinuousOn η (Icc 0 1) := by
      refine .clm_comp (hωc.comp hψ_cont.continuousOn ?_) ?_
      · rw [← hclosure]
        refine MapsTo.closure (fun a ha ↦ ?_) hψ_cont
        lift a to I × I using ⟨Ioo_subset_Icc_self ha.1, Ioo_subset_Icc_self ha.2⟩
        simpa [ψ] using hφt a.1 ha.1 a.2 ha.2
      · exact hcontdiff.continuousOn_fderivWithin hunique (by decide)
    rwa [integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le] at this
    · exact zero_le_one
    · exact s'
    · exact hs'c
    · fun_prop
    · fun_prop
    · exact hf'
    · exact hg'
    · rw [integrableOn_congr_fun_ae hf'g']
      apply integrableOn_zero
  simp [integral_congr_ae hf'g']

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero. We may ignore the behavior on a countable set.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hs : s.Countable)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b)))
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  simp only [← curveIntegral_restrictScalars (𝕜 := 𝕜) (𝕝 := ℝ)]
  set e := ContinuousLinearMap.restrictScalarsL 𝕜 E F ℝ ℝ
  exact φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real hs hφt
    (dω := fun x ↦ e ∘L dω x)
    (fun a ha b hb hs ↦ e.hasFDerivAt.comp_hasFDerivWithinAt _ (hω a ha b hb hs))
    (e.continuous.comp_continuousOn hωc) hdω_symm hcontdiff

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ x ∈ t, HasFDerivWithinAt ω (dω x) t x)
    (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x, dω x u v = dω x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable (s := ∅) (by simp)
    hφt (fun a ha b hb _ ↦ hω _ <| hφt a ha b hb) hωc
    (fun a ha b hb _ ↦ hdω_symm _ <| hφt a ha b hb) hcontdiff

/-- The curve integral of a closed 1-form along the boundary of the image of a unit square
under a smooth map is zero, a version stated in terms of `DiffContOnC1`.

This theorem is stated in terms of a `C^2` homotopy between two paths. -/
theorem curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    {ω : E → E →L[𝕜] F} (φ : (γ₁ : C(I, E)).Homotopy γ₂)
    (hφt : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : DiffContOnCl ℝ ω t)
    (hdω_symm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      fderivWithin ℝ ω t x u v = fderivWithin ℝ ω t x v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x :=
  φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt
    hφt (fun t ht ↦ (hω.differentiableOn t ht).hasFDerivWithinAt) hω.continuousOn
    hdω_symm hcontdiff

end ContinuousMap.Homotopy

namespace Convex

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
  {a b c : E} {s : Set E} {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F}

set_option backward.defeqAttrib.useBackward true in
/-- If `ω` is a closed `1`-form on a convex set,
then `∫ᶜ x in Path.segment a b, ω x + ∫ᶜ x in Path.segment b c, ω x = ∫ᶜ x in Path.segment a c, ω x`
for all `a b c ∈ s`.

This is the key lemma used to establish that closed a `1`-form on  a convex set
has a primitive.
-/
theorem curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric (hs : Convex ℝ s)
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    (∫ᶜ x in .segment a b, ω x) + ∫ᶜ x in .segment b c, ω x = ∫ᶜ x in .segment a c, ω x := by
  set φ := ContinuousMap.Homotopy.affine (Path.segment a b : C(I, E)) (Path.segment a c)
  have hφs : range φ ⊆ s := by
    rw [range_subset_iff]
    intro x
    simp [φ, ha, hb, hc, hs.lineMap_mem]
  have := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := range φ) (ω := ω)
    (dω := dω) ?_ ?_ ?_ ?_ ?_
  · convert this using 2
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_one a b) (lineMap_apply_one a c), curveIntegral_cast]
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_zero a b) (lineMap_apply_zero a c)]
      simp
  · intros
    apply mem_range_self
  · exact fun x hx ↦ (hω x (hφs hx)).mono hφs
  · rw [(isCompact_range <| map_continuous _).isClosed.closure_eq]
    exact fun x hx ↦ (hω x <| hφs hx).continuousWithinAt.mono hφs
  · intro x hx u hu v hv
    apply hdω <;> grw [← hφs] <;> assumption
  · have : EqOn (fun x : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend x.1) x.2)
        (fun x ↦ lineMap (lineMap a b x.2) (lineMap a c x.2) x.1) (Icc 0 1) := by
      rw [Icc_prod_eq]
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to I using hx
      lift y to I using hy
      simp [φ]
    refine .congr ?_ this
    -- TODO: add `ContDiff.lineMap` etc
    simp only [AffineMap.lineMap_apply_module]
    fun_prop

variable [CompleteSpace F]

/-- If `ω` is a closed `1`-form on a convex set `s`,
then the function given by `F b = ∫ᶜ x in Path.segment a b, ω x` is a primitive of `ω` on `s`,
i.e., `dF = ω`.
-/
theorem hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric (hs : Convex ℝ s)
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) :
    HasFDerivWithinAt (∫ᶜ x in .segment a ·, ω x) (ω b) s b := by
  suffices HasFDerivWithinAt (∫ᶜ x in .segment a b, ω x + ∫ᶜ x in .segment b ·, ω x) (ω b) s b from
    this.congr' (fun _ h ↦
      (hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
  refine .const_add _ <| ?_
  refine HasFDerivWithinAt.curveIntegral_segment_source hs ?_ hb
  exact fun x hx ↦ (hω x hx).continuousWithinAt

/-- If `ω` is a closed `1`-form on a convex set `s`, then it admits a primitive,
a version stated in terms of `HasFDerivWithinAt`. -/
theorem exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (hs : Convex ℝ s) (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (curveIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

/-- If `ω` is a closed `1`-form on a convex set `s`, then it admits a primitive,
a version stated in terms of `fderivWithin`. -/
theorem exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric
    (hs : Convex ℝ s) (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a,
      fderivWithin ℝ ω s a x y = fderivWithin ℝ ω s a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a :=
  hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha ↦ (hω a ha).hasFDerivWithinAt) hdω

/-- If `ω` is a closed `1`-form on an open convex set `s`, then it admits a primitive,
a version stated in terms of `fderiv`. -/
theorem exists_forall_hasFDerivAt_of_fderiv_symmetric (hs : Convex ℝ s) (hso : IsOpen s)
    (hω : DifferentiableOn ℝ ω s) (hdω : ∀ a ∈ s, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivAt f (ω a) a := by
  obtain ⟨f, hf⟩ : ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ ↦ ?_
    rw [fderivWithin_eq_fderiv, hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)]
  exact ⟨f, fun a ha ↦ (hf a ha).hasFDerivAt (hso.mem_nhds ha)⟩

end Convex

namespace Convex

variable [CompleteSpace E] {f : 𝕜 → E} {s : Set 𝕜}

/-- If `f : 𝕜 → E`, `𝕜 = ℝ` or `𝕜 = ℂ`, is differentiable on a convex set `s`,
then it admits a primitive. -/
theorem exists_forall_hasDerivWithinAt (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s) :
    ∃ g : 𝕜 → E, ∀ a ∈ s, HasDerivWithinAt g (f a) s a := by
  letI : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  apply hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
  · intro a ha
    exact (ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1).hasFDerivAt
      |>.comp_hasDerivWithinAt a (hf a ha).hasDerivWithinAt |>.restrictScalars ℝ
  · rintro a ha x - y -
    simpa using smul_comm ..

end Convex
