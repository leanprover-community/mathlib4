/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Poincaré lemma for 1-forms

In this file we prove Poincaré lemma for 1-forms for convex sets.
Namely, we show that a closed 1-form on a convex subset of a normed space is exact.

We also prove that the integrals of a closed 1-form
along 2 curves that are joined by a `C²`-smooth homotopy are equal.
 In the future, this will allow us to prove Poincaré lemma for simply connected open sets
and, more generally, for simply connected locally convex sets.

## Main statements

TODO

## Implementation notes

In this file, we represent a 1-form as `ω : E → E →L[𝕜] F`, where `𝕜` is `ℝ` or `ℂ`,
not as `ω : E → E [⋀^Fin 1]→L[𝕜] F`.
A 1-form represented this way is closed
iff its Fréchet derivative `dω : E → E →L[𝕜] E →L[𝕜] F` is symmetric, `dω a x y = dω a y x`.
-/

open scoped unitInterval Interval Pointwise Topology
open AffineMap Filter Function MeasureTheory Set

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {a b c d : E}

namespace ContinuousMap.Homotopy

private theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable_real
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path c d}
    {φ : (γ₁ : C(I, E)).Homotopy γ₂} {s : Set (I × I)} {t : Set E} (hs : s.Countable)
    (hts : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      HasFDerivWithinAt ω (dω <| φ (a, b)) t (φ (a, b))) (hωc : ContinuousOn ω (closure t))
    (hdω_symm : ∀ a ∈ Ioo (0 : I) 1, ∀ b ∈ Ioo (0 : I) 1, (a, b) ∉ s →
      ∀ u ∈ tangentConeAt ℝ t (φ (a, b)), ∀ v ∈ tangentConeAt ℝ t (φ (a, b)),
        dω (φ (a, b)) u v = dω (φ (a, b)) v u)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  -- Let `U` be the interior of the unit square
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
  -- Extend the homotopy `φ` to a continuous map  `ℝ × ℝ → E`
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2 with hψ
  have hψφ : ∀ a b : I, ψ (a, b) = φ (a, b) := by simp [ψ]
  have hψ_cont : Continuous ψ := by fun_prop
  have hψUt : MapsTo ψ U t := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    lift a to I using Ioo_subset_Icc_self ha
    lift b to I using Ioo_subset_Icc_self hb
    simpa [hψφ] using hts a ha b hb
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
      simp only [hs, Path.extend_extends, φ.evalAt_apply]
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
    simp [dη]
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
      with ⟨a, b⟩ hU habs
    lift a to I using Ioo_subset_Icc_self hU.1
    lift b to I using Ioo_subset_Icc_self hU.2
    have hdψ_mem (u) : dψ (a, b) u ∈ tangentConeAt ℝ t (φ (a, b)) := by
      refine tangentConeAt_mono hψUt.image_subset ?_
      rw [← hψφ]
      refine (hdψ _ hU).hasFDerivWithinAt.mapsTo_tangent_cone ?_
      simp [tangentConeAt_of_mem_nhds (hUopen.mem_nhds hU)]
    simp [f', g', dη, hψφ, hdω_symm a hU.1 b hU.2 (by simpa [hmem_s'] using habs)
      _ (hdψ_mem _) _ (hdψ_mem _)]
  suffices ∫ a : ℝ × ℝ in Icc 0 1, f' a (1, 0) + g' a (0, 1) = 0 by
    have hηc : ContinuousOn η (Icc 0 1) := by
      refine .clm_comp (hωc.comp hψ_cont.continuousOn ?_) ?_
      · rw [← hclosure]
        refine MapsTo.closure (fun a ha ↦ ?_) hψ_cont
        lift a to I × I using ⟨Ioo_subset_Icc_self ha.1, Ioo_subset_Icc_self ha.2⟩
        simpa [ψ] using hts a.1 ha.1 a.2 ha.2
      · exact hcontdiff.continuousOn_fderivWithin hunique (by decide)

    rwa [integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le] at this
    · exact zero_le_one
    · exact s'
    · exact hs'c
    · exact hηc.clm_apply continuousOn_const
    · exact hηc.clm_apply continuousOn_const |>.neg
    · exact hf'
    · exact hg'


  rw [← integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le]
/-
  have hdη : ∀ a ∈ U \ (Prod.map (↑) (↑) '' s), HasFDerivAt η (dη a) a := by
    rintro ⟨a, b⟩ ⟨⟨haU, hbU⟩, habs⟩
    lift a to I using Ioo_subset_Icc_self haU
    lift b to I using Ioo_subset_Icc_self hbU
    refine hω (a, b) (by simpa [a.2.1, a.2.2, b.2.1, b.2.2] using habs)
      |>.comp_hasFDerivAt_of_eq ((a : ℝ), (b : ℝ)) (hcontdiff.hasFDerivAt) _ _
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)

  sorry
-/

theorem curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {ω : E → E →L[𝕜] F} {dω : E → E →L[ℝ] E →L[𝕜] F} {γ₁ : Path a b} {γ₂ : Path c d}
    {φ : (γ₁ : C(I, E)).Homotopy γ₂} {s : Set (I × I)} {t : Set E} (hs : s.Countable)
    (hts : ∀ a ∈ Ioo 0 1, ∀ b ∈ Ioo 0 1, φ (a, b) ∈ t)
    (hω : ∀ x ∉ s, HasFDerivWithinAt ω (dω <| φ x) t (φ x)) (hωc : ContinuousOn ω (closure t))
    (hdω : ∀ x ∉ s, ∀ a ∈ tangentConeAt ℝ t (φ x), ∀ b ∈ tangentConeAt ℝ t (φ x),
      dω (φ x) a b = dω (φ x) b a)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (I ×ˢ I)) :
    ∫ᶜ x in γ₁, ω x + ∫ᶜ x in φ.evalAt 1, ω x = ∫ᶜ x in γ₂, ω x + ∫ᶜ x in φ.evalAt 0, ω x := by
  sorry

#exit

theorem ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_of_contDiffOn
    {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F} {γ₁ : Path a b} {γ₂ : Path c d} {s : Set E}
    (φ : (γ₁ : C(I, E)).Homotopy γ₂) (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ x ∈ s, ∀ a ∈ tangentConeAt ℝ s x, ∀ b ∈ tangentConeAt ℝ s x, dω x a b = dω x b a)
    (hφs : ∀ a, φ a ∈ s)
    (hF : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2)
      (I ×ˢ I)) :
    curveIntegral ω γ₁ + curveIntegral ω (φ.evalAt 1) =
      curveIntegral ω γ₂ + curveIntegral ω (φ.evalAt 0) := by
  set ψ : ℝ × ℝ → E := fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2
  have hψs : ∀ a, ψ a ∈ s := fun _ ↦ hφs _
  set U : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo 0 1 with hU
  have hUI' : interior (Icc 0 1) = U := by
    rw [hU, ← interior_Icc, ← interior_prod_eq, Icc_prod_Icc]
    rfl
  have hUI : U ⊆ Icc 0 1 := hUI' ▸ interior_subset
  have hId : UniqueDiffOn ℝ (Icc 0 1 : Set (ℝ × ℝ)) := by
    rw [Icc_prod_eq]
    exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  set dψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fderivWithin ℝ ψ (Icc 0 1)
  set d2ψ : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] E := fderivWithin ℝ dψ (Icc 0 1)
  rw [Icc_prod_Icc, Prod.mk_zero_zero, Prod.mk_one_one] at hF
  have hψ : ∀ a ∈ U, HasFDerivAt ψ (dψ a) a := fun a ha ↦
    hF.differentiableOn (by decide) a (hUI ha) |>.hasFDerivWithinAt
      |>.hasFDerivAt <| mem_of_superset (hUo.mem_nhds ha) hUI
  have hψc : Continuous ψ := by simp only [ψ]; fun_prop
  have hdψ : DifferentiableOn ℝ dψ (Icc 0 1) :=
    (hF.fderivWithin hId le_rfl).differentiableOn le_rfl
  have hdψIoo : ∀ a ∈ Ioo 0 1 ×ˢ Ioo 0 1, HasFDerivAt dψ (d2ψ a) a := fun a ha ↦ by
    refine hdψ _ (hUI ha) |>.hasFDerivWithinAt |>.hasFDerivAt ?_
    exact mem_of_superset (hUo.mem_nhds ha) hUI
  set η : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ω (ψ a) ∘L dψ a
  set dη : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ →L[ℝ] F := fun a ↦
    .compL ℝ (ℝ × ℝ) E F (ω (ψ a)) ∘L d2ψ a + (dω (ψ a)).bilinearComp (dψ a) (dψ a)
  have hηc : ContinuousOn η (Icc 0 1) := by
    refine .clm_comp (.comp (t := s) ?_ ?_ ?_) ?_
    · exact fun x hx ↦ (hω x hx).continuousWithinAt
    · exact hψc.continuousOn
    · exact fun _ _ ↦ hψs _
    · exact hdψ.continuousOn
  have hη : ∀ a ∈ U, HasFDerivAt η (dη a) a := by
    rintro a ha
    have := (hω (ψ a) (hψs _)).comp_hasFDerivAt a (hψ a ha) (.of_forall fun _ ↦ hψs _)
    exact this.clm_comp (hdψIoo a ha)
  set f : ℝ × ℝ → F := fun a ↦ η a (0, 1)
  set g : ℝ × ℝ → F := fun a ↦ -η a (1, 0)
  set f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ ContinuousLinearMap.apply ℝ F (0, 1) ∘L dη a
  set g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] F := fun a ↦ -(ContinuousLinearMap.apply ℝ F (1, 0) ∘L dη a)
  have hd2ψ_symm : ∀ a ∈ Icc 0 1, ∀ x y, d2ψ a x y = d2ψ a y x := by
    intro a ha x y
    simp only [d2ψ, dψ]
    apply Convex.second_derivative_within_at_symmetric (convex_Icc 0 1)
    · simp [hUI', U]
    · simpa only [hUI']
    · exact ha
    · exact (hdψ _ ha).hasFDerivWithinAt.mono interior_subset
  have hdη_symm : ∀ a ∈ Icc 0 1, ∀ x y, dη a x y = dη a y x := by
    intro a ha
    set S := Submodule.span ℝ (tangentConeAt ℝ s (ψ a))
    have H₁ : ∀ x ∈ S, ∀ y ∈ S, dω (ψ a) x y = dω (ψ a) y x := by
      intro x hx y hy
      induction hx, hy using Submodule.span_induction₂ with
      | mem_mem x y hx hy => exact hdω (ψ a) (hψs a) _ hx _ hy
      | zero_left => simp
      | zero_right => simp
      | add_left => simp [*]
      | add_right => simp [*]
      | smul_left => simp [*]
      | smul_right => simp [*]
    have H₂ (z): dψ a z ∈ S := by
      have := (hF.differentiableOn (by decide) a ha).hasFDerivWithinAt.mapsTo_tangent_cone
      refine (this.mono_right ?_).submoduleSpan ?_
      · exact tangentConeAt_mono (image_subset_iff.2 fun _ _ ↦ hψs _)
      · rw [(convex_Icc _ _).span_tangentConeAt] <;> try simp [hUI', hU, ha]
    intro x y
    simp [dη, H₁ _ (H₂ x) _ (H₂ y), hd2ψ_symm a ha x y]
  have hdiv : EqOn (fun a : ℝ × ℝ ↦ f' a (1, 0) + g' a (0, 1)) 0 (Icc 0 1) := by
    intro a ha
    simp [f', g', hdη_symm a ha (1, 0)]
  have := integral_divergence_prod_Icc_of_hasFDerivAt_of_le f g f' g' 0 1 zero_le_one
    (hηc.clm_apply continuousOn_const) (hηc.clm_apply continuousOn_const).neg
    (fun a ha ↦ by exact (ContinuousLinearMap.apply ℝ F (0, 1)).hasFDerivAt.comp a (hη a ha))
    (fun a ha ↦ by exact ((ContinuousLinearMap.apply ℝ F (1, 0)).hasFDerivAt.comp a (hη a ha)).neg)
    ?_
  · rw [setIntegral_congr_fun measurableSet_Icc hdiv, integral_zero'] at this
    have hφ₀ : φ.extend 0 = γ₁ := by
      ext
      apply φ.extend_apply_of_le_zero le_rfl
    have hfi (s : ℝ) (hs : s ∈ I) :
        ∫ t in 0..1, f (s, t) = curveIntegral ω ⟨φ.extend s, rfl, rfl⟩ := by
      rw [curveIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [ContinuousLinearMap.comp_apply, curveIntegralFun, f, η, dψ]
      congr 1
      have : HasDerivWithinAt (fun u : ℝ ↦ ((s : ℝ), u)) (0, 1) I t :=
        (hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_id _ _)
      rw [← this.derivWithin (uniqueDiffOn_Icc_zero_one _ ht), ← fderivWithin_comp_derivWithin]
      · rfl
      · refine hF.differentiableOn (by decide) _ ?_
        rw [← Icc_prod_Icc]
        exact ⟨hs, ht⟩
      · exact this.differentiableWithinAt
      · intro u hu
        rw [← Icc_prod_Icc]
        exact ⟨hs, hu⟩
    have hf₀ : ∫ t in 0..1, f (0, t) = curveIntegral ω γ₁ := by
      rw [hfi 0 (by simp)]
      simp [curveIntegral, curveIntegralFun, Path.extend]
    have hf₁ : ∫ t in 0..1, f (1, t) = curveIntegral ω γ₂ := by
      rw [hfi 1 (by simp)]
      simp [curveIntegral, curveIntegralFun, Path.extend]
    have hgt (s : I) : curveIntegral ω (φ.evalAt s) = -∫ t in 0..1, g (t, s) := by
      rw [← intervalIntegral.integral_neg, curveIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      simp only [ContinuousLinearMap.comp_apply, curveIntegralFun, g, η, dψ, neg_neg]
      congr 1
      · simp [ψ]
      · have : HasDerivWithinAt (fun u : ℝ ↦ (u, (s : ℝ))) (1, 0) I t :=
          (hasDerivWithinAt_id _ _).prodMk (hasDerivWithinAt_const _ _ _)
        rw [← this.derivWithin (uniqueDiffOn_Icc_zero_one _ ht),
          ← fderivWithin_comp_derivWithin (f := (·, s.1))]
        · simp [comp_def, ψ]
        · refine hF.differentiableOn (by decide) _ ?_
          rw [← Icc_prod_Icc]
          exact ⟨ht, s.2⟩
        · exact this.differentiableWithinAt
        · intro u hu
          rw [← Icc_prod_Icc]
          exact ⟨hu, s.2⟩
    rw [← hf₀, ← hf₁, hgt, hgt]
    linear_combination (norm := {dsimp; abel}) this
  · rw [integrableOn_congr_fun hdiv measurableSet_Icc]
    exact integrableOn_zero

theorem hasFDerivWithinAt_curveIntegral_segment_target_source {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace F] {a : E}
    {ω : E → E →L[𝕜] F} {s : Set E} (hs : Convex ℝ s) (hω : ContinuousOn ω s) (ha : a ∈ s) :
    HasFDerivWithinAt (curveIntegral (ω · |>.restrictScalars ℝ) <| .segment a ·) (ω a) s a := by
  simp only [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO, Path.segment_same,
    curveIntegral_refl, sub_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  rcases Metric.continuousWithinAt_iff.mp (hω a ha) ε hε with ⟨δ, hδ₀, hδ⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds _ hδ₀] with b hb hbs
  have : ∫ t in 0..1, ω a (b - a) = ω a (b - a) := by simp
  rw [curveIntegral_segment, ← this, ← intervalIntegral.integral_sub]
  · suffices ∀ t ∈ Ι (0 : ℝ) 1, ‖ω (lineMap a b t) (b - a) - ω a (b - a)‖ ≤ ε * ‖b - a‖ by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const this).trans_eq ?_
      simp
    intro t ht
    replace ht : t ∈ I := by
      rw [uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    rw [← ContinuousLinearMap.sub_apply]
    apply ContinuousLinearMap.le_of_opNorm_le
    refine (hδ (hs.lineMap_mem ha hbs ht) ?_).le
    rw [dist_lineMap_left, Real.norm_of_nonneg ht.1]
    refine lt_of_le_of_lt ?_ hb
    rw [dist_comm]
    exact mul_le_of_le_one_left dist_nonneg ht.2
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.clm_apply ?_ continuousOn_const
    apply (ContinuousLinearMap.continuous_restrictScalars _).comp_continuousOn
    refine hω.comp ?_ ?_
    · simp only [AffineMap.coe_lineMap]
      fun_prop
    · exact fun _ ↦ hs.lineMap_mem ha hbs
  · simp

theorem Convex.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric
    {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    curveIntegral ω (.segment a b) + curveIntegral ω (.segment b c) =
      curveIntegral ω (.segment a c) := by
  set φ := ContinuousMap.Homotopy.affine (Path.segment a b : C(I, E)) (Path.segment a c)
  have := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_of_contDiffOn hω hdω ?_ ?_
  · convert this using 2
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_one a b) (lineMap_apply_one a c), curveIntegral_cast]
    · dsimp [φ]
      rw [← Path.cast_segment (lineMap_apply_zero a b) (lineMap_apply_zero a c)]
      simp
  · simp [Convex.lineMap_mem, φ, *]
  · have : EqOn (fun x : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend x.1) x.2)
        (fun x ↦ lineMap (lineMap a b x.2) (lineMap a c x.2) x.1) (I ×ˢ I) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to I using hx
      lift y to I using hy
      simp [φ]
    refine .congr ?_ this
    -- TODO: add `ContDiff.lineMap` etc
    simp only [AffineMap.lineMap_apply_module]
    fun_prop

theorem Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    [CompleteSpace F] {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x)
    (ha : a ∈ s) (hb : b ∈ s) :
    HasFDerivWithinAt (fun x ↦ curveIntegral ω (.segment a x)) (ω b) s b := by
  suffices HasFDerivWithinAt (fun x ↦
      curveIntegral ω (.segment a b) + curveIntegral ω (.segment b x)) (ω b) s b from
    this.congr' (fun _ h ↦
      (hs.curveIntegral_segment_add_eq_of_hasFDerivWithinAt_symmetric hω hdω ha hb h).symm) hb
  exact .const_add _ <| hasFDerivWithinAt_curveIntegral_segment_target_source hs
    (fun x hx ↦ (hω x hx).continuousWithinAt) hb

theorem Convex.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} {dω : E → E →L[ℝ] E →L[ℝ] F}
    (hω : ∀ x ∈ s, HasFDerivWithinAt ω (dω x) s x)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a, dω a x y = dω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · use (curveIntegral ω <| .segment a ·)
    intro b hb
    exact hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric hω hdω ha hb

theorem Convex.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) {ω : E → E →L[ℝ] F} (hω : DifferentiableOn ℝ ω s)
    (hdω : ∀ a ∈ s, ∀ x ∈ tangentConeAt ℝ s a, ∀ y ∈ tangentConeAt ℝ s a,
      fderivWithin ℝ ω s a x y = fderivWithin ℝ ω s a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a :=
  hs.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric
    (fun a ha ↦ (hω a ha).hasFDerivWithinAt) hdω

theorem Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric [CompleteSpace F]
    {s : Set E} (hs : Convex ℝ s) (hso : IsOpen s) {ω : E → E →L[ℝ] F}
    (hω : DifferentiableOn ℝ ω s) (hdω : ∀ a ∈ s, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f, ∀ a ∈ s, HasFDerivAt f (ω a) a := by
  obtain ⟨f, hf⟩ : ∃ f, ∀ a ∈ s, HasFDerivWithinAt f (ω a) s a := by
    refine hs.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric hω fun a ha x _ y _ ↦ ?_
    rw [fderivWithin_eq_fderiv, hdω a ha]
    exacts [hso.uniqueDiffOn a ha, hω.differentiableAt (hso.mem_nhds ha)]
  exact ⟨f, fun a ha ↦ (hf a ha).hasFDerivAt (hso.mem_nhds ha)⟩
