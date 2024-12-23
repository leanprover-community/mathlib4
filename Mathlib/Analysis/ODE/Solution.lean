/-
Copyright (c) 2024 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.MetricSpace.Contracting

open Function Metric Set Topology
open MeasureTheory.MeasureSpace (volume)
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- this will be proven to be unique on s under conditions on `v` and `s`
structure ODESolution (v : ℝ → E → E) (t₀ : ℝ) (s : Set ℝ) (x₀ : E) where
  toFun : ℝ → E
  isConnected_domain : IsConnected s -- all intervals or singleton
  mem_domain : t₀ ∈ s
  initial : toFun t₀ = x₀
  hasDerivWithinAt : ∀ t ∈ s, HasDerivWithinAt toFun (v t (toFun t)) s t

def LocalFlow (v : ℝ → E → E) (t₀ : ℝ) (s : Set ℝ) (u : Set E) :=
  (x₀ : E) → (hx : x₀ ∈ u) → ODESolution v t₀ s x₀

/-- `Prop` structure holding the hypotheses of the Picard-Lindelöf theorem.

The similarly named `PicardLindelof` structure is part of the internal API for convenience, so as
not to constantly invoke choice, but is not intended for public use. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E] (v : ℝ → E → E) (tMin t₀ tMax : ℝ)
    (x₀ : E) (L : ℝ≥0) (R C : ℝ) : Prop where
  ht₀ : t₀ ∈ Icc tMin tMax
  hR : 0 ≤ R
  lipschitz : ∀ t ∈ Icc tMin tMax, LipschitzOnWith L (v t) (closedBall x₀ R)
  cont : ∀ x ∈ closedBall x₀ R, ContinuousOn (fun t : ℝ => v t x) (Icc tMin tMax)
  norm_le : ∀ t ∈ Icc tMin tMax, ∀ x ∈ closedBall x₀ R, ‖v t x‖ ≤ C
  C_mul_le_R : (C : ℝ) * max (tMax - t₀) (t₀ - tMin) ≤ R

/-- This structure holds arguments of the Picard-Lipschitz (Cauchy-Lipschitz) theorem. It is part of
the internal API for convenience, so as not to constantly invoke choice. Unless you want to use one
of the auxiliary lemmas, use `IsPicardLindelof.exists_forall_hasDerivWithinAt_Icc_eq` instead
of using this structure.

The similarly named `IsPicardLindelof` is a bundled `Prop` holding the long hypotheses of the
Picard-Lindelöf theorem as named arguments. It is used as part of the public API.
-/
structure PicardLindelofData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E → E
  (t₀ tmin tmax : ℝ)
  ht₀ : t₀ ∈ Icc tmin tmax
  x₀ : E
  (C R L : ℝ≥0)
  isPicardLindelof : IsPicardLindelof toFun tmin t₀ tmax x₀ L R C

namespace PicardLindelofData

variable (v : PicardLindelofData E)

instance : CoeFun (PicardLindelofData E) fun _ ↦ ℝ → E → E := ⟨toFun⟩

instance : Inhabited (PicardLindelofData E) :=
  ⟨⟨0, 0, 0, 0, ⟨le_rfl, le_rfl⟩, 0, 0, 0, 0,
      { ht₀ := by rw [Icc_self]; exact mem_singleton _
        hR := le_rfl
        lipschitz := fun _ _ => (LipschitzWith.const 0).lipschitzOnWith
        cont := fun _ _ => by simpa only [Pi.zero_apply] using continuousOn_const
        norm_le := fun _ _ _ _ => norm_zero.le
        C_mul_le_R := (zero_mul _).le }⟩⟩

-- convenience lemmas
lemma tmin_le_tmax : v.tmin ≤ v.tmax := v.ht₀.1.trans v.ht₀.2

-- lemma nonempty_Icc

-- lemma lipschitzOnWith

lemma continuousOn_Icc_prod_closedBall :
    ContinuousOn (uncurry v) (Icc v.tmin v.tmax ×ˢ closedBall v.x₀ v.R) :=
  have : ContinuousOn (uncurry (flip v)) (closedBall v.x₀ v.R ×ˢ Icc v.tmin v.tmax) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ v.L v.isPicardLindelof.cont
      v.isPicardLindelof.lipschitz
  this.comp continuous_swap.continuousOn (preimage_swap_prod _ _).symm.subset

-- why closedBall? able to extend to boundary?
-- this can be derived from lipschitz condition on f
lemma continuousOn_Icc {f : ℝ → E} (hcont : ContinuousOn f (Icc v.tmin v.tmax))
    (hball : ∀ t ∈ Icc v.tmin v.tmax, f t ∈ closedBall v.x₀ v.R) :
    ContinuousOn (fun t ↦ v t (f t)) (Icc v.tmin v.tmax) := by
  have : (fun t ↦ v t (f t)) = (uncurry v) ∘ fun t ↦ (t, (f t)) := rfl
  rw [this]
  apply v.continuousOn_Icc_prod_closedBall.comp <| continuousOn_id.prod hcont
  intro t ht
  exact ⟨ht, hball t ht⟩

lemma intervalIntegrable {f : ℝ → E} (hcont : ContinuousOn f (Icc v.tmin v.tmax))
    (hball : ∀ t ∈ Icc v.tmin v.tmax, f t ∈ closedBall v.x₀ v.R) {t₁ t₂ : ℝ}
    (ht₁ : t₁ ∈ Icc v.tmin v.tmax) (ht₂ : t₂ ∈ Icc v.tmin v.tmax) :
    IntervalIntegrable (fun t ↦ v t (f t)) volume t₁ t₂ :=
  v.continuousOn_Icc hcont hball |>.mono (uIcc_subset_Icc ht₁ ht₂) |>.intervalIntegrable

lemma stronglyMeasurableAtFilter {f : ℝ → E} (hcont : ContinuousOn f (Icc v.tmin v.tmax))
    (hball : ∀ t ∈ Icc v.tmin v.tmax, f t ∈ closedBall v.x₀ v.R) {t : ℝ} :
    StronglyMeasurableAtFilter (fun t ↦ v t (f t)) (𝓝[Icc v.tmin v.tmax] t) volume :=
  v.continuousOn_Icc hcont hball |>.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc _

def odesolutionOfIntegral [CompleteSpace E] {f : ℝ → E} (hcont : ContinuousOn f (Icc v.tmin v.tmax))
    (hball : ∀ t ∈ Icc v.tmin v.tmax, f t ∈ closedBall v.x₀ v.R)
    (hf : ∀ t ∈ Icc v.tmin v.tmax, f t = v.x₀ + ∫ τ in v.t₀..t, v τ (f τ)) :
    ODESolution v v.t₀ (Icc v.tmin v.tmax) v.x₀ where
  toFun := f
  isConnected_domain := isConnected_Icc v.tmin_le_tmax
  mem_domain := v.ht₀
  initial := by simpa using hf v.t₀ v.ht₀
  hasDerivWithinAt t ht := by
    refine HasDerivWithinAt.congr ?_ hf (hf t ht)
    apply HasDerivWithinAt.const_add
    haveI : Fact (t ∈ Icc v.tmin v.tmax) := ⟨ht⟩
    exact intervalIntegral.integral_hasDerivWithinAt_right
      (v.intervalIntegrable hcont hball v.ht₀ ht)
      (v.stronglyMeasurableAtFilter hcont hball)
      (v.continuousOn_Icc hcont hball t ht)

end PicardLindelofData
