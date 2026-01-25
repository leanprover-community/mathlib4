/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Snowflaking of a metric space

Given a (pseudo) (extended) metric space `X` and a number `0 < α ≤ 1`,
one can consider the metric given by `d x y = (dist x y) ^ α`.
The metric space determined by this new metric is said to be the `α`-snowflaking  (or `α`-snowflake)
of `X`. In this file we define `Metric.Snowflaking X α hα₀ hα₁` to be a one-field structure wrapper
around `X` with metric given by this formula.

The use of the term *snowflaking* arises from the fact that if one chooses `X := Set.Icc 0 1` and
`α := log 3 / log 4`, then `Metric.Snowflaking X α … …` is isometric to the von Koch snowflake,
where we equip that space with the natural metric induced by the `α⁻¹`-Hausdorff measure of paths.

Snowflake metrics are used regularly in the geometry of metric spaces where, among other things,
they characterize doubling metrics. In particular, a metric is doubling if and only
if every `α`-snowflaking (with `0 < α < 1`) of it is bilipschitz equivalent to a subset of some
Euclidean space (the dimension of the Euclidean space depends on `α`). See [heinonen2001].

Another reason to introduce this definition is the following.
In the proof of his version of the Morse-Sard theorem,
Moreira [Moreira2001] studies maps of two variables that are Lipschitz continuous in one variable,
but satisfy a stronger assumption `‖f (a, y) - f (a, b)‖ = O(‖y - b‖ ^ (k + α))`
along the second variable, as long as `(a, b)` is one of the "interesting" points.

If we want to apply Vitali covering theorem in this context, we need to cover the set by products
`closedBall a (R ^ (k + α)) ×ˢ closedBall b R` so that both components make a similar contribution
to `‖f (x, y) - f (a, b)‖`. These sets aren't balls in the original metric
(or even subsets of balls that occupy at least a fixed fraction of the volume,
as we require in our version of Vitali theorem).

However, if we change the metric on the first component to the one introduced in this file,
then these sets become balls, and we can apply Vitali theorem.

## References
* [Carlos Gustavo T. de A. Moreira, _Hausdorff measures and the Morse-Sard theorem_]
  [Moreira2001]
-/

@[expose] public section

open scoped ENNReal NNReal Filter Uniformity Topology
open Function

noncomputable section

namespace Metric

/-- A copy of a type with metric given by `dist x y = (dist x.val y.val) ^ α`.

This is defined as a one-field structure. -/
@[ext]
structure Snowflaking (X : Type*) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) where
  /-- The value wrapped in `x : Snowflaking X α hα₀ hα₁`. -/
  val : X

namespace Snowflaking

variable {X : Type*} {α : ℝ} {hα₀ : 0 < α} {hα₁ : α ≤ 1}

/-- The natural equivalence between `Snowflaking X α hr₀ hr₁` and `X`. -/
def ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- The natural equivalence between `X` and `Snowflaking X α hr₀ hr₁`. -/
def toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁ := ofSnowflaking.symm

@[simp]
theorem toSnowflaking.sizeOf_spec [SizeOf X] (x : X) :
    sizeOf (toSnowflaking x : Snowflaking X α hα₀ hα₁) = 1 + sizeOf x :=
  rfl

attribute [nolint simpNF] mk.injEq mk.sizeOf_spec

/-- This definition makes `cases x` and `induction x` use `toSnowflaking` instead of `mk`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def casesOn_toSnowflaking {motive : Snowflaking X α hα₀ hα₁ → Sort*}
    (toSnowflaking : ∀ x, motive (Snowflaking.toSnowflaking x)) (x : Snowflaking X α hα₀ hα₁) :
    motive x :=
  toSnowflaking x.val

@[simp]
theorem mk_eq_toSnowflaking : (mk : X → Snowflaking X α hα₀ hα₁) = toSnowflaking := rfl

@[simp]
theorem val_eq_ofSnowflaking : (val : Snowflaking X α hα₀ hα₁ → X) = ofSnowflaking := rfl

@[simp]
theorem symm_toSnowflaking :
    (toSnowflaking : X ≃ Snowflaking X α hα₀ hα₁).symm = ofSnowflaking :=
  rfl

@[simp]
theorem symm_ofSnowflaking :
    (ofSnowflaking : Snowflaking X α hα₀ hα₁ ≃ X).symm = toSnowflaking :=
  rfl

@[simp]
theorem toSnowflaking_ofSnowflaking (x : Snowflaking X α hα₀ hα₁) :
    toSnowflaking x.ofSnowflaking = x :=
  rfl

@[simp]
theorem ofSnowflaking_toSnowflaking (x : X) :
    (toSnowflaking x : Snowflaking X α hα₀ hα₁).ofSnowflaking = x :=
  rfl

@[simp]
theorem ofSnowflaking_comp_toSnowflaking :
    (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) ∘ toSnowflaking = id :=
  rfl

@[simp]
theorem toSnowflaking_comp_ofSnowflaking :
    (toSnowflaking : X → Snowflaking X α hα₀ hα₁) ∘ ofSnowflaking = id :=
  rfl

theorem image_toSnowflaking_eq_preimage (s : Set X) :
    (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = ofSnowflaking ⁻¹' s :=
  toSnowflaking.image_eq_preimage_symm _

theorem image_ofSnowflaking_eq_preimage (s : Set (Snowflaking X α hα₀ hα₁)) :
    ofSnowflaking '' s = toSnowflaking ⁻¹' s :=
  ofSnowflaking.image_eq_preimage_symm _

@[simp]
theorem image_toSnowflaking_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    toSnowflaking '' (ofSnowflaking '' s) = s :=
  ofSnowflaking.symm_image_image _

@[simp]
theorem image_ofSnowflaking_image_toSnowflaking (s : Set X) :
    ofSnowflaking '' (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = s :=
  ofSnowflaking.image_symm_image _

/-!
### Topological space structure

The topology on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section TopologicalSpace

variable [TopologicalSpace X]

/-- The topological space structure on `Snowflaking X α _ _` is induced from the original space. -/
instance : TopologicalSpace (Snowflaking X α hα₀ hα₁) := .induced Snowflaking.ofSnowflaking ‹_›

@[fun_prop]
theorem continuous_ofSnowflaking : Continuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_toSnowflaking : Continuous (toSnowflaking : X → Snowflaking X α hα₀ hα₁) :=
  continuous_induced_rng.2 continuous_id

/-- The natural homeomorphism between `Snowflaking X α hα₀ hα₁` and `X`. -/
@[simps! -fullyApplied toEquiv apply symm_apply]
def homeomorph : Snowflaking X α hα₀ hα₁ ≃ₜ X where
  toEquiv := ofSnowflaking
  continuous_invFun := continuous_toSnowflaking

/-!
We copy some instances from the underlying space `X` to `Snowflaking X α hα₀ hα₁`.
In the future, we can add more of them, if needed,
or even copy all the topology-related classes, if we get a tactic to do it automatically.
-/

instance [T0Space X] : T0Space (Snowflaking X α hα₀ hα₁) :=
  homeomorph.symm.t0Space

instance [T2Space X] : T2Space (Snowflaking X α hα₀ hα₁) :=
  homeomorph.symm.t2Space

instance [SecondCountableTopology X] : SecondCountableTopology (Snowflaking X α hα₀ hα₁) :=
  homeomorph.secondCountableTopology

end TopologicalSpace

/-!
### Bornology

The bornology on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section Bornology

variable [Bornology X]

instance : Bornology (Snowflaking X α hα₀ hα₁) := .induced ofSnowflaking

open Bornology

@[simp]
theorem isBounded_image_ofSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
    IsBounded (ofSnowflaking '' s) ↔ IsBounded s :=
  isBounded_induced.symm

@[simp]
theorem isBounded_preimage_toSnowflaking_iff {s : Set (Snowflaking X α hα₀ hα₁)} :
    IsBounded (toSnowflaking ⁻¹' s) ↔ IsBounded s := by
  rw [← image_ofSnowflaking_eq_preimage, isBounded_image_ofSnowflaking_iff]

@[simp]
theorem isBounded_image_toSnowflaking_iff {s : Set X} :
    IsBounded (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← isBounded_image_ofSnowflaking_iff, image_ofSnowflaking_image_toSnowflaking]

@[simp]
theorem isBounded_preimage_ofSnowflaking_iff {s : Set X} :
    IsBounded (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) ↔ IsBounded s := by
  rw [← image_toSnowflaking_eq_preimage, isBounded_image_toSnowflaking_iff]

end Bornology

/-!
### Uniform space structure

The uniform space structure on `Snowflaking X α hα₀ hα₁` is induced from `X`.
-/

section UniformSpace

variable [UniformSpace X]

instance : UniformSpace (Snowflaking X α hα₀ hα₁) :=
  UniformSpace.comap Snowflaking.ofSnowflaking ‹_›

theorem uniformContinuous_ofSnowflaking :
    UniformContinuous (ofSnowflaking : Snowflaking X α hα₀ hα₁ → X) :=
  uniformContinuous_comap

theorem uniformContinuous_toSnowflaking :
    UniformContinuous (toSnowflaking : X → Snowflaking X α hα₀ hα₁) :=
  uniformContinuous_comap' uniformContinuous_id

/-- The natural uniform space equivalence between `Snowflaking X α hα hα₁`
and the underlying space. -/
@[simps! toEquiv apply symm_apply]
def uniformEquiv : Snowflaking X α hα₀ hα₁ ≃ᵤ X where
  toEquiv := ofSnowflaking
  uniformContinuous_toFun := uniformContinuous_ofSnowflaking
  uniformContinuous_invFun := uniformContinuous_toSnowflaking

end UniformSpace

/-!
### Extended distance and a (pseudo) extended metric space structure

Th extended distance on `Snowflaking X α hα₀ hα₁`
is given by `edist x y = (edist x.ofSnowflaking y.ofSnowflaking) ^ α`.

If the original space is a (pseudo) extended metric space, then so is `Snowflaking X α hα₀ hα₁`.
-/

section EDist

variable [EDist X]

instance : EDist (Snowflaking X α hα₀ hα₁) where
  edist x y := edist x.ofSnowflaking y.ofSnowflaking ^ α

theorem edist_def (x y : Snowflaking X α hα₀ hα₁) :
    edist x y = edist x.ofSnowflaking y.ofSnowflaking ^ α :=
  rfl

@[simp]
theorem edist_toSnowflaking_toSnowflaking (x y : X) :
    edist (toSnowflaking x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = edist x y ^ α :=
  rfl

@[simp]
theorem edist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) :
    edist x.ofSnowflaking y.ofSnowflaking = edist x y ^ α⁻¹ := by
  rw [edist_def, ENNReal.rpow_rpow_inv hα₀.ne']

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace X]

instance : PseudoEMetricSpace (Snowflaking X α hα₀ hα₁) where
  edist_self x := by simp [edist_def, hα₀]
  edist_comm x y := by rw [edist_def, edist_def, edist_comm]
  edist_triangle x y z := by
    simp only [edist_def]
    grw [edist_triangle x.ofSnowflaking y.ofSnowflaking z.ofSnowflaking,
      ENNReal.rpow_add_le_add_rpow _ _ hα₀.le hα₁]
  toUniformSpace := inferInstance
  uniformity_edist := by
    have H : (𝓤 X).HasBasis (0 < ·) fun x => {p | edist p.1 p.2 < x ^ (α⁻¹)} := by
      refine EMetric.mk_uniformity_basis (fun _ _ ↦ by positivity) fun ε hε ↦
        ⟨ε ^ α, by positivity, ?_⟩
      rw [ENNReal.rpow_rpow_inv hα₀.ne']
    simp (disch := positivity) [uniformity_comap, H.eq_biInf, ENNReal.rpow_lt_rpow_iff]

@[simp]
theorem preimage_ofSnowflaking_emetricBall (x : X) (r : ℝ≥0∞) :
    ofSnowflaking ⁻¹' EMetric.ball x r =
      EMetric.ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_lt_rpow_iff]

@[simp]
theorem image_toSnowflaking_emetricBall (x : X) (r : ℝ≥0∞) :
    toSnowflaking '' EMetric.ball x r =
      EMetric.ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_emetricBall]

@[simp]
theorem preimage_toSnowflaking_emetricBall (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    toSnowflaking ⁻¹' EMetric.ball x d = EMetric.ball x.ofSnowflaking (d ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_emetricBall,
    toSnowflaking_ofSnowflaking, ENNReal.rpow_inv_rpow hα₀.ne']

@[simp]
theorem image_ofSnowflaking_emetricBall (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    ofSnowflaking '' EMetric.ball x d = EMetric.ball x.ofSnowflaking (d ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_emetricBall]

@[simp]
theorem preimage_ofSnowflaking_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    ofSnowflaking ⁻¹' EMetric.closedBall x r =
      EMetric.closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [ENNReal.rpow_le_rpow_iff]

@[simp]
theorem image_toSnowflaking_emetricClosedBall (x : X) (r : ℝ≥0∞) :
    toSnowflaking '' EMetric.closedBall x r =
      EMetric.closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_emetricClosedBall]

@[simp]
theorem preimage_toSnowflaking_emetricClosedBall (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    toSnowflaking ⁻¹' EMetric.closedBall x d = EMetric.closedBall x.ofSnowflaking (d ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_emetricClosedBall,
    toSnowflaking_ofSnowflaking, ENNReal.rpow_inv_rpow hα₀.ne']

@[simp]
theorem image_ofSnowflaking_emetricClosedBall (x : Snowflaking X α hα₀ hα₁) (d : ℝ≥0∞) :
    ofSnowflaking '' EMetric.closedBall x d =
      EMetric.closedBall x.ofSnowflaking (d ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_emetricClosedBall]

@[simp]
theorem ediam_image_ofSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    ediam (ofSnowflaking '' s) = ediam s ^ α⁻¹ := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [ENNReal.rpow_inv_le_iff hα₀, ediam_le_iff, Set.forall_mem_image,
    edist_ofSnowflaking_ofSnowflaking]

@[simp]
theorem ediam_preimage_toSnowflaking (s : Set (Snowflaking X α hα₀ hα₁)) :
    ediam (toSnowflaking ⁻¹' s) = ediam s ^ α⁻¹ := by
  rw [← image_ofSnowflaking_eq_preimage, ediam_image_ofSnowflaking]

@[simp]
theorem ediam_preimage_ofSnowflaking (s : Set X) :
    ediam (ofSnowflaking ⁻¹' s : Set (Snowflaking X α hα₀ hα₁)) = ediam s ^ α := by
  rw [← ENNReal.rpow_inv_rpow hα₀.ne' (ediam _), ← ediam_preimage_toSnowflaking,
    ← Set.preimage_comp, ofSnowflaking_comp_toSnowflaking, Set.preimage_id]

@[simp]
theorem ediam_image_toSnowflaking (s : Set X) :
    ediam (toSnowflaking '' s : Set (Snowflaking X α hα₀ hα₁)) = ediam s ^ α := by
  simp [image_toSnowflaking_eq_preimage]

end PseudoEMetricSpace

instance [EMetricSpace X] : EMetricSpace (Snowflaking X α hα₀ hα₁) :=
  .ofT0PseudoEMetricSpace _

/-!
### Distance and a (pseudo) metric space structure

Th extended distance on `Snowflaking X α hα₀ hα₁`
is given by `dist x y = (dist x.ofSnowflaking y.ofSnowflaking) ^ α`.

If the original space is a (pseudo) metric space, then so is `Snowflaking X α hα₀ hα₁`.
-/

instance [Dist X] : Dist (Snowflaking X α hα₀ hα₁) where
  dist x y := dist x.ofSnowflaking y.ofSnowflaking ^ α

@[simp]
theorem dist_toSnowflaking_toSnowflaking [Dist X] (x y : X) :
    dist (toSnowflaking x : Snowflaking X α hα₀ hα₁) (toSnowflaking y) = dist x y ^ α :=
  rfl

section PseudoMetricSpace

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
  letI aux : PseudoMetricSpace (Snowflaking X α hα₀ hα₁) :=
    PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
      (by intro x y; cases x; cases y; rw [dist_toSnowflaking_toSnowflaking]; positivity)
      (by
        intro x y; cases x; cases y
        rw [edist_toSnowflaking_toSnowflaking, dist_toSnowflaking_toSnowflaking,
          ← ENNReal.ofReal_rpow_of_nonneg, ← edist_dist] <;> positivity)
  aux.replaceBornology fun s ↦ by
    rw [← isBounded_preimage_toSnowflaking_iff, Metric.isBounded_iff, Metric.isBounded_iff]
    constructor
    · rintro ⟨C, hC⟩
      use C ^ α
      rintro ⟨x⟩ hx ⟨y⟩ hy
      grw [mk_eq_toSnowflaking, dist_toSnowflaking_toSnowflaking, hC hx hy]
    · rintro ⟨C, hC⟩
      use C ^ α⁻¹
      intro x hx y hy
      grw [← hC hx hy, dist_toSnowflaking_toSnowflaking, Real.rpow_rpow_inv (by positivity) hα₀.ne']

open Metric

@[simp]
theorem dist_ofSnowflaking_ofSnowflaking (x y : Snowflaking X α hα₀ hα₁) :
    dist x.ofSnowflaking y.ofSnowflaking = dist x y ^ α⁻¹ := by
  cases x; cases y
  simp [Real.rpow_rpow_inv dist_nonneg hα₀.ne']

@[simp]
theorem preimage_ofSnowflaking_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking ⁻¹' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_lt_rpow_iff]

@[simp]
theorem image_toSnowflaking_ball (x : X) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking '' ball x r = ball (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_ball x hr]

@[simp]
theorem preimage_toSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking ⁻¹' ball x r = ball x.ofSnowflaking (r ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_ball _ (by positivity),
    toSnowflaking_ofSnowflaking, Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
theorem image_ofSnowflaking_ball (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking '' ball x r = ball x.ofSnowflaking (r ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_ball _ hr]

@[simp]
theorem preimage_ofSnowflaking_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking ⁻¹' closedBall x r =
      closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  ext ⟨y⟩
  simp (disch := positivity) [Real.rpow_le_rpow_iff]

@[simp]
theorem image_toSnowflaking_closedBall (x : X) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking '' closedBall x r =
      closedBall (toSnowflaking x : Snowflaking X α hα₀ hα₁) (r ^ α) := by
  rw [image_toSnowflaking_eq_preimage, preimage_ofSnowflaking_closedBall x hr]

@[simp]
theorem preimage_toSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    toSnowflaking ⁻¹' closedBall x r = closedBall x.ofSnowflaking (r ^ α⁻¹) := by
  rw [toSnowflaking.preimage_eq_iff_eq_image, image_toSnowflaking_closedBall _ (by positivity),
    toSnowflaking_ofSnowflaking, Real.rpow_inv_rpow hr hα₀.ne']

@[simp]
theorem image_ofSnowflaking_closedBall (x : Snowflaking X α hα₀ hα₁) {r : ℝ} (hr : 0 ≤ r) :
    ofSnowflaking '' closedBall x r = closedBall x.ofSnowflaking (r ^ α⁻¹) := by
  rw [image_ofSnowflaking_eq_preimage, preimage_toSnowflaking_closedBall _ hr]

end PseudoMetricSpace

instance [MetricSpace X] : MetricSpace (Snowflaking X α hα₀ hα₁) :=
  .ofT0PseudoMetricSpace _

end Snowflaking
end Metric
