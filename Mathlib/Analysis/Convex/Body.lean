/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance.Basic

#align_import analysis.convex.body from "leanprover-community/mathlib"@"858a10cf68fd6c06872950fc58c4dcc68d465591"

/-!
# Convex bodies

This file contains the definition of the type `ConvexBody V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`ConvexBody V` is a module over the nonnegative reals (`NNReal`) and a pseudo-metric space.
If `V` is a normed space, `ConvexBody V` is a metric space.

## TODO

- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets
- Characterise the interaction of the distance with algebraic operations, eg
  `dist (a • K) (a • L) = ‖a‖ * dist K L`, `dist (a +ᵥ K) (a +ᵥ L) = dist K L`

## Tags

convex, convex body
-/


open Pointwise

open NNReal

variable {V : Type*}

/-- Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
structure ConvexBody (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul ℝ V] where
  carrier : Set V
  convex' : Convex ℝ carrier
  isCompact' : IsCompact carrier
  nonempty' : carrier.Nonempty
#align convex_body ConvexBody

namespace ConvexBody

section TVS

variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

instance : SetLike (ConvexBody V) V where
  coe := ConvexBody.carrier
  coe_injective' K L h := by
    cases K
    cases L
    congr

protected theorem convex (K : ConvexBody V) : Convex ℝ (K : Set V) :=
  K.convex'
#align convex_body.convex ConvexBody.convex

protected theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.isCompact'
#align convex_body.is_compact ConvexBody.isCompact

-- porting note: new theorem
protected theorem isClosed [T2Space V] (K : ConvexBody V) : IsClosed (K : Set V) :=
  K.isCompact.isClosed

protected theorem nonempty (K : ConvexBody V) : (K : Set V).Nonempty :=
  K.nonempty'
#align convex_body.nonempty ConvexBody.nonempty

@[ext]
protected theorem ext {K L : ConvexBody V} (h : (K : Set V) = L) : K = L :=
  SetLike.ext' h
#align convex_body.ext ConvexBody.ext

@[simp]
theorem coe_mk (s : Set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set V) = s :=
  rfl
#align convex_body.coe_mk ConvexBody.coe_mk

/-- A convex body that is symmetric contains `0`. -/
theorem zero_mem_of_symmetric (K : ConvexBody V) (h_symm : ∀ x ∈ K, - x ∈ K) : 0 ∈ K := by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show 0 = (1/2 : ℝ) • x + (1/2 : ℝ) • (- x) by field_simp]
  apply convex_iff_forall_pos.mp K.convex hx (h_symm x hx)
  all_goals linarith

section ContinuousAdd

variable [ContinuousAdd V]

-- we cannot write K + L to avoid reducibility issues with the set.has_add instance
-- porting note: todo: is this^ still true?
instance : Add (ConvexBody V) where
  add K L :=
    ⟨Set.image2 (· + ·) K L, K.convex.add L.convex, K.isCompact.add L.isCompact,
      K.nonempty.add L.nonempty⟩

instance : Zero (ConvexBody V) where
  zero := ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩

instance : SMul ℕ (ConvexBody V) where
  smul := nsmulRec

-- porting note: add @[simp, norm_cast]; we leave it out for now to reproduce mathlib3 behavior.
theorem coe_nsmul : ∀ (n : ℕ) (K : ConvexBody V), ↑(n • K) = n • (K : Set V)
  | 0, _ => rfl
  | (n + 1), K => congr_arg₂ (Set.image2 (· + ·)) rfl (coe_nsmul n K)

instance : AddMonoid (ConvexBody V) :=
  SetLike.coe_injective.addMonoid (↑) rfl (fun _ _ ↦ rfl) fun _ _ ↦ coe_nsmul _ _

@[simp] -- porting note: add norm_cast; we leave it out for now to reproduce mathlib3 behavior.
theorem coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L :=
  rfl
#align convex_body.coe_add ConvexBody.coe_add

@[simp] -- porting note: add norm_cast; we leave it out for now to reproduce mathlib3 behavior.
theorem coe_zero : (↑(0 : ConvexBody V) : Set V) = 0 :=
  rfl
#align convex_body.coe_zero ConvexBody.coe_zero

instance : Inhabited (ConvexBody V) :=
  ⟨0⟩

instance : AddCommMonoid (ConvexBody V) :=
  SetLike.coe_injective.addCommMonoid (↑) rfl (fun _ _ ↦ rfl) fun _ _ ↦ coe_nsmul _ _

end ContinuousAdd

variable [ContinuousSMul ℝ V]

instance : SMul ℝ (ConvexBody V) where
  smul c K := ⟨c • (K : Set V), K.convex.smul _, K.isCompact.smul _, K.nonempty.smul_set⟩

@[simp] -- porting note: add norm_cast; we leave it out for now to reproduce mathlib3 behavior.
theorem coe_smul (c : ℝ) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
#align convex_body.coe_smul ConvexBody.coe_smul

variable [ContinuousAdd V]

instance : DistribMulAction ℝ (ConvexBody V) :=
  SetLike.coe_injective.distribMulAction ⟨⟨(↑), coe_zero⟩, coe_add⟩ coe_smul

@[simp] -- porting note: add norm_cast; we leave it out for now to reproduce mathlib3 behavior.
theorem coe_smul' (c : ℝ≥0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
#align convex_body.coe_smul' ConvexBody.coe_smul'

/-- The convex bodies in a fixed space $V$ form a module over the nonnegative reals.
-/
instance : Module ℝ≥0 (ConvexBody V) where
  add_smul c d K := SetLike.ext' <| Convex.add_smul K.convex c.coe_nonneg d.coe_nonneg
  zero_smul K := SetLike.ext' <| Set.zero_smul_set K.nonempty

theorem smul_le_of_le (K : ConvexBody V) (h_zero : 0 ∈ K) {a b : ℝ≥0} (h : a ≤ b) :
    a • K ≤ b • K := by
  rw [← SetLike.coe_subset_coe, coe_smul', coe_smul']
  by_cases ha : a = 0
  · rw [ha, Set.zero_smul_set K.nonempty, Set.zero_subset]
    exact Set.mem_smul_set.mpr ⟨0, h_zero, smul_zero _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rw [← Set.mem_inv_smul_set_iff₀ ha, smul_smul]
    exact Convex.mem_smul_of_zero_mem K.convex h_zero hy
      (by rwa [← NNReal.mul_le_iff_le_inv ha, mul_one] : 1 ≤ a⁻¹ * b)

end TVS

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] (K L : ConvexBody V)

protected theorem isBounded : Bornology.IsBounded (K : Set V) :=
  K.isCompact.isBounded
#align convex_body.bounded ConvexBody.isBounded

theorem hausdorffEdist_ne_top {K L : ConvexBody V} : EMetric.hausdorffEdist (K : Set V) L ≠ ⊤ := by
  apply_rules [Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.isBounded]
#align convex_body.Hausdorff_edist_ne_top ConvexBody.hausdorffEdist_ne_top

/-- Convex bodies in a fixed seminormed space $V$ form a pseudo-metric space under the Hausdorff
metric. -/
noncomputable instance : PseudoMetricSpace (ConvexBody V) where
  dist K L := Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle K L M := Metric.hausdorffDist_triangle hausdorffEdist_ne_top
  edist_dist _ _ := by exact ENNReal.coe_nnreal_eq _

@[simp, norm_cast]
theorem hausdorffDist_coe : Metric.hausdorffDist (K : Set V) L = dist K L :=
  rfl
#align convex_body.Hausdorff_dist_coe ConvexBody.hausdorffDist_coe

@[simp, norm_cast]
theorem hausdorffEdist_coe : EMetric.hausdorffEdist (K : Set V) L = edist K L := by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal hausdorffEdist_ne_top).symm
#align convex_body.Hausdorff_edist_coe ConvexBody.hausdorffEdist_coe

open Filter

/-- Let `K` be a convex body that contains `0` and let `u n` be a sequence of nonnegative real
numbers that tends to `0`. Then the intersection of the dilated bodies `(1 + u n) • K` is equal
to `K`. -/
theorem iInter_smul_eq_self [T2Space V] {u : ℕ → ℝ≥0} (K : ConvexBody V) (h_zero : 0 ∈ K)
    (hu : Tendsto u atTop (nhds 0)) :
    ⋂ n : ℕ, (1 + (u n : ℝ)) • (K : Set V) = K := by
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨C, hC_pos, hC_bdd⟩ := K.isBounded.exists_pos_norm_le
    rw [← K.isClosed.closure_eq, SeminormedAddCommGroup.mem_closure_iff]
    rw [← NNReal.tendsto_coe, NormedAddCommGroup.tendsto_atTop] at hu
    intro ε hε
    obtain ⟨n, hn⟩ := hu (ε / C) (div_pos hε hC_pos)
    obtain ⟨y, hyK, rfl⟩ := Set.mem_smul_set.mp (Set.mem_iInter.mp h n)
    refine ⟨y, hyK, ?_⟩
    rw [show (1 + u n : ℝ) • y - y = (u n : ℝ) • y by rw [add_smul, one_smul, add_sub_cancel'],
      norm_smul, Real.norm_eq_abs]
    specialize hn n le_rfl
    rw [_root_.lt_div_iff' hC_pos, mul_comm, NNReal.coe_zero, sub_zero, Real.norm_eq_abs] at hn
    refine lt_of_le_of_lt ?_ hn
    exact mul_le_mul_of_nonneg_left (hC_bdd _ hyK) (abs_nonneg _)
  · refine Set.mem_iInter.mpr (fun n => Convex.mem_smul_of_zero_mem K.convex h_zero h ?_)
    exact (le_add_iff_nonneg_right _).mpr (by positivity)

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Convex bodies in a fixed normed space `V` form a metric space under the Hausdorff metric. -/
noncomputable instance : MetricSpace (ConvexBody V) where
  eq_of_dist_eq_zero {K L} hd := ConvexBody.ext <|
    (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hausdorffEdist_ne_top).1 hd

end NormedAddCommGroup

end ConvexBody
