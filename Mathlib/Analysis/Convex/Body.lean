/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

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
- Characterise the interaction of the distance with algebraic operations, e.g.
  `dist (a • K) (a • L) = ‖a‖ * dist K L`, `dist (a +ᵥ K) (a +ᵥ L) = dist K L`

## Tags

convex, convex body
-/

@[expose] public section


open scoped Pointwise Topology NNReal

variable {V : Type*}

/-- Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
structure ConvexBody (V : Type*) [TopologicalSpace V] [AddCommMonoid V] [SMul ℝ V] where
  /-- The **carrier set** underlying a convex body: the set of points contained in it -/
  carrier : Set V
  /-- A convex body has convex carrier set -/
  convex' : Convex ℝ carrier
  /-- A convex body has compact carrier set -/
  isCompact' : IsCompact carrier
  /-- A convex body has non-empty carrier set -/
  nonempty' : carrier.Nonempty

namespace ConvexBody

section TVS

variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

instance : SetLike (ConvexBody V) V where
  coe := ConvexBody.carrier
  coe_injective' K L h := by
    cases K
    cases L
    congr

instance : PartialOrder (ConvexBody V) := .ofSetLike (ConvexBody V) V

protected theorem convex (K : ConvexBody V) : Convex ℝ (K : Set V) :=
  K.convex'

protected theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.isCompact'

protected theorem isClosed [T2Space V] (K : ConvexBody V) : IsClosed (K : Set V) :=
  K.isCompact.isClosed

protected theorem nonempty (K : ConvexBody V) : (K : Set V).Nonempty :=
  K.nonempty'

@[ext]
protected theorem ext {K L : ConvexBody V} (h : (K : Set V) = L) : K = L :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : Set V) = s :=
  rfl

/-- A convex body that is symmetric contains `0`. -/
theorem zero_mem_of_symmetric (K : ConvexBody V) (h_symm : ∀ x ∈ K, -x ∈ K) : 0 ∈ K := by
  obtain ⟨x, hx⟩ := K.nonempty
  rw [show 0 = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) by simp]
  apply convex_iff_forall_pos.mp K.convex hx (h_symm x hx)
  all_goals linarith

section ContinuousAdd

instance : Zero (ConvexBody V) where
  zero := ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩

@[simp, norm_cast]
theorem coe_zero : (↑(0 : ConvexBody V) : Set V) = 0 :=
  rfl

instance : Inhabited (ConvexBody V) :=
  ⟨0⟩

variable [ContinuousAdd V]

instance : Add (ConvexBody V) where
  add K L :=
    ⟨K + L, K.convex.add L.convex, K.isCompact.add L.isCompact,
      K.nonempty.add L.nonempty⟩

instance : SMul ℕ (ConvexBody V) where
  smul := nsmulRec

@[simp, norm_cast]
theorem coe_nsmul : ∀ (n : ℕ) (K : ConvexBody V), ↑(n • K) = n • (K : Set V)
  | 0, _ => rfl
  | (n + 1), K => congr_arg₂ (Set.image2 (· + ·)) (coe_nsmul n K) rfl

noncomputable instance : AddMonoid (ConvexBody V) :=
  SetLike.coe_injective.addMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ coe_nsmul _ _

@[simp, norm_cast]
theorem coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L :=
  rfl

noncomputable instance : AddCommMonoid (ConvexBody V) :=
  SetLike.coe_injective.addCommMonoid _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ coe_nsmul _ _

end ContinuousAdd

variable [ContinuousSMul ℝ V]

instance : SMul ℝ (ConvexBody V) where
  smul c K := ⟨c • (K : Set V), K.convex.smul _, K.isCompact.smul _, K.nonempty.smul_set⟩

@[simp, norm_cast]
theorem coe_smul (c : ℝ) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl

@[simp, norm_cast]
theorem coe_smul' (c : ℝ≥0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl

theorem smul_le_of_le (K : ConvexBody V) (h_zero : 0 ∈ K) {a b : ℝ≥0} (h : a ≤ b) :
    a • K ≤ b • K := by
  rw [← SetLike.coe_subset_coe, coe_smul', coe_smul']
  obtain rfl | ha := eq_zero_or_pos a
  · rw [Set.zero_smul_set K.nonempty, Set.zero_subset]
    exact Set.mem_smul_set.mpr ⟨0, h_zero, smul_zero _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
    rw [← Set.mem_inv_smul_set_iff₀ ha.ne', smul_smul]
    refine Convex.mem_smul_of_zero_mem K.convex h_zero hy (?_ : 1 ≤ a⁻¹ * b)
    rwa [le_inv_mul_iff₀ ha, mul_one]

variable [ContinuousAdd V]

noncomputable instance : DistribMulAction ℝ (ConvexBody V) :=
  SetLike.coe_injective.distribMulAction ⟨⟨_, coe_zero⟩, coe_add⟩ coe_smul

/-- The convex bodies in a fixed space $V$ form a module over the nonnegative reals. -/
noncomputable instance : Module ℝ≥0 (ConvexBody V) where
  add_smul c d K := SetLike.ext' <| Convex.add_smul K.convex c.coe_nonneg d.coe_nonneg
  zero_smul K := SetLike.ext' <| Set.zero_smul_set K.nonempty

end TVS

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] (K L : ConvexBody V)

protected theorem isBounded : Bornology.IsBounded (K : Set V) :=
  K.isCompact.isBounded

theorem hausdorffEDist_ne_top {K L : ConvexBody V} : Metric.hausdorffEDist (K : Set V) L ≠ ⊤ := by
  apply_rules [Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.isBounded]

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top := hausdorffEDist_ne_top

/-- Convex bodies in a fixed seminormed space $V$ form a pseudo-metric space under the Hausdorff
metric. -/
noncomputable instance : PseudoMetricSpace (ConvexBody V) where
  dist K L := Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle _ _ _ := Metric.hausdorffDist_triangle hausdorffEDist_ne_top

@[simp, norm_cast]
theorem hausdorffDist_coe : Metric.hausdorffDist (K : Set V) L = dist K L :=
  rfl

@[simp, norm_cast]
theorem hausdorffEDist_coe : Metric.hausdorffEDist (K : Set V) L = edist K L := by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal hausdorffEDist_ne_top).symm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_coe := hausdorffEDist_coe

open Filter

/-- Let `K` be a convex body that contains `0` and let `u n` be a sequence of nonnegative real
numbers that tends to `0`. Then the intersection of the dilated bodies `(1 + u n) • K` is equal
to `K`. -/
theorem iInter_smul_eq_self [T2Space V] {u : ℕ → ℝ≥0} (K : ConvexBody V) (h_zero : 0 ∈ K)
    (hu : Tendsto u atTop (𝓝 0)) :
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
    rw [show (1 + u n : ℝ) • y - y = (u n : ℝ) • y by rw [add_smul, one_smul, add_sub_cancel_left],
      norm_smul, Real.norm_eq_abs]
    specialize hn n le_rfl
    rw [lt_div_iff₀' hC_pos, mul_comm, NNReal.coe_zero, sub_zero, Real.norm_eq_abs] at hn
    refine lt_of_le_of_lt ?_ hn
    exact mul_le_mul_of_nonneg_left (hC_bdd _ hyK) (abs_nonneg _)
  · refine Set.mem_iInter.mpr (fun n => Convex.mem_smul_of_zero_mem K.convex h_zero h ?_)
    exact le_add_of_nonneg_right (by positivity)

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Convex bodies in a fixed normed space `V` form a metric space under the Hausdorff metric. -/
noncomputable instance : MetricSpace (ConvexBody V) where
  eq_of_dist_eq_zero {K L} hd := ConvexBody.ext <|
    (K.isClosed.hausdorffDist_zero_iff_eq L.isClosed hausdorffEDist_ne_top).1 hd

end NormedAddCommGroup

end ConvexBody
