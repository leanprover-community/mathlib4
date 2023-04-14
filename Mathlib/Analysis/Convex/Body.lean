/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert

! This file was ported from Lean 3 source module analysis.convex.body
! leanprover-community/mathlib commit 858a10cf68fd6c06872950fc58c4dcc68d465591
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Convex bodies

This file contains the definition of the type `convex_body V`
consisting of
convex, compact, nonempty subsets of a real topological vector space `V`.

`convex_body V` is a module over the nonnegative reals (`nnreal`) and a pseudo-metric space.
If `V` is a normed space, `convex_body V` is a metric space.

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

variable {V : Type _}

/-- Let `V` be a real topological vector space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
structure ConvexBody (V : Type _) [TopologicalSpace V] [AddCommMonoid V] [SMul ℝ V] where
  carrier : Set V
  convex' : Convex ℝ carrier
  is_compact' : IsCompact carrier
  nonempty' : carrier.Nonempty
#align convex_body ConvexBody

namespace ConvexBody

section TVS

variable [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

instance : SetLike (ConvexBody V) V
    where
  coe := ConvexBody.carrier
  coe_injective' K L h := by
    cases K
    cases L
    congr

protected theorem convex (K : ConvexBody V) : Convex ℝ (K : Set V) :=
  K.convex'
#align convex_body.convex ConvexBody.convex

protected theorem isCompact (K : ConvexBody V) : IsCompact (K : Set V) :=
  K.is_compact'
#align convex_body.is_compact ConvexBody.isCompact

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

section ContinuousAdd

variable [ContinuousAdd V]

instance : AddMonoid (ConvexBody V)
    where
  -- we cannot write K + L to avoid reducibility issues with the set.has_add instance
  add K L :=
    ⟨Set.image2 (· + ·) K L, K.Convex.add L.Convex, K.IsCompact.add L.IsCompact,
      K.Nonempty.add L.Nonempty⟩
  add_assoc K L M := by
    ext
    simp only [coe_mk, Set.image2_add, add_assoc]
  zero := ⟨0, convex_singleton 0, isCompact_singleton, Set.singleton_nonempty 0⟩
  zero_add K := by
    ext
    simp only [coe_mk, Set.image2_add, zero_add]
  add_zero K := by
    ext
    simp only [coe_mk, Set.image2_add, add_zero]

@[simp]
theorem coe_add (K L : ConvexBody V) : (↑(K + L) : Set V) = (K : Set V) + L :=
  rfl
#align convex_body.coe_add ConvexBody.coe_add

@[simp]
theorem coe_zero : (↑(0 : ConvexBody V) : Set V) = 0 :=
  rfl
#align convex_body.coe_zero ConvexBody.coe_zero

instance : Inhabited (ConvexBody V) :=
  ⟨0⟩

instance : AddCommMonoid (ConvexBody V) :=
  { ConvexBody.addMonoid with
    add_comm := fun K L => by
      ext
      simp only [coe_add, add_comm] }

end ContinuousAdd

variable [ContinuousSMul ℝ V]

instance : SMul ℝ (ConvexBody V)
    where smul c K := ⟨c • (K : Set V), K.Convex.smul _, K.IsCompact.smul _, K.Nonempty.smul_set⟩

@[simp]
theorem coe_smul (c : ℝ) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
#align convex_body.coe_smul ConvexBody.coe_smul

variable [ContinuousAdd V]

instance : DistribMulAction ℝ (ConvexBody V)
    where
  toSMul := ConvexBody.hasSmul
  one_smul K := by
    ext
    simp only [coe_smul, one_smul]
  mul_smul c d K := by
    ext
    simp only [coe_smul, mul_smul]
  smul_add c K L := by
    ext
    simp only [coe_smul, coe_add, smul_add]
  smul_zero c := by
    ext
    simp only [coe_smul, coe_zero, smul_zero]

@[simp]
theorem coe_smul' (c : ℝ≥0) (K : ConvexBody V) : (↑(c • K) : Set V) = c • (K : Set V) :=
  rfl
#align convex_body.coe_smul' ConvexBody.coe_smul'

/-- The convex bodies in a fixed space $V$ form a module over the nonnegative reals.
-/
instance : Module ℝ≥0 (ConvexBody V)
    where
  add_smul c d K := by
    ext1
    simp only [coe_smul, coe_add]
    exact Convex.add_smul K.convex (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  zero_smul K := by
    ext1
    exact Set.zero_smul_set K.nonempty

end TVS

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] (K L : ConvexBody V)

protected theorem bounded : Metric.Bounded (K : Set V) :=
  K.IsCompact.Bounded
#align convex_body.bounded ConvexBody.bounded

theorem hausdorffEdist_ne_top {K L : ConvexBody V} : EMetric.hausdorffEdist (K : Set V) L ≠ ⊤ := by
  apply_rules [Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded, ConvexBody.nonempty,
    ConvexBody.bounded]
#align convex_body.Hausdorff_edist_ne_top ConvexBody.hausdorffEdist_ne_top

/-- Convex bodies in a fixed seminormed space $V$ form a pseudo-metric space under the Hausdorff
metric. -/
noncomputable instance : PseudoMetricSpace (ConvexBody V)
    where
  dist K L := Metric.hausdorffDist (K : Set V) L
  dist_self _ := Metric.hausdorffDist_self_zero
  dist_comm _ _ := Metric.hausdorffDist_comm
  dist_triangle K L M := Metric.hausdorffDist_triangle hausdorffEdist_ne_top

@[simp, norm_cast]
theorem hausdorffDist_coe : Metric.hausdorffDist (K : Set V) L = dist K L :=
  rfl
#align convex_body.Hausdorff_dist_coe ConvexBody.hausdorffDist_coe

@[simp, norm_cast]
theorem hausdorffEdist_coe : EMetric.hausdorffEdist (K : Set V) L = edist K L :=
  by
  rw [edist_dist]
  exact (ENNReal.ofReal_toReal Hausdorff_edist_ne_top).symm
#align convex_body.Hausdorff_edist_coe ConvexBody.hausdorffEdist_coe

end SeminormedAddCommGroup

section NormedAddCommGroup

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Convex bodies in a fixed normed space `V` form a metric space under the Hausdorff metric. -/
noncomputable instance : MetricSpace (ConvexBody V)
    where eq_of_dist_eq_zero K L hd :=
    ConvexBody.ext <|
      (K.IsCompact.IsClosed.hausdorffDist_zero_iff_eq L.IsCompact.IsClosed hausdorffEdist_ne_top).mp
        hd

end NormedAddCommGroup

end ConvexBody

