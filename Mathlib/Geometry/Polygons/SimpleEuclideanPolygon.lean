/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
import Mathlib.Geometry.Polygons.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.Basic

/-!
# Simple Euclidean Polygons and the Jordan Curve Theorem

This file defines simple polygons (non-self-intersecting) and establishes their connection
to the Jordan Curve Theorem.

## Main definitions

* `IsSimpleClosedCurve`: A set in 2D Euclidean space that can be parameterized by a continuous
  injective function from `AddCircle 1`.
* `JordanDecomposition`: The decomposition of the plane minus a simple closed curve into
  a bounded interior and unbounded exterior.
* `SimplePolygon`: A polygon whose non-adjacent edges are disjoint and adjacent edges
  intersect only at their shared vertex.
* `SimpleEuclideanPolygon`: A simple polygon in 2-dimensional Euclidean space.
* `SimplePolygon.boundaryParam`: A piecewise linear parameterization of the polygon boundary
  on `[0, 1]`.
* `SimplePolygon.circleMap`: The boundary parameterization lifted to `AddCircle 1`.
* `SimplePolygon.jordanDecomp`: The Jordan decomposition applied to a simple polygon's boundary.

## Main theorems

* `SimplePolygon.boundaryParam_continuousOn`: The boundary parameterization is
    continuous on `[0, 1]`.
* `SimplePolygon.boundaryParam_injOn_Ico`: The boundary parameterization is injective on `[0, 1)`.
* `SimplePolygon.circleMap_continuous`: The circle map is continuous.
* `SimplePolygon.circleMap_injective`: The circle map is injective.
* `SimplePolygon.circleMap_range`: The range of the circle map equals the polygon boundary.
* `SimplePolygon.boundary_isSimpleClosedCurve`: The boundary of a simple polygon is a simple
    closed curve.

## References

* Jordan Curve Theorem (stated as an axiom)
-/

open Set Topology

/-- A simple closed curve in 2D Euclidean space is a set that can be parameterized by a
continuous injective function from `AddCircle 1`. -/
def IsSimpleClosedCurve (γ : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2),
    Continuous f ∧ Function.Injective f ∧ range f = γ

/-- The Jordan decomposition of the plane minus a simple closed curve. -/
structure JordanDecomposition (γ : Set (EuclideanSpace ℝ (Fin 2))) where
  /-- The bounded interior region. -/
  interior : Set (EuclideanSpace ℝ (Fin 2))
  /-- The unbounded exterior region. -/
  exterior : Set (EuclideanSpace ℝ (Fin 2))
  /-- The curve, interior, and exterior partition the plane. -/
  partition : γ ∪ interior ∪ exterior = univ
  /-- The interior is connected. -/
  interior_isConnected : IsConnected interior
  /-- The exterior is connected. -/
  exterior_isConnected : IsConnected exterior
  /-- The interior is open. -/
  interior_isOpen : IsOpen interior
  /-- The exterior is open. -/
  exterior_isOpen : IsOpen exterior
  /-- The interior is bounded. -/
  interior_isBounded : Bornology.IsBounded interior
  /-- The exterior is unbounded. -/
  exterior_not_bounded : ¬Bornology.IsBounded exterior
  /-- The frontier of the interior is the curve. -/
  frontier_interior : frontier interior = γ
  /-- The frontier of the exterior is the curve. -/
  frontier_exterior : frontier exterior = γ

/-- The Jordan Curve Theorem: every simple closed curve in the plane separates it into
exactly two connected components, a bounded interior and an unbounded exterior. -/
noncomputable axiom jordan_curve_theorem {γ : Set (EuclideanSpace ℝ (Fin 2))}
    (hγ : IsSimpleClosedCurve γ) : JordanDecomposition γ

/-- A simple Eulicdean polygon is a polygon where non-adjacent vertices are distinct,
non-adjacent edges are disjoint, and adjacent edges intersect only at their shared vertex. -/
structure SimpleEuclideanPolygon (n : ℕ) [NeZero n] : Type
    extends EuclideanPolygon n where
  non_adjacent_edges_disjoint :
      ∀ i j : Fin n,
        (j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) →
          Disjoint (toPolygon.edgeSet i) (toPolygon.edgeSet j)

  adjacent_edges_inter :
      ∀ i : Fin n,
        (toPolygon.edgeSet i ∩ toPolygon.edgeSet (i + 1))
          = ({toPolygon.vertices (i + 1)} : Set (EuclideanSpace ℝ (Fin 2)))

  adj_vertices_distinct : ∀ i, toPolygon.vertices i ≠ toPolygon.vertices (i + 1)

namespace SimpleEuclideanPolygon
variable {n : ℕ} [NeZero n]
variable (poly : SimpleEuclideanPolygon n)

/-- The piecewise linear parameterization of the polygon boundary on `[0, 1]`.
For `t ∈ [k/n, (k+1)/n]`, the point lies on edge `k`. -/
noncomputable def boundaryParam : ℝ → EuclideanSpace ℝ (Fin 2) := fun t =>
    if t = 1 then poly.toPolygon.vertices 0
  else
    let i : Fin n := ⟨⌊t * n⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
    let t' : ℝ := t * n - i
    poly.toPolygon.edgePath i t'

lemma boundaryParam_zero_eq_one : poly.boundaryParam 0 = poly.boundaryParam 1 := by
  simp only [boundaryParam]
  simp only [zero_ne_one, ↓reduceIte, zero_mul, Int.floor_zero, Int.toNat_zero, Nat.zero_mod,
    Fin.mk_zero', CharP.cast_eq_zero, sub_self]
  simp only [Polygon.edgePath]
  simp only [zero_add, AffineMap.lineMap_apply_zero]

lemma boundaryParam_continuousOn_piece (k : Fin n) :
  ContinuousOn poly.boundaryParam (Icc (k / n) ((k.val + 1) / n)) := by
    unfold boundaryParam
    let lo : ℝ := k.val / n
    let hi : ℝ := (k.val + 1) / n
    have onPiece : ∀ x ∈ Icc lo hi, (⌊x * n⌋.toNat % n = ↑k ∨ x = hi) := by
      intro x xin
      have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      by_cases h : x = hi
      right
      exact h
      simp only [Icc,lo,hi] at xin
      simp only [hi] at h
      push_neg at h
      have neqkplus1 : x * ↑n ≠ ↑↑k + 1 := by
        contrapose! h
        rw [eq_div_iff (ne_of_gt hn)]
        exact h
      have : ↑↑k ≤ x * ↑n ∧ x * ↑n < ↑↑k + 1 := by
        obtain ⟨hlo, hhi⟩ := xin
        constructor
        exact (mul_inv_le_iff₀ hn).mp hlo
        have : x * ↑n ≤ ↑↑k + 1 := by exact (le_div_iff₀ hn).mp hhi
        exact Std.lt_of_le_of_ne this neqkplus1
      left
      have floorEq : ⌊x * ↑n⌋ = ↑k := by
        rw [Int.floor_eq_iff]
        exact_mod_cast this
      simp only [floorEq, Int.toNat_natCast, Nat.mod_eq_of_lt k.isLt]
    by_cases last : (k.val + 1 : ℝ) / n = 1
    intro x hx
    have hk_eq : k.val + 1 = n := by
      have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      have h := div_eq_one_iff_eq hn |>.mp last
      exact_mod_cast h
    by_cases hx1 : x = 1
    subst hx1
    refine ContinuousWithinAt.congr_of_eventuallyEq
      (f := fun t => poly.toPolygon.edgePath k (t * ↑n - ↑↑k)) ?_ ?_ ?_
    · apply Continuous.continuousWithinAt
      unfold Polygon.edgePath
      continuity
    · apply eventually_nhdsWithin_of_forall
      intro t ht
      by_cases ht1 : t = 1
      · subst ht1
        simp only [↓reduceIte, one_mul, Polygon.edgePath]
        have hparam : (↑n : ℝ) - ↑↑k = 1 := by
          have hkval : k.val = n - 1 := by omega
          have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
          have : (n : ℝ) - (n - 1 : ℕ) = 1 := by
            rw [Nat.cast_sub hn_pos]
            ring
          rw [hkval]
          exact this
        rw [hparam, AffineMap.lineMap_apply_one]
        congr 1
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_zero]
        have h1 : (1 : Fin n).val = 1 % n := rfl
        simp only [h1, Nat.add_mod_mod, hk_eq, Nat.mod_self]
      · simp only [ht1, ↓reduceIte]
        have ht' := onPiece t ht
        rcases ht' with hfloor | heq
        · simp only [hfloor]
        · simp only [hi] at heq
          rw [last] at heq
          exact absurd heq ht1
    · -- eq_at: show they agree at t = 1
      simp only [↓reduceIte, one_mul, Polygon.edgePath]
      have hparam : (↑n : ℝ) - ↑↑k = 1 := by
        have hkval : k.val = n - 1 := by omega
        have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
        have : (n : ℝ) - (n - 1 : ℕ) = 1 := by
          rw [Nat.cast_sub hn_pos]
          ring
        rw [hkval]
        exact this
      rw [hparam, AffineMap.lineMap_apply_one]
      congr 1
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_zero]
      have h1 : (1 : Fin n).val = 1 % n := rfl
      simp only [h1, Nat.add_mod_mod, hk_eq, Nat.mod_self]
    simp only [lo,hi] at onPiece
    have hx' := onPiece x hx
    rcases hx' with onSegment | atEnd
    apply ContinuousWithinAt.congr_of_eventuallyEq
      _ (eventually_nhdsWithin_of_forall (fun t ht => ?_))
    simp only [hx1]
    simp only [↓reduceIte, onSegment]
    simp only [Fin.eta]
    rfl
    apply Continuous.continuousWithinAt
    unfold Polygon.edgePath
    apply Continuous.comp
    exact AffineMap.lineMap_continuous
    continuity
    by_cases ht1 : t = 1
    simp only [ht1, if_true]
    have hparam : (1 : ℝ) * ↑n - ↑↑k = 1 := by
      have h := div_eq_one_iff_eq (Nat.cast_ne_zero.mpr (NeZero.ne n)) |>.mp last
      field_simp
      linarith
    rw [hparam]
    simp only [Polygon.edgePath]
    simp only [AffineMap.lineMap_apply_one]
    congr 1
    have : (k + 1 : Fin n).val = 0 := by
      simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod]
      simp only [hk_eq, Nat.mod_self]
    exact Fin.ext this.symm
    simp only [ht1, ite_false]
    congr 1
    ext
    exact (onPiece t ht).resolve_right (fun h => ht1 (last ▸ h))
    congr 1
    exact_mod_cast (onPiece t ht).resolve_right (fun h => ht1 (last ▸ h))
    exact absurd (atEnd.trans last) hx1
    intro x hx
    simp only [lo,hi] at onPiece
    have hx' := onPiece x hx
    rcases hx' with onSegment | atEnd
    have hx1 : x ≠ 1 := by
      intro heq
      subst heq
      have h1 : (1 : ℝ) ≤ hi := hx.2
      have hk_lt : k.val + 1 < n := by
        by_contra h; push_neg at h
        apply last
        have heq : k.val + 1 = n := le_antisymm (Nat.succ_le_of_lt k.isLt) h
        have : (↑↑k + 1 : ℝ) = ↑n := by exact_mod_cast heq
        rw [this, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
      have h2 : hi < 1 := by
        simp only [hi]
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
        rw [div_lt_one hn_pos]
        norm_cast
      linarith
    apply ContinuousWithinAt.congr_of_eventuallyEq
      _ (eventually_nhdsWithin_of_forall (fun t ht => ?_))
    simp only [hx1]
    simp only [↓reduceIte, onSegment]
    simp only [Fin.eta]
    rfl
    apply Continuous.continuousWithinAt
    unfold Polygon.edgePath
    apply Continuous.comp
    exact AffineMap.lineMap_continuous
    continuity
    have : k + 1 ≠ n := by
      intro h
      apply last
      rw [div_eq_one_iff_eq (Nat.cast_ne_zero.mpr (NeZero.ne n))]
      exact_mod_cast h
    have : (↑k + 1) % n = ↑k + 1 := by
      refine Nat.mod_eq_of_lt ?_
      have := k.isLt
      omega
    have hk_lt : k.val + 1 < n := by omega
    have ht1 : t ≠ 1 := by
      intro heq
      subst heq
      have h1 : (1 : ℝ) ≤ hi := ht.2
      have h2 : hi < 1 := by
        simp only [hi]
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
        rw [div_lt_one hn_pos]
        norm_cast
      linarith
    simp only [ht1, ↓reduceIte]
    specialize onPiece t
    apply onPiece at ht
    rcases ht with onSegment' | atEnd'
    simp only [onSegment']
    simp only [atEnd']
    simp only [div_mul_cancel_of_invertible, Int.floor_add_one, Int.floor_natCast,
      Int.toNat_natCast_add_one, add_sub_cancel_left]
    simp only [this]
    simp only [Nat.cast_add, Nat.cast_one, sub_self]
    simp only [Polygon.edgePath]
    simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add]
    rw[← this]
    norm_num
    have hx1 : x ≠ 1 := by
      intro heq
      subst heq
      have h1 : (1 : ℝ) ≤ hi := hx.2
      have hk_lt : k.val + 1 < n := by
        by_contra h; push_neg at h
        apply last
        have heq : k.val + 1 = n := le_antisymm (Nat.succ_le_of_lt k.isLt) h
        have : (↑↑k + 1 : ℝ) = ↑n := by exact_mod_cast heq
        rw [this, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
      have h2 : hi < 1 := by
        simp only [hi]
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
        rw [div_lt_one hn_pos]
        norm_cast
      linarith
    subst atEnd
    refine ContinuousWithinAt.congr_of_eventuallyEq (f := fun t =>
      poly.toPolygon.edgePath k (t * ↑n - ↑↑k)) ?cont ?eq_on ?eq_at
    apply Continuous.continuousWithinAt
    simp only [Polygon.edgePath]
    continuity
    apply eventually_nhdsWithin_of_forall
    intro x hx'
    have hx1 : x ≠ 1 := by
      have hk_le : k.val + 1 ≤ n := by omega
      have hk_lt : k.val + 1 < n := by
        refine Nat.lt_of_le_of_ne hk_le ?_
        intro heq
        apply last
        have h : (↑↑k + 1 : ℝ) = ↑n := by
          exact_mod_cast heq
        rw [h, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
      have hx_le : x ≤ (↑↑k + 1)/↑n := by
        exact (Set.mem_Icc.mp hx').right
      have h : (↑↑k + 1)/↑n < 1 := by
        have h1 : (↑↑k + 1 : ℝ) < (n : ℝ) := by
          norm_cast
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
        exact Nat.div_lt_one_iff (NeZero.pos n) |>.mpr hk_lt
      have xle1 : x < 1 := by
        have h' : (↑↑k + 1 : ℝ) / ↑n < 1 := by
          have hk_lt : k.val + 1 < n := by omega
          have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
          rw [div_lt_one hn_pos]
          norm_cast
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
        linarith
      exact Ne.symm (ne_of_gt xle1)
    simp only [hx1, ↓reduceIte]
    specialize onPiece x
    apply onPiece at hx'
    rcases hx' with onSegment | atEnd
    simp only [onSegment]
    subst atEnd
    simp only [div_mul_cancel_of_invertible, Int.floor_add_one, Int.floor_natCast,
      Int.toNat_natCast_add_one, add_sub_cancel_left]
    have hk_lt : k.val + 1 < n := by
      by_contra h
      push_neg at h
      have hle : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
      have heq : k.val + 1 = n := le_antisymm hle h
      apply last
      have heq' : (↑↑k + 1 : ℝ) = (n : ℝ) := by exact_mod_cast heq
      rw [heq']
      field_simp
      simp only [div_self_of_invertible]
    have : (↑k + 1) % n = ↑k + 1 := by
      exact Nat.mod_eq_of_lt hk_lt
    simp only [this,Polygon.edgePath]
    simp only [Nat.cast_add, Nat.cast_one, sub_self, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one]
    congr 1
    ext
    simp only [Fin.val_add]
    convert (Nat.mod_eq_of_lt hk_lt).symm
    simp only [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt (by omega : 1 < n)
    simp only [hx1, ↓reduceIte]
    simp only [div_mul_cancel_of_invertible, Int.floor_add_one, Int.floor_natCast,
      Int.toNat_natCast_add_one, add_sub_cancel_left]
    have hk_lt : k.val + 1 < n := by
      by_contra h
      push_neg at h
      have hle : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
      have heq : k.val + 1 = n := le_antisymm hle h
      apply last
      have heq' : (↑↑k + 1 : ℝ) = (n : ℝ) := by exact_mod_cast heq
      rw [heq']
      field_simp
      simp only [div_self_of_invertible]
    have mod_eq : (k.val + 1) % n = k.val + 1 := Nat.mod_eq_of_lt hk_lt
    simp only [mod_eq, Polygon.edgePath]
    have param_eq : (↑↑k + 1 : ℝ) - ↑(k.val + 1) = 0 := by simp
    simp only [param_eq, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    congr 1
    ext
    simp only [Fin.val_add]
    have hk_lt : k.val + 1 < n := by
      by_contra h
      push_neg at h
      have hle : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
      have heq : k.val + 1 = n := le_antisymm hle h
      apply hx1
      have : (↑↑k + 1 : ℝ) = ↑n := by exact_mod_cast heq
      rw [this, div_self (Nat.cast_ne_zero.mpr (NeZero.ne n))]
    have h1 : (1 : Fin n).val = 1 := by
      exact Nat.mod_eq_of_lt (by omega : 1 < n)
    rw [h1]
    exact mod_eq.symm

lemma boundaryParam_continuousOn : ContinuousOn poly.boundaryParam (Icc 0 1) := by
  have hn : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
  have cover :
      (Icc (0:ℝ) 1) = ⋃ k : Fin n, Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ)) := by
    ext x
    simp only [mem_iUnion, mem_Icc]
    constructor
    · -- x ∈ [0, 1] → x ∈ some [k/n, (k+1)/n]
      intro ⟨hx0, hx1⟩
      by_cases hx_eq_1 : x = 1
      · -- x = 1: use k = n - 1 (the last segment)
        have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
        use ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩
        simp only [hx_eq_1]
        have hsub : (n - 1 : ℕ) + 1 = n := Nat.sub_add_cancel h1
        constructor
        · -- (n-1)/n ≤ 1
          rw [div_le_one hn]
          have : (n - 1 : ℕ) ≤ n := Nat.sub_le n 1
          exact_mod_cast this
        · -- 1 ≤ ((n-1)+1)/n = n/n = 1
          have heq : ((n - 1 : ℕ) : ℝ) + 1 = n := by
            simp only [Nat.cast_sub h1, Nat.cast_one, sub_add_cancel]
          rw [heq, div_self (ne_of_gt hn)]
      · -- x < 1: use k = ⌊x * n⌋
        have hx_lt_1 : x < 1 := lt_of_le_of_ne hx1 hx_eq_1
        have hxn_nonneg : 0 ≤ x * n := mul_nonneg hx0 (le_of_lt hn)
        have hxn_lt_n : x * n < n := by nlinarith
        have hfloor_nonneg : 0 ≤ ⌊x * n⌋ := Int.floor_nonneg.mpr hxn_nonneg
        have hfloor_lt_n : ⌊x * n⌋ < n := Int.floor_lt.mpr hxn_lt_n
        have hfloor_toNat : (⌊x * n⌋.toNat : ℤ) = ⌊x * n⌋ := Int.toNat_of_nonneg hfloor_nonneg
        have hfloor_toNat_lt : ⌊x * n⌋.toNat < n := by
          have : (⌊x * n⌋.toNat : ℤ) < n := hfloor_toNat ▸ hfloor_lt_n
          exact Int.ofNat_lt.mp this
        use ⟨⌊x * n⌋.toNat, hfloor_toNat_lt⟩
        constructor
        · -- k/n ≤ x
          rw [div_le_iff₀ hn]
          have hle : (⌊x * n⌋ : ℝ) ≤ x * n := Int.floor_le (x * n)
          have hcast : (⌊x * n⌋.toNat : ℝ) = (⌊x * n⌋ : ℝ) := by
            rw [← Int.cast_natCast, hfloor_toNat]
          rw [hcast]
          exact hle
        · -- x ≤ (k+1)/n
          rw [le_div_iff₀ hn]
          have hlt : x * n < ⌊x * n⌋ + 1 := Int.lt_floor_add_one (x * n)
          have hcast : (⌊x * n⌋.toNat + 1 : ℝ) = (⌊x * n⌋ : ℝ) + 1 := by
            congr 1
            rw [← Int.cast_natCast, hfloor_toNat]
          rw [hcast]
          linarith
    · -- x ∈ some [k/n, (k+1)/n] → x ∈ [0, 1]
      intro ⟨k, hk_lo, hk_hi⟩
      constructor
      · -- 0 ≤ x
        have h0 : (0 : ℝ) ≤ k / n := div_nonneg (Nat.cast_nonneg k) (le_of_lt hn)
        linarith
      · -- x ≤ 1
        have hle : (k.val + 1 : ℝ) ≤ n := by
          have : k.val + 1 ≤ n := k.isLt
          exact_mod_cast this
        have h1 : (↑↑k + 1) / (↑n : ℝ) ≤ 1 := div_le_one_of_le₀ hle (le_of_lt hn)
        linarith
  have contOnCover :
      ContinuousOn poly.boundaryParam
        (⋃ k : Fin n, Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))) := by
    have hloc :
        LocallyFinite (fun k : Fin n => Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))) :=
      locallyFinite_of_finite (fun k : Fin n => Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ)))
    refine (LocallyFinite.continuousOn_iUnion (g := poly.boundaryParam) (f := fun k : Fin n =>
      Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))) hloc ?_ ?_)
    · intro k
      simpa using (isClosed_Icc :
        IsClosed (Icc (k/(n:ℝ)) ((k.val + 1)/(n:ℝ))))
    · intro k
      simpa using poly.boundaryParam_continuousOn_piece k
  simpa [cover] using contOnCover

/-- The boundary parameterization lifted to `AddCircle 1`. -/
noncomputable def circleMap : AddCircle (1 : ℝ) → EuclideanSpace ℝ (Fin 2) :=
  AddCircle.liftIco 1 0 poly.boundaryParam

lemma circleMap_continuous : Continuous poly.circleMap := by
  apply AddCircle.liftIco_continuous
  · simpa using poly.boundaryParam_zero_eq_one
  · simpa using poly.boundaryParam_continuousOn

lemma edgePaths_injOn_Ico : ∀ i : Fin n, InjOn (poly.toPolygon.edgePath i) (Ico 0 1) := by
  unfold Polygon.edgePath
  intro i x hx y hy h
  have hv : poly.toPolygon.vertices i ≠ poly.toPolygon.vertices (i + 1)
    := poly.adj_vertices_distinct i
  set v0 := poly.toPolygon.vertices i
  set v1 := poly.toPolygon.vertices (i + 1)
  have hdir : (v1 - v0) ≠ 0 := by
    -- v1 - v0 = 0 ↔ v1 = v0
    simp only [ne_eq, sub_eq_zero]
    push_neg
    exact Ne.symm (poly.adj_vertices_distinct i)
  -- rewrite lineMap to v0 + t • (v1 - v0)
  have h' : v0 + x • (v1 - v0) = v0 + y • (v1 - v0) := by
    -- If this `simpa` doesn't work in your file, see note below.
    simpa [v0, v1, AffineMap.lineMap_apply] using h
  -- cancel v0
  have h'' : x • (v1 - v0) = y • (v1 - v0) := by
    exact add_left_cancel h'
  -- turn that into (x - y) • (v1 - v0) = 0
  have hxmy : (x - y) • (v1 - v0) = 0 := by
    have : x • (v1 - v0) - y • (v1 - v0) = 0 := by
      simpa using (sub_eq_zero.mpr h'')
    simpa [sub_smul] using this
  -- now scalar * nonzero vector = 0 ⇒ scalar = 0
  have : x - y = 0 := (smul_eq_zero.mp hxmy).resolve_right hdir
  exact sub_eq_zero.mp this

lemma boundaryParam_injOn_Ico : InjOn poly.boundaryParam (Ico 0 1) := by
  intro x hx y hy hxy
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hx_ne1 : x ≠ (1 : ℝ) := ne_of_lt hx.2
  have hy_ne1 : y ≠ (1 : ℝ) := ne_of_lt hy.2
  -- unfold boundaryParam on Ico, so no `t = 1` branch
  simp only [boundaryParam, hx_ne1, ↓reduceIte, hy_ne1] at hxy
  -- indices
  set ix : Fin n :=
    ⟨⌊x * (n : ℝ)⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
  set iy : Fin n :=
    ⟨⌊y * (n : ℝ)⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
  -- parameters (Nat mod)
  set tx : ℝ := x * (n : ℝ) - ((⌊x * (n : ℝ)⌋.toNat % n : ℕ) : ℝ)
  set ty : ℝ := y * (n : ℝ) - ((⌊y * (n : ℝ)⌋.toNat % n : ℕ) : ℝ)
  --------------------------------------------------------------------
  -- htx : tx ∈ Ico 0 1  (nat-mod version)
  --------------------------------------------------------------------
  have htx : tx ∈ Ico (0 : ℝ) 1 := by
    have hx_mul_lt : x * (n : ℝ) < (n : ℝ) := by
      nlinarith [hx.2, npos]
    have hx_mul_nonneg : 0 ≤ x * (n : ℝ) := by
      nlinarith [hx.1, le_of_lt npos]
    have hfloor_nonneg : 0 ≤ (⌊x * (n : ℝ)⌋ : ℤ) :=
      Int.floor_nonneg.mpr hx_mul_nonneg
    have hfloor_lt_n : (⌊x * (n : ℝ)⌋ : ℤ) < n :=
      Int.floor_lt.mpr hx_mul_lt
    have hfloor_toNat : (⌊x * (n : ℝ)⌋.toNat : ℤ) = ⌊x * (n : ℝ)⌋ :=
      Int.toNat_of_nonneg hfloor_nonneg
    have hfloor_toNat_lt : ⌊x * (n : ℝ)⌋.toNat < n := by
      have : (⌊x * (n : ℝ)⌋.toNat : ℤ) < n := by
        simpa [hfloor_toNat] using hfloor_lt_n
      exact Int.ofNat_lt.mp this
    have hmod_eq :
        ⌊x * (n : ℝ)⌋.toNat % n = ⌊x * (n : ℝ)⌋.toNat :=
      Nat.mod_eq_of_lt hfloor_toNat_lt
    have htoNat_cast :
        (⌊x * (n : ℝ)⌋.toNat : ℝ) = (⌊x * (n : ℝ)⌋ : ℝ) := by
      rw [← Int.cast_natCast, hfloor_toNat]
    have hfloor_le : (⌊x * (n : ℝ)⌋ : ℝ) ≤ x * (n : ℝ) := by
      exact_mod_cast (Int.floor_le (x * (n : ℝ)))
    have h0 : 0 ≤ x * (n : ℝ) - (⌊x * (n : ℝ)⌋.toNat : ℝ) := by
      have : 0 ≤ x * (n : ℝ) - (⌊x * (n : ℝ)⌋ : ℝ) :=
        sub_nonneg.mpr hfloor_le
      simp [htoNat_cast]
    have h1 : x * (n : ℝ) - (⌊x * (n : ℝ)⌋.toNat : ℝ) < 1 := by
      have hlt : x * (n : ℝ) < (⌊x * (n : ℝ)⌋ : ℝ) + 1 := by
        exact_mod_cast (Int.lt_floor_add_one (x * (n : ℝ)))
      have : x * (n : ℝ) - (⌊x * (n : ℝ)⌋ : ℝ) < 1 := by
        linarith
      simpa [htoNat_cast] using this
    -- rewrite tx with hmod_eq
    have : tx = x * (n : ℝ) - (⌊x * (n : ℝ)⌋.toNat : ℝ) := by
      simp [tx, hmod_eq]
    -- finish
    simpa [this] using (And.intro h0 h1)
  --------------------------------------------------------------------
  -- hty : ty ∈ Ico 0 1  (nat-mod version)
  --------------------------------------------------------------------
  have hty : ty ∈ Ico (0 : ℝ) 1 := by
    have hy_mul_lt : y * (n : ℝ) < (n : ℝ) := by
      nlinarith [hy.2, npos]
    have hy_mul_nonneg : 0 ≤ y * (n : ℝ) := by
      nlinarith [hy.1, le_of_lt npos]
    have hfloor_nonneg : 0 ≤ (⌊y * (n : ℝ)⌋ : ℤ) :=
      Int.floor_nonneg.mpr hy_mul_nonneg
    have hfloor_lt_n : (⌊y * (n : ℝ)⌋ : ℤ) < n :=
      Int.floor_lt.mpr hy_mul_lt
    have hfloor_toNat : (⌊y * (n : ℝ)⌋.toNat : ℤ) = ⌊y * (n : ℝ)⌋ :=
      Int.toNat_of_nonneg hfloor_nonneg
    have hfloor_toNat_lt : ⌊y * (n : ℝ)⌋.toNat < n := by
      have : (⌊y * (n : ℝ)⌋.toNat : ℤ) < n := by
        simpa [hfloor_toNat] using hfloor_lt_n
      exact Int.ofNat_lt.mp this
    have hmod_eq :
        ⌊y * (n : ℝ)⌋.toNat % n = ⌊y * (n : ℝ)⌋.toNat :=
      Nat.mod_eq_of_lt hfloor_toNat_lt
    have htoNat_cast :
        (⌊y * (n : ℝ)⌋.toNat : ℝ) = (⌊y * (n : ℝ)⌋ : ℝ) := by
      rw [← Int.cast_natCast, hfloor_toNat]
    have hfloor_le : (⌊y * (n : ℝ)⌋ : ℝ) ≤ y * (n : ℝ) := by
      exact_mod_cast (Int.floor_le (y * (n : ℝ)))
    have h0 : 0 ≤ y * (n : ℝ) - (⌊y * (n : ℝ)⌋.toNat : ℝ) := by
      have : 0 ≤ y * (n : ℝ) - (⌊y * (n : ℝ)⌋ : ℝ) :=
        sub_nonneg.mpr hfloor_le
      simp only [htoNat_cast]
      exact this
    have h1 : y * (n : ℝ) - (⌊y * (n : ℝ)⌋.toNat : ℝ) < 1 := by
      have hlt : y * (n : ℝ) < (⌊y * (n : ℝ)⌋ : ℝ) + 1 := by
        exact_mod_cast (Int.lt_floor_add_one (y * (n : ℝ)))
      have : y * (n : ℝ) - (⌊y * (n : ℝ)⌋ : ℝ) < 1 := by
        linarith
      simp only [htoNat_cast]
      exact this
    have : ty = y * (n : ℝ) - (⌊y * (n : ℝ)⌋.toNat : ℝ) := by
      simp [ty, hmod_eq]
    simpa [this] using (And.intro h0 h1)
  --------------------------------------------------------------------
  -- CASE 1: same edge
  --------------------------------------------------------------------
  by_cases sameEdge : ix = iy
  · -- rewrite hxy onto one edge and use InjOn to get tx = ty
    have hxy' : poly.toPolygon.edgePath ix tx = poly.toPolygon.edgePath ix ty := by
      simpa [sameEdge] using hxy
    have htparam : tx = ty := (poly.edgePaths_injOn_Ico ix) htx hty hxy'
    have hx_mul_lt : x * (n : ℝ) < (n : ℝ) := by nlinarith [hx.2, npos]
    have hy_mul_lt : y * (n : ℝ) < (n : ℝ) := by nlinarith [hy.2, npos]
    have hfloorx_nonneg : 0 ≤ (⌊x * (n : ℝ)⌋ : ℤ) := by
      have : 0 ≤ x * (n : ℝ) := by nlinarith [hx.1, le_of_lt npos]
      exact Int.floor_nonneg.mpr this
    have hfloory_nonneg : 0 ≤ (⌊y * (n : ℝ)⌋ : ℤ) := by
      have : 0 ≤ y * (n : ℝ) := by nlinarith [hy.1, le_of_lt npos]
      exact Int.floor_nonneg.mpr this
    have hfloorx_lt_n : (⌊x * (n : ℝ)⌋ : ℤ) < n := Int.floor_lt.mpr hx_mul_lt
    have hfloory_lt_n : (⌊y * (n : ℝ)⌋ : ℤ) < n := Int.floor_lt.mpr hy_mul_lt
    have hx_floor_toNat : (⌊x * (n : ℝ)⌋.toNat : ℤ) = ⌊x * (n : ℝ)⌋ :=
      Int.toNat_of_nonneg hfloorx_nonneg
    have hy_floor_toNat : (⌊y * (n : ℝ)⌋.toNat : ℤ) = ⌊y * (n : ℝ)⌋ :=
      Int.toNat_of_nonneg hfloory_nonneg
    have hx_toNat_lt : ⌊x * (n : ℝ)⌋.toNat < n := by
      have : (⌊x * (n : ℝ)⌋.toNat : ℤ) < n := by
        simpa [hx_floor_toNat] using hfloorx_lt_n
      exact Int.ofNat_lt.mp this
    have hy_toNat_lt : ⌊y * (n : ℝ)⌋.toNat < n := by
      have : (⌊y * (n : ℝ)⌋.toNat : ℤ) < n := by
        simpa [hy_floor_toNat] using hfloory_lt_n
      exact Int.ofNat_lt.mp this
    have hx_mod : ⌊x * (n : ℝ)⌋.toNat % n = ⌊x * (n : ℝ)⌋.toNat :=
      Nat.mod_eq_of_lt hx_toNat_lt
    have hy_mod : ⌊y * (n : ℝ)⌋.toNat % n = ⌊y * (n : ℝ)⌋.toNat :=
      Nat.mod_eq_of_lt hy_toNat_lt
    have hval : (⌊x * (n : ℝ)⌋.toNat % n) = (⌊y * (n : ℝ)⌋.toNat % n) := by
      -- compare Fin.val
      simpa [ix, iy] using congrArg Fin.val sameEdge
    have hfloorNat : ⌊x * (n : ℝ)⌋.toNat = ⌊y * (n : ℝ)⌋.toNat := by
      -- mod is identity on both sides
      simpa [hx_mod, hy_mod] using hval
    -- now tx=ty becomes x*n = y*n, then x=y
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt npos
    have hmul : x * (n : ℝ) = y * (n : ℝ) := by
      -- expand tx/ty, rewrite hfloorNat
      have : x * (n : ℝ) - ((⌊x * (n : ℝ)⌋.toNat % n : ℕ) : ℝ)
            =
            y * (n : ℝ) - ((⌊y * (n : ℝ)⌋.toNat % n : ℕ) : ℝ) := by
        simpa [tx, ty] using htparam
      -- replace the casts using hfloorNat and cancel
      have hcast : ((⌊x * (n : ℝ)⌋.toNat % n : ℕ) : ℝ)
                 = ((⌊y * (n : ℝ)⌋.toNat % n : ℕ) : ℝ) := by
        -- mod is identity, and floors equal
        have : (⌊x * (n : ℝ)⌋.toNat % n) = (⌊y * (n : ℝ)⌋.toNat % n) := by
          simp [hy_mod, hfloorNat]
        exact_mod_cast this
      linarith [this, hcast]
    have : x = y := by
      -- cancel the nonzero factor n
      have := (mul_eq_mul_right_iff).1 hmul
      rcases this with hxy' | hn
      · exact hxy'
      · exact (hn0 hn).elim
    exact this
  --------------------------------------------------------------------
  -- CASE 2: adjacent (ix = iy + 1)
  --------------------------------------------------------------------
  by_cases adjEdges : ix = iy + 1
  · -- The point lies in edgeSet iy ∩ edgeSet ix
    -- Which equals edgeSet iy ∩ edgeSet (iy + 1) = {vertices (iy + 1)}
    -- On edge iy, this vertex is at parameter 1, contradicting ty < 1
    have htxIcc : tx ∈ Icc (0 : ℝ) 1 := ⟨htx.1, le_of_lt htx.2⟩
    have htyIcc : ty ∈ Icc (0 : ℝ) 1 := ⟨hty.1, le_of_lt hty.2⟩
    have xin : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet ix := by
      simpa [poly.toPolygon.edgeSet_eq_image ix] using mem_image_of_mem (poly.toPolygon.edgePath ix) htxIcc
    have yin0 : poly.toPolygon.edgePath iy ty ∈ poly.toPolygon.edgeSet iy := by
      simpa [poly.toPolygon.edgeSet_eq_image iy] using mem_image_of_mem (poly.toPolygon.edgePath iy) htyIcc
    have yin : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet iy := by simpa [hxy] using yin0
    -- The point is in the intersection
    have hp : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet iy ∩ poly.toPolygon.edgeSet (iy + 1) := by
      rw [← adjEdges]; exact ⟨yin, xin⟩
    -- By adjacent_edges_inter, this intersection is {vertices (iy + 1)}
    rw [poly.adjacent_edges_inter iy] at hp
    simp only [mem_singleton_iff] at hp
    -- So poly.toPolygon.edgePath iy ty = vertices (iy + 1)
    have hty_vertex : poly.toPolygon.edgePath iy ty = poly.toPolygon.vertices (iy + 1) := by
      rw [← hxy, hp]
    -- On edge iy, edgePath iy 1 = vertices (iy + 1)
    have hedge_at_1 : poly.toPolygon.edgePath iy 1 = poly.toPolygon.vertices (iy + 1) := by
      simp only [Polygon.edgePath, AffineMap.lineMap_apply_one]
    -- lineMap is injective when endpoints are distinct
    have hne : poly.toPolygon.vertices iy ≠ poly.toPolygon.vertices (iy + 1) := poly.adj_vertices_distinct iy
    have hty_eq_1 : ty = 1 := by
      have heq : poly.toPolygon.edgePath iy ty = poly.toPolygon.edgePath iy 1 := hty_vertex.trans hedge_at_1.symm
      simp only [Polygon.edgePath, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at heq
      have hdir : poly.toPolygon.vertices (iy + 1) - poly.toPolygon.vertices iy ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      -- heq : ty • (v1 - v0) + v0 = 1 • (v1 - v0) + v0
      -- Subtract v0 from both sides
      have h2 : ty • (poly.toPolygon.vertices (iy + 1) - poly.toPolygon.vertices iy) =
                (1 : ℝ) • (poly.toPolygon.vertices (iy + 1) - poly.toPolygon.vertices iy) := by
        have h := congrArg (· - poly.toPolygon.vertices iy) heq
        simp only [add_sub_cancel_right] at h
        exact h
      have h3 : (ty - 1) • (poly.toPolygon.vertices (iy + 1) - poly.toPolygon.vertices iy) = 0 := by
        rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hdir)
    -- But ty ∈ Ico 0 1, so ty < 1
    exact absurd hty_eq_1 (ne_of_lt hty.2)
  --------------------------------------------------------------------
  -- CASE 3: adjacent (iy = ix + 1)
  --------------------------------------------------------------------
  by_cases adjEdges' : iy = ix + 1
  · -- Similar: the point lies in edgeSet ix ∩ edgeSet (ix + 1) = {vertices (ix + 1)}
    -- On edge ix, this vertex is at parameter 1, contradicting tx < 1
    have htxIcc : tx ∈ Icc (0 : ℝ) 1 := ⟨htx.1, le_of_lt htx.2⟩
    have htyIcc : ty ∈ Icc (0 : ℝ) 1 := ⟨hty.1, le_of_lt hty.2⟩
    have xin : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet ix := by
      simpa [poly.toPolygon.edgeSet_eq_image ix] using mem_image_of_mem (poly.toPolygon.edgePath ix) htxIcc
    have yin0 : poly.toPolygon.edgePath iy ty ∈ poly.toPolygon.edgeSet iy := by
      simpa [poly.toPolygon.edgeSet_eq_image iy] using mem_image_of_mem (poly.toPolygon.edgePath iy) htyIcc
    have yin : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet iy := by simpa [hxy] using yin0
    -- The point is in the intersection
    have hp : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet ix ∩ poly.toPolygon.edgeSet (ix + 1) := by
      rw [← adjEdges']; exact ⟨xin, yin⟩
    -- By adjacent_edges_inter, this intersection is {vertices (ix + 1)}
    rw [poly.adjacent_edges_inter ix] at hp
    simp only [mem_singleton_iff] at hp
    -- So poly.toPolygon.edgePath ix tx = vertices (ix + 1)
    -- On edge ix, edgePath ix 1 = vertices (ix + 1)
    have hedge_at_1 : poly.toPolygon.edgePath ix 1 = poly.toPolygon.vertices (ix + 1) := by
      simp only [Polygon.edgePath, AffineMap.lineMap_apply_one]
    -- lineMap is injective when endpoints are distinct
    have hne : poly.toPolygon.vertices ix ≠ poly.toPolygon.vertices (ix + 1)
      := poly.adj_vertices_distinct ix
    have htx_eq_1 : tx = 1 := by
      have heq : poly.toPolygon.edgePath ix tx = poly.toPolygon.edgePath ix 1
        := hp.trans hedge_at_1.symm
      simp only [Polygon.edgePath, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at heq
      have hdir : poly.toPolygon.vertices (ix + 1) - poly.toPolygon.vertices ix ≠ 0
        := sub_ne_zero.mpr (Ne.symm hne)
      -- heq : tx • (v1 - v0) + v0 = 1 • (v1 - v0) + v0
      -- Subtract v0 from both sides
      have h2 : tx • (poly.toPolygon.vertices (ix + 1) - poly.toPolygon.vertices ix) =
                (1 : ℝ) • (poly.toPolygon.vertices (ix + 1) - poly.toPolygon.vertices ix) := by
        have h := congrArg (· - poly.toPolygon.vertices ix) heq
        simp only [add_sub_cancel_right] at h
        exact h
      have h3 : (tx - 1) • (poly.toPolygon.vertices (ix + 1) - poly.toPolygon.vertices ix) = 0 := by
        rw [sub_smul, h2, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hdir)
    -- But tx ∈ Ico 0 1, so tx < 1
    exact absurd htx_eq_1 (ne_of_lt htx.2)
  --------------------------------------------------------------------
  -- CASE 4: non-adjacent → disjoint contradiction
  --------------------------------------------------------------------
  have sameEdge : ix ≠ iy := by simpa using sameEdge
  have adjEdges : ix ≠ iy + 1 := by simpa using adjEdges
  have adjEdges' : iy ≠ ix + 1 := by simpa using adjEdges'
  have htriple : ix ≠ iy ∧ ix ≠ iy + 1 ∧ iy ≠ ix + 1 :=
    ⟨sameEdge, adjEdges, adjEdges'⟩
  have hdisj : Disjoint (poly.toPolygon.edgeSet iy) (poly.toPolygon.edgeSet ix) :=
    poly.non_adjacent_edges_disjoint iy ix htriple
  -- show the common point lies in both edge sets
  have xin : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet ix := by
    -- tx ∈ Icc 0 1
    have htxIcc : tx ∈ Icc (0 : ℝ) 1 := ⟨htx.1, le_of_lt htx.2⟩
  -- reduce goal to membership in the image, then use mem_image_of_mem
    refine (poly.toPolygon.edgeSet_eq_image ix).symm ▸ ?_
    exact mem_image_of_mem (poly.toPolygon.edgePath ix) htxIcc
  have yin0 : poly.toPolygon.edgePath iy ty ∈ poly.toPolygon.edgeSet iy := by
    have htyIcc : ty ∈ Icc (0 : ℝ) 1 := ⟨hty.1, le_of_lt hty.2⟩
  -- reduce goal to membership in the image, then use mem_image_of_mem
    refine (poly.toPolygon.edgeSet_eq_image iy).symm ▸ ?_
    exact mem_image_of_mem (poly.toPolygon.edgePath iy) htyIcc
  have yin : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet iy := by
  -- rewrite using hxy
    simpa [hxy] using yin0
  have hp : poly.toPolygon.edgePath ix tx ∈ poly.toPolygon.edgeSet iy ∩ poly.toPolygon.edgeSet ix :=
    ⟨yin, xin⟩
  exact (hdisj.le_bot hp).elim

lemma circleMap_injective : Function.Injective poly.circleMap := by
  unfold Function.Injective
  intro a₁ a₂
  unfold circleMap
  simp only [AddCircle.liftIco, AddCircle.equivIco]
  simp only [Function.comp_apply, restrict_apply]
  simp only [QuotientAddGroup.equivIcoMod]
  simp only [Equiv.coe_fn_mk]
  intro h
  set t₁ := AddCircle.equivIco 1 0 a₁ with ht₁_def
  set t₂ := AddCircle.equivIco 1 0 a₂ with ht₂_def
  have ht₁_mem : t₁.val ∈ Ico (0 : ℝ) 1 := by simpa using t₁.property
  have ht₂_mem : t₂.val ∈ Ico (0 : ℝ) 1 := by simpa using t₂.property
  have heq : t₁.val = t₂.val := poly.boundaryParam_injOn_Ico ht₁_mem ht₂_mem h
  have : t₁ = t₂ := Subtype.ext heq
  calc a₁ = (AddCircle.equivIco 1 0).symm t₁ := by simp [ht₁_def]
    _ = (AddCircle.equivIco 1 0).symm t₂ := by rw [this]
    _ = a₂ := by simp [ht₂_def]

lemma circleMap_range : range poly.circleMap = poly.toPolygon.boundary := by
  unfold circleMap Polygon.boundary
  ext p
  simp only [mem_range, mem_iUnion]
  constructor
  · -- Forward: if p is in the range of circleMap, it's in some edgeSet
    intro ⟨a, ha⟩
    -- Get the representative t ∈ [0, 1)
    let t := (AddCircle.equivIco 1 0 a).val
    have ht_mem : t ∈ Ico (0 : ℝ) 1 := by simpa using (AddCircle.equivIco 1 0 a).property
    have ht1 : t ≠ 1 := ne_of_lt ht_mem.2
    -- The segment index
    let i : Fin n := ⟨⌊t * n⌋.toNat % n, Nat.mod_lt _ (NeZero.pos n)⟩
    use i
    -- boundaryParam t ∈ edgeSet i
    simp only [Polygon.edgeSet]
    -- liftIco applies boundaryParam to the representative
    simp only [AddCircle.liftIco, Function.comp_apply, Set.restrict_apply] at ha
    simp only [boundaryParam] at ha
    rw [← ha]
    -- edgePath i (t * n - i) is in segment
    unfold Polygon.edgePath
    -- Need to show lineMap is in segment for parameter in [0, 1]
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    -- First, establish that i.val = ⌊t * n⌋ (since t * n < n)
    have ht_mul_n_lt : t * n < n := by
      have ht1 : t < 1 := ht_mem.2
      have : t * n < 1 * n := by nlinarith
      linarith
    have ht_mul_n_nonneg : 0 ≤ t * n := by
      have h0 : 0 ≤ t := ht_mem.1
      nlinarith
    have hfloor_nonneg : 0 ≤ ⌊t * n⌋ := Int.floor_nonneg.mpr ht_mul_n_nonneg
    have hfloor_lt_n : ⌊t * n⌋ < n := Int.floor_lt.mpr ht_mul_n_lt
    have hfloor_toNat : (⌊t * n⌋.toNat : ℤ) = ⌊t * n⌋ := Int.toNat_of_nonneg hfloor_nonneg
    have hfloor_toNat_lt : ⌊t * n⌋.toNat < n := by
      have : (⌊t * n⌋.toNat : ℤ) < n := hfloor_toNat ▸ hfloor_lt_n
      exact Int.ofNat_lt.mp this
    have hmod_eq : ⌊t * n⌋.toNat % n = ⌊t * n⌋.toNat := Nat.mod_eq_of_lt hfloor_toNat_lt
    have hi_val : (i.val : ℝ) = ⌊t * n⌋ := by
      simp only [i, hmod_eq]
      have : (⌊t * n⌋.toNat : ℝ) = (⌊t * n⌋.toNat : ℤ) := by norm_cast
      rw [this, hfloor_toNat]
    -- The parameter t * n - i is in [0, 1]
    have hparam_nonneg : 0 ≤ t * n - i := by
      rw [hi_val]
      exact sub_nonneg.mpr (Int.floor_le (t * n))
    have hparam_le_one : t * n - i ≤ 1 := by
      rw [hi_val]
      have := Int.lt_floor_add_one (t * n)
      linarith
    split_ifs with ht1'
    · -- Case t = 1, contradicts ht1
      exact absurd ht1' ht1
    · -- Case t ≠ 1
      rw [segment_eq_image_lineMap]
      have hparam_mem : t * n - i ∈ Icc (0 : ℝ) 1 := ⟨hparam_nonneg, hparam_le_one⟩
      exact mem_image_of_mem _ hparam_mem
  · -- Backward: if p is in some edgeSet, it's in the range of circleMap
    intro h
    rcases h with ⟨i, hi⟩
    rw[poly.toPolygon.edgeSet_eq_image i,mem_image] at hi
    rcases hi with ⟨t, htmem⟩
    let s : ℝ := (i.val + t) / n
    by_cases s1 : s = 1
    have nit : n = (i : ℕ)  + t := by
      have hn0 : ( (n : ℝ) ) ≠ 0 := by
        exact_mod_cast (NeZero.ne n)
      have hs : ((↑↑i + t) / (n : ℝ)) = (1 : ℝ) := by
        simpa [s] using s1
      have h : (↑↑i + t) = (1 : ℝ) * (n : ℝ) := by
        exact (div_eq_iff hn0).1 hs
      simpa [one_mul, add_comm, add_left_comm, add_assoc] using h.symm
    have tle1 : t ≤ 1 := (Set.mem_Icc.mp htmem.left).right
    have nlei1 : n ≤ (i : ℕ) + 1 := by
      have hreal : (n : ℝ) ≤ (i : ℝ) + 1 := by
        linarith [nit, tle1]
      exact_mod_cast hreal
    have : n ≥ (i : ℕ) + 1 := Nat.succ_le_of_lt i.isLt
    have ni1 : n = (i : ℕ) + 1 := by exact Nat.le_antisymm nlei1 this
    have t1 : t = 1 := by
      have hthisR : (n : ℝ) = (i : ℝ) + 1 := by
      -- cast `this` to ℝ
        have := congrArg (fun m : ℕ => (m : ℝ)) ni1
        -- simplify the cast of `(i : ℕ) + 1`
        simpa [Nat.cast_add, Nat.cast_one] using this
      have hit : (i : ℝ) + t = (i : ℝ) + 1 := by
        -- rewrite `(n:ℝ)` using `nit` and `hthisR`
        calc
          (i : ℝ) + t = (n : ℝ) := by simpa using nit.symm
          _ = (i : ℝ) + 1 := hthisR
      exact add_left_cancel hit
    have hp : p = poly.toPolygon.edgePath i 1 := by
      calc
        p = poly.toPolygon.edgePath i t := by simpa using htmem.2.symm
        _ = poly.toPolygon.edgePath i 1 := by simp [t1]
    unfold Polygon.edgePath at hp
    simp only [AffineMap.lineMap_apply_one] at hp
    have hn3 : (3 : ℕ) ≤ n := poly.n_ge_3
    have h1lt : (1 : ℕ) < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hn3
    have hmod : ((i : ℕ) + 1) % n = 0 := by
      -- rewrite the denominator using ni1, so it's x % x
      simp only [ni1, Nat.mod_self]
    have hi_add_one : (i + 1 : Fin n) = 0 := by
      apply Fin.ext
      -- (i+1).val = (i.val + 1) % n
      -- and 0.val = 0
      simp only [Fin.val_add, Fin.coe_ofNat_eq_mod, Nat.add_mod_mod, hmod, Nat.zero_mod]
    have hwrap : poly.toPolygon.vertices (i + 1) = poly.toPolygon.vertices 0 := by
      simp only [hi_add_one]
    rw[hp]
    simp only [hwrap]
    unfold boundaryParam
    use (0 : AddCircle (1:ℝ))
    have h0 : (0 : ℝ) ∈ Set.Ico (0:ℝ) (0 + (1:ℝ)) := by simp only [zero_add, mem_Ico,
      le_refl, zero_lt_one, and_self]
    let f : ℝ → EuclideanSpace ℝ (Fin 2) :=
      fun t =>
        if t = 1 then poly.toPolygon.vertices 0
        else
          poly.toPolygon.edgePath
            ⟨⌊t * (n:ℝ)⌋.toNat % n, by
              simpa using (by
                exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))
                )⟩
            (t * (n:ℝ) - (⌊t * (n:ℝ)⌋.toNat % n : ℕ))
    have hlift : AddCircle.liftIco (1:ℝ) 0 f 0 = f 0 := by
  -- `0` in AddCircle is the coercion of `⟨0,h0⟩`
      simpa [f] using
        (AddCircle.liftIco_coe_apply (p := (1:ℝ)) (a := (0:ℝ)) (f := f) (x := (0:ℝ)) h0)
    rw [hlift]
    simp only [zero_ne_one, ↓reduceIte, zero_mul, Int.floor_zero, Int.toNat_zero, Nat.zero_mod,
      Fin.mk_zero', CharP.cast_eq_zero, sub_self, f]
    simp only [Polygon.edgePath]
    simp only [zero_add, AffineMap.lineMap_apply_zero]
    use s
    simp only [AddCircle.liftIco, Function.comp_apply, Set.restrict_apply]
    have hs_nonneg : 0 ≤ s := by
      simp only [s]
      apply div_nonneg
      · have := htmem.1.1; linarith
      · exact le_of_lt (Nat.cast_pos.mpr (NeZero.pos n))
    have hs_le_one : s ≤ 1 := by
      simp only [s]
      rw [div_le_one (Nat.cast_pos.mpr (NeZero.pos n))]
      have hi_nat : i.val ≤ n - 1 := by omega
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
      have hi : (i.val : ℝ) ≤ n - 1 := by
        have : (n - 1 : ℕ) = (n : ℝ) - 1 := by simp [Nat.cast_sub hn1]
        calc (i.val : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hi_nat
          _ = n - 1 := this
      linarith [htmem.1.2]
    have hs_lt_one : s < 1 := lt_of_le_of_ne hs_le_one s1
    have hrep : ↑((AddCircle.equivIco (1 : ℝ) 0) (s : AddCircle (1 : ℝ))) = s := by
      have hs_mem : s ∈ Ico (0 : ℝ) (0 + 1) := by simp [hs_nonneg, hs_lt_one]
      simp only [AddCircle.equivIco_coe_eq hs_mem]
    rw[hrep]
    simp only [boundaryParam, if_neg s1]
    have : ⌊s * ↑n⌋.toNat % n = ↑i ∨ s = (↑↑i + 1) / ↑n := by
      have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      by_cases ht1 : t = 1
      · -- t = 1 means s = (i + 1) / n
        right
        simp only [s, ht1]
      · -- t < 1 means floor lands on i
        left
        have ht_lt_one : t < 1 := lt_of_le_of_ne htmem.1.2 ht1
        have hsn_eq : s * n = i.val + t := by simp only [s]; field_simp
        have hlo : (i.val : ℝ) ≤ s * n := by rw [hsn_eq]; linarith [htmem.1.1]
        have hhi : s * n < i.val + 1 := by rw [hsn_eq]; linarith
        have floorEq : ⌊s * n⌋ = i.val := by
          rw [Int.floor_eq_iff]
          constructor
          · exact_mod_cast hlo
          · exact_mod_cast hhi
        simp only [floorEq, Int.toNat_natCast, Nat.mod_eq_of_lt i.isLt]
    rcases this with onSegment | atEdge
    simp only [onSegment]
    simp only [Fin.eta]
    have : (s * ↑n - ↑↑i) = t := by
      simp only [s]
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      field_simp
      ring
    rw[this]
    exact htmem.right
    have : ⌊s * ↑n⌋.toNat % n = ↑i + 1 := by
      rw [atEdge]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      -- Simplify (i + 1) / n * n = i + 1
      rw [div_mul_cancel₀ _ hn_ne]
      -- ⌊i + 1⌋ = i + 1 since it's a nat
      have heq : (↑↑i + 1 : ℝ) = ((i.val + 1 : ℕ) : ℝ) := by simp
      rw [heq, Int.floor_natCast, Int.toNat_natCast]
      -- (i + 1) % n = i + 1 since i + 1 < n
      have hi_lt : i.val + 1 < n := by
        have h : s < 1 := hs_lt_one
        rw [atEdge, div_lt_one hn_pos] at h
        exact_mod_cast h
      exact Nat.mod_eq_of_lt hi_lt
    simp only [this]
    simp only [Nat.cast_add, Nat.cast_one]
    have : s * ↑n = i + 1 := by
      rw [atEdge]
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      field_simp
    simp only [this]
    simp only [sub_self]
    rw[← htmem.right]
    have t1 : t = 1 := by
      have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      have hs_eq : (i.val + t : ℝ) / n = s := rfl
      rw [atEdge] at hs_eq
      field_simp at hs_eq
      linarith
    simp only [t1]
    unfold Polygon.edgePath
    simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    congr 1
    apply Fin.ext
    simp only [Fin.val_add]
    have hi_lt : i.val + 1 < n := by
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
      have h : s < 1 := hs_lt_one
      rw [atEdge, div_lt_one hn_pos] at h
      exact_mod_cast h
    simp only [Fin.val_one']
    have h1_lt : 1 < n := by omega
    rw [Nat.mod_eq_of_lt h1_lt]
    exact (Nat.mod_eq_of_lt hi_lt).symm

/-- The boundary of a simple polygon is a simple closed curve. -/
theorem boundary_isSimpleClosedCurve : IsSimpleClosedCurve poly.toPolygon.boundary :=
  ⟨poly.circleMap, poly.circleMap_continuous, poly.circleMap_injective, poly.circleMap_range⟩

/-- The Jordan decomposition of a simple polygon's boundary. -/
noncomputable def jordanDecomp (poly : SimpleEuclideanPolygon n) :
    JordanDecomposition poly.toPolygon.boundary :=
  jordan_curve_theorem (γ := poly.toPolygon.boundary) (boundary_isSimpleClosedCurve poly)

noncomputable def interior : Set (EuclideanSpace ℝ (Fin 2)) :=
  (jordanDecomp poly).interior

noncomputable def exterior : Set (EuclideanSpace ℝ (Fin 2)) :=
  (jordanDecomp poly).exterior

@[simp] lemma interior_def :
    poly.interior = (jordanDecomp poly).interior := rfl

@[simp] lemma exterior_def :
    poly.exterior = (jordanDecomp poly).exterior := rfl



end SimpleEuclideanPolygon
