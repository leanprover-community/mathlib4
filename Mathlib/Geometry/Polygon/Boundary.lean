/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Geometry.Polygon.Simple
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Polygon Boundary Map
-/

@[expose] public section

namespace Polygon

open Set AffineMap

variable {R V P : Type*} [Ring R] [LinearOrder R] [FloorRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

/-- The piecewise-linear boundary parametrization on `R` formed by concatenating edges. -/
noncomputable def boundaryParam (poly : Polygon P n) (t : R) : P :=
  let i : Fin n := ⟨(Int.floor t).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  let f : R := Int.fract t
  poly.edgePath (R := R) i f

noncomputable def boundaryMap [IsStrictOrderedRing R] [Archimedean R]
    (poly : Polygon P n) : AddCircle (n : R) → P :=
  haveI : Fact ((0 : R) < (n : R)) := ⟨by exact_mod_cast Nat.pos_of_neZero n⟩
  AddCircle.liftIco (p := (n : R)) (a := (0 : R)) (poly.boundaryParam (R := R))

variable {R V P : Type*}
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
variable [Archimedean R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]
variable {poly : Polygon P n}

private instance : Fact ((0 : R) < (n : R)) := ⟨by exact_mod_cast Nat.pos_of_neZero n⟩

theorem range_boundaryMap : Set.range (poly.boundaryMap (R := R)) = poly.boundary R := by
  ext p
  simp only [mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨t, htmem, rfl⟩ := AddCircle.eq_coe_Ico q
    simp only [boundaryMap, boundary, mem_iUnion]
    rw [AddCircle.liftIco_coe_apply (by simpa [zero_add])]
    simp only [boundaryParam]
    let i : Fin n := ⟨(Int.floor t).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
    use i
    rw [edgeSet_eq_image_edgePath]
    exact ⟨Int.fract t, Ico_subset_Icc_self ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, rfl⟩
  · simp only [boundary, mem_iUnion]
    rintro ⟨i, hp⟩
    rw [edgeSet_eq_image_edgePath] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    by_cases hu1 : u < 1
    · let t : R := i + u
      have ht_lo : (0 : R) ≤ t := add_nonneg (by exact_mod_cast i.val.zero_le) hu.1
      have ht_hi : t < n := by
        calc ↑↑i + u < ↑↑i + 1 := by simp only [add_lt_add_iff_left]; exact hu1
          _ ≤ n := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      have htmem : t ∈ Ico (0 : R) n := ⟨ht_lo, ht_hi⟩
      use t
      simp only [boundaryMap]
      rw [AddCircle.liftIco_coe_apply (by simpa [zero_add])]
      have h : ⌊t⌋ = (i : ℤ) := Int.floor_eq_iff.mpr (by
          simp only [t, Int.cast_natCast]
          exact ⟨le_add_of_nonneg_right hu.1, by simp only [add_lt_add_iff_left]; exact hu1⟩)
      have hfloor : ⌊t⌋.toNat % n = i := by
        simp [h, Int.toNat_natCast, Nat.mod_eq_of_lt i.isLt]
      have hfrac : Int.fract t = u := by
        simp [Int.fract, h, t, Int.cast_natCast]
      simp only [boundaryParam, hfloor, hfrac]
    · push_neg at hu1
      simp only [le_antisymm hu.2 hu1, edgePath, AffineMap.lineMap_apply_one]
      let t : R := ((i + 1 : Fin n) : ℕ)
      have htmem : t ∈ Ico (0 : R) n := by
        simp only [t, Set.mem_Ico]
        exact ⟨by exact_mod_cast (i+1 : Fin n).val.zero_le,
               by exact_mod_cast (i+1 : Fin n).isLt⟩
      use t
      simp only [boundaryMap]
      rw [AddCircle.liftIco_coe_apply (by simpa [zero_add])]
      simp only [boundaryParam, Int.floor_natCast, Int.toNat_natCast,
        Nat.mod_eq_of_lt (i+1 : Fin n).isLt, t, edgePath, Fin.eta,
        Int.fract_natCast, lineMap_apply_zero]

theorem isSimple_boundaryMap_injective [IsDomain R] [Module.IsTorsionFree R V]
    (h : poly.IsSimple R) : Function.Injective (poly.boundaryMap (R := R)) := by
  intro x y heq
  obtain ⟨s, hs_mem, rfl⟩ := AddCircle.eq_coe_Ico x
  obtain ⟨t, htmem, rfl⟩ := AddCircle.eq_coe_Ico y
  have hs_mem' : s ∈ Ico (0 : R) n := by simpa [zero_add] using hs_mem
  have htmem' : t ∈ Ico (0 : R) n := by simpa [zero_add] using htmem
  simp only [boundaryMap] at heq
  rw [AddCircle.liftIco_coe_apply (by simpa [zero_add]),
      AddCircle.liftIco_coe_apply (by simpa [zero_add])] at heq
  unfold boundaryParam at heq
  simp only at heq
  let sindex : Fin n := ⟨(Int.floor s).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  let tindex : Fin n := ⟨(Int.floor t).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  by_cases hindex : sindex = tindex
  · simp only [sindex, tindex] at hindex
    have hfrac : Int.fract s = Int.fract t := by
      rw [hindex] at heq
      exact lineMap_injective R (h.hasNondegenerateEdges tindex) heq
    simp only [Fin.mk.injEq] at hindex
    have hfloor : ⌊s⌋ = ⌊t⌋ := by
      have := Int.floor_nonneg.mpr hs_mem'.1
      have := Int.floor_nonneg.mpr htmem'.1
      have : ⌊s⌋ < n := by exact_mod_cast (Int.floor_le s).trans_lt hs_mem'.2
      have : ⌊t⌋ < n := by exact_mod_cast (Int.floor_le t).trans_lt htmem'.2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hindex
      omega
    have hst : s = t := by
      rw [← Int.floor_add_fract s, ← Int.floor_add_fract t, hfloor, hfrac]
    simp only [hst]
  · have hp_in_both : poly.edgePath R sindex (Int.fract s) ∈
        poly.edgeSet R sindex ∩ poly.edgeSet R tindex :=
      ⟨by rw [edgeSet_eq_image_edgePath]
          exact ⟨_, Ico_subset_Icc_self ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, rfl⟩,
       by rw [edgeSet_eq_image_edgePath, heq]
          exact ⟨_, Ico_subset_Icc_self ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, rfl⟩⟩
    by_cases hadj : tindex = sindex + 1
    · simp only [hadj, h.adjacent_inter sindex, mem_singleton_iff] at hp_in_both
      exact absurd (lineMap_injective R (h.hasNondegenerateEdges sindex)
        (hp_in_both.trans (lineMap_apply_one ..).symm)) (ne_of_lt (Int.fract_lt_one s))
    · by_cases hadj' : sindex = tindex + 1
      · have hinter := h.adjacent_inter tindex
        rw [← hadj'] at hinter
        rw [Set.inter_comm, hinter, mem_singleton_iff] at hp_in_both
        have h1 : poly.edgePath R tindex 1 = poly (tindex + 1) := lineMap_apply_one ..
        have heq' : poly.edgePath R tindex (Int.fract t) = poly.edgePath R tindex 1 := by
          rw [h1, ← show poly.vertices sindex = poly.vertices (tindex + 1) from by rw [hadj'],
            ← hp_in_both, ← heq]
        exact absurd (lineMap_injective R (h.hasNondegenerateEdges tindex) heq')
          (ne_of_lt (Int.fract_lt_one t))
      · have hdisj := h.nonadjacent_disjoint hindex hadj' hadj
        exact (Set.disjoint_iff.mp hdisj hp_in_both).elim

end Polygon
