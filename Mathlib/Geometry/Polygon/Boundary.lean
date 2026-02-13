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

This file defines a map from `AddCircle n` to the boundary points of a polygon, and proves
basic properties of that map

## Main results

* `Polygon.range_boundaryMap`: the range of the boundary map equals the polygon boundary.
* `Polygon.isSimple_iff_boundaryMap_injective`: a polygon is simple if and only if its
  boundary map is injective.
-/

@[expose] public section

namespace Polygon

open Set AffineMap

variable {R V P : Type*}
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [Archimedean R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

local instance : Fact ((0 : R) < (n : R)) := ⟨by exact_mod_cast Nat.pos_of_neZero n⟩

@[local simp]
private lemma finRotate_eq (i : Fin n) : finRotate n i = i + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact finRotate_succ_apply i

variable (R) in
/-- A map from `AddCircle n` to the boundary points of the polygon. -/
noncomputable def boundaryMap (poly : Polygon P n) : AddCircle (n : R) → P :=
  let boundaryParam : R → P := fun t =>
    let i : Fin n := ⟨(Int.floor t).toNat % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
    let f : R := Int.fract t
    poly.edgePath R i f
  AddCircle.liftIco (n : R) (0 : R) boundaryParam

variable {poly : Polygon P n}

/-- The range of the `boundaryMap` is the `boundary`. -/
theorem range_boundaryMap : Set.range (poly.boundaryMap R) = poly.boundary R := by
  ext p
  simp only [mem_range]
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨t, htmem, rfl⟩ := AddCircle.eq_coe_Ico q
    simp only [boundaryMap, boundary, mem_iUnion]
    rw [AddCircle.liftIco_coe_apply (by simpa [zero_add])]
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
      simp only [hfloor, hfrac]
    · push_neg at hu1
      simp only [le_antisymm hu.2 hu1, edgePath, finRotate_eq, AffineMap.lineMap_apply_one]
      let t : R := ((i + 1 : Fin n) : ℕ)
      have htmem : t ∈ Ico (0 : R) n := by
        simp only [t, Set.mem_Ico]
        exact ⟨by exact_mod_cast (i+1 : Fin n).val.zero_le,
               by exact_mod_cast (i+1 : Fin n).isLt⟩
      use t
      simp only [boundaryMap]
      rw [AddCircle.liftIco_coe_apply (by simpa [zero_add])]
      simp only [Int.floor_natCast, Int.toNat_natCast,
        Nat.mod_eq_of_lt (i+1 : Fin n).isLt, t, edgePath, Fin.eta,
        Int.fract_natCast, lineMap_apply_zero]

/-- A polygon is simple if and only if its `boundaryMap` is injective. -/
theorem isSimple_iff_boundaryMap_injective [IsDomain R] [Module.IsTorsionFree R V]
    (hn : 3 ≤ n) : poly.IsSimple R ↔ Function.Injective (poly.boundaryMap R) := by
  constructor
  · intro h x y heq
    obtain ⟨s, hs_mem, rfl⟩ := AddCircle.eq_coe_Ico x
    obtain ⟨t, htmem, rfl⟩ := AddCircle.eq_coe_Ico y
    have hs_mem' : s ∈ Ico (0 : R) n := by simpa [zero_add] using hs_mem
    have htmem' : t ∈ Ico (0 : R) n := by simpa [zero_add] using htmem
    simp only [boundaryMap] at heq
    rw [AddCircle.liftIco_coe_apply (by simpa [zero_add]),
        AddCircle.liftIco_coe_apply (by simpa [zero_add])] at heq
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
        have eone_s : poly.edgePath R sindex 1 = poly (sindex + 1) := by simp [edgePath]
        exact absurd (lineMap_injective R (h.hasNondegenerateEdges sindex)
          (hp_in_both.trans eone_s.symm)) (ne_of_lt (Int.fract_lt_one s))
      · by_cases hadj' : sindex = tindex + 1
        · have hinter := h.adjacent_inter tindex
          rw [← hadj'] at hinter
          rw [Set.inter_comm, hinter, mem_singleton_iff] at hp_in_both
          have h1 : poly.edgePath R tindex 1 = poly (tindex + 1) := by simp [edgePath]
          have heq' : poly.edgePath R tindex (Int.fract t) = poly.edgePath R tindex 1 := by
            rw [h1, ← show poly.vertices sindex = poly.vertices (tindex + 1) from by rw [hadj'],
              ← hp_in_both, ← heq]
          exact absurd (lineMap_injective R (h.hasNondegenerateEdges tindex) heq')
            (ne_of_lt (Int.fract_lt_one t))
        · have hdisj := h.nonadjacent_disjoint _ _ hindex hadj' hadj
          exact (Set.disjoint_iff.mp hdisj hp_in_both).elim
  · intro h
    have nmem (k : Fin n) : (↑(k : ℕ) : R) ∈ Ico (0 : R) (0 + ↑n) := by
      simp only [zero_add]
      exact ⟨by exact_mod_cast k.val.zero_le, by exact_mod_cast k.isLt⟩
    have bnat (k : Fin n) :
        poly.boundaryMap R ↑(↑(k : ℕ) : R) = poly k := by
      simp only [boundaryMap]; rw [AddCircle.liftIco_coe_apply (nmem k)]
      simp [Int.floor_natCast, Int.toNat_natCast,
        Nat.mod_eq_of_lt k.isLt, Int.fract_natCast, edgePath, lineMap_apply_zero]
    have eone (k : Fin n) : poly.edgePath R k 1 = poly (k + 1) := by
      simp [edgePath]
    have fmem (k : Fin n) (w : R) (hw0 : 0 ≤ w) (hw1 : w < 1) :
        (↑(k : ℕ) + w : R) ∈ Ico (0 : R) (0 + ↑n) := by
      simp only [zero_add, mem_Ico]
      exact ⟨add_nonneg (by exact_mod_cast k.val.zero_le) hw0,
        calc (↑(k : ℕ) + w : R)
            < ↑(k : ℕ) + 1 := by simp only [add_lt_add_iff_left]; exact hw1
          _ ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.isLt⟩
    have floor_frac (k : Fin n) (w : R) (hw0 : 0 ≤ w) (hw1 : w < 1) :
        ⌊(↑(k : ℕ) + w : R)⌋ = (k : ℤ) := Int.floor_eq_iff.mpr (by
      simp only [Int.cast_natCast]
      exact ⟨le_add_of_nonneg_right hw0,
        by simp only [add_lt_add_iff_left]; exact_mod_cast hw1⟩)
    have bfrac (k : Fin n) (w : R) (hw0 : 0 ≤ w) (hw1 : w < 1) :
        poly.boundaryMap R ↑(↑(k : ℕ) + w : R) =
          poly.edgePath R k w := by
      simp only [boundaryMap]; rw [AddCircle.liftIco_coe_apply (fmem k w hw0 hw1)]
      simp only [floor_frac k w hw0 hw1, Int.toNat_natCast,
        Nat.mod_eq_of_lt k.isLt, Fin.eta, Int.fract, Int.cast_natCast,
        add_sub_cancel_left]
    have inj_eq (a b : R) (ha : a ∈ Ico (0 : R) (0 + ↑n))
        (hb : b ∈ Ico (0 : R) (0 + ↑n))
        (hab : poly.boundaryMap R ↑a =
          poly.boundaryMap R ↑b) : a = b :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico ha hb).mp (h hab)
    have hone : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt (show 1 < n by omega)
    have fin_ne_succ (i : Fin n) : (i : ℕ) ≠ ((i + 1 : Fin n) : ℕ) := by
      simp only [ne_eq, Fin.val_add_eq_ite, hone]
      split_ifs <;> omega
    have fin_ne_succ_succ (i : Fin n) :
        (i : ℕ) ≠ ((i + 1 + 1 : Fin n) : ℕ) := by
      simp only [ne_eq, Fin.val_add_eq_ite, hone]
      split_ifs <;> omega
    constructor
    · intro i heq
      rw [finRotate_eq] at heq
      absurd (show (i : ℕ) = ((i + 1 : Fin n) : ℕ) from by
        exact_mod_cast inj_eq _ _ (nmem i) (nmem (i + 1))
          (by rw [bnat i, bnat (i + 1), heq]))
      exact fin_ne_succ i
    · intro i j hij hij1 hji1
      rw [Set.disjoint_left]
      intro p hp_i hp_j
      rw [edgeSet_eq_image_edgePath] at hp_i hp_j
      obtain ⟨u, hu, rfl⟩ := hp_i
      obtain ⟨v, hv, hpv⟩ := hp_j
      rcases eq_or_lt_of_le hu.2 with rfl | hu1 <;>
        rcases eq_or_lt_of_le hv.2 with rfl | hv1
      · have := inj_eq _ _ (nmem (i + 1)) (nmem (j + 1))
            (by rw [bnat (i+1), bnat (j+1), ← eone i,
                    ← eone j, hpv])
        exact hij (add_right_cancel
          (Fin.ext (by exact_mod_cast this)))
      · have heq := inj_eq _ _ (nmem (i + 1))
            (fmem j v hv.1 hv1)
            (by rw [bnat (i+1), bfrac j v hv.1 hv1, hpv]
                exact (eone i).symm)
        have := congrArg Int.floor heq
        rw [Int.floor_natCast,
            floor_frac j v hv.1 hv1] at this
        exact hji1 (Fin.ext (by exact_mod_cast this)).symm
      · have heq := inj_eq _ _
            (fmem i u hu.1 hu1) (nmem (j + 1))
            (by rw [bfrac i u hu.1 hu1, bnat (j+1),
                    ← eone j, ← hpv])
        have := congrArg Int.floor heq
        rw [floor_frac i u hu.1 hu1,
            Int.floor_natCast] at this
        exact hij1 (Fin.ext (by exact_mod_cast this))
      · have heq := inj_eq _ _
            (fmem i u hu.1 hu1) (fmem j v hv.1 hv1)
            (by rw [bfrac i u hu.1 hu1,
                    bfrac j v hv.1 hv1, hpv])
        have := congrArg Int.floor heq
        rw [floor_frac i u hu.1 hu1,
            floor_frac j v hv.1 hv1] at this
        exact hij (Fin.ext (by exact_mod_cast this))
    · intro i
      apply Set.eq_singleton_iff_unique_mem.mpr
      constructor
      · constructor
        · rw [edgeSet_eq_image_edgePath]
          exact ⟨1, right_mem_Icc.mpr zero_le_one,
            by simp [edgePath]⟩
        · rw [edgeSet_eq_image_edgePath]
          exact ⟨0, left_mem_Icc.mpr zero_le_one,
            by simp [edgePath]⟩
      · intro p ⟨hp_i, hp_i1⟩
        rw [edgeSet_eq_image_edgePath] at hp_i hp_i1
        obtain ⟨u, hu, rfl⟩ := hp_i
        obtain ⟨v, hv, hpv⟩ := hp_i1
        rcases eq_or_lt_of_le hu.2 with rfl | hu1
        · simp [edgePath]
        · rcases eq_or_lt_of_le hv.1 with hv0 | hv0
          · rw [← hv0] at hpv
            simp only [edgePath, finRotate_eq, lineMap_apply_zero] at hpv ⊢
            exact hpv.symm
          · rcases eq_or_lt_of_le hv.2 with rfl | hv1
            · have heq := inj_eq _ _
                (fmem i u hu.1 hu1) (nmem (i + 1 + 1))
                (by rw [bfrac i u hu.1 hu1,
                        bnat (i + 1 + 1)]
                    exact hpv.symm ▸ by simp [edgePath])
              have := congrArg Int.floor heq
              rw [floor_frac i u hu.1 hu1,
                  Int.floor_natCast] at this
              exact absurd (by exact_mod_cast this)
                (fin_ne_succ_succ i)
            · have heq := inj_eq _ _
                (fmem i u hu.1 hu1)
                (fmem (i + 1) v hv0.le hv1)
                (by rw [bfrac i u hu.1 hu1,
                        bfrac (i+1) v hv0.le hv1, hpv])
              have := congrArg Int.floor heq
              rw [floor_frac i u hu.1 hu1,
                  floor_frac (i+1) v hv0.le hv1] at this
              exact absurd (by exact_mod_cast this)
                (fin_ne_succ i)

end Polygon
