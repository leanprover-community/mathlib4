/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Order.Interval.Set.Disjoint

#align_import wiedijk_100_theorems.cubing_a_cube from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

/-!
Proof that a cube (in dimension n ≥ 3) cannot be cubed:
There does not exist a partition of a cube into finitely many smaller cubes (at least two)
of different sizes.

We follow the proof described here:
http://www.alaricstephen.com/main-featured/2017/9/28/cubing-a-cube-proof
-/


open Real Set Function Fin

namespace Theorems100

noncomputable section

namespace «82»

variable {n : ℕ}

/-- Given three intervals `I, J, K` such that `J ⊂ I`,
  neither endpoint of `J` coincides with an endpoint of `I`, `¬ (K ⊆ J)` and
  `K` does not lie completely to the left nor completely to the right of `J`.
  Then `I ∩ K \ J` is nonempty. -/
theorem Ico_lemma {α} [LinearOrder α] {x₁ x₂ y₁ y₂ z₁ z₂ w : α} (h₁ : x₁ < y₁) (hy : y₁ < y₂)
    (h₂ : y₂ < x₂) (hz₁ : z₁ ≤ y₂) (hz₂ : y₁ ≤ z₂) (hw : w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂) :
    ∃ w, w ∈ Ico x₁ x₂ ∧ w ∉ Ico y₁ y₂ ∧ w ∈ Ico z₁ z₂ := by
  simp only [not_and, not_lt, mem_Ico] at hw
  refine ⟨max x₁ (min w y₂), ?_, ?_, ?_⟩
  · simp [le_refl, lt_trans h₁ (lt_trans hy h₂), h₂]
  · simp (config := { contextual := true }) [hw, lt_irrefl, not_le_of_lt h₁]
  · simp [hw.2.1, hw.2.2, hz₁, lt_of_lt_of_le h₁ hz₂]
#align theorems_100.«82».Ico_lemma Theorems100.«82».Ico_lemma

/-- A (hyper)-cube (in standard orientation) is a vector `b` consisting of the bottom-left point
of the cube, a width `w` and a proof that `w > 0`. We use functions from `Fin n` to denote vectors.
-/
structure Cube (n : ℕ) : Type where
  b : Fin n → ℝ -- bottom-left coordinate
  w : ℝ -- width
  hw : 0 < w
#align theorems_100.«82».cube Theorems100.«82».Cube

namespace Cube

theorem hw' (c : Cube n) : 0 ≤ c.w :=
  le_of_lt c.hw
#align theorems_100.«82».cube.hw' Theorems100.«82».Cube.hw'

/-- The j-th side of a cube is the half-open interval `[b j, b j + w)` -/
def side (c : Cube n) (j : Fin n) : Set ℝ :=
  Ico (c.b j) (c.b j + c.w)
#align theorems_100.«82».cube.side Theorems100.«82».Cube.side

@[simp]
theorem b_mem_side (c : Cube n) (j : Fin n) : c.b j ∈ c.side j := by simp [side, Cube.hw, le_refl]
#align theorems_100.«82».cube.b_mem_side Theorems100.«82».Cube.b_mem_side

def toSet (c : Cube n) : Set (Fin n → ℝ) :=
  {x | ∀ j, x j ∈ side c j}
#align theorems_100.«82».cube.to_set Theorems100.«82».Cube.toSet

theorem side_nonempty (c : Cube n) (i : Fin n) : (side c i).Nonempty := by simp [side, c.hw]
#align theorems_100.«82».cube.side_nonempty Theorems100.«82».Cube.side_nonempty

theorem univ_pi_side (c : Cube n) : pi univ (side c) = c.toSet :=
  ext fun _ => mem_univ_pi
#align theorems_100.«82».cube.univ_pi_side Theorems100.«82».Cube.univ_pi_side

theorem toSet_subset {c c' : Cube n} : c.toSet ⊆ c'.toSet ↔ ∀ j, c.side j ⊆ c'.side j := by
  simp only [← univ_pi_side, univ_pi_subset_univ_pi_iff, (c.side_nonempty _).ne_empty, exists_false,
    or_false_iff]
#align theorems_100.«82».cube.to_set_subset Theorems100.«82».Cube.toSet_subset

theorem toSet_disjoint {c c' : Cube n} :
    Disjoint c.toSet c'.toSet ↔ ∃ j, Disjoint (c.side j) (c'.side j) := by
  simp only [← univ_pi_side, disjoint_univ_pi]
#align theorems_100.«82».cube.to_set_disjoint Theorems100.«82».Cube.toSet_disjoint

theorem b_mem_toSet (c : Cube n) : c.b ∈ c.toSet := by simp [toSet]
#align theorems_100.«82».cube.b_mem_to_set Theorems100.«82».Cube.b_mem_toSet

protected def tail (c : Cube (n + 1)) : Cube n :=
  ⟨tail c.b, c.w, c.hw⟩
#align theorems_100.«82».cube.tail Theorems100.«82».Cube.tail

theorem side_tail (c : Cube (n + 1)) (j : Fin n) : c.tail.side j = c.side j.succ :=
  rfl
#align theorems_100.«82».cube.side_tail Theorems100.«82».Cube.side_tail

def bottom (c : Cube (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = c.b 0 ∧ tail x ∈ c.tail.toSet}
#align theorems_100.«82».cube.bottom Theorems100.«82».Cube.bottom

theorem b_mem_bottom (c : Cube (n + 1)) : c.b ∈ c.bottom := by
  simp [bottom, toSet, side, Cube.hw, le_refl, Cube.tail]
#align theorems_100.«82».cube.b_mem_bottom Theorems100.«82».Cube.b_mem_bottom

def xm (c : Cube (n + 1)) : ℝ :=
  c.b 0 + c.w
#align theorems_100.«82».cube.xm Theorems100.«82».Cube.xm

theorem b_lt_xm (c : Cube (n + 1)) : c.b 0 < c.xm := by simp [xm, hw]
#align theorems_100.«82».cube.b_lt_xm Theorems100.«82».Cube.b_lt_xm

theorem b_ne_xm (c : Cube (n + 1)) : c.b 0 ≠ c.xm :=
  ne_of_lt c.b_lt_xm
#align theorems_100.«82».cube.b_ne_xm Theorems100.«82».Cube.b_ne_xm

def shiftUp (c : Cube (n + 1)) : Cube (n + 1) :=
  ⟨cons c.xm <| tail c.b, c.w, c.hw⟩
#align theorems_100.«82».cube.shift_up Theorems100.«82».Cube.shiftUp

@[simp]
theorem tail_shiftUp (c : Cube (n + 1)) : c.shiftUp.tail = c.tail := by simp [shiftUp, Cube.tail]
#align theorems_100.«82».cube.tail_shift_up Theorems100.«82».Cube.tail_shiftUp

@[simp]
theorem head_shiftUp (c : Cube (n + 1)) : c.shiftUp.b 0 = c.xm :=
  rfl
#align theorems_100.«82».cube.head_shift_up Theorems100.«82».Cube.head_shiftUp

def unitCube : Cube n :=
  ⟨fun _ => 0, 1, by norm_num⟩
#align theorems_100.«82».cube.unit_cube Theorems100.«82».Cube.unitCube

@[simp]
theorem side_unitCube {j : Fin n} : unitCube.side j = Ico 0 1 := by
  norm_num [unitCube, side]
#align theorems_100.«82».cube.side_unit_cube Theorems100.«82».Cube.side_unitCube

end Cube

open Cube

variable {ι : Type} {cs : ι → Cube (n + 1)} {i i' : ι}

/-- A finite family of (at least 2) cubes partitioning the unit cube with different sizes -/
structure Correct (cs : ι → Cube n) : Prop where
  PairwiseDisjoint : Pairwise (Disjoint on Cube.toSet ∘ cs)
  iUnion_eq : ⋃ i : ι, (cs i).toSet = unitCube.toSet
  Injective : Injective (Cube.w ∘ cs)
  three_le : 3 ≤ n
#align theorems_100.«82».correct Theorems100.«82».Correct

namespace Correct

variable (h : Correct cs)

theorem toSet_subset_unitCube {i} : (cs i).toSet ⊆ unitCube.toSet := by
  convert h.iUnion_eq ▸ subset_iUnion _ i
#align theorems_100.«82».correct.to_set_subset_unit_cube Theorems100.«82».Correct.toSet_subset_unitCube

theorem side_subset {i j} : (cs i).side j ⊆ Ico 0 1 := by
  simpa only [side_unitCube] using toSet_subset.1 h.toSet_subset_unitCube j
#align theorems_100.«82».correct.side_subset Theorems100.«82».Correct.side_subset

theorem zero_le_of_mem_side {i j x} (hx : x ∈ (cs i).side j) : 0 ≤ x :=
  (side_subset h hx).1
#align theorems_100.«82».correct.zero_le_of_mem_side Theorems100.«82».Correct.zero_le_of_mem_side

theorem zero_le_of_mem {i p} (hp : p ∈ (cs i).toSet) (j) : 0 ≤ p j :=
  zero_le_of_mem_side h (hp j)
#align theorems_100.«82».correct.zero_le_of_mem Theorems100.«82».Correct.zero_le_of_mem

theorem zero_le_b {i j} : 0 ≤ (cs i).b j :=
  zero_le_of_mem h (cs i).b_mem_toSet j
#align theorems_100.«82».correct.zero_le_b Theorems100.«82».Correct.zero_le_b

theorem b_add_w_le_one {j} : (cs i).b j + (cs i).w ≤ 1 := by
  have : side (cs i) j ⊆ Ico 0 1 := side_subset h
  rw [side, Ico_subset_Ico_iff] at this
  · convert this.2
  · simp [hw]
#align theorems_100.«82».correct.b_add_w_le_one Theorems100.«82».Correct.b_add_w_le_one

theorem nontrivial_fin : Nontrivial (Fin n) :=
  Fin.nontrivial_iff_two_le.2 (Nat.le_of_succ_le_succ h.three_le)
#align theorems_100.«82».correct.nontrivial_fin Theorems100.«82».Correct.nontrivial_fin

/-- The width of any cube in the partition cannot be 1. -/
theorem w_ne_one [Nontrivial ι] (i : ι) : (cs i).w ≠ 1 := by
  intro hi
  cases' exists_ne i with i' hi'
  let p := (cs i').b
  have hp : p ∈ (cs i').toSet := (cs i').b_mem_toSet
  have h2p : p ∈ (cs i).toSet := by
    intro j; constructor
    trans (0 : ℝ)
    · rw [← add_le_add_iff_right (1 : ℝ)]; convert b_add_w_le_one h
      · rw [hi]
      · rw [zero_add]
    · apply zero_le_b h
    · apply lt_of_lt_of_le (side_subset h <| (cs i').b_mem_side j).2
      simp [hi, zero_le_b h]
  exact (h.PairwiseDisjoint hi').le_bot ⟨hp, h2p⟩
#align theorems_100.«82».correct.w_ne_one Theorems100.«82».Correct.w_ne_one

/-- The top of a cube (which is the bottom of the cube shifted up by its width) must be covered by
  bottoms of (other) cubes in the family. -/
theorem shiftUp_bottom_subset_bottoms (hc : (cs i).xm ≠ 1) :
    (cs i).shiftUp.bottom ⊆ ⋃ i : ι, (cs i).bottom := by
  intro p hp; cases' hp with hp0 hps; rw [tail_shiftUp] at hps
  have : p ∈ (unitCube : Cube (n + 1)).toSet := by
    simp only [toSet, forall_fin_succ, hp0, side_unitCube, mem_setOf_eq, mem_Ico, head_shiftUp]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← zero_add (0 : ℝ)]; apply add_le_add
      · apply zero_le_b h
      · apply (cs i).hw'
    · exact lt_of_le_of_ne (b_add_w_le_one h) hc
    intro j; exact side_subset h (hps j)
  rw [← h.2, mem_iUnion] at this; rcases this with ⟨i', hi'⟩
  rw [mem_iUnion]; use i'; refine ⟨?_, fun j => hi' j.succ⟩
  have : i ≠ i' := by rintro rfl; apply not_le_of_lt (hi' 0).2; rw [hp0]; rfl
  have := h.1 this
  rw [onFun, comp_apply, comp_apply, toSet_disjoint, exists_fin_succ] at this
  rcases this with (h0 | ⟨j, hj⟩)
  · rw [hp0]; symm; apply eq_of_Ico_disjoint h0 (by simp [hw]) _
    convert hi' 0; rw [hp0]; rfl
  · exfalso; apply not_disjoint_iff.mpr ⟨tail p j, hps j, hi' j.succ⟩ hj
#align theorems_100.«82».correct.shift_up_bottom_subset_bottoms Theorems100.«82».Correct.shiftUp_bottom_subset_bottoms

end Correct

/-- A valley is a square on which cubes in the family of cubes are placed, so that the cubes
  completely cover the valley and none of those cubes is partially outside the square.
  We also require that no cube on it has the same size as the valley (so that there are at least
  two cubes on the valley).
  This is the main concept in the formalization.
  We prove that the smallest cube on a valley has another valley on the top of it, which
  gives an infinite sequence of cubes in the partition, which contradicts the finiteness.
  A valley is characterized by a cube `c` (which is not a cube in the family `cs`) by considering
  the bottom face of `c`. -/
def Valley (cs : ι → Cube (n + 1)) (c : Cube (n + 1)) : Prop :=
  (c.bottom ⊆ ⋃ i : ι, (cs i).bottom) ∧
  (∀ i, (cs i).b 0 = c.b 0 →
    (∃ x, x ∈ (cs i).tail.toSet ∩ c.tail.toSet) → (cs i).tail.toSet ⊆ c.tail.toSet) ∧
  ∀ i : ι, (cs i).b 0 = c.b 0 → (cs i).w ≠ c.w
#align theorems_100.«82».valley Theorems100.«82».Valley

variable {c : Cube (n + 1)} (h : Correct cs) (v : Valley cs c)

/-- The bottom of the unit cube is a valley -/
theorem valley_unitCube [Nontrivial ι] (h : Correct cs) : Valley cs unitCube := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    simp only [bottom, and_imp, mem_iUnion, mem_setOf_eq]
    intro h0 hv
    have : v ∈ (unitCube : Cube (n + 1)).toSet := by
      dsimp only [toSet, unitCube, mem_setOf_eq]
      rw [forall_fin_succ, h0]; constructor
      · norm_num [side, unitCube]
      · exact hv
    rw [← h.2, mem_iUnion] at this; rcases this with ⟨i, hi⟩
    use i
    constructor
    · apply le_antisymm
      · rw [h0]; exact h.zero_le_b
      · exact (hi 0).1
    intro j; exact hi _
  · intro i _ _; rw [toSet_subset]; intro j; convert h.side_subset using 1; simp [side_tail]
  · intro i _; exact h.w_ne_one i
#align theorems_100.«82».valley_unit_cube Theorems100.«82».valley_unitCube

/-- the cubes which lie in the valley `c` -/
def bcubes (cs : ι → Cube (n + 1)) (c : Cube (n + 1)) : Set ι :=
  {i : ι | (cs i).b 0 = c.b 0 ∧ (cs i).tail.toSet ⊆ c.tail.toSet}
#align theorems_100.«82».bcubes Theorems100.«82».bcubes

/-- A cube which lies on the boundary of a valley in dimension `j` -/
def OnBoundary (_ : i ∈ bcubes cs c) (j : Fin n) : Prop :=
  c.b j.succ = (cs i).b j.succ ∨ (cs i).b j.succ + (cs i).w = c.b j.succ + c.w
#align theorems_100.«82».on_boundary Theorems100.«82».OnBoundary

theorem tail_sub (hi : i ∈ bcubes cs c) : ∀ j, (cs i).tail.side j ⊆ c.tail.side j := by
  rw [← toSet_subset]; exact hi.2
#align theorems_100.«82».tail_sub Theorems100.«82».tail_sub

theorem bottom_mem_side (hi : i ∈ bcubes cs c) : c.b 0 ∈ (cs i).side 0 := by
  convert b_mem_side (cs i) _ using 1; rw [hi.1]
#align theorems_100.«82».bottom_mem_side Theorems100.«82».bottom_mem_side

theorem b_le_b (hi : i ∈ bcubes cs c) (j : Fin n) : c.b j.succ ≤ (cs i).b j.succ :=
  (tail_sub hi j <| b_mem_side _ _).1
#align theorems_100.«82».b_le_b Theorems100.«82».b_le_b

theorem t_le_t (hi : i ∈ bcubes cs c) (j : Fin n) :
    (cs i).b j.succ + (cs i).w ≤ c.b j.succ + c.w := by
  have h' := tail_sub hi j; dsimp only [side] at h'; rw [Ico_subset_Ico_iff] at h'
  · exact h'.2
  · simp [hw]
#align theorems_100.«82».t_le_t Theorems100.«82».t_le_t

/-- Every cube in the valley must be smaller than it -/
theorem w_lt_w (hi : i ∈ bcubes cs c) : (cs i).w < c.w := by
  apply lt_of_le_of_ne _ (v.2.2 i hi.1)
  have j : Fin n := ⟨1, Nat.le_of_succ_le_succ h.three_le⟩
  rw [← add_le_add_iff_left ((cs i).b j.succ)]
  apply le_trans (t_le_t hi j); rw [add_le_add_iff_right]; apply b_le_b hi
#align theorems_100.«82».w_lt_w Theorems100.«82».w_lt_w

/-- There are at least two cubes in a valley -/
theorem nontrivial_bcubes : (bcubes cs c).Nontrivial := by
  rcases v.1 c.b_mem_bottom with ⟨_, ⟨i, rfl⟩, hi⟩
  have h2i : i ∈ bcubes cs c :=
    ⟨hi.1.symm, v.2.1 i hi.1.symm ⟨tail c.b, hi.2, fun j => c.b_mem_side j.succ⟩⟩
  let j : Fin (n + 1) := ⟨2, h.three_le⟩
  have hj : 0 ≠ j := by simp only [Fin.ext_iff, Ne]; norm_num
  let p : Fin (n + 1) → ℝ := fun j' => if j' = j then c.b j + (cs i).w else c.b j'
  have hp : p ∈ c.bottom := by
    constructor
    · simp only [p, bottom, if_neg hj]
    intro j'; simp only [tail, side_tail]
    by_cases hj' : j'.succ = j
    · simp [p, if_pos, side, hj', hw', w_lt_w h v h2i]
    · simp [p, if_neg hj']
  rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩
  have h2i' : i' ∈ bcubes cs c := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩
  refine ⟨i, h2i, i', h2i', ?_⟩
  rintro rfl
  apply not_le_of_lt (hi'.2 ⟨1, Nat.le_of_succ_le_succ h.three_le⟩).2
  simp only [tail, Cube.tail, p]
  rw [if_pos, add_le_add_iff_right]
  · exact (hi.2 _).1
  rfl
#align theorems_100.«82».nontrivial_bcubes Theorems100.«82».nontrivial_bcubes

/-- There is a cube in the valley -/
theorem nonempty_bcubes : (bcubes cs c).Nonempty :=
  (nontrivial_bcubes h v).nonempty
#align theorems_100.«82».nonempty_bcubes Theorems100.«82».nonempty_bcubes

variable [Finite ι]

/-- There is a smallest cube in the valley -/
theorem exists_mi : ∃ i ∈ bcubes cs c, ∀ i' ∈ bcubes cs c, (cs i).w ≤ (cs i').w :=
  (bcubes cs c).exists_min_image (fun i => (cs i).w) (Set.toFinite _) (nonempty_bcubes h v)
#align theorems_100.«82».exists_mi Theorems100.«82».exists_mi

/-- We let `mi` be the (index for the) smallest cube in the valley `c` -/
def mi : ι :=
  Classical.choose <| exists_mi h v
#align theorems_100.«82».mi Theorems100.«82».mi

variable {h v}

theorem mi_mem_bcubes : mi h v ∈ bcubes cs c :=
  (Classical.choose_spec <| exists_mi h v).1
#align theorems_100.«82».mi_mem_bcubes Theorems100.«82».mi_mem_bcubes

theorem mi_minimal (hi : i ∈ bcubes cs c) : (cs <| mi h v).w ≤ (cs i).w :=
  (Classical.choose_spec <| exists_mi h v).2 i hi
#align theorems_100.«82».mi_minimal Theorems100.«82».mi_minimal

theorem mi_strict_minimal (hii' : mi h v ≠ i) (hi : i ∈ bcubes cs c) :
    (cs <| mi h v).w < (cs i).w :=
  (mi_minimal hi).lt_of_ne <| h.Injective.ne hii'
#align theorems_100.«82».mi_strict_minimal Theorems100.«82».mi_strict_minimal

/-- The top of `mi` cannot be 1, since there is a larger cube in the valley -/
theorem mi_xm_ne_one : (cs <| mi h v).xm ≠ 1 := by
  apply ne_of_lt; rcases (nontrivial_bcubes h v).exists_ne (mi h v) with ⟨i, hi, h2i⟩
  · apply lt_of_lt_of_le _ h.b_add_w_le_one
    · exact i
    · exact 0
    rw [xm, mi_mem_bcubes.1, hi.1, _root_.add_lt_add_iff_left]
    exact mi_strict_minimal h2i.symm hi
#align theorems_100.«82».mi_xm_ne_one Theorems100.«82».mi_xm_ne_one

/-- If `mi` lies on the boundary of the valley in dimension j, then this lemma expresses that all
  other cubes on the same boundary extend further from the boundary.
  More precisely, there is a j-th coordinate `x : ℝ` in the valley, but not in `mi`,
  such that every cube that shares a (particular) j-th coordinate with `mi` also contains j-th
  coordinate `x` -/
theorem smallest_onBoundary {j} (bi : OnBoundary (mi_mem_bcubes : mi h v ∈ _) j) :
    ∃ x : ℝ, x ∈ c.side j.succ \ (cs <| mi h v).side j.succ ∧
      ∀ ⦃i'⦄ (_ : i' ∈ bcubes cs c),
        i' ≠ mi h v → (cs <| mi h v).b j.succ ∈ (cs i').side j.succ → x ∈ (cs i').side j.succ := by
  let i := mi h v; have hi : i ∈ bcubes cs c := mi_mem_bcubes
  cases' bi with bi bi
  · refine ⟨(cs i).b j.succ + (cs i).w, ⟨?_, ?_⟩, ?_⟩
    · simp [side, bi, hw', w_lt_w h v hi]
    · intro h'; simpa [lt_irrefl] using h'.2
    intro i' hi' i'_i h2i'; constructor
    · apply le_trans h2i'.1
      simp [hw']
    apply lt_of_lt_of_le (add_lt_add_left (mi_strict_minimal i'_i.symm hi') _)
    simp [bi.symm, b_le_b hi']
  let s := bcubes cs c \ {i}
  have hs : s.Nonempty := by
    rcases (nontrivial_bcubes h v).exists_ne i with ⟨i', hi', h2i'⟩
    exact ⟨i', hi', h2i'⟩
  rcases Set.exists_min_image s (w ∘ cs) (Set.toFinite _) hs with ⟨i', ⟨hi', h2i'⟩, h3i'⟩
  rw [mem_singleton_iff] at h2i'
  let x := c.b j.succ + c.w - (cs i').w
  have hx : x < (cs i).b j.succ := by
    dsimp only [x]; rw [← bi, add_sub_assoc, add_lt_iff_neg_left, sub_lt_zero]
    apply mi_strict_minimal (Ne.symm h2i') hi'
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · simp only [side, neg_lt_zero, hw, add_lt_iff_neg_left, and_true_iff, mem_Ico, sub_eq_add_neg, x]
    rw [add_assoc, le_add_iff_nonneg_right, ← sub_eq_add_neg, sub_nonneg]
    apply le_of_lt (w_lt_w h v hi')
  · simp only [side, not_and_or, not_lt, not_le, mem_Ico]; left; exact hx
  intro i'' hi'' h2i'' h3i''; constructor; swap; · apply lt_trans hx h3i''.2
  rw [le_sub_iff_add_le]
  refine le_trans ?_ (t_le_t hi'' j); rw [add_le_add_iff_left]; apply h3i' i'' ⟨hi'', _⟩
  simp [mem_singleton, h2i'']
#align theorems_100.«82».smallest_on_boundary Theorems100.«82».smallest_onBoundary

variable (h v)

/-- `mi` cannot lie on the boundary of the valley. Otherwise, the cube adjacent to it in the `j`-th
  direction will intersect one of the neighbouring cubes on the same boundary as `mi`. -/
theorem mi_not_onBoundary (j : Fin n) : ¬OnBoundary (mi_mem_bcubes : mi h v ∈ _) j := by
  let i := mi h v; have hi : i ∈ bcubes cs c := mi_mem_bcubes
  haveI := h.nontrivial_fin
  rcases exists_ne j with ⟨j', hj'⟩
  intro hj
  rcases smallest_onBoundary hj with ⟨x, ⟨hx, h2x⟩, h3x⟩
  let p : Fin (n + 1) → ℝ := cons (c.b 0) fun j₂ => if j₂ = j then x else (cs i).b j₂.succ
  have hp : p ∈ c.bottom := by
    suffices ∀ j' : Fin n, ite (j' = j) x ((cs i).b j'.succ) ∈ c.side j'.succ by
      simpa [p, bottom, toSet, tail, side_tail]
    intro j₂
    by_cases hj₂ : j₂ = j
    · simp [hj₂, hx]
    simp only [hj₂, if_false]; apply tail_sub hi; apply b_mem_side
  rcases v.1 hp with ⟨_, ⟨i', rfl⟩, hi'⟩
  have h2i' : i' ∈ bcubes cs c := ⟨hi'.1.symm, v.2.1 i' hi'.1.symm ⟨tail p, hi'.2, hp.2⟩⟩
  have i_i' : i ≠ i' := by rintro rfl; simpa [p, side_tail, h2x] using hi'.2 j
  have : Nonempty (↥((cs i').tail.side j' \ (cs i).tail.side j')) := by
    apply nonempty_Ico_sdiff
    · apply mi_strict_minimal i_i' h2i'
    · apply hw
  rcases this with ⟨⟨x', hx'⟩⟩
  let p' : Fin (n + 1) → ℝ := cons (c.b 0) fun j₂ => if j₂ = j' then x' else (cs i).b j₂.succ
  have hp' : p' ∈ c.bottom := by
    suffices ∀ j : Fin n, ite (j = j') x' ((cs i).b j.succ) ∈ c.side j.succ by
      simpa [p', bottom, toSet, tail, side_tail]
    intro j₂
    by_cases hj₂ : j₂ = j'; · simp [hj₂]; apply tail_sub h2i'; apply hx'.1
    simp only [if_congr, if_false, hj₂]; apply tail_sub hi; apply b_mem_side
  rcases v.1 hp' with ⟨_, ⟨i'', rfl⟩, hi''⟩
  have h2i'' : i'' ∈ bcubes cs c := ⟨hi''.1.symm, v.2.1 i'' hi''.1.symm ⟨tail p', hi''.2, hp'.2⟩⟩
  have i'_i'' : i' ≠ i'' := by
    rintro ⟨⟩
    have : (cs i).b ∈ (cs i').toSet := by
      simp only [toSet, forall_fin_succ, hi.1, bottom_mem_side h2i', true_and_iff, mem_setOf_eq]
      intro j₂; by_cases hj₂ : j₂ = j
      · simpa [p', side_tail, hj'.symm, hj₂] using hi''.2 j
      · simpa [p, hj₂] using hi'.2 j₂
    apply not_disjoint_iff.mpr ⟨(cs i).b, (cs i).b_mem_toSet, this⟩ (h.1 i_i')
  have i_i'' : i ≠ i'' := by intro h; induction h; simpa [p', hx'.2] using hi''.2 j'
  apply Not.elim _ (h.1 i'_i'')
  simp_rw [onFun, comp, toSet_disjoint, not_exists, not_disjoint_iff, forall_fin_succ]
  refine ⟨⟨c.b 0, bottom_mem_side h2i', bottom_mem_side h2i''⟩, ?_⟩
  intro j₂
  by_cases hj₂ : j₂ = j
  · cases hj₂; refine ⟨x, ?_, ?_⟩
    · convert hi'.2 j using 1; simp [p]
    apply h3x h2i'' i_i''.symm; convert hi''.2 j using 1; simp [p', hj'.symm]
  by_cases h2j₂ : j₂ = j'
  · cases h2j₂; refine ⟨x', hx'.1, ?_⟩; convert hi''.2 j' using 1; simp [p']
  refine ⟨(cs i).b j₂.succ, ?_, ?_⟩
  · convert hi'.2 j₂ using 1; simp [p, hj₂]
  · convert hi''.2 j₂ using 1; simp [p', h2j₂]
#align theorems_100.«82».mi_not_on_boundary Theorems100.«82».mi_not_onBoundary

variable {h v}

/-- The same result that `mi` cannot lie on the boundary of the valley written as inequalities. -/
theorem mi_not_onBoundary' (j : Fin n) :
    c.tail.b j < (cs (mi h v)).tail.b j ∧
      (cs (mi h v)).tail.b j + (cs (mi h v)).w < c.tail.b j + c.w := by
  have := mi_not_onBoundary h v j
  simp only [OnBoundary, not_or] at this; cases' this with h1 h2
  constructor
  · apply lt_of_le_of_ne (b_le_b mi_mem_bcubes _) h1
  apply lt_of_le_of_ne _ h2
  apply ((Ico_subset_Ico_iff _).mp (tail_sub mi_mem_bcubes j)).2
  simp [hw]
#align theorems_100.«82».mi_not_on_boundary' Theorems100.«82».mi_not_onBoundary'

/-- The top of `mi` gives rise to a new valley, since the neighbouring cubes extend further upward
  than `mi`. -/
theorem valley_mi : Valley cs (cs (mi h v)).shiftUp := by
  let i := mi h v; have hi : i ∈ bcubes cs c := mi_mem_bcubes
  refine ⟨?_, ?_, ?_⟩
  · intro p; apply h.shiftUp_bottom_subset_bottoms mi_xm_ne_one
  · rintro i' hi' ⟨p2, hp2, h2p2⟩; simp only [head_shiftUp] at hi'
    classical
    by_contra h2i'
    rw [tail_shiftUp] at h2p2
    simp only [not_subset, tail_shiftUp] at h2i'
    rcases h2i' with ⟨p1, hp1, h2p1⟩
    have : ∃ p3, p3 ∈ (cs i').tail.toSet ∧ p3 ∉ (cs i).tail.toSet ∧ p3 ∈ c.tail.toSet := by
      simp only [toSet, not_forall, mem_setOf_eq] at h2p1; cases' h2p1 with j hj
      rcases Ico_lemma (mi_not_onBoundary' j).1 (by simp [hw]) (mi_not_onBoundary' j).2
          (le_trans (hp2 j).1 <| le_of_lt (h2p2 j).2) (le_trans (h2p2 j).1 <| le_of_lt (hp2 j).2)
          ⟨hj, hp1 j⟩ with
        ⟨w, hw, h2w, h3w⟩
      refine ⟨fun j' => if j' = j then w else p2 j', ?_, ?_, ?_⟩
      · intro j'; by_cases h : j' = j
        · simp only [if_pos h]; exact h ▸ h3w
        · simp only [if_neg h]; exact hp2 j'
      · simp only [toSet, not_forall, mem_setOf_eq]; use j; rw [if_pos rfl]; convert h2w
      · intro j'; by_cases h : j' = j
        · simp only [if_pos h, side_tail]; exact h ▸ hw
        · simp only [if_neg h]; apply hi.2; apply h2p2
    rcases this with ⟨p3, h1p3, h2p3, h3p3⟩
    let p := @cons n (fun _ => ℝ) (c.b 0) p3
    have hp : p ∈ c.bottom := by refine ⟨rfl, ?_⟩; rwa [tail_cons]
    rcases v.1 hp with ⟨_, ⟨i'', rfl⟩, hi''⟩
    have h2i'' : i'' ∈ bcubes cs c := by
      use hi''.1.symm; apply v.2.1 i'' hi''.1.symm
      use tail p; constructor
      · exact hi''.2
      · rw [tail_cons]; exact h3p3
    have h3i'' : (cs i).w < (cs i'').w := by
      apply mi_strict_minimal _ h2i''; rintro rfl; apply h2p3; convert hi''.2
    let p' := @cons n (fun _ => ℝ) (cs i).xm p3
    have hp' : p' ∈ (cs i').toSet := by simpa [p', toSet, forall_fin_succ, hi'.symm] using h1p3
    have h2p' : p' ∈ (cs i'').toSet := by
      simp only [p', toSet, forall_fin_succ, cons_succ, cons_zero, mem_setOf_eq]
      refine ⟨?_, by simpa [toSet] using hi''.2⟩
      have : (cs i).b 0 = (cs i'').b 0 := by rw [hi.1, h2i''.1]
      simp [side, hw', xm, this, h3i'']
    apply not_disjoint_iff.mpr ⟨p', hp', h2p'⟩
    apply h.1
    rintro rfl
    apply (cs i).b_ne_xm
    rw [← hi', ← hi''.1, hi.1]
    rfl
  · intro i' hi' h2i'
    dsimp only [shiftUp] at h2i'
    replace h2i' := h.Injective h2i'.symm
    induction h2i'
    exact b_ne_xm (cs i) hi'
#align theorems_100.«82».valley_mi Theorems100.«82».valley_mi

variable (h) [Nontrivial ι]

/-- We get a sequence of cubes whose size is decreasing -/
noncomputable def sequenceOfCubes : ℕ → { i : ι // Valley cs (cs i).shiftUp }
  | 0 =>
    let v := valley_unitCube h
    ⟨mi h v, valley_mi⟩
  | k + 1 =>
    let v := (sequenceOfCubes k).2
    ⟨mi h v, valley_mi⟩
#align theorems_100.«82».sequence_of_cubes Theorems100.«82».sequenceOfCubes

def decreasingSequence (k : ℕ) : ℝ :=
  (cs (sequenceOfCubes h k).1).w
#align theorems_100.«82».decreasing_sequence Theorems100.«82».decreasingSequence

theorem strictAnti_sequenceOfCubes : StrictAnti <| decreasingSequence h :=
  strictAnti_nat_of_succ_lt fun k => by
    let v := (sequenceOfCubes h k).2; dsimp only [decreasingSequence, sequenceOfCubes]
    apply w_lt_w h v (mi_mem_bcubes : mi h v ∈ _)
#align theorems_100.«82».strict_anti_sequence_of_cubes Theorems100.«82».strictAnti_sequenceOfCubes

theorem injective_sequenceOfCubes : Injective (sequenceOfCubes h) :=
  @Injective.of_comp _ _ _ (fun x : { _i : ι // _ } => (cs x.1).w) _
    (strictAnti_sequenceOfCubes h).injective
#align theorems_100.«82».injective_sequence_of_cubes Theorems100.«82».injective_sequenceOfCubes

/-- The infinite sequence of cubes contradicts the finiteness of the family. -/
theorem not_correct : ¬Correct cs := fun h =>
  (Finite.of_injective _ <| injective_sequenceOfCubes h).false
#align theorems_100.«82».not_correct Theorems100.«82».not_correct

/-- **Dissection of Cubes**: A cube cannot be cubed. -/
theorem cannot_cube_a_cube :
    ∀ {n : ℕ}, n ≥ 3 →                         -- In ℝ^n for n ≥ 3
    ∀ {s : Set (Cube n)}, s.Finite →           -- given a finite collection of (hyper)cubes
    s.Nontrivial →                             -- containing at least two elements
    s.PairwiseDisjoint Cube.toSet →            -- which is pairwise disjoint
    ⋃ c ∈ s, Cube.toSet c = unitCube.toSet →   -- whose union is the unit cube
    InjOn Cube.w s →                           -- such that the widths of all cubes are different
    False := by                                -- then we can derive a contradiction
  intro n hn s hfin h2 hd hU hinj
  cases' n with n
  · cases hn
  exact @not_correct n s (↑) hfin.to_subtype h2.coe_sort
    ⟨hd.subtype _ _, (iUnion_subtype _ _).trans hU, hinj.injective, hn⟩
#align theorems_100.«82».cannot_cube_a_cube Theorems100.«82».cannot_cube_a_cube

end «82»

end

end Theorems100
