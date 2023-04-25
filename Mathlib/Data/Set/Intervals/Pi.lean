/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.pi
! leanprover-community/mathlib commit 4020ddee5b4580a409bfda7d2f42726ce86ae674
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Intervals.UnorderedInterval
import Mathlib.Data.Set.Lattice

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

variable {ι : Type _} {α : ι → Type _}

namespace Set

section PiPreorder

variable [∀ i, Preorder (α i)] (x y : ∀ i, α i)

@[simp]
theorem pi_univ_Ici : (pi univ fun i ↦ Ici (x i)) = Ici x :=
  ext fun y ↦ by simp [Pi.le_def]
#align set.pi_univ_Ici Set.pi_univ_Ici

@[simp]
theorem pi_univ_Iic : (pi univ fun i ↦ Iic (x i)) = Iic x :=
  ext fun y ↦ by simp [Pi.le_def]
#align set.pi_univ_Iic Set.pi_univ_Iic

@[simp]
theorem pi_univ_Icc : (pi univ fun i ↦ Icc (x i) (y i)) = Icc x y :=
  ext fun y ↦ by simp [Pi.le_def, forall_and]
#align set.pi_univ_Icc Set.pi_univ_Icc

theorem piecewise_mem_Icc {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : ∀ i ∈ s, f₁ i ∈ Icc (g₁ i) (g₂ i)) (h₂ : ∀ (i) (_ : i ∉ s), f₂ i ∈ Icc (g₁ i) (g₂ i)) :
    s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  ⟨le_piecewise (fun i hi ↦ (h₁ i hi).1) fun i hi ↦ (h₂ i hi).1,
    piecewise_le (fun i hi ↦ (h₁ i hi).2) fun i hi ↦ (h₂ i hi).2⟩
#align set.piecewise_mem_Icc Set.piecewise_mem_Icc

theorem piecewise_mem_Icc' {s : Set ι} [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, α i}
    (h₁ : f₁ ∈ Icc g₁ g₂) (h₂ : f₂ ∈ Icc g₁ g₂) : s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
  piecewise_mem_Icc (fun _ _ ↦ ⟨h₁.1 _, h₁.2 _⟩) fun _ _ ↦ ⟨h₂.1 _, h₂.2 _⟩
#align set.piecewise_mem_Icc' Set.piecewise_mem_Icc'

section Nonempty

variable [Nonempty ι]

theorem pi_univ_Ioi_subset : (pi univ fun i ↦ Ioi (x i)) ⊆ Ioi x := fun z hz ↦
  ⟨fun i ↦ le_of_lt <| hz i trivial, fun h ↦
    (Nonempty.elim ‹Nonempty ι›) fun i ↦ not_lt_of_le (h i) (hz i trivial)⟩
#align set.pi_univ_Ioi_subset Set.pi_univ_Ioi_subset

theorem pi_univ_Iio_subset : (pi univ fun i ↦ Iio (x i)) ⊆ Iio x :=
  @pi_univ_Ioi_subset ι (fun i ↦ (α i)ᵒᵈ) _ x _
#align set.pi_univ_Iio_subset Set.pi_univ_Iio_subset

theorem pi_univ_Ioo_subset : (pi univ fun i ↦ Ioo (x i) (y i)) ⊆ Ioo x y := fun _ hx ↦
  ⟨(pi_univ_Ioi_subset _) fun i hi ↦ (hx i hi).1, (pi_univ_Iio_subset _) fun i hi ↦ (hx i hi).2⟩
#align set.pi_univ_Ioo_subset Set.pi_univ_Ioo_subset

theorem pi_univ_Ioc_subset : (pi univ fun i ↦ Ioc (x i) (y i)) ⊆ Ioc x y := fun _ hx ↦
  ⟨(pi_univ_Ioi_subset _) fun i hi ↦ (hx i hi).1, fun i ↦ (hx i trivial).2⟩
#align set.pi_univ_Ioc_subset Set.pi_univ_Ioc_subset

theorem pi_univ_Ico_subset : (pi univ fun i ↦ Ico (x i) (y i)) ⊆ Ico x y := fun _ hx ↦
  ⟨fun i ↦ (hx i trivial).1, (pi_univ_Iio_subset _) fun i hi ↦ (hx i hi).2⟩
#align set.pi_univ_Ico_subset Set.pi_univ_Ico_subset

end Nonempty

variable [DecidableEq ι]

open Function (update)

theorem pi_univ_Ioc_update_left {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
    (pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) =
      { z | m < z i₀ } ∩ pi univ fun i ↦ Ioc (x i) (y i) := by
  have : Ioc m (y i₀) = Ioi m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, ← inter_assoc,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)]
  simp_rw [univ_pi_update i₀ _ _ fun i z ↦ Ioc z (y i), ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl
#align set.pi_univ_Ioc_update_left Set.pi_univ_Ioc_update_left

theorem pi_univ_Ioc_update_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
    (pi univ fun i ↦ Ioc (x i) (update y i₀ m i)) =
      { z | z i₀ ≤ m } ∩ pi univ fun i ↦ Ioc (x i) (y i) := by
  have : Ioc (x i₀) m = Iic m ∩ Ioc (x i₀) (y i₀) := by
    rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_left_comm,
      inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)]
  simp_rw [univ_pi_update i₀ y m fun i z ↦ Ioc (x i) z, ← pi_inter_compl ({i₀} : Set ι),
    singleton_pi', ← inter_assoc, this]
  rfl
#align set.pi_univ_Ioc_update_right Set.pi_univ_Ioc_update_right

theorem disjoint_pi_univ_Ioc_update_left_right {x y : ∀ i, α i} {i₀ : ι} {m : α i₀} :
    Disjoint (pi univ fun i ↦ Ioc (x i) (update y i₀ m i))
      (pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) :=
  by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine' (h₁ i₀ (mem_univ _)).2.not_lt _
  simpa only [Function.update_same] using (h₂ i₀ (mem_univ _)).1
#align set.disjoint_pi_univ_Ioc_update_left_right Set.disjoint_pi_univ_Ioc_update_left_right

end PiPreorder

section PiLattice

variable [∀ i, Lattice (α i)]

@[simp]
theorem pi_univ_uIcc (a b : ∀ i, α i) : (pi univ fun i => uIcc (a i) (b i)) = uIcc a b :=
  pi_univ_Icc _ _
#align set.pi_univ_uIcc Set.pi_univ_uIcc

end PiLattice

variable [DecidableEq ι] [∀ i, LinearOrder (α i)]

open Function (update)

theorem pi_univ_Ioc_update_union (x y : ∀ i, α i) (i₀ : ι) (m : α i₀) (hm : m ∈ Icc (x i₀) (y i₀)) :
    ((pi univ fun i ↦ Ioc (x i) (update y i₀ m i)) ∪
        pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) =
      pi univ fun i ↦ Ioc (x i) (y i) := by
  simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2, ← union_inter_distrib_right,
    ← setOf_or, le_or_lt, setOf_true, univ_inter]
#align set.pi_univ_Ioc_update_union Set.pi_univ_Ioc_update_union

/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
theorem Icc_diff_pi_univ_Ioo_subset (x y x' y' : ∀ i, α i) :
    (Icc x y \ pi univ fun i ↦ Ioo (x' i) (y' i)) ⊆
      (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y :=
  by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simp at ha'
  simp [le_update_iff, update_le_iff, hxa, hay, hxa _, hay _, ← exists_or]
  rcases ha' with ⟨w, hw⟩
  apply Exists.intro w
  cases lt_or_le (x' w) (a w) <;> simp_all
#align set.Icc_diff_pi_univ_Ioo_subset Set.Icc_diff_pi_univ_Ioo_subset

/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
theorem Icc_diff_pi_univ_Ioc_subset (x y z : ∀ i, α i) :
    (Icc x z \ pi univ fun i ↦ Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (update z i (y i)) := by
  rintro a ⟨⟨hax, haz⟩, hay⟩
  simpa [not_and_or, hax, le_update_iff, haz _] using hay
#align set.Icc_diff_pi_univ_Ioc_subset Set.Icc_diff_pi_univ_Ioc_subset

end Set
