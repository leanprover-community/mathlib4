/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Data.Set.Lattice

#align_import data.set.intervals.pi from "leanprover-community/mathlib"@"e4bc74cbaf429d706cb9140902f7ca6c431e75a4"

/-!
# Intervals in `pi`-space

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

-- Porting note: Added, since dot notation no longer works on `Function.update`
open Function

variable {ι : Type*} {α : ι → Type*}

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
    (h₁ : ∀ i ∈ s, f₁ i ∈ Icc (g₁ i) (g₂ i)) (h₂ : ∀ i ∉ s, f₂ i ∈ Icc (g₁ i) (g₂ i)) :
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
    (pi univ fun i ↦ Ioc (update x i₀ m i) (y i)) := by
  rw [disjoint_left]
  rintro z h₁ h₂
  refine (h₁ i₀ (mem_univ _)).2.not_lt ?_
  simpa only [Function.update_same] using (h₂ i₀ (mem_univ _)).1
#align set.disjoint_pi_univ_Ioc_update_left_right Set.disjoint_pi_univ_Ioc_update_left_right

end PiPreorder

section PiPartialOrder

variable [DecidableEq ι] [∀ i, PartialOrder (α i)]

-- Porting note: Dot notation on `Function.update` broke
theorem image_update_Icc (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Icc a b = Icc (update f i a) (update f i b) := by
  ext x
  rw [← Set.pi_univ_Icc]
  refine ⟨?_, fun h => ⟨x i, ?_, ?_⟩⟩
  · rintro ⟨c, hc, rfl⟩
    simpa [update_le_update_iff]
  · simpa only [Function.update_same] using h i (mem_univ i)
  · ext j
    obtain rfl | hij := eq_or_ne i j
    · exact Function.update_same _ _ _
    · simpa only [Function.update_noteq hij.symm, le_antisymm_iff] using h j (mem_univ j)
#align set.image_update_Icc Set.image_update_Icc

theorem image_update_Ico (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Ico a b = Ico (update f i a) (update f i b) := by
  rw [← Icc_diff_right, ← Icc_diff_right, image_diff (update_injective _ _), image_singleton,
    image_update_Icc]
#align set.image_update_Ico Set.image_update_Ico

theorem image_update_Ioc (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Ioc a b = Ioc (update f i a) (update f i b) := by
  rw [← Icc_diff_left, ← Icc_diff_left, image_diff (update_injective _ _), image_singleton,
    image_update_Icc]
#align set.image_update_Ioc Set.image_update_Ioc

theorem image_update_Ioo (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' Ioo a b = Ioo (update f i a) (update f i b) := by
  rw [← Ico_diff_left, ← Ico_diff_left, image_diff (update_injective _ _), image_singleton,
    image_update_Ico]
#align set.image_update_Ioo Set.image_update_Ioo

theorem image_update_Icc_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Icc a (f i) = Icc (update f i a) f := by simpa using image_update_Icc f i a (f i)
#align set.image_update_Icc_left Set.image_update_Icc_left

theorem image_update_Ico_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Ico a (f i) = Ico (update f i a) f := by simpa using image_update_Ico f i a (f i)
#align set.image_update_Ico_left Set.image_update_Ico_left

theorem image_update_Ioc_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Ioc a (f i) = Ioc (update f i a) f := by simpa using image_update_Ioc f i a (f i)
#align set.image_update_Ioc_left Set.image_update_Ioc_left

theorem image_update_Ioo_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' Ioo a (f i) = Ioo (update f i a) f := by simpa using image_update_Ioo f i a (f i)
#align set.image_update_Ioo_left Set.image_update_Ioo_left

theorem image_update_Icc_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Icc (f i) b = Icc f (update f i b) := by simpa using image_update_Icc f i (f i) b
#align set.image_update_Icc_right Set.image_update_Icc_right

theorem image_update_Ico_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Ico (f i) b = Ico f (update f i b) := by simpa using image_update_Ico f i (f i) b
#align set.image_update_Ico_right Set.image_update_Ico_right

theorem image_update_Ioc_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Ioc (f i) b = Ioc f (update f i b) := by simpa using image_update_Ioc f i (f i) b
#align set.image_update_Ioc_right Set.image_update_Ioc_right

theorem image_update_Ioo_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' Ioo (f i) b = Ioo f (update f i b) := by simpa using image_update_Ioo f i (f i) b
#align set.image_update_Ioo_right Set.image_update_Ioo_right

variable [∀ i, One (α i)]

@[to_additive]
theorem image_mulSingle_Icc (i : ι) (a b : α i) :
    Pi.mulSingle i '' Icc a b = Icc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Icc _ _ _ _
#align set.image_mul_single_Icc Set.image_mulSingle_Icc
#align set.image_single_Icc Set.image_single_Icc

@[to_additive]
theorem image_mulSingle_Ico (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ico a b = Ico (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ico _ _ _ _
#align set.image_mul_single_Ico Set.image_mulSingle_Ico
#align set.image_single_Ico Set.image_single_Ico

@[to_additive]
theorem image_mulSingle_Ioc (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ioc a b = Ioc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ioc _ _ _ _
#align set.image_mul_single_Ioc Set.image_mulSingle_Ioc
#align set.image_single_Ioc Set.image_single_Ioc

@[to_additive]
theorem image_mulSingle_Ioo (i : ι) (a b : α i) :
    Pi.mulSingle i '' Ioo a b = Ioo (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_Ioo _ _ _ _
#align set.image_mul_single_Ioo Set.image_mulSingle_Ioo
#align set.image_single_Ioo Set.image_single_Ioo

@[to_additive]
theorem image_mulSingle_Icc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Icc a 1 = Icc (Pi.mulSingle i a) 1 :=
  image_update_Icc_left _ _ _
#align set.image_mul_single_Icc_left Set.image_mulSingle_Icc_left
#align set.image_single_Icc_left Set.image_single_Icc_left

@[to_additive]
theorem image_mulSingle_Ico_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ico a 1 = Ico (Pi.mulSingle i a) 1 :=
  image_update_Ico_left _ _ _
#align set.image_mul_single_Ico_left Set.image_mulSingle_Ico_left
#align set.image_single_Ico_left Set.image_single_Ico_left

@[to_additive]
theorem image_mulSingle_Ioc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ioc a 1 = Ioc (Pi.mulSingle i a) 1 :=
  image_update_Ioc_left _ _ _
#align set.image_mul_single_Ioc_left Set.image_mulSingle_Ioc_left
#align set.image_single_Ioc_left Set.image_single_Ioc_left

@[to_additive]
theorem image_mulSingle_Ioo_left (i : ι) (a : α i) :
    Pi.mulSingle i '' Ioo a 1 = Ioo (Pi.mulSingle i a) 1 :=
  image_update_Ioo_left _ _ _
#align set.image_mul_single_Ioo_left Set.image_mulSingle_Ioo_left
#align set.image_single_Ioo_left Set.image_single_Ioo_left

@[to_additive]
theorem image_mulSingle_Icc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Icc 1 b = Icc 1 (Pi.mulSingle i b) :=
  image_update_Icc_right _ _ _
#align set.image_mul_single_Icc_right Set.image_mulSingle_Icc_right
#align set.image_single_Icc_right Set.image_single_Icc_right

@[to_additive]
theorem image_mulSingle_Ico_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ico 1 b = Ico 1 (Pi.mulSingle i b) :=
  image_update_Ico_right _ _ _
#align set.image_mul_single_Ico_right Set.image_mulSingle_Ico_right
#align set.image_single_Ico_right Set.image_single_Ico_right

@[to_additive]
theorem image_mulSingle_Ioc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ioc 1 b = Ioc 1 (Pi.mulSingle i b) :=
  image_update_Ioc_right _ _ _
#align set.image_mul_single_Ioc_right Set.image_mulSingle_Ioc_right
#align set.image_single_Ioc_right Set.image_single_Ioc_right

@[to_additive]
theorem image_mulSingle_Ioo_right (i : ι) (b : α i) :
    Pi.mulSingle i '' Ioo 1 b = Ioo 1 (Pi.mulSingle i b) :=
  image_update_Ioo_right _ _ _
#align set.image_mul_single_Ioo_right Set.image_mulSingle_Ioo_right
#align set.image_single_Ioo_right Set.image_single_Ioo_right

end PiPartialOrder

section PiLattice

variable [∀ i, Lattice (α i)]

@[simp]
theorem pi_univ_uIcc (a b : ∀ i, α i) : (pi univ fun i => uIcc (a i) (b i)) = uIcc a b :=
  pi_univ_Icc _ _
#align set.pi_univ_uIcc Set.pi_univ_uIcc

variable [DecidableEq ι]

theorem image_update_uIcc (f : ∀ i, α i) (i : ι) (a b : α i) :
    update f i '' uIcc a b = uIcc (update f i a) (update f i b) :=
  (image_update_Icc _ _ _ _).trans <| by simp_rw [uIcc, update_sup, update_inf]
#align set.image_update_uIcc Set.image_update_uIcc

theorem image_update_uIcc_left (f : ∀ i, α i) (i : ι) (a : α i) :
    update f i '' uIcc a (f i) = uIcc (update f i a) f := by
  simpa using image_update_uIcc f i a (f i)
#align set.image_update_uIcc_left Set.image_update_uIcc_left

theorem image_update_uIcc_right (f : ∀ i, α i) (i : ι) (b : α i) :
    update f i '' uIcc (f i) b = uIcc f (update f i b) := by
  simpa using image_update_uIcc f i (f i) b
#align set.image_update_uIcc_right Set.image_update_uIcc_right

variable [∀ i, One (α i)]

@[to_additive]
theorem image_mulSingle_uIcc (i : ι) (a b : α i) :
    Pi.mulSingle i '' uIcc a b = uIcc (Pi.mulSingle i a) (Pi.mulSingle i b) :=
  image_update_uIcc _ _ _ _
#align set.image_mul_single_uIcc Set.image_mulSingle_uIcc
#align set.image_single_uIcc Set.image_single_uIcc

@[to_additive]
theorem image_mulSingle_uIcc_left (i : ι) (a : α i) :
    Pi.mulSingle i '' uIcc a 1 = uIcc (Pi.mulSingle i a) 1 :=
  image_update_uIcc_left _ _ _
#align set.image_mul_single_uIcc_left Set.image_mulSingle_uIcc_left
#align set.image_single_uIcc_left Set.image_single_uIcc_left

@[to_additive]
theorem image_mulSingle_uIcc_right (i : ι) (b : α i) :
    Pi.mulSingle i '' uIcc 1 b = uIcc 1 (Pi.mulSingle i b) :=
  image_update_uIcc_right _ _ _
#align set.image_mul_single_uIcc_right Set.image_mulSingle_uIcc_right
#align set.image_single_uIcc_right Set.image_single_uIcc_right

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
    (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y := by
  rintro a ⟨⟨hxa, hay⟩, ha'⟩
  simp at ha'
  simp only [ge_iff_le, le_update_iff, ne_eq, not_and, not_forall, not_le, exists_prop, gt_iff_lt,
    update_le_iff, mem_union, mem_iUnion, mem_Icc, hxa, hay _, implies_true, and_true, true_and,
    hxa _, hay, ← exists_or]
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
