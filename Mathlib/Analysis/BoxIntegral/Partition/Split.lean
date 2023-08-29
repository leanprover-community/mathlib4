/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.BoxIntegral.Partition.Basic

#align_import analysis.box_integral.partition.split from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Split a box along one or more hyperplanes

## Main definitions

A hyperplane `{x : ι → ℝ | x i = a}` splits a rectangular box `I : BoxIntegral.Box ι` into two
smaller boxes. If `a ∉ Ioo (I.lower i, I.upper i)`, then one of these boxes is empty, so it is not a
box in the sense of `BoxIntegral.Box`.

We introduce the following definitions.

* `BoxIntegral.Box.splitLower I i a` and `BoxIntegral.Box.splitUpper I i a` are these boxes (as
  `WithBot (BoxIntegral.Box ι)`);
* `BoxIntegral.Prepartition.split I i a` is the partition of `I` made of these two boxes (or of one
   box `I` if one of these boxes is empty);
* `BoxIntegral.Prepartition.splitMany I s`, where `s : Finset (ι × ℝ)` is a finite set of
  hyperplanes `{x : ι → ℝ | x i = a}` encoded as pairs `(i, a)`, is the partition of `I` made by
  cutting it along all the hyperplanes in `s`.

## Main results

The main result `BoxIntegral.Prepartition.exists_iUnion_eq_diff` says that any prepartition `π` of
`I` admits a prepartition `π'` of `I` that covers exactly `I \ π.iUnion`. One of these prepartitions
is available as `BoxIntegral.Prepartition.compl`.

## Tags

rectangular box, partition, hyperplane
-/


noncomputable section

open Classical BigOperators Filter

open Function Set Filter

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

namespace Box

variable {I : Box ι} {i : ι} {x : ℝ} {y : ι → ℝ}

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `BoxIntegral.Box.splitLower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). As usual, we represent a box that may be empty as
`WithBot (BoxIntegral.Box ι)`. -/
def splitLower (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' I.lower (update I.upper i (min x (I.upper i)))
#align box_integral.box.split_lower BoxIntegral.Box.splitLower

@[simp]
theorem coe_splitLower : (splitLower I i x : Set (ι → ℝ)) = ↑I ∩ { y | y i ≤ x } := by
  rw [splitLower, coe_mk']
  -- ⊢ (Set.pi univ fun i_1 => Ioc (lower I i_1) (update I.upper i (min x (upper I  …
  ext y
  -- ⊢ (y ∈ Set.pi univ fun i_1 => Ioc (lower I i_1) (update I.upper i (min x (uppe …
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_setOf_eq, forall_and, ← Pi.le_def,
    le_update_iff, le_min_iff, and_assoc, and_forall_ne (p := fun j => y j ≤ upper I j) i, mem_def]
  rw [and_comm (a := y i ≤ x), Pi.le_def]
  -- 🎉 no goals
#align box_integral.box.coe_split_lower BoxIntegral.Box.coe_splitLower

theorem splitLower_le : I.splitLower i x ≤ I :=
  withBotCoe_subset_iff.1 <| by simp
                                -- 🎉 no goals
#align box_integral.box.split_lower_le BoxIntegral.Box.splitLower_le

@[simp]
theorem splitLower_eq_bot {i x} : I.splitLower i x = ⊥ ↔ x ≤ I.lower i := by
  rw [splitLower, mk'_eq_bot, exists_update_iff I.upper fun j y => y ≤ I.lower j]
  -- ⊢ (min x (upper I i) ≤ lower I i ∨ ∃ x x_1, upper I x ≤ lower I x) ↔ x ≤ lower …
  simp [(I.lower_lt_upper _).not_le]
  -- 🎉 no goals
#align box_integral.box.split_lower_eq_bot BoxIntegral.Box.splitLower_eq_bot

@[simp]
theorem splitLower_eq_self : I.splitLower i x = I ↔ I.upper i ≤ x := by
  simp [splitLower, update_eq_iff]
  -- 🎉 no goals
#align box_integral.box.split_lower_eq_self BoxIntegral.Box.splitLower_eq_self

theorem splitLower_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, I.lower j < update I.upper i x j :=
      (forall_update_iff I.upper fun j y => I.lower j < y).2
        ⟨h.1, fun j _ => I.lower_lt_upper _⟩) :
    I.splitLower i x = (⟨I.lower, update I.upper i x, h'⟩ : Box ι) := by
  simp only [splitLower, mk'_eq_coe, min_eq_left h.2.le, update]
  -- 🎉 no goals
#align box_integral.box.split_lower_def BoxIntegral.Box.splitLower_def

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `BoxIntegral.Box.splitUpper I i x` is the box `I ∩ {y | x < y i}`
(if it is nonempty). As usual, we represent a box that may be empty as
`WithBot (BoxIntegral.Box ι)`. -/
def splitUpper (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' (update I.lower i (max x (I.lower i))) I.upper
#align box_integral.box.split_upper BoxIntegral.Box.splitUpper

@[simp]
theorem coe_splitUpper : (splitUpper I i x : Set (ι → ℝ)) = ↑I ∩ { y | x < y i } := by
  rw [splitUpper, coe_mk']
  -- ⊢ (Set.pi univ fun i_1 => Ioc (update I.lower i (max x (lower I i)) i_1) (uppe …
  ext y
  -- ⊢ (y ∈ Set.pi univ fun i_1 => Ioc (update I.lower i (max x (lower I i)) i_1) ( …
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_setOf_eq, forall_and,
    forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc (a := x < y i),
    and_forall_ne (p := fun j => lower I j < y j) i, mem_def]
  exact and_comm
  -- 🎉 no goals
#align box_integral.box.coe_split_upper BoxIntegral.Box.coe_splitUpper

theorem splitUpper_le : I.splitUpper i x ≤ I :=
  withBotCoe_subset_iff.1 <| by simp
                                -- 🎉 no goals
#align box_integral.box.split_upper_le BoxIntegral.Box.splitUpper_le

@[simp]
theorem splitUpper_eq_bot {i x} : I.splitUpper i x = ⊥ ↔ I.upper i ≤ x := by
  rw [splitUpper, mk'_eq_bot, exists_update_iff I.lower fun j y => I.upper j ≤ y]
  -- ⊢ (upper I i ≤ max x (lower I i) ∨ ∃ x x_1, upper I x ≤ lower I x) ↔ upper I i …
  simp [(I.lower_lt_upper _).not_le]
  -- 🎉 no goals
#align box_integral.box.split_upper_eq_bot BoxIntegral.Box.splitUpper_eq_bot

@[simp]
theorem splitUpper_eq_self : I.splitUpper i x = I ↔ x ≤ I.lower i := by
  simp [splitUpper, update_eq_iff]
  -- 🎉 no goals
#align box_integral.box.split_upper_eq_self BoxIntegral.Box.splitUpper_eq_self

theorem splitUpper_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, update I.lower i x j < I.upper j :=
      (forall_update_iff I.lower fun j y => y < I.upper j).2
        ⟨h.2, fun j _ => I.lower_lt_upper _⟩) :
    I.splitUpper i x = (⟨update I.lower i x, I.upper, h'⟩ : Box ι) := by
  simp only [splitUpper, mk'_eq_coe, max_eq_left h.1.le, update]
  -- 🎉 no goals
#align box_integral.box.split_upper_def BoxIntegral.Box.splitUpper_def

theorem disjoint_splitLower_splitUpper (I : Box ι) (i : ι) (x : ℝ) :
    Disjoint (I.splitLower i x) (I.splitUpper i x) := by
  rw [← disjoint_withBotCoe, coe_splitLower, coe_splitUpper]
  -- ⊢ Disjoint (↑I ∩ {y | y i ≤ x}) (↑I ∩ {y | x < y i})
  refine' (Disjoint.inf_left' _ _).inf_right' _
  -- ⊢ Disjoint {y | y i ≤ x} {y | x < y i}
  rw [Set.disjoint_left]
  -- ⊢ ∀ ⦃a : ι → ℝ⦄, a ∈ {y | y i ≤ x} → ¬a ∈ {y | x < y i}
  exact fun y (hle : y i ≤ x) hlt => not_lt_of_le hle hlt
  -- 🎉 no goals
#align box_integral.box.disjoint_split_lower_split_upper BoxIntegral.Box.disjoint_splitLower_splitUpper

theorem splitLower_ne_splitUpper (I : Box ι) (i : ι) (x : ℝ) :
    I.splitLower i x ≠ I.splitUpper i x := by
  cases' le_or_lt x (I.lower i) with h
  -- ⊢ splitLower I i x ≠ splitUpper I i x
  · rw [splitUpper_eq_self.2 h, splitLower_eq_bot.2 h]
    -- ⊢ ⊥ ≠ ↑I
    exact WithBot.bot_ne_coe
    -- 🎉 no goals
  · refine' (disjoint_splitLower_splitUpper I i x).ne _
    -- ⊢ splitLower I i x ≠ ⊥
    rwa [Ne.def, splitLower_eq_bot, not_le]
    -- 🎉 no goals
#align box_integral.box.split_lower_ne_split_upper BoxIntegral.Box.splitLower_ne_splitUpper

end Box

namespace Prepartition

variable {I J : Box ι} {i : ι} {x : ℝ}

/-- The partition of `I : Box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : Box ι) (i : ι) (x : ℝ) : Prepartition I :=
  ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      -- ⊢ ∀ (J : WithBot (Box ι)), J = Box.splitLower I i x ∨ J = Box.splitUpper I i x …
      rintro J (rfl | rfl)
      -- ⊢ Box.splitLower I i x ≤ ↑I
      exacts [Box.splitLower_le, Box.splitUpper_le])
      -- 🎉 no goals
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and_iff, Set.mem_singleton_iff,
        pairwise_insert_of_symmetric symmetric_disjoint, pairwise_singleton]
      rintro J rfl -
      -- ⊢ Disjoint (Box.splitLower I i x) (Box.splitUpper I i x)
      exact I.disjoint_splitLower_splitUpper i x)
      -- 🎉 no goals
#align box_integral.prepartition.split BoxIntegral.Prepartition.split

@[simp]
theorem mem_split_iff : J ∈ split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x := by
  simp [split]
  -- 🎉 no goals
#align box_integral.prepartition.mem_split_iff BoxIntegral.Prepartition.mem_split_iff

theorem mem_split_iff' : J ∈ split I i x ↔
    (J : Set (ι → ℝ)) = ↑I ∩ { y | y i ≤ x } ∨ (J : Set (ι → ℝ)) = ↑I ∩ { y | x < y i } := by
  simp [mem_split_iff, ← Box.withBotCoe_inj]
  -- 🎉 no goals
#align box_integral.prepartition.mem_split_iff' BoxIntegral.Prepartition.mem_split_iff'

@[simp]
theorem iUnion_split (I : Box ι) (i : ι) (x : ℝ) : (split I i x).iUnion = I := by
  simp [split, ← inter_union_distrib_left, ← setOf_or, le_or_lt]
  -- 🎉 no goals
#align box_integral.prepartition.Union_split BoxIntegral.Prepartition.iUnion_split

theorem isPartitionSplit (I : Box ι) (i : ι) (x : ℝ) : IsPartition (split I i x) :=
  isPartition_iff_iUnion_eq.2 <| iUnion_split I i x
#align box_integral.prepartition.is_partition_split BoxIntegral.Prepartition.isPartitionSplit

-- Porting note: In the type, changed `Option.elim` to `Option.elim'`
theorem sum_split_boxes {M : Type*} [AddCommMonoid M] (I : Box ι) (i : ι) (x : ℝ) (f : Box ι → M) :
    (∑ J in (split I i x).boxes, f J) =
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f := by
  rw [split, sum_ofWithBot, Finset.sum_pair (I.splitLower_ne_splitUpper i x)]
  -- 🎉 no goals
#align box_integral.prepartition.sum_split_boxes BoxIntegral.Prepartition.sum_split_boxes

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
theorem split_of_not_mem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ := by
  refine' ((isPartitionTop I).eq_of_boxes_subset fun J hJ => _).symm
  -- ⊢ J ∈ (split I i x).boxes
  rcases mem_top.1 hJ with rfl; clear hJ
  -- ⊢ J ∈ (split J i x).boxes
                                -- ⊢ J ∈ (split J i x).boxes
  rw [mem_boxes, mem_split_iff]
  -- ⊢ ↑J = Box.splitLower J i x ∨ ↑J = Box.splitUpper J i x
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  -- ⊢ ↑J = Box.splitLower J i x ∨ ↑J = Box.splitUpper J i x
  cases h <;> [right; left]
  -- ⊢ ↑J = Box.splitUpper J i x
  · rwa [eq_comm, Box.splitUpper_eq_self]
    -- 🎉 no goals
  · rwa [eq_comm, Box.splitLower_eq_self]
    -- 🎉 no goals
#align box_integral.prepartition.split_of_not_mem_Ioo BoxIntegral.Prepartition.split_of_not_mem_Ioo

theorem coe_eq_of_mem_split_of_mem_le {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J)
    (h₃ : y i ≤ x) : (J : Set (ι → ℝ)) = ↑I ∩ { y | y i ≤ x } := by
  refine' (mem_split_iff'.1 h₁).resolve_right fun H => _
  -- ⊢ False
  rw [← Box.mem_coe, H] at h₂
  -- ⊢ False
  exact h₃.not_lt h₂.2
  -- 🎉 no goals
#align box_integral.prepartition.coe_eq_of_mem_split_of_mem_le BoxIntegral.Prepartition.coe_eq_of_mem_split_of_mem_le

theorem coe_eq_of_mem_split_of_lt_mem {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J)
    (h₃ : x < y i) : (J : Set (ι → ℝ)) = ↑I ∩ { y | x < y i } := by
  refine' (mem_split_iff'.1 h₁).resolve_left fun H => _
  -- ⊢ False
  rw [← Box.mem_coe, H] at h₂
  -- ⊢ False
  exact h₃.not_le h₂.2
  -- 🎉 no goals
#align box_integral.prepartition.coe_eq_of_mem_split_of_lt_mem BoxIntegral.Prepartition.coe_eq_of_mem_split_of_lt_mem

@[simp]
theorem restrict_split (h : I ≤ J) (i : ι) (x : ℝ) : (split J i x).restrict I = split I i x := by
  refine' ((isPartitionSplit J i x).restrict h).eq_of_boxes_subset _
  -- ⊢ (restrict (split J i x) I).boxes ⊆ (split I i x).boxes
  simp only [Finset.subset_iff, mem_boxes, mem_restrict', exists_prop, mem_split_iff']
  -- ⊢ ∀ ⦃x_1 : Box ι⦄, (∃ J', (↑J' = ↑J ∩ {y | y i ≤ x} ∨ ↑J' = ↑J ∩ {y | x < y i} …
  have : ∀ s, (I ∩ s : Set (ι → ℝ)) ⊆ J := fun s => (inter_subset_left _ _).trans h
  -- ⊢ ∀ ⦃x_1 : Box ι⦄, (∃ J', (↑J' = ↑J ∩ {y | y i ≤ x} ∨ ↑J' = ↑J ∩ {y | x < y i} …
  rintro J₁ ⟨J₂, H₂ | H₂, H₁⟩ <;> [left; right] <;>
  -- ⊢ ↑J₁ = ↑I ∩ {y | y i ≤ x}
    simp [H₁, H₂, inter_left_comm (I : Set (ι → ℝ)), this]
    -- 🎉 no goals
    -- 🎉 no goals
#align box_integral.prepartition.restrict_split BoxIntegral.Prepartition.restrict_split

theorem inf_split (π : Prepartition I) (i : ι) (x : ℝ) :
    π ⊓ split I i x = π.biUnion fun J => split J i x :=
  biUnion_congr_of_le rfl fun _ hJ => restrict_split hJ i x
#align box_integral.prepartition.inf_split BoxIntegral.Prepartition.inf_split

/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
def splitMany (I : Box ι) (s : Finset (ι × ℝ)) : Prepartition I :=
  s.inf fun p => split I p.1 p.2
#align box_integral.prepartition.split_many BoxIntegral.Prepartition.splitMany

@[simp]
theorem splitMany_empty (I : Box ι) : splitMany I ∅ = ⊤ :=
  Finset.inf_empty
#align box_integral.prepartition.split_many_empty BoxIntegral.Prepartition.splitMany_empty

@[simp]
theorem splitMany_insert (I : Box ι) (s : Finset (ι × ℝ)) (p : ι × ℝ) :
    splitMany I (insert p s) = splitMany I s ⊓ split I p.1 p.2 := by
  rw [splitMany, Finset.inf_insert, inf_comm, splitMany]
  -- 🎉 no goals
#align box_integral.prepartition.split_many_insert BoxIntegral.Prepartition.splitMany_insert

theorem splitMany_le_split (I : Box ι) {s : Finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
    splitMany I s ≤ split I p.1 p.2 :=
  Finset.inf_le hp
#align box_integral.prepartition.split_many_le_split BoxIntegral.Prepartition.splitMany_le_split

theorem isPartition_splitMany (I : Box ι) (s : Finset (ι × ℝ)) : IsPartition (splitMany I s) :=
  Finset.induction_on s (by simp only [splitMany_empty, isPartitionTop]) fun a s _ hs => by
                            -- 🎉 no goals
    simpa only [splitMany_insert, inf_split] using hs.biUnion fun J _ => isPartitionSplit _ _ _
    -- 🎉 no goals
#align box_integral.prepartition.is_partition_split_many BoxIntegral.Prepartition.isPartition_splitMany

@[simp]
theorem iUnion_splitMany (I : Box ι) (s : Finset (ι × ℝ)) : (splitMany I s).iUnion = I :=
  (isPartition_splitMany I s).iUnion_eq
#align box_integral.prepartition.Union_split_many BoxIntegral.Prepartition.iUnion_splitMany

theorem inf_splitMany {I : Box ι} (π : Prepartition I) (s : Finset (ι × ℝ)) :
    π ⊓ splitMany I s = π.biUnion fun J => splitMany J s := by
  induction' s using Finset.induction_on with p s _ ihp
  -- ⊢ π ⊓ splitMany I ∅ = biUnion π fun J => splitMany J ∅
  · simp
    -- 🎉 no goals
  · simp_rw [splitMany_insert, ← inf_assoc, ihp, inf_split, biUnion_assoc]
    -- 🎉 no goals
#align box_integral.prepartition.inf_split_many BoxIntegral.Prepartition.inf_splitMany

/-- Let `s : Finset (ι × ℝ)` be a set of hyperplanes `{x : ι → ℝ | x i = r}` in `ι → ℝ` encoded as
pairs `(i, r)`. Suppose that this set contains all faces of a box `J`. The hyperplanes of `s` split
a box `I` into subboxes. Let `Js` be one of them. If `J` and `Js` have nonempty intersection, then
`Js` is a subbox of `J`.  -/
theorem not_disjoint_imp_le_of_subset_of_mem_splitMany {I J Js : Box ι} {s : Finset (ι × ℝ)}
    (H : ∀ i, {(i, J.lower i), (i, J.upper i)} ⊆ s) (HJs : Js ∈ splitMany I s)
    (Hn : ¬Disjoint (J : WithBot (Box ι)) Js) : Js ≤ J := by
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at H
  -- ⊢ Js ≤ J
  rcases Box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩
  -- ⊢ Js ≤ J
  refine' fun y hy i => ⟨_, _⟩
  -- ⊢ Box.lower J i < y i
  · rcases splitMany_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.lower i), Hle⟩
    -- ⊢ Box.lower J i < y i
    have := Hle hxs
    -- ⊢ Box.lower J i < y i
    rw [← Box.coe_subset_coe, coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1] at Hle
    -- ⊢ Box.lower J i < y i
    exact (Hle hy).2
    -- 🎉 no goals
  · rcases splitMany_le_split I (H i).2 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.upper i), Hle⟩
    -- ⊢ y i ≤ Box.upper J i
    have := Hle hxs
    -- ⊢ y i ≤ Box.upper J i
    rw [← Box.coe_subset_coe, coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2] at Hle
    -- ⊢ y i ≤ Box.upper J i
    exact (Hle hy).2
    -- 🎉 no goals
#align box_integral.prepartition.not_disjoint_imp_le_of_subset_of_mem_split_many BoxIntegral.Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitMany

section Fintype

variable [Finite ι]

/-- Let `s` be a finite set of boxes in `ℝⁿ = ι → ℝ`. Then there exists a finite set `t₀` of
hyperplanes (namely, the set of all hyperfaces of boxes in `s`) such that for any `t ⊇ t₀`
and any box `I` in `ℝⁿ` the following holds. The hyperplanes from `t` split `I` into subboxes.
Let `J'` be one of them, and let `J` be one of the boxes in `s`. If these boxes have a nonempty
intersection, then `J' ≤ J`. -/
theorem eventually_not_disjoint_imp_le_of_mem_splitMany (s : Finset (Box ι)) :
    ∀ᶠ t : Finset (ι × ℝ) in atTop, ∀ (I : Box ι), ∀ J ∈ s, ∀ J' ∈ splitMany I t,
      ¬Disjoint (J : WithBot (Box ι)) J' → J' ≤ J := by
  cases nonempty_fintype ι
  -- ⊢ ∀ᶠ (t : Finset (ι × ℝ)) in atTop, ∀ (I J : Box ι), J ∈ s → ∀ (J' : Box ι), J …
  refine' eventually_atTop.2
    ⟨s.biUnion fun J => Finset.univ.biUnion fun i => {(i, J.lower i), (i, J.upper i)},
      fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_splitMany (fun i => _) hJ'⟩
  exact fun p hp =>
    ht (Finset.mem_biUnion.2 ⟨J, hJ, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hp⟩⟩)
#align box_integral.prepartition.eventually_not_disjoint_imp_le_of_mem_split_many BoxIntegral.Prepartition.eventually_not_disjoint_imp_le_of_mem_splitMany

theorem eventually_splitMany_inf_eq_filter (π : Prepartition I) :
    ∀ᶠ t : Finset (ι × ℝ) in atTop,
      π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J ⊆ π.iUnion := by
  refine' (eventually_not_disjoint_imp_le_of_mem_splitMany π.boxes).mono fun t ht => _
  -- ⊢ π ⊓ splitMany I t = filter (splitMany I t) fun J => ↑J ⊆ Prepartition.iUnion π
  refine' le_antisymm ((biUnion_le_iff _).2 fun J hJ => _) (le_inf (fun J hJ => _) (filter_le _ _))
  -- ⊢ restrict (splitMany I t) J ≤ restrict (filter (splitMany I t) fun J => ↑J ⊆  …
  · refine' ofWithBot_mono _
    -- ⊢ ∀ (J_1 : WithBot (Box ι)), J_1 ∈ Finset.image (fun J' => ↑J ⊓ ↑J') (splitMan …
    simp only [Finset.mem_image, exists_prop, mem_boxes, mem_filter]
    -- ⊢ ∀ (J_1 : WithBot (Box ι)), (∃ a, a ∈ splitMany I t ∧ ↑J ⊓ ↑a = J_1) → J_1 ≠  …
    rintro _ ⟨J₁, h₁, rfl⟩ hne
    -- ⊢ ∃ J', (∃ a, (a ∈ splitMany I t ∧ ↑a ⊆ Prepartition.iUnion π) ∧ ↑J ⊓ ↑a = J') …
    refine' ⟨_, ⟨J₁, ⟨h₁, Subset.trans _ (π.subset_iUnion hJ)⟩, rfl⟩, le_rfl⟩
    -- ⊢ ↑J₁ ⊆ ↑J
    exact ht I J hJ J₁ h₁ (mt disjoint_iff.1 hne)
    -- 🎉 no goals
  · rw [mem_filter] at hJ
    -- ⊢ ∃ I', I' ∈ π ∧ J ≤ I'
    rcases Set.mem_iUnion₂.1 (hJ.2 J.upper_mem) with ⟨J', hJ', hmem⟩
    -- ⊢ ∃ I', I' ∈ π ∧ J ≤ I'
    refine' ⟨J', hJ', ht I _ hJ' _ hJ.1 <| Box.not_disjoint_coe_iff_nonempty_inter.2 _⟩
    -- ⊢ Set.Nonempty (↑J' ∩ ↑J)
    exact ⟨J.upper, hmem, J.upper_mem⟩
    -- 🎉 no goals
#align box_integral.prepartition.eventually_split_many_inf_eq_filter BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter

theorem exists_splitMany_inf_eq_filter_of_finite (s : Set (Prepartition I)) (hs : s.Finite) :
    ∃ t : Finset (ι × ℝ),
      ∀ π ∈ s, π ⊓ splitMany I t = (splitMany I t).filter fun J => ↑J ⊆ π.iUnion :=
  haveI := fun π (_ : π ∈ s) => eventually_splitMany_inf_eq_filter π
  (hs.eventually_all.2 this).exists
#align box_integral.prepartition.exists_split_many_inf_eq_filter_of_finite BoxIntegral.Prepartition.exists_splitMany_inf_eq_filter_of_finite

/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`splitMany I s ≤ π`. -/
theorem IsPartition.exists_splitMany_le {I : Box ι} {π : Prepartition I} (h : IsPartition π) :
    ∃ s, splitMany I s ≤ π := by
  refine' (eventually_splitMany_inf_eq_filter π).exists.imp fun s hs => _
  -- ⊢ splitMany I s ≤ π
  rwa [h.iUnion_eq, filter_of_true, inf_eq_right] at hs
  -- ⊢ ∀ (J : Box ι), J ∈ splitMany I s → ↑J ⊆ ↑I
  exact fun J hJ => le_of_mem _ hJ
  -- 🎉 no goals
#align box_integral.prepartition.is_partition.exists_split_many_le BoxIntegral.Prepartition.IsPartition.exists_splitMany_le

/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.iUnion`. -/
theorem exists_iUnion_eq_diff (π : Prepartition I) :
    ∃ π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion := by
  rcases π.eventually_splitMany_inf_eq_filter.exists with ⟨s, hs⟩
  -- ⊢ ∃ π', Prepartition.iUnion π' = ↑I \ Prepartition.iUnion π
  use (splitMany I s).filter fun J => ¬(J : Set (ι → ℝ)) ⊆ π.iUnion
  -- ⊢ Prepartition.iUnion (filter (splitMany I s) fun J => ¬↑J ⊆ Prepartition.iUni …
  simp [← hs]
  -- 🎉 no goals
#align box_integral.prepartition.exists_Union_eq_diff BoxIntegral.Prepartition.exists_iUnion_eq_diff

/-- If `π` is a prepartition of `I`, then `π.compl` is a prepartition of `I`
such that `π.compl.iUnion = I \ π.iUnion`. -/
def compl (π : Prepartition I) : Prepartition I :=
  π.exists_iUnion_eq_diff.choose
#align box_integral.prepartition.compl BoxIntegral.Prepartition.compl

@[simp]
theorem iUnion_compl (π : Prepartition I) : π.compl.iUnion = ↑I \ π.iUnion :=
  π.exists_iUnion_eq_diff.choose_spec
#align box_integral.prepartition.Union_compl BoxIntegral.Prepartition.iUnion_compl

/-- Since the definition of `BoxIntegral.Prepartition.compl` uses `Exists.choose`,
the result depends only on `π.iUnion`. -/
theorem compl_congr {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π₂.iUnion) : π₁.compl = π₂.compl := by
  dsimp only [compl]
  -- ⊢ Exists.choose (_ : ∃ π', Prepartition.iUnion π' = ↑I \ Prepartition.iUnion π …
  congr 1
  -- ⊢ (fun π' => Prepartition.iUnion π' = ↑I \ Prepartition.iUnion π₁) = fun π' => …
  rw [h]
  -- 🎉 no goals
#align box_integral.prepartition.compl_congr BoxIntegral.Prepartition.compl_congr

theorem IsPartition.compl_eq_bot {π : Prepartition I} (h : IsPartition π) : π.compl = ⊥ := by
  rw [← iUnion_eq_empty, iUnion_compl, h.iUnion_eq, diff_self]
  -- 🎉 no goals
#align box_integral.prepartition.is_partition.compl_eq_bot BoxIntegral.Prepartition.IsPartition.compl_eq_bot

@[simp]
theorem compl_top : (⊤ : Prepartition I).compl = ⊥ :=
  (isPartitionTop I).compl_eq_bot
#align box_integral.prepartition.compl_top BoxIntegral.Prepartition.compl_top

end Fintype

end Prepartition

end BoxIntegral
