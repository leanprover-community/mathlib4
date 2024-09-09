/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Common

/-!
# Intervals without endpoints ordering

In any lattice `α`, we define `uIcc a b` to be `Icc (a ⊓ b) (a ⊔ b)`, which in a linear order is
the set of elements lying between `a` and `b`.

`Icc a b` requires the assumption `a ≤ b` to be meaningful, which is sometimes inconvenient. The
interval as defined in this file is always the set of things lying between `a` and `b`, regardless
of the relative order of `a` and `b`.

For real numbers, `uIcc a b` is the same as `segment ℝ a b`.

In a product or pi type, `uIcc a b` is the smallest box containing `a` and `b`. For example,
`uIcc (1, -1) (-1, 1) = Icc (-1, -1) (1, 1)` is the square of vertices `(1, -1)`, `(-1, -1)`,
`(-1, 1)`, `(1, 1)`.

In `Finset α` (seen as a hypercube of dimension `Fintype.card α`), `uIcc a b` is the smallest
subcube containing both `a` and `b`.

## Notation

We use the localized notation `[[a, b]]` for `uIcc a b`. One can open the locale `Interval` to
make the notation available.

-/


open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

section Lattice

variable [Lattice α] [Lattice β] {a a₁ a₂ b b₁ b₂ c x : α}

/-- `uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `Set.Icc (a ⊓ b) (a ⊔ b)`. In a product type,
`uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Set α := Icc (a ⊓ b) (a ⊔ b)

-- Porting note: temporarily remove `scoped[uIcc]` and use `[[]]` instead of `[]` before a
-- workaround is found.
-- Porting note 2 : now `scoped[Interval]` works again.
/-- `[[a, b]]` denotes the set of elements lying between `a` and `b`, inclusive. -/
scoped[Interval] notation "[[" a ", " b "]]" => Set.uIcc a b

open Interval

@[simp] lemma dual_uIcc (a b : α) : [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]] :=
  -- Note: needed to hint `(α := α)` after #8386 (elaboration order?)
  dual_Icc (α := α)

@[simp]
lemma uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]
lemma uIcc_of_ge (h : b ≤ a) : [[a, b]] = Icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

lemma uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by simp_rw [uIcc, inf_comm, sup_comm]

lemma uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b := uIcc_of_le h.le
lemma uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a := uIcc_of_ge h.le

-- Porting note (#10618): `simp` can prove this
-- @[simp]
lemma uIcc_self : [[a, a]] = {a} := by simp [uIcc]

@[simp] lemma nonempty_uIcc : [[a, b]].Nonempty := nonempty_Icc.2 inf_le_sup

lemma Icc_subset_uIcc : Icc a b ⊆ [[a, b]] := Icc_subset_Icc inf_le_left le_sup_right
lemma Icc_subset_uIcc' : Icc b a ⊆ [[a, b]] := Icc_subset_Icc inf_le_right le_sup_left

@[simp] lemma left_mem_uIcc : a ∈ [[a, b]] := ⟨inf_le_left, le_sup_left⟩
@[simp] lemma right_mem_uIcc : b ∈ [[a, b]] := ⟨inf_le_right, le_sup_right⟩

lemma mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [[a, b]] := Icc_subset_uIcc ⟨ha, hb⟩
lemma mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [[a, b]] := Icc_subset_uIcc' ⟨hb, ha⟩

lemma uIcc_subset_uIcc (h₁ : a₁ ∈ [[a₂, b₂]]) (h₂ : b₁ ∈ [[a₂, b₂]]) :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] :=
  Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)

lemma uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) :
    [[a₁, b₁]] ⊆ Icc a₂ b₂ :=
  Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)

lemma uIcc_subset_uIcc_iff_mem :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₁ ∈ [[a₂, b₂]] ∧ b₁ ∈ [[a₂, b₂]] :=
  Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h =>
    uIcc_subset_uIcc h.1 h.2

lemma uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup

lemma uIcc_subset_uIcc_right (h : x ∈ [[a, b]]) : [[x, b]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc

lemma uIcc_subset_uIcc_left (h : x ∈ [[a, b]]) : [[a, x]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h

lemma bdd_below_bdd_above_iff_subset_uIcc (s : Set α) :
    BddBelow s ∧ BddAbove s ↔ ∃ a b, s ⊆ [[a, b]] :=
  bddBelow_bddAbove_iff_subset_Icc.trans
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, fun _ hx => Icc_subset_uIcc (h hx)⟩, fun ⟨_, _, h⟩ => ⟨_, _, h⟩⟩

section Prod

@[simp]
theorem uIcc_prod_uIcc (a₁ a₂ : α) (b₁ b₂ : β) :
    [[a₁, a₂]] ×ˢ [[b₁, b₂]] = [[(a₁, b₁), (a₂, b₂)]] :=
  Icc_prod_Icc _ _ _ _

theorem uIcc_prod_eq (a b : α × β) : [[a, b]] = [[a.1, b.1]] ×ˢ [[a.2, b.2]] := by simp

end Prod

end Lattice

open Interval

section DistribLattice

variable [DistribLattice α] {a a₁ a₂ b b₁ b₂ c x : α}

lemma eq_of_mem_uIcc_of_mem_uIcc (ha : a ∈ [[b, c]]) (hb : b ∈ [[a, c]]) : a = b :=
  eq_of_inf_eq_sup_eq (inf_congr_right ha.1 hb.1) <| sup_congr_right ha.2 hb.2

lemma eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [[a, c]] → c ∈ [[a, b]] → b = c := by
  simpa only [uIcc_comm a] using eq_of_mem_uIcc_of_mem_uIcc

lemma uIcc_injective_right (a : α) : Injective fun b => uIcc b a := fun b c h => by
  rw [Set.ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)

lemma uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a

end DistribLattice

section LinearOrder
variable [LinearOrder α]

section Lattice
variable [Lattice β] {f : α → β} {s : Set α} {a b : α}

lemma _root_.MonotoneOn.mapsTo_uIcc (hf : MonotoneOn f (uIcc a b)) :
    MapsTo f (uIcc a b) (uIcc (f a) (f b)) := by
  rw [uIcc, uIcc, ← hf.map_sup, ← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

lemma _root_.AntitoneOn.mapsTo_uIcc (hf : AntitoneOn f (uIcc a b)) :
    MapsTo f (uIcc a b) (uIcc (f a) (f b)) := by
  rw [uIcc, uIcc, ← hf.map_sup, ← hf.map_inf] <;>
    apply_rules [left_mem_uIcc, right_mem_uIcc, hf.mapsTo_Icc]

lemma _root_.Monotone.mapsTo_uIcc (hf : Monotone f) : MapsTo f (uIcc a b) (uIcc (f a) (f b)) :=
  (hf.monotoneOn _).mapsTo_uIcc

lemma _root_.Antitone.mapsTo_uIcc (hf : Antitone f) : MapsTo f (uIcc a b) (uIcc (f a) (f b)) :=
  (hf.antitoneOn _).mapsTo_uIcc

lemma _root_.MonotoneOn.image_uIcc_subset (hf : MonotoneOn f (uIcc a b)) :
    f '' uIcc a b ⊆ uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset

lemma _root_.AntitoneOn.image_uIcc_subset (hf : AntitoneOn f (uIcc a b)) :
    f '' uIcc a b ⊆ uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset

lemma _root_.Monotone.image_uIcc_subset (hf : Monotone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
  (hf.monotoneOn _).image_uIcc_subset

lemma _root_.Antitone.image_uIcc_subset (hf : Antitone f) : f '' uIcc a b ⊆ uIcc (f a) (f b) :=
  (hf.antitoneOn _).image_uIcc_subset

end Lattice

variable [LinearOrder β] {f : α → β} {s : Set α} {a a₁ a₂ b b₁ b₂ c d x : α}

theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl

lemma uIcc_of_not_le (h : ¬a ≤ b) : [[a, b]] = Icc b a := uIcc_of_gt <| lt_of_not_ge h
lemma uIcc_of_not_ge (h : ¬b ≤ a) : [[a, b]] = Icc a b := uIcc_of_lt <| lt_of_not_ge h

lemma uIcc_eq_union : [[a, b]] = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm] <;> rfl

lemma mem_uIcc : a ∈ [[b, c]] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]

lemma not_mem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [[a, b]] :=
  not_mem_Icc_of_lt <| lt_min_iff.mpr ⟨ha, hb⟩

lemma not_mem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [[a, b]] :=
  not_mem_Icc_of_gt <| max_lt_iff.mpr ⟨ha, hb⟩

lemma uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'

/-- A sort of triangle inequality. -/
lemma uIcc_subset_uIcc_union_uIcc : [[a, c]] ⊆ [[a, b]] ∪ [[b, c]] := fun x => by
  simp only [mem_uIcc, mem_union]
  rcases le_total x b with h2 | h2 <;> tauto

lemma monotone_or_antitone_iff_uIcc :
    Monotone f ∨ Antitone f ↔ ∀ a b c, c ∈ [[a, b]] → f c ∈ [[f a, f b]] := by
  constructor
  · rintro (hf | hf) a b c <;> simp_rw [← Icc_min_max, ← hf.map_min, ← hf.map_max]
    exacts [fun hc => ⟨hf hc.1, hf hc.2⟩, fun hc => ⟨hf hc.2, hf hc.1⟩]
  contrapose!
  rw [not_monotone_not_antitone_iff_exists_le_le]
  rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_lt <| max_lt hfab hfcb⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_lt <| lt_min hfba hfbc⟩

-- Porting note: mathport expands the syntactic sugar `∀ a b c ∈ s` differently than Lean3
lemma monotoneOn_or_antitoneOn_iff_uIcc :
    MonotoneOn f s ∨ AntitoneOn f s ↔
      ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), c ∈ [[a, b]] → f c ∈ [[f a, f b]] := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, monotone_or_antitone_iff_uIcc,
    mem_uIcc]

-- Porting note: what should the naming scheme be here? This is a term, so should be `uIoc`,
-- but we also want to match the `Ioc` convention.
/-- The open-closed uIcc with unordered bounds. -/
def uIoc : α → α → Set α := fun a b => Ioc (min a b) (max a b)

-- Porting note: removed `scoped[uIcc]` temporarily before a workaround is found
-- Below is a capital iota
/-- `Ι a b` denotes the open-closed interval with unordered bounds. Here, `Ι` is a capital iota,
distinguished from a capital `i`. -/
notation "Ι" => Set.uIoc

@[simp] lemma uIoc_of_le (h : a ≤ b) : Ι a b = Ioc a b := by simp [uIoc, h]
@[simp] lemma uIoc_of_ge (h : b ≤ a) : Ι a b = Ioc b a := by simp [uIoc, h]

lemma uIoc_eq_union : Ι a b = Ioc a b ∪ Ioc b a := by
  cases le_total a b <;> simp [uIoc, *]

lemma mem_uIoc : a ∈ Ι b c ↔ b < a ∧ a ≤ c ∨ c < a ∧ a ≤ b := by
  rw [uIoc_eq_union, mem_union, mem_Ioc, mem_Ioc]

lemma not_mem_uIoc : a ∉ Ι b c ↔ a ≤ b ∧ a ≤ c ∨ c < a ∧ b < a := by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, not_lt, ← not_le]
  tauto

@[simp] lemma left_mem_uIoc : a ∈ Ι a b ↔ b < a := by simp [mem_uIoc]
@[simp] lemma right_mem_uIoc : b ∈ Ι a b ↔ a < b := by simp [mem_uIoc]

lemma forall_uIoc_iff {P : α → Prop} :
    (∀ x ∈ Ι a b, P x) ↔ (∀ x ∈ Ioc a b, P x) ∧ ∀ x ∈ Ioc b a, P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, forall_and]

lemma uIoc_subset_uIoc_of_uIcc_subset_uIcc {a b c d : α}
    (h : [[a, b]] ⊆ [[c, d]]) : Ι a b ⊆ Ι c d :=
  Ioc_subset_Ioc (uIcc_subset_uIcc_iff_le.1 h).1 (uIcc_subset_uIcc_iff_le.1 h).2

lemma uIoc_comm (a b : α) : Ι a b = Ι b a := by simp only [uIoc, min_comm a b, max_comm a b]

lemma Ioc_subset_uIoc : Ioc a b ⊆ Ι a b := Ioc_subset_Ioc (min_le_left _ _) (le_max_right _ _)
lemma Ioc_subset_uIoc' : Ioc a b ⊆ Ι b a := Ioc_subset_Ioc (min_le_right _ _) (le_max_left _ _)

lemma uIoc_subset_uIcc : Ι a b ⊆ uIcc a b := Ioc_subset_Icc_self

lemma eq_of_mem_uIoc_of_mem_uIoc : a ∈ Ι b c → b ∈ Ι a c → a = b := by
  simp_rw [mem_uIoc]; rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;> apply le_antisymm <;>
    first |assumption|exact le_of_lt ‹_›|exact le_trans ‹_› (le_of_lt ‹_›)

lemma eq_of_mem_uIoc_of_mem_uIoc' : b ∈ Ι a c → c ∈ Ι a b → b = c := by
  simpa only [uIoc_comm a] using eq_of_mem_uIoc_of_mem_uIoc

lemma eq_of_not_mem_uIoc_of_not_mem_uIoc (ha : a ≤ c) (hb : b ≤ c) :
    a ∉ Ι b c → b ∉ Ι a c → a = b := by
  simp_rw [not_mem_uIoc]
  rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;>
      apply le_antisymm <;>
    first |assumption|exact le_of_lt ‹_›|
    exact absurd hb (not_le_of_lt ‹c < b›)|exact absurd ha (not_le_of_lt ‹c < a›)

lemma uIoc_injective_right (a : α) : Injective fun b => Ι b a := by
  rintro b c h
  rw [Set.ext_iff] at h
  obtain ha | ha := le_or_lt b a
  · have hb := (h b).not
    simp only [ha, left_mem_uIoc, not_lt, true_iff_iff, not_mem_uIoc, ← not_le,
      and_true_iff, not_true, false_and_iff, not_false_iff, true_iff_iff, or_false_iff] at hb
    refine hb.eq_of_not_lt fun hc => ?_
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, iff_not_self, -not_le] using h c
  · refine
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le ?_)
    simpa [ha, ha.not_le, mem_uIoc] using h b

lemma uIoc_injective_left (a : α) : Injective (Ι a) := by
  simpa only [uIoc_comm] using uIoc_injective_right a

end LinearOrder

end Set
