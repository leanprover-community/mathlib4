/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Data.Set.Order
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Interval.Set.Image
import Mathlib.Order.Interval.Set.LinearOrder
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

We use the localized notation `[[a, b]]` for `uIcc a b`. One can open the scope `Interval` to
make the notation available.

-/


open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

section Lattice

variable [Lattice α] [Lattice β] {a a₁ a₂ b b₁ b₂ x : α}

/-- `uIcc a b` is the set of elements lying between `a` and `b`, with `a` and `b` included.
Note that we define it more generally in a lattice as `Set.Icc (a ⊓ b) (a ⊔ b)`. In a product type,
`uIcc` corresponds to the bounding box of the two elements. -/
def uIcc (a b : α) : Set α := Icc (a ⊓ b) (a ⊔ b)

/-- `[[a, b]]` denotes the set of elements lying between `a` and `b`, inclusive. -/
scoped[Interval] notation "[[" a ", " b "]]" => Set.uIcc a b

open Interval

@[simp]
lemma uIcc_toDual (a b : α) : [[toDual a, toDual b]] = ofDual ⁻¹' [[a, b]] :=
  -- Note: needed to hint `(α := α)` after https://github.com/leanprover-community/mathlib4/pull/8386 (elaboration order?)
  Icc_toDual (α := α)

@[deprecated (since := "2025-03-20")]
alias dual_uIcc := uIcc_toDual

@[simp]
theorem uIcc_ofDual (a b : αᵒᵈ) : [[ofDual a, ofDual b]] = toDual ⁻¹' [[a, b]] :=
  Icc_ofDual

@[simp]
lemma uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp]
lemma uIcc_of_ge (h : b ≤ a) : [[a, b]] = Icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]

lemma uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by simp_rw [uIcc, inf_comm, sup_comm]

lemma uIcc_of_lt (h : a < b) : [[a, b]] = Icc a b := uIcc_of_le h.le
lemma uIcc_of_gt (h : b < a) : [[a, b]] = Icc b a := uIcc_of_ge h.le

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

variable [DistribLattice α] {a b c : α}

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
variable [Lattice β] {f : α → β} {a b : α}

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

variable [LinearOrder β] {f : α → β} {s : Set α} {a a₁ a₂ b b₁ b₂ c : α}

theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl

lemma uIcc_of_not_le (h : ¬a ≤ b) : [[a, b]] = Icc b a := uIcc_of_gt <| lt_of_not_ge h
lemma uIcc_of_not_ge (h : ¬b ≤ a) : [[a, b]] = Icc a b := uIcc_of_lt <| lt_of_not_ge h

lemma uIcc_eq_union : [[a, b]] = Icc a b ∪ Icc b a := by rw [Icc_union_Icc', max_comm] <;> rfl

lemma mem_uIcc : a ∈ [[b, c]] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]

lemma notMem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉ [[a, b]] :=
  notMem_Icc_of_lt <| lt_min_iff.mpr ⟨ha, hb⟩

@[deprecated (since := "2025-05-23")] alias not_mem_uIcc_of_lt := notMem_uIcc_of_lt

lemma notMem_uIcc_of_gt (ha : a < c) (hb : b < c) : c ∉ [[a, b]] :=
  notMem_Icc_of_gt <| max_lt_iff.mpr ⟨ha, hb⟩

@[deprecated (since := "2025-05-23")] alias not_mem_uIcc_of_gt := notMem_uIcc_of_gt

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
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.2.not_gt <| max_lt hfab hfcb⟩
  · exact ⟨a, c, b, Icc_subset_uIcc ⟨hab, hbc⟩, fun h => h.1.not_gt <| lt_min hfba hfbc⟩

lemma monotoneOn_or_antitoneOn_iff_uIcc :
    MonotoneOn f s ∨ AntitoneOn f s ↔
      ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), c ∈ [[a, b]] → f c ∈ [[f a, f b]] := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, monotone_or_antitone_iff_uIcc,
    mem_uIcc]

/-- The open-closed uIcc with unordered bounds. -/
def uIoc : α → α → Set α := fun a b => Ioc (min a b) (max a b)

-- Below is a capital iota
/-- `Ι a b` denotes the open-closed interval with unordered bounds. Here, `Ι` is a capital iota,
distinguished from a capital `i`. -/
scoped[Interval] notation "Ι" => Set.uIoc

open scoped Interval

@[simp] lemma uIoc_of_le (h : a ≤ b) : Ι a b = Ioc a b := by simp [uIoc, h]
@[simp] lemma uIoc_of_ge (h : b ≤ a) : Ι a b = Ioc b a := by simp [uIoc, h]

lemma uIoc_eq_union : Ι a b = Ioc a b ∪ Ioc b a := by
  cases le_total a b <;> simp [uIoc, *]

lemma mem_uIoc : a ∈ Ι b c ↔ b < a ∧ a ≤ c ∨ c < a ∧ a ≤ b := by
  rw [uIoc_eq_union, mem_union, mem_Ioc, mem_Ioc]

lemma notMem_uIoc : a ∉ Ι b c ↔ a ≤ b ∧ a ≤ c ∨ c < a ∧ b < a := by
  simp only [uIoc_eq_union, mem_union, mem_Ioc, ← not_le]
  tauto

@[deprecated (since := "2025-05-23")] alias not_mem_uIoc := notMem_uIoc

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
    first | assumption | exact le_of_lt ‹_› | exact le_trans ‹_› (le_of_lt ‹_›)

lemma eq_of_mem_uIoc_of_mem_uIoc' : b ∈ Ι a c → c ∈ Ι a b → b = c := by
  simpa only [uIoc_comm a] using eq_of_mem_uIoc_of_mem_uIoc

lemma eq_of_notMem_uIoc_of_notMem_uIoc (ha : a ≤ c) (hb : b ≤ c) :
    a ∉ Ι b c → b ∉ Ι a c → a = b := by
  simp_rw [notMem_uIoc]
  rintro (⟨_, _⟩ | ⟨_, _⟩) (⟨_, _⟩ | ⟨_, _⟩) <;>
      apply le_antisymm <;>
    first | assumption | exact le_of_lt ‹_› |
    exact absurd hb (not_le_of_gt ‹c < b›) | exact absurd ha (not_le_of_gt ‹c < a›)

@[deprecated (since := "2025-05-23")]
alias eq_of_not_mem_uIoc_of_not_mem_uIoc := eq_of_notMem_uIoc_of_notMem_uIoc

lemma uIoc_injective_right (a : α) : Injective fun b => Ι b a := by
  rintro b c h
  rw [Set.ext_iff] at h
  obtain ha | ha := le_or_gt b a
  · have hb := (h b).not
    simp only [ha, left_mem_uIoc, true_iff, notMem_uIoc, ← not_le,
      and_true, not_true, false_and, not_false_iff, or_false] at hb
    refine hb.eq_of_not_lt fun hc => ?_
    simpa [ha, and_iff_right hc, ← @not_le _ _ _ a, iff_not_self, -not_le] using h c
  · refine
      eq_of_mem_uIoc_of_mem_uIoc ((h _).1 <| left_mem_uIoc.2 ha)
        ((h _).2 <| left_mem_uIoc.2 <| ha.trans_le ?_)
    simpa [ha, ha.not_ge, mem_uIoc] using h b

lemma uIoc_injective_left (a : α) : Injective (Ι a) := by
  simpa only [uIoc_comm] using uIoc_injective_right a

lemma uIoc_union_uIoc (h : b ∈ [[a, c]]) : Ι a b ∪ Ι b c = Ι a c := by
  wlog hac : a ≤ c generalizing a c
  · rw [uIoc_comm, union_comm, uIoc_comm, this _ (le_of_not_ge hac), uIoc_comm]
    rwa [uIcc_comm]
  rw [uIcc_of_le hac] at h
  rw [uIoc_of_le h.1, uIoc_of_le h.2, uIoc_of_le hac, Ioc_union_Ioc_eq_Ioc h.1 h.2]

section uIoo

/-- `uIoo a b` is the set of elements lying between `a` and `b`, with `a` and `b` not included.
Note that we define it more generally in a lattice as `Set.Ioo (a ⊓ b) (a ⊔ b)`. In a product type,
`uIoo` corresponds to the bounding box of the two elements. -/
def uIoo (a b : α) : Set α := Ioo (a ⊓ b) (a ⊔ b)

@[simp]
lemma uIoo_toDual (a b : α) : uIoo (toDual a) (toDual b) = ofDual ⁻¹' uIoo a b :=
  Ioo_toDual (α := α)

@[deprecated (since := "2025-03-20")]
alias dual_uIoo := uIoo_toDual

@[simp]
theorem uIoo_ofDual (a b : αᵒᵈ) : uIoo (ofDual a) (ofDual b) = toDual ⁻¹' uIoo a b :=
  Ioo_ofDual

@[simp] lemma uIoo_of_le (h : a ≤ b) : uIoo a b = Ioo a b := by
  rw [uIoo, inf_eq_left.2 h, sup_eq_right.2 h]

@[simp] lemma uIoo_of_ge (h : b ≤ a) : uIoo a b = Ioo b a := by
  rw [uIoo, inf_eq_right.2 h, sup_eq_left.2 h]

lemma uIoo_comm (a b : α) : uIoo a b = uIoo b a := by simp_rw [uIoo, inf_comm, sup_comm]

lemma uIoo_of_lt (h : a < b) : uIoo a b = Ioo a b := uIoo_of_le h.le

lemma uIoo_of_gt (h : b < a) : uIoo a b = Ioo b a := uIoo_of_ge h.le

lemma uIoo_self : uIoo a a = ∅ := by simp [uIoo]

lemma Ioo_subset_uIoo : Ioo a b ⊆ uIoo a b := Ioo_subset_Ioo inf_le_left le_sup_right

/-- Same as `Ioo_subset_uIoo` but with `Ioo a b` replaced by `Ioo b a`. -/
lemma Ioo_subset_uIoo' : Ioo b a ⊆ uIoo a b := Ioo_subset_Ioo inf_le_right le_sup_left

variable {x : α}

lemma mem_uIoo_of_lt (ha : a < x) (hb : x < b) : x ∈ uIoo a b := Ioo_subset_uIoo ⟨ha, hb⟩

lemma mem_uIoo_of_gt (hb : b < x) (ha : x < a) : x ∈ uIoo a b := Ioo_subset_uIoo' ⟨hb, ha⟩

variable {a b : α}

theorem Ioo_min_max : Ioo (min a b) (max a b) = uIoo a b := rfl

lemma uIoo_of_not_le (h : ¬a ≤ b) : uIoo a b = Ioo b a := uIoo_of_gt <| lt_of_not_ge h

lemma uIoo_of_not_ge (h : ¬b ≤ a) : uIoo a b = Ioo a b := uIoo_of_lt <| lt_of_not_ge h

theorem uIoo_subset_uIcc {α : Type*} [LinearOrder α] (a : α) (b : α) : uIoo a b ⊆ uIcc a b := by
  simp [uIoo, uIcc, Ioo_subset_Icc_self]

end uIoo

end LinearOrder

end Set
