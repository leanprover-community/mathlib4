/-
Copyright (c) 2018 Sébastian Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastian Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.CompileInductive

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete,
rather than complete, lattice. We add a prefix `c` to distinguish them from the versions for
complete lattices, giving names `ciSup_xxx` or `ciInf_xxx`.
-/

public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section

/-!
Extension of `iSup` and `iInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [Preorder α]

@[simp]
theorem WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    ⨅ i, f i = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]

@[norm_cast]
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι → α} (hf : BddBelow (range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f) hf, ← range_comp, Function.comp_def]

@[norm_cast]
theorem WithTop.coe_iSup [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
  rw [iSup, iSup, WithTop.coe_sSup' h, ← range_comp, Function.comp_def]

@[simp]
theorem WithBot.ciSup_empty [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    ⨆ i, f i = ⊥ :=
  WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι → α} (hf : BddAbove (range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  WithTop.coe_iInf (α := αᵒᵈ) hf

theorem WithBot.coe_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty)
    {α : Type*} [CompleteLattice α] (f : ι → α) :
    ⨆ i ∈ s, f i = ⨆ i ∈ s, (f i : WithBot α) := by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr fun i ↦ ?_) <| iSup_le_iff.mpr <| fun _ ↦ iSup_le_iff.mpr <|
      fun hi ↦ WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i ∈ s
  · simpa only [iSup_pos h] using by apply le_biSup _ h
  · simpa only [iSup_neg h] using le_trans (by simp) (le_biSup _ hj)

@[norm_cast]
theorem WithBot.coe_iInf [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  WithTop.coe_iSup (α := αᵒᵈ) _ h

theorem WithBot.coe_biInf {ι : Type*} {s : Set ι} {α : Type*} [CompleteLattice α] (f : ι → α) :
    ⨅ i ∈ s, f i = ⨅ i ∈ s, (f i : WithBot α) := by
  refine le_antisymm (by simpa using fun _ ↦ biInf_le _) <|
    (le_iInf_iff.mpr fun i ↦ ?_).trans_eq (WithBot.coe_iInf _ (OrderBot.bddBelow _)).symm
  by_cases h : i ∈ s
  · simpa only [iInf_pos h] using by apply biInf_le _ h
  · simp [iInf_neg h]

end

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {a b : α}

theorem isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H

theorem isLUB_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H

theorem isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H

theorem isGLB_ciInf_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  isLUB_ciSup_set (α := αᵒᵈ) H Hne

theorem ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

theorem le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range

theorem ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

theorem le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image

theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : ⨆ i, f i = a :=
  H.csSup_eq (range_nonempty f)

theorem IsLUB.ciSup_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    ⨆ i : s, f i = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : ⨅ i, f i = a :=
  H.csInf_eq (range_nonempty f)

theorem IsGLB.ciInf_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    ⨅ i : s, f i = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- The indexed supremum of a function is bounded above by a uniform bound -/
theorem ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (range_nonempty f) (by rwa [forall_mem_range])

/-- The indexed supremum of a function is bounded below by the value taken at one point -/
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)

theorem le_ciSup_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (le_ciSup H c)

/-- If the set of all `f i j` is bounded above, then so is the set of the supremums of every row -/
theorem BddAbove.range_iSup_of_iUnion_range {κ : ι → Sort*} {f : ∀ i, κ i → α}
    (H : BddAbove <| ⋃ i, range (f i)) : BddAbove <| range fun i ↦ ⨆ j, f i j := by
  have ⟨a, h⟩ := H
  refine ⟨a ⊔ (sSup ∅), fun x ⟨i, hx⟩ ↦ hx ▸ ?_⟩
  cases isEmpty_or_nonempty <| κ i
  · exact iSup_of_empty' (f i) ▸ le_sup_right
  exact ciSup_le fun j ↦ le_sup_of_le_left <| h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

theorem le_ciSup₂ {κ : ι → Sort*} {f : ∀ i, κ i → α} (H : BddAbove <| ⋃ i, range (f i)) (i : ι)
    (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_ciSup_of_le H.range_iSup_of_iUnion_range i <|
    le_ciSup (H.mono <| subset_iUnion (range <| f ·) i) j

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
theorem ciSup_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)

theorem le_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
theorem ciInf_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g :=
  ciSup_mono (α := αᵒᵈ) B H

/-- The indexed minimum of a function is bounded below by a uniform lower bound -/
theorem le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  ciSup_le (α := αᵒᵈ) H

/-- The indexed infimum of a function is bounded above by the value taken at one point -/
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  le_ciSup (α := αᵒᵈ) H c

theorem ciInf_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  le_ciSup_of_le (α := αᵒᵈ) H c h

/-- If the set of all `f i j` is bounded below, then so is the set of the infimums of every row -/
theorem BddBelow.range_iInf_of_iUnion_range {κ : ι → Sort*} {f : ∀ i, κ i → α}
    (H : BddBelow <| ⋃ i, range (f i)) : BddBelow <| range fun i ↦ ⨅ j, f i j := by
  have ⟨a, h⟩ := H
  refine ⟨a ⊓ (sInf ∅), fun x ⟨i, hx⟩ ↦ hx ▸ ?_⟩
  cases isEmpty_or_nonempty <| κ i
  · exact iInf_of_isEmpty (f i) ▸ inf_le_right
  exact le_ciInf fun j ↦ inf_le_of_left_le <| h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩

theorem ciInf₂_le {κ : ι → Sort*} {f : ∀ i, κ i → α} (H : BddBelow <| ⋃ i, range (f i)) (i : ι)
    (j : κ i) : ⨅ (i) (j), f i j ≤ f i j :=
  ciInf_le_of_le H.range_iInf_of_iUnion_range i <|
    ciInf_le (H.mono <| subset_iUnion (range <| f ·) i) j

theorem ciInf_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    ⨅ i : s, f i ≤ f c :=
  le_ciSup_set (α := αᵒᵈ) H hc

lemma ciInf_le_ciSup [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) (hf' : BddAbove (range f)) :
    ⨅ i, f i ≤ ⨆ i, f i :=
  (ciInf_le hf (Classical.arbitrary _)).trans <| le_ciSup hf' (Classical.arbitrary _)

lemma ciSup_prod {f : β × γ → α} (hf : BddAbove (Set.range f)) :
    ⨆ p, f p = ⨆ b, ⨆ c, f (b, c) := by
  rcases isEmpty_or_nonempty β
  · simp [iSup_of_empty']
  rcases isEmpty_or_nonempty γ
  · simp [iSup_of_empty']
  have h₁ : BddAbove (Set.range fun b ↦ ⨆ c, f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    refine ⟨B, fun y hy ↦ ?_⟩
    obtain ⟨z, rfl⟩ := Set.mem_range.mp hy
    exact ciSup_le fun c ↦ by grind
  have h₂ b : BddAbove (Set.range fun c ↦ f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    exact ⟨B, by grind⟩
  refine eq_of_forall_ge_iff fun c ↦ ?_
  rw [ciSup_le_iff (bddAbove_iff_subset_Iic.mpr hf), ciSup_le_iff h₁]
  conv_rhs => enter [b]; rw [ciSup_le_iff (h₂ b)]
  simp [Prod.forall]

lemma ciInf_prod {f : β × γ → α} (hf : BddBelow (Set.range f)) :
    ⨅ p, f p = ⨅ b, ⨅ c, f (b, c) :=
  ciSup_prod (α := αᵒᵈ) hf

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : ⨅ i : ι, f i = b :=
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) h₁ h₂

lemma Set.Iic_ciInf [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) :
    Iic (⨅ i, f i) = ⋂ i, Iic (f i) := by
  ext
  simpa using le_ciInf_iff hf

lemma Set.Ici_ciSup [Nonempty ι] {f : ι → α} (hf : BddAbove (range f)) :
    Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  Iic_ciInf (α := αᵒᵈ) hf

theorem ciSup_subtype {p : ι → Prop} {f : Subtype p → α}
    (hf : BddAbove (Set.range f)) (hf' : sSup ∅ ≤ iSup f) :
    iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ := by
  cases isEmpty_or_nonempty (Subtype p)
  · rw [iSup_of_empty', cbiSup_eq_of_forall_not fun i h ↦ isEmptyElim (⟨i, h⟩ : Subtype p)]
  have : Nonempty ι := (nonempty_subtype.mp ‹_›).nonempty
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩) i := by simp [h]
    rw [this]
    refine le_ciSup (f := (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩)) ?_ i
    simp_rw [ciSup_eq_ite]
    refine (hf.union (bddAbove_singleton (a := sSup ∅))).mono ?_
    grind
  · refine ciSup_le fun i ↦ ?_
    simp_rw [ciSup_eq_ite]
    split_ifs
    · exact le_ciSup hf ?_
    · exact hf'

theorem ciInf_subtype {p : ι → Prop} {f : Subtype p → α}
    (hf : BddBelow (Set.range f)) (hf' : iInf f ≤ sInf ∅) :
    iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  ciSup_subtype (α := αᵒᵈ) hf hf'

theorem cbiSup_eq_ciSup_subtype {p : ι → Prop} {f : ∀ i, p i → α}
    (hf : BddAbove (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : sSup ∅ ≤ ⨆ (i : Subtype p), f i i.prop) :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciSup_subtype' := cbiSup_eq_ciSup_subtype

theorem cbiInf_eq_ciInf_subtype {p : ι → Prop} {f : ∀ i, p i → α}
    (hf : BddBelow (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : ⨅ (i : Subtype p), f i i.prop ≤ sInf ∅) :
    ⨅ (i) (h), f i h = ⨅ x : Subtype p, f x x.property :=
  (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciInf_subtype' := cbiInf_eq_ciInf_subtype

theorem ciSup_subtype_fun {ι} {s : Set ι} {f : ι → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  ciSup_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciSup_subtype'' := ciSup_subtype_fun

theorem ciInf_subtype_fun {ι} {s : Set ι} {f : ι → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    ⨅ i : s, f i = ⨅ (t : ι) (_ : t ∈ s), f t :=
  ciInf_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciInf_subtype'' := ciInf_subtype_fun

theorem csSup_image {s : Set β} {f : β → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← ciSup_subtype_fun hf hf', iSup, Set.image_eq_range]

theorem csInf_image {s : Set β} {f : β → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    sInf (f '' s) = ⨅ a ∈ s, f a :=
  csSup_image (α := αᵒᵈ) hf hf'

theorem cbiSup_id {s : Set α} (hs : BddAbove s) (h : sSup ∅ ≤ sSup s) : ⨆ i ∈ s, i = sSup s := by
  rw [← csSup_image (Subtype.range_coe ▸ hs), Set.image_id']
  · convert h
    rw [← sSup_range, Subtype.range_coe]

theorem cbiInf_id {s : Set α} (hs : BddBelow s) (h : sInf s ≤ sInf ∅) : ⨅ i ∈ s, i = sInf s := by
  rw [← csInf_image (Subtype.range_coe ▸ hs), Set.image_id']
  · convert h
    rw [← sInf_range, Subtype.range_coe]

lemma ciSup_image {ι ι' : Type*} {s : Set ι} {f : ι → ι'} {g : ι' → α}
    (hf : BddAbove (Set.range fun i : s ↦ g (f i))) (hg' : sSup ∅ ≤ ⨆ i : s, g (f i)) :
    ⨆ i ∈ (f '' s), g i = ⨆ x ∈ s, g (f x) := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · rw [Set.image_empty, cbiSup_empty, cbiSup_empty]
  have hg : BddAbove (Set.range fun i : f '' s ↦ g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ ≤ ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.Nonempty.to_subtype hs
    refine ciSup_le ?_
    intro ⟨i, h⟩
    obtain ⟨t, ht⟩ : ∃ t : f '' s, g t = g (f (Subtype.mk i h)) := by
      have : f i ∈ f '' s := Set.mem_image_of_mem _ h
      exact ⟨⟨f i, this⟩, by simp⟩
    rw [← ht]
    refine le_ciSup_set ?_ t.prop
    simpa [bddAbove_def] using hf
  rw [← csSup_image hg hf', ← csSup_image hf hg', ← Set.image_comp, comp_def]

lemma ciInf_image {ι ι' : Type*} {s : Set ι} {f : ι → ι'} {g : ι' → α}
    (hf : BddBelow (Set.range fun i : s ↦ g (f i))) (hg' : ⨅ i : s, g (f i) ≤ sInf ∅) :
    ⨅ i ∈ (f '' s), g i = ⨅ x ∈ s, g (f x) :=
  ciSup_image (α := αᵒᵈ) hf hg'

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {a b : α}

/-- Indexed version of `exists_lt_of_lt_csSup`.
When `b < iSup f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι → α} (h : b < iSup f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

/-- Indexed version of `exists_lt_of_csInf_lt`.
When `iInf f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α} (h : iInf f < a) : ∃ i, f i < a :=
  exists_lt_of_lt_ciSup (α := αᵒᵈ) h

theorem lt_ciSup_iff [Nonempty ι] {f : ι → α} (hb : BddAbove (range f)) :
    a < iSup f ↔ ∃ i, a < f i := by
  simpa only [mem_range, exists_exists_eq_and] using lt_csSup_iff hb (range_nonempty _)

theorem ciInf_lt_iff [Nonempty ι] {f : ι → α} (hb : BddBelow (range f)) :
    iInf f < a ↔ ∃ i, f i < a := by
  simpa only [mem_range, exists_exists_eq_and] using csInf_lt_iff hb (range_nonempty _)

theorem cbiSup_of_not_bddAbove {p : ι → Prop} {f : ∀ i, p i → α}
    (h : ¬BddAbove (range fun i : Subtype p ↦ f i i.prop)) :
    ⨆ (i : ι), ⨆ (h : p i), f i h = sSup ∅ :=
  ciSup_of_not_bddAbove fun ⟨u, hu⟩ ↦ h ⟨u, fun _ ⟨x, hx⟩ ↦ hx ▸ hu ⟨x, ciSup_pos x.prop⟩⟩

theorem cbiInf_of_not_bddBelow {p : ι → Prop} {f : ∀ i, p i → α}
    (h : ¬BddBelow (range fun i : Subtype p ↦ f i i.prop)) :
    ⨅ (i : ι), ⨅ (h : p i), f i h = sInf ∅ :=
  ciInf_of_not_bddBelow fun ⟨u, hu⟩ ↦ h ⟨u, fun _ ⟨x, hx⟩ ↦ hx ▸ hu ⟨x, ciInf_pos x.prop⟩⟩

theorem cbiSup_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sSup ∅ := by
  rcases le_or_gt (sSup ∅) (iSup f) with le | gt
  · rw [max_eq_left le]
    by_cases bdd : BddAbove (range f)
    · rw [← ciSup_subtype bdd le]
    · rw [ciSup_of_not_bddAbove bdd, cbiSup_of_not_bddAbove bdd]
  have ⟨i, hi⟩ := not_forall.mp hp
  have : Nonempty ι := ⟨i⟩
  have bdd : BddAbove (range f) := not_not.mp fun h ↦ gt.ne (ciSup_of_not_bddAbove h)
  rw [max_eq_right gt.le]
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j ↦ ?_) ?_
  · by_cases hj : p j
    · exact ((ciSup_pos hj).trans_le (le_ciSup bdd ⟨j, hj⟩)).trans gt.le
    · exact (ciSup_neg hj).le
  · exact fun w hw ↦ ⟨i, hw.trans_eq (ciSup_neg hi).symm⟩

theorem cbiInf_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f ⊓ sInf ∅ :=
  cbiSup_eq_of_not_forall (α := αᵒᵈ) hp

theorem ciInf_eq_bot_of_bot_mem [OrderBot α] {f : ι → α} (hs : ⊥ ∈ range f) : iInf f = ⊥ :=
  csInf_eq_bot_of_bot_mem hs

theorem ciSup_eq_top_of_top_mem [OrderTop α] {f : ι → α} (hs : ⊤ ∈ range f) : iSup f = ⊤ :=
  csSup_eq_top_of_top_mem hs

@[deprecated (since := "2026-04-05")] alias ciInf_eq_top_of_top_mem := ciSup_eq_top_of_top_mem

variable [WellFoundedLT α]

theorem ciInf_mem [Nonempty ι] (f : ι → α) : iInf f ∈ range f :=
  csInf_mem (range_nonempty f)

lemma ciInf_eq_iff [Nonempty ι] (f : ι → α) (n : α) :
    ⨅ i, (f i) = n ↔ (∃ i, f i = n) ∧ ∀ i, n ≤ f i := by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · rintro rfl
    exact ⟨ciInf_mem f, ciInf_le (OrderBot.bddBelow ..)⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (ciInf_le (OrderBot.bddBelow ..) _) (le_ciInf h)

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {a : α}

@[simp]
theorem ciSup_of_empty [IsEmpty ι] (f : ι → α) : ⨆ i, f i = ⊥ := by
  rw [iSup_of_empty', csSup_empty]

theorem ciSup_false (f : False → α) : ⨆ i, f i = ⊥ :=
  ciSup_of_empty f

theorem le_ciSup_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [iSup, h, le_csSup_iff', upperBounds]

theorem le_ciInf_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  le_ciInf_iff (OrderBot.bddBelow _)

theorem ciInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i := ciInf_le (OrderBot.bddBelow _) _

lemma ciInf_le_of_le' (c : ι) : f c ≤ a → iInf f ≤ a := ciInf_le_of_le (OrderBot.bddBelow _) _

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `ciSup_le_iff`. -/
theorem ciSup_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  (csSup_le_iff' h).trans forall_mem_range

theorem ciSup_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  csSup_le' <| forall_mem_range.2 h

@[simp]
theorem ciSup_bot : ⨆ _ : ι, (⊥ : α) = ⊥ := le_bot_iff.mp (ciSup_le' fun _ ↦ bot_le)

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `lt_ciSup_iff`. -/
theorem lt_ciSup_iff' {f : ι → α} (h : BddAbove (range f)) : a < iSup f ↔ ∃ i, a < f i := by
  simpa only [not_le, not_forall] using (ciSup_le_iff' h).not

theorem exists_lt_of_lt_ciSup' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact ciSup_le' h

theorem ciSup_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  ciSup_le' fun i => Exists.elim (h i) (le_ciSup_of_le hg)

lemma ciSup_or' (p q : Prop) (f : p ∨ q → α) :
    ⨆ (h : p ∨ q), f h = (⨆ h : p, f (.inl h)) ⊔ ⨆ h : q, f (.inr h) := by
  by_cases hp : p <;>
  by_cases hq : q <;>
  simp [hp, hq]

end ConditionallyCompleteLinearOrderBot

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne

theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_csSup hne hbdd, sSup_image']

theorem l_ciSup (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']

theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf

theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd

theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd

theorem u_ciInf (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf

theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne

end GaloisConnection

namespace OrderIso

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd

theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd

theorem map_ciSup (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf

theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne

theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd

theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd

theorem map_ciInf (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf

theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrderBot β]

@[simp]
lemma map_ciSup' (e : α ≃o β) (f : ι → α) : e (⨆ i, f i) = ⨆ i, e (f i) := by
  cases isEmpty_or_nonempty ι
  · simp [map_bot]
  by_cases hf : BddAbove (range f)
  · exact e.map_ciSup hf
  · have hfe : ¬ BddAbove (range fun i ↦ e (f i)) := by
      simpa [Set.Nonempty, BddAbove, upperBounds, e.surjective.forall] using hf
    simp [map_bot, hf, hfe]

end ConditionallyCompleteLinearOrderBot
end OrderIso

section WithTopBot

namespace WithTop
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α}

lemma iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f) := by
  rw [iSup_eq_top, not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩

lemma iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f) :=
  lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

lemma iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι := by simp [isEmpty_iff]

lemma iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι := by
  rw [lt_top_iff_ne_top, Ne, iInf_coe_eq_top, not_isEmpty_iff]

end WithTop

end WithTopBot
