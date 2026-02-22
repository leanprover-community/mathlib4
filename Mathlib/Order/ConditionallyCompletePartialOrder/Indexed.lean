/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete
partial order, as opposed to a conditionally complete lattice.

## TODO

+ Use `@[to_dual]` in the `GaloisConnection` and `OrderIso` sections.

-/

public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section ConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α] {a b : α}

@[to_dual]
theorem Directed.isLUB_ciSup [Nonempty ι] {f : ι → α} (hd : Directed (· ≤ ·) f)
    (H : BddAbove (range f)) : IsLUB (range f) (⨆ i, f i) :=
  hd.directedOn_range.isLUB_csSup (range_nonempty f) H

@[to_dual]
theorem DirectedOn.isLUB_ciSup_set {f : β → α} {s : Set β} (hd : DirectedOn (· ≤ ·) (f '' s))
    (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact hd.isLUB_csSup (Hne.image _) H

@[to_dual Directed.le_ciInf_iff]
theorem Directed.ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α}
    (hd : Directed (· ≤ ·) f) (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| hd.isLUB_ciSup hf).trans forall_mem_range

@[to_dual DirectedOn.le_ciInf_set_iff]
theorem DirectedOn.ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hd : DirectedOn (· ≤ ·) (f '' s)) (hf : BddAbove (f '' s)) :
    ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| hd.isLUB_ciSup_set hf hs).trans forall_mem_image

@[to_dual Directed.ciInf_le_of_le]
theorem Directed.le_ciSup_of_le {f : ι → α} (hd : Directed (· ≤ ·) f)
    (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (hd.le_ciSup H c)

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[to_dual (attr := gcongr low)
/-- The indexed infimum of two functions are comparable if the functions are pointwise
comparable -/]
theorem Directed.ciSup_mono {f g : ι → α} (hdf : Directed (· ≤ ·) f)
    (hdg : Directed (· ≤ ·) g) (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact hdf.ciSup_le fun x ↦ hdg.le_ciSup_of_le B x (H x)

@[to_dual DirectedOn.ciInf_set_le]
theorem DirectedOn.le_ciSup_set {f : β → α} {s : Set β} (hd : DirectedOn (· ≤ ·) (f '' s))
    (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) : f c ≤ ⨆ i : s, f i :=
  (hd.le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

@[to_dual (attr := simp)]
theorem ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a := by
  rw [iSup, range_const, csSup_singleton]

@[to_dual (attr := simp)]
theorem ciSup_unique [Unique ι] {s : ι → α} : ⨆ i, s i = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[to_dual]
theorem ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨆ i, s i = s i :=
  @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[to_dual]
theorem ciSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp := by
  simp [hp]

@[to_dual]
lemma ciSup_neg {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨆ (h : p), f h = sSup (∅ : Set α) := by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

@[to_dual]
lemma ciSup_eq_ite {p : Prop} [Decidable p] {f : p → α} :
    (⨆ h : p, f h) = if h : p then f h else sSup (∅ : Set α) := by
  by_cases H : p <;> simp [ciSup_neg, H]

@[to_dual]
theorem cbiSup_eq_of_forall {p : ι → Prop} {f : Subtype p → α} (hp : ∀ i, p i) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f := by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp
  · rintro - ⟨i, rfl⟩
    simp

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual Directed.ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/]
theorem Directed.ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α}
    (hd : Directed (· ≤ ·) f) (h₁ : ∀ i, f i ≤ b) (h₂ : ∀ w, w < b → ∃ i, w < f i) :
    ⨆ i : ι, f i = b :=
  hd.directedOn_range.csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f)
    (forall_mem_range.mpr h₁) fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- **Nested intervals lemma**: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.ciSup_mem_iInter_Icc_of_antitone [Preorder β] [IsDirectedOrder β]
    {f g : β → α} (hf : Monotone f) (hg : Antitone g) (h : f ≤ g) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine mem_iInter.2 fun n => ?_
  haveI : Nonempty β := ⟨n⟩
  have h₁ : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  have h₂ : Directed (· ≤ ·) f := hf.directed_le
  exact ⟨h₂.le_ciSup ⟨g <| n, forall_mem_range.2 h₁⟩ _, h₂.ciSup_le h₁⟩

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem ciSup_mem_iInter_Icc_of_antitone_Icc [Preorder β] [IsDirectedOrder β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

@[to_dual]
lemma Directed.Ici_ciSup [Nonempty ι] {f : ι → α} (hd : Directed (· ≤ ·) f)
    (hf : BddAbove (range f)) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) := by
  ext
  simpa using hd.ciSup_le_iff hf

@[to_dual]
theorem ciSup_Iic [Preorder β] {f : β → α} (a : β) (hf : Monotone f) :
    ⨆ x : Iic a, f x = f a := by
  have hd : Directed (· ≤ ·) (fun x : Iic a ↦ f x) := fun x y ↦ ⟨⟨a, le_refl a⟩, ⟨hf x.2, hf y.2⟩⟩
  have H : BddAbove (range fun x : Iic a ↦ f x) := ⟨f a, fun _ ↦ by aesop⟩
  apply (hd.le_ciSup H (⟨a, le_refl a⟩ : Iic a)).antisymm'
  rw [hd.ciSup_le_iff H]
  rintro ⟨a, h⟩
  exact hf h

end ConditionallyCompletePartialOrderSup

lemma Directed.ciInf_le_ciSup [ConditionallyCompletePartialOrder α] [Nonempty ι] {f : ι → α}
    (hd : Directed (· ≥ ·) f) (hf : BddBelow (range f))
    (hd' : Directed (· ≤ ·) f) (hf' : BddAbove (range f)) :
    ⨅ i, f i ≤ ⨆ i, f i :=
  (hd.ciInf_le hf (Classical.arbitrary _)).trans <| hd'.le_ciSup hf' (Classical.arbitrary _)

namespace GaloisConnection

section Sup

variable [ConditionallyCompletePartialOrderSup α] [ConditionallyCompletePartialOrderSup β]
    [Nonempty ι] {l : α → β} {u : β → α}

theorem l_csSup_of_directedOn' (gc : GaloisConnection l u) {s : Set α}
    (hd : DirectedOn (· ≤ ·) s) (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) :=
  gc.isLUB_l_image (hd.isLUB_csSup hne hbdd) |>.unique <|
    (hd.mono_comp gc.monotone_l).isLUB_csSup (hne.image l) (gc.monotone_l.map_bddAbove hbdd)

theorem l_csSup_of_directedOn (gc : GaloisConnection l u) {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x := by
  simpa only [← comp_def, ← sSup_range, range_comp, Subtype.range_coe_subtype, setOf_mem_eq]
    using gc.l_csSup_of_directedOn' hd hne hbdd

theorem l_ciSup_of_directed (gc : GaloisConnection l u) {f : ι → α} (hd : Directed (· ≤ ·) f)
    (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i) := by
  rw [iSup, gc.l_csSup_of_directedOn hd.directedOn_range (range_nonempty _) hf, iSup_range']

theorem l_ciSup_set_of_directedOn (gc : GaloisConnection l u) {s : Set γ} {f : γ → α}
    (hd : DirectedOn (· ≤ ·) (f '' s)) (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  refine gc.l_ciSup_of_directed ?_ hf
  simpa [directedOn_range, ← comp_def, range_comp]

end Sup

section Inf

variable [ConditionallyCompletePartialOrderInf α] [ConditionallyCompletePartialOrderInf β]
    [Nonempty ι] {l : α → β} {u : β → α}

theorem u_csInf_of_directedOn (gc : GaloisConnection l u) {s : Set β} (hd : DirectedOn (· ≥ ·) s)
    (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup_of_directedOn hd hne hbdd

theorem u_csInf_of_directedOn' (gc : GaloisConnection l u) {s : Set β} (hd : DirectedOn (· ≥ ·) s)
    (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup_of_directedOn' hd hne hbdd

theorem u_ciInf_of_directed (gc : GaloisConnection l u) {f : ι → β} (hd : Directed (· ≥ ·) f)
    (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup_of_directed hd hf

theorem u_ciInf_set_of_directedOn (gc : GaloisConnection l u) {s : Set γ} {f : γ → β}
    (hd : DirectedOn (· ≥ ·) (f '' s)) (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set_of_directedOn hd hf hne

end Inf

end GaloisConnection

namespace OrderIso

section Sup

variable [ConditionallyCompletePartialOrderSup α] [ConditionallyCompletePartialOrderSup β]
  [Nonempty ι]

-- these need to have `directed` in their names.
theorem map_csSup_of_directedOn (e : α ≃o β) {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup_of_directedOn hd hne hbdd

theorem map_csSup_of_directedOn' (e : α ≃o β) {s : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup_of_directedOn' hd hne hbdd

theorem map_ciSup_of_directed (e : α ≃o β) {f : ι → α} (hd : Directed (· ≤ ·) f)
    (hf : BddAbove (range f)) : e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup_of_directed hd hf

theorem map_ciSup_set_of_directedOn (e : α ≃o β) {s : Set γ} {f : γ → α}
    (hd : DirectedOn (· ≤ ·) (f '' s)) (hf : BddAbove (f '' s)) (hne : s.Nonempty) :
    e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set_of_directedOn hd hf hne

end Sup

section Inf

variable [ConditionallyCompletePartialOrderInf α] [ConditionallyCompletePartialOrderInf β]
  [Nonempty ι]

theorem map_csInf_of_directedOn (e : α ≃o β) {s : Set α} (hd : DirectedOn (· ≥ ·) s)
    (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup_of_directedOn hd hne hbdd

theorem map_csInf_of_directedOn' (e : α ≃o β) {s : Set α} (hd : DirectedOn (· ≥ ·) s)
    (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup_of_directedOn' hd hne hbdd

theorem map_ciInf_of_directed (e : α ≃o β) {f : ι → α} (hd : Directed (· ≥ ·) f)
    (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup_of_directed hd hf

theorem map_ciInf_set_of_directedOn (e : α ≃o β) {s : Set γ} {f : γ → α}
    (hd : DirectedOn (· ≥ ·) (f '' s)) (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set_of_directedOn hd hf hne

end Inf

end OrderIso
