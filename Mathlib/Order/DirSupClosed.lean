/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.UpperLower.Basic

import Mathlib.Data.Set.Lattice

/-!
# Sets closed under directed suprema

We say that a set `s` is closed under directed suprema whenever it contains all least upper bounds
for nonempty, directed subsets. Conversely, a set `s` is inaccessible by directed suprema whenever
its complement is closed under directed suprema. Equivalently, if the least upper bound of a
nonempty directed set `t` is contained in `s`, then `t` and `s` must have nonempty intersection.

## Main definitions

- `DirSupClosed`: sets closed under directed suprema.
- `DirSupInacc`: sets inaccessible by directed suprema.
-/

@[expose] public section

variable {α : Type*} {s t : Set α} {D D₁ D₂ : Set (Set α)}

open Set

section Preorder
variable [Preorder α]

/-- A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInaccOn` set. -/
def DirSupClosedOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A predicate for a set which is inaccessible by directed suprema of nonempty sets in `D`.
This is the complement of a `DirSupClosedOn` set. -/
def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

/-- A predicate for a set which is closed under directed suprema of nonempty sets.
This is the complement of a `DirSupInacc` set. -/
def DirSupClosed (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s

/-- A predicate for a set which is inaccessible by directed suprema of nonempty sets.
This is the complement of a `DirSupClosed` set. -/
def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

@[simp] lemma dirSupClosedOn_univ : DirSupClosedOn univ s ↔ DirSupClosed s := by
  simp [DirSupClosedOn, DirSupClosed]

@[simp] lemma dirSupInaccOn_univ : DirSupInaccOn univ s ↔ DirSupInacc s := by
  simp [DirSupInaccOn, DirSupInacc]

alias ⟨DirSupClosed.of_univ, DirSupClosed.to_univ⟩ := dirSupClosedOn_univ
alias ⟨DirSupInacc.of_univ, DirSupInacc.to_univ⟩ := dirSupInaccOn_univ

@[simp] lemma DirSupClosed.dirSupClosedOn : DirSupClosed s → DirSupClosedOn D s := @fun h _ _ ↦ @h _
@[simp] lemma DirSupInacc.dirSupInaccOn : DirSupInacc s → DirSupInaccOn D s := @fun h _ _ ↦ @h _

@[gcongr]
lemma DirSupClosedOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupClosedOn D₂ s) : DirSupClosedOn D₁ s :=
  fun _ a ↦ hf (hD a)

@[gcongr]
lemma DirSupInaccOn.mono (hD : D₁ ⊆ D₂) (hf : DirSupInaccOn D₂ s) : DirSupInaccOn D₁ s :=
  fun _ a ↦ hf (hD a)

@[simp]
lemma dirSupClosedOn_compl : DirSupClosedOn D sᶜ ↔ DirSupInaccOn D s := by
  simp_rw [DirSupClosedOn, DirSupInaccOn, ← not_disjoint_iff_nonempty_inter]
  grind

@[simp]
lemma dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s := by
  rw [← dirSupClosedOn_univ, dirSupClosedOn_compl, dirSupInaccOn_univ]

@[simp]
lemma dirSupInaccOn_compl : DirSupInaccOn D sᶜ ↔ DirSupClosedOn D s := by
  rw [← dirSupClosedOn_compl, compl_compl]

@[simp]
lemma dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s := by
  rw [← dirSupClosed_compl, compl_compl]

alias ⟨DirSupClosedOn.of_compl, DirSupInaccOn.compl⟩ := dirSupClosedOn_compl
alias ⟨DirSupInaccOn.of_compl, DirSupClosedOn.compl⟩ := dirSupInaccOn_compl
alias ⟨DirSupClosed.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl
alias ⟨DirSupInacc.of_compl, DirSupClosed.compl⟩ := dirSupInacc_compl

@[simp] theorem DirSupClosed.empty : DirSupClosed (∅ : Set α) := by simp [DirSupClosed]
@[simp] theorem DirSupInacc.empty : DirSupInacc (∅ : Set α) := by simp [DirSupInacc]
@[simp] theorem DirSupClosedOn.empty : DirSupClosedOn D ∅ := DirSupClosed.empty.dirSupClosedOn
@[simp] theorem DirSupInaccOn.empty : DirSupInaccOn D ∅ := DirSupInacc.empty.dirSupInaccOn

@[simp] theorem DirSupClosed.univ : DirSupClosed (univ : Set α) := by simp [DirSupClosed]
@[simp] theorem DirSupInacc.univ : DirSupInacc (univ : Set α) := by simp [← compl_empty]
@[simp] theorem DirSupClosedOn.univ : DirSupClosedOn D univ := DirSupClosed.univ.dirSupClosedOn
@[simp] theorem DirSupInaccOn.univ : DirSupInaccOn D univ := DirSupInacc.univ.dirSupInaccOn

theorem DirSupClosedOn.sInter {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupClosedOn D x) :
    DirSupClosedOn D (⋂₀ s) :=
  fun _d hD hds hd hd' _a ha t ht ↦ hs t ht hD (hds.trans fun _x hx ↦ hx _ ht) hd hd' ha

theorem DirSupClosed.sInter {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupClosed x) :
    DirSupClosed (⋂₀ s) :=
  .of_univ (.sInter fun x hx ↦ (hs x hx).to_univ)

theorem DirSupInaccOn.sUnion {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupInaccOn D x) :
    DirSupInaccOn D (⋃₀ s) := by
  rw [← dirSupClosedOn_compl, Set.compl_sUnion]
  apply DirSupClosedOn.sInter
  rintro x ⟨x, hx, rfl⟩
  exact (hs x hx).compl

theorem DirSupInacc.sUnion {s : Set (Set α)} (hs : ∀ x ∈ s, DirSupInacc x) :
    DirSupInacc (⋃₀ s) :=
  .of_univ (.sUnion fun x hx ↦ (hs x hx).to_univ)

lemma DirSupClosedOn.inter (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) :
    DirSupClosedOn D (s ∩ t) := by
  rw [← sInter_pair]
  refine .sInter ?_
  simpa [hs]

lemma DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∩ t) := by
  simpa using hs.to_univ.inter ht.to_univ

lemma DirSupInaccOn.union (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) :
    DirSupInaccOn D (s ∪ t) := by
  rw [← dirSupClosedOn_compl, compl_union]; exact hs.compl.inter ht.compl

lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∪ t) := by
  rw [← dirSupClosed_compl, compl_union]; exact hs.compl.inter ht.compl

theorem directedOn_union (h : DirectedOn (· ≤ ·) (s ∪ t)) :
    DirectedOn (· ≤ ·) s ∨ DirectedOn (· ≤ ·) t := by
  simp_rw [DirectedOn]
  by_contra!
  obtain ⟨⟨a, ha, b, hb, hab⟩, ⟨c, hc, d, hd, hcd⟩⟩ := this
  obtain ⟨x, hx, hax, hbx⟩ := h a (.inl ha) b (.inl hb)
  obtain ⟨y, hy, hcy, hdy⟩ := h c (.inr hc) d (.inr hd)
  obtain ⟨z, hz | hz, hxz, hyz⟩ := h x hx y hy
  · exact hab z hz (hax.trans hxz) (hbx.trans hxz)
  · exact hcd z hz (hcy.trans hyz) (hdy.trans hyz)

theorem directedOn_union' (hn : (s ∪ t).Nonempty) (h : DirectedOn (· ≤ ·) (s ∪ t)) :
    DirectedOn (· ≤ ·) s ∧ s.Nonempty ∨ DirectedOn (· ≤ ·) t ∧ t.Nonempty := by
  obtain h | h := directedOn_union h
  · obtain rfl | hs := s.eq_empty_or_nonempty
    · aesop
    · exact .inl ⟨h, hs⟩
  · obtain rfl | ht := t.eq_empty_or_nonempty
    · aesop
    · exact .inr ⟨h, ht⟩

theorem DirSupClosedOn.union (hDL : IsLowerSet D)
    (hs : DirSupClosedOn D s) (ht : DirSupClosedOn D t) : DirSupClosedOn D (s ∪ t) := by
  intro d hD hdu hd₀ hd₁ a ha
  have hdst : d ∩ s ∪ d ∩ t = d := by grind
  rw [← hdst] at hd₀ hd₁
  wlog h : DirectedOn (· ≤ ·) (d ∩ s) ∧ (d ∩ s).Nonempty
  · rw [union_comm] at hdu hd₀ hd₁ hdst ⊢
    exact this hDL ht hs hD hdu hd₀ hd₁ ha hdst <| (directedOn_union' hd₀ hd₁).resolve_right h
  · obtain ⟨hds, hn⟩ := h
    by_cases had : a ∈ lowerBounds (upperBounds (d ∩ s))
    · exact .inl <| hs (hDL inter_subset_left hD) inter_subset_right hn hds
        ⟨fun b hb ↦ ha.1 hb.1, had⟩
    · simp only [lowerBounds, mem_setOf_eq, not_forall] at had
      obtain ⟨b, hb, hb'⟩ := had
      have key : {x ∈ d | ¬ x ≤ b} ⊆ d ∩ t :=
        fun a ⟨had, hab⟩ ↦ ⟨had, (hdu had).resolve_left fun has ↦ hab <| hb ⟨had, has⟩⟩
      obtain ⟨w, hw⟩ : {x ∈ d | ¬ x ≤ b}.Nonempty := by
        simp_rw [Set.Nonempty, mem_setOf]
        by_contra! ht
        apply hb' (ha.2 <| hdst ▸ _)
        rintro c (hc | hc)
        · exact hb hc
        · exact ht _ hc.1
      refine Or.inr <| ht (hDL inter_subset_left hD) (key.trans inter_subset_right)
        ⟨w, hw⟩ (fun x hx y hy ↦ ?_) ?_
      · obtain ⟨z, hz, hz'⟩ := hd₁ _ (.inr (key hx)) _ (.inr (key hy))
        rw [hdst] at hz
        exact ⟨z, ⟨⟨hz, mt hz'.1.trans hx.2⟩, hz'⟩⟩
      · refine ⟨fun x hx ↦ ha.1 hx.1, fun x hx ↦ ha.2 fun y hy ↦ ?_⟩
        by_cases hyb : y ≤ b
        · obtain ⟨z, hz, hxz, hyz⟩ := hd₁ _ (hdst ▸ hy) _ (.inr (key hw))
          exact hxz.trans (hx ⟨hdst ▸ hz, fun hzb ↦ hw.2 (hyz.trans hzb)⟩)
        · exact hx ⟨hy, hyb⟩

theorem DirSupInaccOn.inter (hDL : IsLowerSet D)
    (hs : DirSupInaccOn D s) (ht : DirSupInaccOn D t) : DirSupInaccOn D (s ∩ t) := by
  rw [← dirSupClosedOn_compl, compl_inter]; exact hs.compl.union hDL ht.compl

theorem DirSupClosed.union (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∪ t) :=
  .of_univ (hs.to_univ.union isLowerSet_univ ht.to_univ)

theorem DirSupInacc.inter (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∩ t) :=
  .of_univ (hs.to_univ.inter isLowerSet_univ ht.to_univ)

theorem dirSupInaccOn_of_inter_subset
    (h : ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s) : DirSupInaccOn D s := by
  intro d hd₀ hd₁ hd₂ a hda hd₃
  obtain ⟨b, hbd, hb⟩ := h hd₀ hd₁ hd₂ hda hd₃
  exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

theorem dirSupInacc_of_inter_subset
    (h : ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s) : DirSupInacc s :=
  .of_univ (dirSupInaccOn_of_inter_subset (by simpa))

/-- If `d` is a set whose LUB is contained in a `DirSupInaccOn` set, then there's an entire tail of
the set contained. -/
theorem dirSupInaccOn_iff_inter_subset (hDL : IsLowerSet D) :
    DirSupInaccOn D s ↔ ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s where
  mpr := dirSupInaccOn_of_inter_subset
  mp h t hD ht₀ ht₁ a ha has := by
    by_contra! H
    have H : ∀ b : t, ∃ c, b.1 ≤ c ∧ c ∈ t ∧ c ∉ s := by simpa [not_subset, and_assoc] using H
    choose f hf using H
    have := ht₀.to_subtype
    have hft : range f ⊆ t := by grind
    apply (h (hDL hft hD) (range_nonempty f) _ _ has).ne_empty
    · aesop
    · intro a ha b hb
      obtain ⟨c, hc, _, _⟩ := ht₁ _ (hft ha) _ (hft hb)
      have := hf ⟨c, hc⟩
      grind
    · exact ⟨upperBounds_mono_set hft ha.1,
        fun b hb ↦ ha.2 fun c hc ↦ (hf ⟨c, hc⟩).1.trans (hb <| by simp)⟩

/-- If `d` is a set whose LUB is contained in a `DirSupInaccOn` set, then there's an entire tail of
the set contained. -/
theorem dirSupInacc_iff_inter_subset :
    DirSupInacc s ↔ ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ ⦃a : α⦄, IsLUB d a → a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s := by
  simpa using dirSupInaccOn_iff_inter_subset isLowerSet_univ

lemma IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s :=
  fun _d hds ⟨_b, hb⟩ _ _a ha ↦ hs (ha.1 hb) <| hds hb

lemma IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s :=
  hs.compl.dirSupClosed.of_compl

lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) := fun _d h _ _ _a ha ↦ (isLUB_le_iff ha).2 h

end Preorder

section CompleteLattice
variable [CompleteLattice α]

lemma dirSupClosedOn_iff_forall_sSup : DirSupClosedOn D s ↔
    ∀ ⦃d⦄, d ∈ D → d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosedOn, isLUB_iff_sSup_eq]

lemma dirSupInaccOn_iff_forall_sSup : DirSupInaccOn D s ↔
    ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInaccOn, isLUB_iff_sSup_eq]

lemma dirSupClosed_iff_forall_sSup : DirSupClosed s ↔
    ∀ ⦃d⦄, d ⊆ s → d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s := by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

lemma dirSupInacc_iff_forall_sSup : DirSupInacc s ↔
    ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

end CompleteLattice
