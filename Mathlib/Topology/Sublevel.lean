/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/

import Mathlib.Topology.Semicontinuous

/-! # Sublevel sets

* `Set.leSublevel f b`, the sublevel set of a function `f`, `{ x | f x ≤ b }`

* `Set.leSublevelOn A f b`, the sublevel set of on `A`, `{ x ∈ A | f x ≤ b }`

* `Set.leOverlevel f b`, the overlevel set of a function `f`, `{ x | b ≤ f x }`

* `Set.leOverlevelOn A f b`, the overlevel set of `f` on `A`, `{ x ∈ A | b ≤ f x }`

* `Set.ltSublevel f b`, the strict sublevel set of a function `f`, `{ x | f x < b }`

* `Set.ltSublevelOn A f b`, the strict sublevel set of on `A`, `{ x ∈ A | f x < b }`

* `Set.ltOverlevel f b`, the strict overlevel set of a function `f`, `{ x | b < f x }`

* `Set.ltOverlevelOn A f b`, the strict overlevel set of `f` on `A`, `{ x ∈ A | b < f x }`

* `Set.isClosed_leSublevel_iff`: `f` is lower semicontinuous
  if and only if all sublevels are closed.

* `Set.open_ltSublevel_iff`: `f` is upper semicontinuous
  if and only if all strict sublevels are open.

* `Set.isCompact_leSublevelOn`, the sublevels of a lower semicontinuous function
  on a compact set are compact.

* `Set.inter_leSublevelOn_empty_iff_exists_finset_inter`,
  an intersection of sublevels of a lower semicontinuous function
  on a compact set is empty if and only if
  a finite sub-intersection is already empty.

-/

open Function

namespace Set

open scoped Set.Notation

variable {α β : Type*}

variable (A : Set α) (f : α → β) (b : β)

section leSublevel

section LE

variable [LE β]

/-- The sublevel sets of a function -/
def leSublevel : Set α := { x | f x ≤ b }

/-- The sublevel sets of a function -/
def leSublevelOn : Set α := { x ∈ A | f x ≤ b }

/-- The overlevel sets of `f`. -/
def leOverlevel : Set α := leSublevel (β := βᵒᵈ) f b

/-- The overlevel sets of `f` on `s`. -/
def leOverlevelOn : Set α := leSublevelOn (β := βᵒᵈ) A f b

variable {A f b}

theorem mem_leSublevel_iff {a : α} :
    a ∈ Set.leSublevel f b ↔ f a ≤ b := by
  simp [leSublevel]

theorem mem_leSublevelOn_iff {a : α} :
    a ∈ A.leSublevelOn f b ↔ a ∈ A ∧ f a ≤ b := by
  simp [leSublevelOn]

theorem leSublevelOn_eq_inter :
    A.leSublevelOn f b = A ∩ leSublevel f b := rfl

theorem leSublevelOn_subset :
    leSublevelOn A f b ⊆ A := fun _ hx ↦ hx.1

theorem le_of_mem_leSublevelOn {x : α} (hx : x ∈ leSublevelOn A f b) :
    f x ≤ b := hx.2

theorem leSublevel_restrict_eq_coe_val_preimage :
    leSublevel (A.restrict f) b = A ↓∩ A.leSublevelOn f b := by
  ext ⟨x, hx⟩
  simp [mem_leSublevel_iff, mem_leSublevelOn_iff, hx]

theorem mem_leOverlevel_iff {a : α} :
    a ∈ Set.leOverlevel f b ↔ b ≤ f a := mem_leSublevel_iff

theorem mem_leOverlevelOn_iff {a : α} :
    a ∈ A.leOverlevelOn f b ↔ a ∈ A ∧ b ≤ f a := mem_leSublevelOn_iff

theorem leOverlevelOn_eq_inter :
    A.leOverlevelOn f b = A ∩ leOverlevel f b := leSublevelOn_eq_inter

theorem leOverlevelOn_subset :
    leOverlevelOn A f b ⊆ A := leSublevelOn_subset

theorem le_of_mem_leOverlevelOn {x : α} (hx : x ∈ leOverlevelOn A f b) :
    b ≤ f x := le_of_mem_leSublevelOn hx

theorem leOverlevel_restrict_eq_coe_val_preimage :
    leOverlevel (A.restrict f) b = A ↓∩ A.leOverlevelOn f b :=
  leSublevel_restrict_eq_coe_val_preimage

end LE

section LT

variable [LT β]

/-- The strict sublevel sets of `f`. -/
def ltSublevel : Set α := { x | f x < b }

/-- The strict sublevel sets of `f` on `A`. -/
def ltSublevelOn : Set α := { x ∈ A | f x < b }

/-- The strict overlevel sets of `f`. -/
def ltOverlevel : Set α := ltSublevel (β := βᵒᵈ) f b

/-- The strict overlevel sets of `f` on `s`. -/
def ltOverlevelOn : Set α := ltSublevelOn (β := βᵒᵈ) A f b

variable {A f b}

theorem mem_ltSublevel_iff {a : α} :
    a ∈ ltSublevel f b ↔ f a < b := by
  simp [ltSublevel]

theorem mem_ltSublevelOn_iff {a : α} :
    a ∈ A.ltSublevelOn f b ↔ a ∈ A ∧ f a < b := by
  simp [ltSublevelOn]

theorem ltSublevelOn_eq_inter :
    A.ltSublevelOn f b = A ∩ ltSublevel f b := rfl

theorem ltSublevelOn_subset :
    ltSublevelOn A f b ⊆ A :=
  fun _ hx ↦ hx.1

theorem lt_of_mem_leSublevelOn {x : α} (hx : x ∈ ltSublevelOn A f b) :
    f x < b := hx.2

theorem mem_ltOverlevel_iff {a : α} :
    a ∈ ltOverlevel f b ↔ b < f a := mem_ltSublevel_iff

theorem mem_ltOverlevelOn_iff {a : α} :
    a ∈ A.ltOverlevelOn f b ↔ a ∈ A ∧ b < f a := mem_ltSublevelOn_iff

theorem ltOverlevelOn_eq_inter :
    A.ltOverlevelOn f b = A ∩ ltOverlevel f b := ltSublevelOn_eq_inter

theorem ltOverlevelOn_subset :
    ltOverlevelOn A f b ⊆ A := ltSublevelOn_subset

theorem lt_of_mem_leOverlevelOn {x : α} (hx : x ∈ ltOverlevelOn A f b) :
    b < f x := lt_of_mem_leSublevelOn hx

theorem ltSublevel_restrict_eq_coe_val_preimage :
    ltSublevel (A.restrict f) b = A ↓∩ A.ltSublevelOn f b := by
  ext ⟨x, hx⟩
  simp [mem_ltSublevel_iff, mem_ltSublevelOn_iff, hx]

theorem ltOverlevel_restrict_eq_coe_val_preimage :
    ltOverlevel (A.restrict f) b = A ↓∩ A.ltOverlevelOn f b :=
  ltSublevel_restrict_eq_coe_val_preimage

end LT

section Preorder

variable [Preorder β]

theorem monotone_leSublevel :
    Monotone (fun b ↦ leSublevel f b) :=
  fun _ _ hbc _ hb ↦ le_trans hb hbc

theorem monotone_leSublevelOn :
    Monotone (fun b ↦ A.leSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, le_trans hb hbc⟩

theorem antitone_leOverlevel :
    Antitone (fun b ↦ leOverlevel f b) :=
  fun _ _ hbc _ hb ↦ le_trans hbc hb

theorem antitone_leOverlevelOn :
    Antitone (fun b ↦ A.leOverlevelOn f b) :=
  fun _ _ hbc a ⟨ha, hb⟩ ↦ ⟨ha, by apply le_trans hbc hb⟩

theorem monotone_ltSublevel :
    Monotone (fun b ↦ ltSublevel f b) :=
  fun _ _ hbc _ hb ↦ lt_of_lt_of_le hb hbc

theorem monotone_ltSublevelOn :
    Monotone (fun b ↦ A.ltSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, lt_of_lt_of_le hb hbc⟩

theorem antitone_ltOverlevel :
    Antitone (fun b ↦ ltOverlevel f b) :=
  fun _ _ hbc _ hb ↦ lt_of_le_of_lt hbc hb

theorem antitone_ltOverlevelOn :
    Antitone (fun b ↦ A.ltOverlevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, by apply lt_of_le_of_lt hbc hb⟩

end Preorder

section LinearOrder

variable [LinearOrder β]

theorem leSublevel_empty_iff :
    leSublevel f b = ∅ ↔ ∀ x, b < f x := by
  simp [Set.ext_iff, mem_leSublevel_iff]

theorem leSublevelOn_empty_iff :
    leSublevelOn A f b = ∅ ↔ ∀ x ∈ A, b < f x := by
  simp [leSublevelOn]

theorem leOverlevel_empty_iff :
    leOverlevel f b = ∅ ↔ ∀ x, f x < b := by
  simp [Set.ext_iff, mem_leOverlevel_iff]

theorem leOverlevelOn_empty_iff :
    leOverlevelOn A f b = ∅ ↔ ∀ x ∈ A, f x < b := by
  apply leSublevelOn_empty_iff

theorem inter_leSublevelOn_empty_iff {ι : Type*} {f : ι → α → β} {I : Set ι} (ne_A : A.Nonempty) :
    ⋂ i ∈ I, leSublevelOn A (f i) b = ∅ ↔ ∀ x ∈ A, ∃ i ∈ I, b < f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_A
  · have : ¬(IsEmpty α) := fun _ ↦ IsEmpty.exists_iff.mp ne_A
    simpa [this] using ne_A
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ A <;> simp [hx, mem_leSublevelOn_iff, mem_iInter]
  exact ne_A

theorem inter_leOverlevelOn_empty_iff {ι : Type*} {f : ι → α → β} {I : Set ι} (ne_A : A.Nonempty) :
    ⋂ i ∈ I, leOverlevelOn A (f i) b = ∅ ↔ ∀ x ∈ A, ∃ i ∈ I, f i x < b := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_A
  · have : ¬(IsEmpty α) := fun _ ↦ IsEmpty.exists_iff.mp ne_A
    simpa [this] using ne_A
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ A <;> simp [hx, mem_leOverlevelOn_iff, mem_iInter]
  exact ne_A

theorem ltSublevel_empty_iff :
    ltSublevel f b = ∅ ↔ ∀ x, b ≤ f x := by
  simp [Set.ext_iff, mem_ltSublevel_iff]

theorem ltSublevelOn_empty_iff :
    ltSublevelOn A f b = ∅ ↔ ∀ x ∈ A, b ≤ f x := by
  simp [ltSublevelOn]

theorem ltOverlevel_empty_iff :
    ltOverlevel f b = ∅ ↔ ∀ x, f x ≤ b := by
  simp [Set.ext_iff, mem_ltOverlevel_iff]

theorem ltOverlevelOn_empty_iff :
    ltOverlevelOn A f b = ∅ ↔ ∀ x ∈ A, f x ≤ b := by
  apply ltSublevelOn_empty_iff

theorem inter_ltSublevelOn_empty_iff {ι : Type*} {f : ι → α → β} {I : Set ι} (ne_A : A.Nonempty) :
    ⋂ i ∈ I, ltSublevelOn A (f i) b = ∅ ↔ ∀ x ∈ A, ∃ i ∈ I, b ≤ f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_I
  · have : ¬(IsEmpty α) := fun _ ↦ IsEmpty.exists_iff.mp ne_A
    simpa [this] using ne_A
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ A <;> simp [hx, mem_ltSublevelOn_iff, mem_iInter]
  exact ne_I

variable [TopologicalSpace α]

theorem isClosed_leSublevel_iff :
    (∀ b, IsClosed (leSublevel f b)) ↔ LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.symm

theorem isClosed_val_preimage_leSublevelOn_iff :
    (∀ b, IsClosed (A ↓∩ leSublevelOn A f b)) ↔ LowerSemicontinuousOn f A := by
  rw [← lowerSemicontinuous_restrict_iff, ← isClosed_leSublevel_iff]
  simp_rw [← leSublevel_restrict_eq_coe_val_preimage]

theorem isClosed_leSublevelOn_iff (hA : IsClosed A) :
    (∀ b, IsClosed (leSublevelOn A f b)) ↔ LowerSemicontinuousOn f A := by
  simp_rw [leSublevelOn_eq_inter, ← IsClosed.inter_preimage_val_iff,
    Topology.IsInducing.subtypeVal.isClosed_iff]
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  congr! with b s hs
  rw [Subtype.preimage_val_eq_preimage_val_iff]
  exact eq_comm

theorem isCompact_leSublevelOn (hfA : LowerSemicontinuousOn f A) (kA : IsCompact A) :
    IsCompact (leSublevelOn A f b) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfA
  obtain ⟨v, hv, hv'⟩ := hfA b
  haveI kA' : CompactSpace A := isCompact_iff_compactSpace.mp kA
  suffices leSublevelOn A f b = Subtype.val '' (A ↓∩ leSublevelOn A f b) by
    rw [this, ← Topology.IsInducing.subtypeVal.isCompact_iff]
    apply IsClosed.isCompact
    rw [Topology.IsInducing.subtypeVal.isClosed_iff]
    use v, hv
    rw [Subtype.preimage_coe_eq_preimage_coe_iff, ← hv']
    ext x
    simp [mem_leSublevelOn_iff]
  simp [leSublevelOn_subset]

theorem open_ltSublevel_iff :
    (∀ b, IsOpen (ltSublevel f b)) ↔ UpperSemicontinuous f :=
  upperSemicontinuous_iff_isOpen_preimage.symm

theorem open_val_preimage_ltSublevelOn_iff :
    (∀ b, IsOpen (A ↓∩ ltSublevelOn A f b)) ↔ UpperSemicontinuousOn f A := by
  rw [← upperSemicontinuousOn_iff_restrict, ← open_ltSublevel_iff]
  simp_rw [← ltSublevel_restrict_eq_coe_val_preimage]

theorem open_ltSublevelOn_iff (hA : IsOpen A) :
    (∀ b, IsOpen (ltSublevelOn A f b)) ↔ UpperSemicontinuousOn f A := by
  rw [← open_val_preimage_ltSublevelOn_iff]
  congr! with b
  apply hA.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen
  intro a ha
  rw [mem_ltSublevelOn_iff] at ha
  simpa using ha.1

theorem inter_leSublevelOn_empty_iff_exists_finset_inter
    {ι α : Type*} {f : ι → α → β} {A : Set α}
    {I : Set ι} (ne_I : I.Nonempty)
    [TopologicalSpace α] (ks : IsCompact A)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) A) :
    ⋂ i ∈ I, leSublevelOn A (f i) b = ∅ ↔
      ∃ u : Finset I, ∀ x ∈ A, ∃ i ∈ u, b < f i x := by
  symm
  constructor
  · rintro ⟨u, hu⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro x
    by_cases hx : x ∈ A
    · simp [mem_leSublevelOn_iff, hx]
      obtain ⟨i, hi, hi'⟩ := hu x hx
      use i.val, i.prop
    · simpa [mem_leSublevelOn_iff, hx] using ne_I
  intro H
  have := IsCompact.elim_finite_subfamily_closedOn ks (fun i ↦ leSublevel (f i) b) (I := I) ?_ ?_
  · obtain ⟨u, hu⟩ := this
    use u
    intro x hx
    rw [Set.eq_empty_iff_forall_notMem] at hu
    specialize hu x
    simp only [iInter_coe_set, mem_inter_iff, hx, mem_iInter, true_and, not_forall] at hu
    obtain ⟨i, hi, hi', hi''⟩ := hu
    use ⟨i, hi⟩, hi'
    simpa [mem_leSublevel_iff] using hi''
  · intro i hi
    specialize hfi i hi
    rw [← isClosed_val_preimage_leSublevelOn_iff] at hfi
    convert hfi b using 1
    ext ⟨x, hx⟩
    simp [hx, mem_leSublevel_iff, mem_leSublevelOn_iff]
  · rwa [← Set.inter_biInter ne_I]

end LinearOrder

end leSublevel

end Set
