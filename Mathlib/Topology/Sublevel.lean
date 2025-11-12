/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/

import Mathlib.Topology.Semicontinuous

/-! # Sublevel sets

* `IsCompact.elim_finite_subfamily_closedOn`, if a finite
  family of closed sets doesn't meet a compact set,
  then a finite sub-family already doesn't meet that compact set.

* `Set.LeSublevel f b`, the sublevel set of a function `f`, `{ x | f x ≤ b }`

* `Set.LeSublevelOn A f b`, the sublevel set of on `A`, `{ x ∈ A | f x ≤ b }`

* `Set.LeOverlevel f b`, the overlevel set of a function `f`, `{ x | b ≤ f x }`

* `Set.LeOverlevelOn A f b`, the overlevel set of `f` on `A`, `{ x ∈ A | b ≤ f x }`

* `Set.LtSublevel f b`, the strict sublevel set of a function `f`, `{ x | f x < b }`

* `Set.LtSublevelOn A f b`, the strict sublevel set of on `A`, `{ x ∈ A | f x < b }`

* `Set.LtOverlevel f b`, the strict overlevel set of a function `f`, `{ x | b < f x }`

* `Set.LtOverlevelOn A f b`, the strict overlevel set of `f` on `A`, `{ x ∈ A | b < f x }`

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

variable {α β : Type*}

variable (A : Set α) (f : α → β) (b : β)

section LeSublevel

section LE

variable [LE β]

/-- The sublevel sets of a function -/
def LeSublevel : Set α := { x | f x ≤ b }

/-- The sublevel sets of a function -/
def LeSublevelOn : Set α := { x ∈ A | f x ≤ b }

/-- The overlevel sets of `f`. -/
def LeOverlevel : Set α := LeSublevel (β := βᵒᵈ) f b

/-- The overlevel sets of `f` on `s`. -/
def LeOverlevelOn : Set α := LeSublevelOn (β := βᵒᵈ) A f b

variable {A f b}

theorem mem_leSublevel_iff {a : α} :
  a ∈ Set.LeSublevel f b ↔ f a ≤ b := by
  simp [LeSublevel]

theorem mem_leSublevelOn_iff {a : α} :
  a ∈ A.LeSublevelOn f b ↔ a ∈ A ∧ f a ≤ b := by
  simp [LeSublevelOn]

theorem leSublevelOn_eq_inter :
    A.LeSublevelOn f b = A ∩ LeSublevel f b := rfl

theorem leSublevelOn_subset : LeSublevelOn A f b ⊆ A :=
  fun _ hx ↦ hx.1

theorem le_of_mem_leSublevelOn {x : α} (hx : x ∈ LeSublevelOn A f b) :
    f x ≤ b := hx.2

theorem leSublevel_restrict_eq_coe_val_preimage :
    LeSublevel (A.restrict f) b = Subtype.val ⁻¹' (A.LeSublevelOn f b) := by
  ext ⟨x, hx⟩
  simp [mem_leSublevel_iff, mem_leSublevelOn_iff, hx]

theorem mem_leOverlevel_iff {a : α} :
  a ∈ Set.LeOverlevel f b ↔ b ≤ f a := mem_leSublevel_iff

theorem mem_leOverlevelOn_iff {a : α} :
  a ∈ A.LeOverlevelOn f b ↔ a ∈ A ∧ b ≤ f a := mem_leSublevelOn_iff

theorem leOverlevelOn_eq_inter :
    A.LeOverlevelOn f b = A ∩ LeOverlevel f b := leSublevelOn_eq_inter

theorem leOverlevelOn_subset : LeOverlevelOn A f b ⊆ A := leSublevelOn_subset

theorem le_of_mem_leOverlevelOn {x : α} (hx : x ∈ LeOverlevelOn A f b) :
    b ≤ f x := le_of_mem_leSublevelOn hx

theorem leOverlevel_restrict_eq_coe_val_preimage :
    LeOverlevel (A.restrict f) b = Subtype.val ⁻¹' (A.LeOverlevelOn f b) :=
  leSublevel_restrict_eq_coe_val_preimage

end LE

section LT

variable [LT β]

/-- The strict sublevel sets of `f`. -/
def LtSublevel : Set α := { x | f x < b }

/-- The strict sublevel sets of `f` on `A`. -/
def LtSublevelOn : Set α := { x ∈ A | f x < b }

/-- The strict overlevel sets of `f`. -/
def LtOverlevel : Set α := LtSublevel (β := βᵒᵈ) f b

/-- The strict overlevel sets of `f` on `s`. -/
def LtOverlevelOn : Set α := LtSublevelOn (β := βᵒᵈ) A f b

variable {A f b}

theorem mem_ltSublevel_iff {a : α} :
  a ∈ Set.LtSublevel f b ↔ f a < b := by
  simp [LtSublevel]

theorem mem_ltSublevelOn_iff {a : α} :
  a ∈ A.LtSublevelOn f b ↔ a ∈ A ∧ f a < b := by
  simp [LtSublevelOn]

theorem ltSublevelOn_eq_inter :
    A.LtSublevelOn f b = A ∩ LtSublevel f b := rfl

theorem ltSublevelOn_subset : LtSublevelOn A f b ⊆ A :=
  fun _ hx ↦ hx.1

theorem lt_of_mem_leSublevelOn {x : α} (hx : x ∈ LtSublevelOn A f b) :
    f x < b := hx.2

theorem mem_ltOverlevel_iff {a : α} :
  a ∈ Set.LtOverlevel f b ↔ b < f a := mem_ltSublevel_iff

theorem mem_ltOverlevelOn_iff {a : α} :
  a ∈ A.LtOverlevelOn f b ↔ a ∈ A ∧ b < f a := mem_ltSublevelOn_iff

theorem ltOverlevelOn_eq_inter :
    A.LtOverlevelOn f b = A ∩ LtOverlevel f b := ltSublevelOn_eq_inter

theorem ltOverlevelOn_subset : LtOverlevelOn A f b ⊆ A := ltSublevelOn_subset

theorem lt_of_mem_leOverlevelOn {x : α} (hx : x ∈ LtOverlevelOn A f b) :
    b < f x := lt_of_mem_leSublevelOn hx

theorem ltSublevel_restrict_eq_coe_val_preimage :
    LtSublevel (A.restrict f) b = Subtype.val ⁻¹' (A.LtSublevelOn f b) := by
  ext ⟨x, hx⟩
  simp [mem_ltSublevel_iff, mem_ltSublevelOn_iff, hx]

theorem ltOverlevel_restrict_eq_coe_val_preimage :
    LtOverlevel (A.restrict f) b = Subtype.val ⁻¹' (A.LtOverlevelOn f b) :=
  ltSublevel_restrict_eq_coe_val_preimage

end LT

section Preorder

variable [Preorder β]

theorem monotone_leSublevel :
    Monotone (fun b ↦ LeSublevel f b) :=
  fun _ _ hbc _ hb ↦ le_trans hb hbc

theorem monotone_leSublevelOn :
    Monotone (fun b ↦ A.LeSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, le_trans hb hbc⟩

theorem antitone_leOverlevel :
    Antitone (fun b ↦ LeOverlevel f b) :=
fun _ _ hbc _ hb ↦ le_trans hbc hb

theorem antitone_leOverlevelOn :
    Antitone (fun b ↦ A.LeOverlevelOn f b) :=
  fun _ _ hbc a ⟨ha, hb⟩ ↦ ⟨ha, by apply le_trans hbc hb⟩

theorem monotone_ltSublevel :
    Monotone (fun b ↦ LtSublevel f b) :=
  fun _ _ hbc _ hb ↦ lt_of_lt_of_le hb hbc

theorem monotone_ltSublevelOn :
    Monotone (fun b ↦ A.LtSublevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, lt_of_lt_of_le hb hbc⟩

theorem antitone_ltOverlevel :
    Antitone (fun b ↦ LtOverlevel f b) :=
  fun _ _ hbc _ hb ↦ lt_of_le_of_lt hbc hb

theorem antitone_ltOverlevelOn :
    Antitone (fun b ↦ A.LtOverlevelOn f b) :=
  fun _ _ hbc _ ⟨ha, hb⟩ ↦ ⟨ha, by apply lt_of_le_of_lt hbc hb⟩

end Preorder

section LinearOrder

variable [LinearOrder β]

theorem leSublevel_empty_iff :
    LeSublevel f b = ∅ ↔ ∀ x, b < f x := by
  simp [Set.ext_iff, mem_leSublevel_iff]

theorem leSublevelOn_empty_iff :
    LeSublevelOn A f b = ∅ ↔ ∀ x ∈ A, b < f x := by
  simp [LeSublevelOn]

theorem leOverlevel_empty_iff :
    LeOverlevel f b = ∅ ↔ ∀ x, f x < b := by
  simp [Set.ext_iff, mem_leOverlevel_iff]

theorem leOverlevelOn_empty_iff :
    LeOverlevelOn A f b = ∅ ↔ ∀ x ∈ A, f x < b := by
  apply leSublevelOn_empty_iff

theorem inter_leSublevelOn_empty_iff {ι : Type*} {f : ι → α → β} {I : Set ι} (ne_A : A.Nonempty) :
    ⋂ i ∈ I, LeSublevelOn A (f i) b = ∅ ↔ ∀ x ∈ A, ∃ i ∈ I, b < f i x := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_A
  · have : ¬(IsEmpty α) := fun _ ↦ IsEmpty.exists_iff.mp ne_A
    simpa [this] using ne_A
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ A <;> simp [hx, mem_leSublevelOn_iff, mem_iInter]
  exact ne_A

theorem inter_leOverlevelOn_empty_iff {ι : Type*} {f : ι → α → β} {I : Set ι} (ne_A : A.Nonempty) :
    ⋂ i ∈ I, LeOverlevelOn A (f i) b = ∅ ↔ ∀ x ∈ A, ∃ i ∈ I, f i x < b := by
  rcases I.eq_empty_or_nonempty with ⟨rfl⟩ | ne_A
  · have : ¬(IsEmpty α) := fun _ ↦ IsEmpty.exists_iff.mp ne_A
    simpa [this] using ne_A
  rw [Set.ext_iff]
  apply forall_congr'
  intro x
  by_cases hx : x ∈ A <;> simp [hx, mem_leOverlevelOn_iff, mem_iInter]
  exact ne_A

theorem ltSublevel_empty_iff :
    LtSublevel f b = ∅ ↔ ∀ x, b ≤ f x := by
  simp [Set.ext_iff, mem_ltSublevel_iff]

theorem ltSublevelOn_empty_iff :
    LtSublevelOn A f b = ∅ ↔ ∀ x ∈ A, b ≤ f x := by
  simp [LtSublevelOn]

theorem ltOverlevel_empty_iff :
    LtOverlevel f b = ∅ ↔ ∀ x, f x ≤ b := by
  simp [Set.ext_iff, mem_ltOverlevel_iff]

theorem ltOverlevelOn_empty_iff :
    LtOverlevelOn A f b = ∅ ↔ ∀ x ∈ A, f x ≤ b := by
  apply ltSublevelOn_empty_iff

theorem inter_ltSublevelOn_empty_iff {ι : Type*} {f : ι → α → β} {I : Set ι} (ne_A : A.Nonempty) :
    ⋂ i ∈ I, LtSublevelOn A (f i) b = ∅ ↔ ∀ x ∈ A, ∃ i ∈ I, b ≤ f i x := by
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
    (∀ b, IsClosed (LeSublevel f b)) ↔ LowerSemicontinuous f :=
  lowerSemicontinuous_iff_isClosed_preimage.symm

theorem isClosed_val_preimage_leSublevelOn_iff :
    (∀ b, IsClosed (Subtype.val ⁻¹' (LeSublevelOn A f b) : Set A)) ↔ LowerSemicontinuousOn f A := by
  rw [← lowerSemicontinuous_restrict_iff, ← isClosed_leSublevel_iff]
  simp_rw [← leSublevel_restrict_eq_coe_val_preimage]

theorem isClosed_leSublevelOn_iff (hA : IsClosed A) :
    (∀ b, IsClosed (LeSublevelOn A f b)) ↔ LowerSemicontinuousOn f A := by
  simp_rw [leSublevelOn_eq_inter, ← IsClosed.inter_preimage_val_iff,
      Topology.IsInducing.subtypeVal.isClosed_iff]
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  apply forall_congr'
  intro b
  apply exists_congr
  simp only [and_congr_right_iff]
  intro s hs
  rw [Subtype.preimage_val_eq_preimage_val_iff]
  exact eq_comm

theorem isCompact_leSublevelOn (hfA : LowerSemicontinuousOn f A) (kA : IsCompact A) :
    IsCompact (LeSublevelOn A f b) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfA
  obtain ⟨v, hv, hv'⟩ := hfA b
  haveI kA' : CompactSpace A := isCompact_iff_compactSpace.mp kA
  suffices LeSublevelOn A f b = Subtype.val '' (Subtype.val ⁻¹' (LeSublevelOn A f b) : Set A) by
    rw [this, ← Topology.IsInducing.subtypeVal.isCompact_iff]
    apply IsClosed.isCompact
    rw [Topology.IsInducing.subtypeVal.isClosed_iff]
    use v, hv
    rw [Subtype.preimage_coe_eq_preimage_coe_iff, ← hv']
    ext x
    simp [mem_leSublevelOn_iff]
  simp [leSublevelOn_subset]

theorem open_ltSublevel_iff :
    (∀ b, IsOpen (LtSublevel f b)) ↔ UpperSemicontinuous f :=
  upperSemicontinuous_iff_isOpen_preimage.symm

theorem open_val_preimage_ltSublevelOn_iff :
    (∀ b, IsOpen (Subtype.val ⁻¹' (LtSublevelOn A f b) : Set A)) ↔ UpperSemicontinuousOn f A := by
  rw [← upperSemicontinuousOn_iff_restrict, ← open_ltSublevel_iff]
  simp_rw [← ltSublevel_restrict_eq_coe_val_preimage]

theorem open_ltSublevelOn_iff (hA : IsOpen A) :
    (∀ b, IsOpen (LtSublevelOn A f b)) ↔ UpperSemicontinuousOn f A := by
  rw [← open_val_preimage_ltSublevelOn_iff]
  apply forall_congr'
  intro b
  apply hA.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen
  intro a ha
  rw [mem_ltSublevelOn_iff] at ha
  simpa using ha.1

theorem inter_leSublevelOn_empty_iff_exists_finset_inter
    {ι α : Type*} {f : ι → α → β} {A : Set α}
    {I : Set ι} (ne_I : I.Nonempty)
    [TopologicalSpace α] (ks : IsCompact A)
    (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) A) :
    ⋂ i ∈ I, LeSublevelOn A (f i) b = ∅ ↔
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
  have := IsCompact.elim_finite_subfamily_closedOn ks (fun i ↦ LeSublevel (f i) b) (I := I) ?_ ?_
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

end LeSublevel

end Set
