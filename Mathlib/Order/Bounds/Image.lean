/-
Copyright (c) 2017 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Paul Lezeau
-/
import Mathlib.Data.Set.NAry
import Mathlib.Order.Bounds.Basic

/-!

# Images of upper/lower bounds under monotone functions

In this file we prove various results about the behaviour of bounds under monotone/antitone maps.
-/

open Function Set

open OrderDual (toDual ofDual)

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace MonotoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} {a : α}

theorem mem_upperBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) (Has : a ∈ upperBounds s)
    (Hat : a ∈ t) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Hst H) Hat (Has H)

theorem mem_upperBounds_image_self (Hf : MonotoneOn f t) :
    a ∈ upperBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.mem_upperBounds_image subset_rfl

theorem mem_lowerBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) (Has : a ∈ lowerBounds s)
    (Hat : a ∈ t) : f a ∈ lowerBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf Hat (Hst H) (Has H)

theorem mem_lowerBounds_image_self (Hf : MonotoneOn f t) :
    a ∈ lowerBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.mem_lowerBounds_image subset_rfl

theorem image_upperBounds_subset_upperBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image Hst ha.1 ha.2

theorem image_lowerBounds_subset_lowerBounds_image (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    f '' (lowerBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upperBounds_subset_upperBounds_image Hst

/-- The image under a monotone function on a set `t` of a subset which has an upper bound in `t`
  is bounded above. -/
theorem map_bddAbove (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    (upperBounds s ∩ t).Nonempty → BddAbove (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_upperBounds_image Hst hs ht⟩

/-- The image under a monotone function on a set `t` of a subset which has a lower bound in `t`
  is bounded below. -/
theorem map_bddBelow (Hf : MonotoneOn f t) (Hst : s ⊆ t) :
    (lowerBounds s ∩ t).Nonempty → BddBelow (f '' s) := fun ⟨C, hs, ht⟩ =>
  ⟨f C, Hf.mem_lowerBounds_image Hst hs ht⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_isLeast (Hf : MonotoneOn f t) (Ha : IsLeast t a) : IsLeast (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image_self Ha.2 Ha.1⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_isGreatest (Hf : MonotoneOn f t) (Ha : IsGreatest t a) : IsGreatest (f '' t) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upperBounds_image_self Ha.2 Ha.1⟩

end MonotoneOn

namespace AntitoneOn

variable [Preorder α] [Preorder β] {f : α → β} {s t : Set α} {a : α}

theorem mem_upperBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) (Has : a ∈ lowerBounds s) :
    a ∈ t → f a ∈ upperBounds (f '' s) :=
  Hf.dual_right.mem_lowerBounds_image Hst Has

theorem mem_upperBounds_image_self (Hf : AntitoneOn f t) :
    a ∈ lowerBounds t → a ∈ t → f a ∈ upperBounds (f '' t) :=
  Hf.dual_right.mem_lowerBounds_image_self

theorem mem_lowerBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    a ∈ upperBounds s → a ∈ t → f a ∈ lowerBounds (f '' s) :=
  Hf.dual_right.mem_upperBounds_image Hst

theorem mem_lowerBounds_image_self (Hf : AntitoneOn f t) :
    a ∈ upperBounds t → a ∈ t → f a ∈ lowerBounds (f '' t) :=
  Hf.dual_right.mem_upperBounds_image_self

theorem image_lowerBounds_subset_upperBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    f '' (lowerBounds s ∩ t) ⊆ upperBounds (f '' s) :=
  Hf.dual_right.image_lowerBounds_subset_lowerBounds_image Hst

theorem image_upperBounds_subset_lowerBounds_image (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    f '' (upperBounds s ∩ t) ⊆ lowerBounds (f '' s) :=
  Hf.dual_right.image_upperBounds_subset_upperBounds_image Hst

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bddAbove (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    (upperBounds s ∩ t).Nonempty → BddBelow (f '' s) :=
  Hf.dual_right.map_bddAbove Hst

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bddBelow (Hf : AntitoneOn f t) (Hst : s ⊆ t) :
    (lowerBounds s ∩ t).Nonempty → BddAbove (f '' s) :=
  Hf.dual_right.map_bddBelow Hst

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_isGreatest (Hf : AntitoneOn f t) : IsGreatest t a → IsLeast (f '' t) (f a) :=
  Hf.dual_right.map_isGreatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_isLeast (Hf : AntitoneOn f t) : IsLeast t a → IsGreatest (f '' t) (f a) :=
  Hf.dual_right.map_isLeast

end AntitoneOn

namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β} (Hf : Monotone f) {a : α} {s : Set α}

include Hf

theorem mem_upperBounds_image (Ha : a ∈ upperBounds s) : f a ∈ upperBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)

theorem mem_lowerBounds_image (Ha : a ∈ lowerBounds s) : f a ∈ lowerBounds (f '' s) :=
  forall_mem_image.2 fun _ H => Hf (Ha H)

theorem image_upperBounds_subset_upperBounds_image :
    f '' upperBounds s ⊆ upperBounds (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Hf.mem_upperBounds_image ha

theorem image_lowerBounds_subset_lowerBounds_image : f '' lowerBounds s ⊆ lowerBounds (f '' s) :=
  Hf.dual.image_upperBounds_subset_upperBounds_image

/-- The image under a monotone function of a set which is bounded above is bounded above. See also
`BddAbove.image2`. -/
theorem map_bddAbove : BddAbove s → BddAbove (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_upperBounds_image hC⟩

/-- The image under a monotone function of a set which is bounded below is bounded below. See also
`BddBelow.image2`. -/
theorem map_bddBelow : BddBelow s → BddBelow (f '' s)
  | ⟨C, hC⟩ => ⟨f C, Hf.mem_lowerBounds_image hC⟩

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_lowerBounds_image Ha.2⟩

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_isGreatest (Ha : IsGreatest s a) : IsGreatest (f '' s) (f a) :=
  ⟨mem_image_of_mem _ Ha.1, Hf.mem_upperBounds_image Ha.2⟩

end Monotone

namespace Antitone

variable [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f) {a : α} {s : Set α}

include hf

theorem mem_upperBounds_image : a ∈ lowerBounds s → f a ∈ upperBounds (f '' s) :=
  hf.dual_right.mem_lowerBounds_image

theorem mem_lowerBounds_image : a ∈ upperBounds s → f a ∈ lowerBounds (f '' s) :=
  hf.dual_right.mem_upperBounds_image

theorem image_lowerBounds_subset_upperBounds_image : f '' lowerBounds s ⊆ upperBounds (f '' s) :=
  hf.dual_right.image_lowerBounds_subset_lowerBounds_image

theorem image_upperBounds_subset_lowerBounds_image : f '' upperBounds s ⊆ lowerBounds (f '' s) :=
  hf.dual_right.image_upperBounds_subset_upperBounds_image

/-- The image under an antitone function of a set which is bounded above is bounded below. -/
theorem map_bddAbove : BddAbove s → BddBelow (f '' s) :=
  hf.dual_right.map_bddAbove

/-- The image under an antitone function of a set which is bounded below is bounded above. -/
theorem map_bddBelow : BddBelow s → BddAbove (f '' s) :=
  hf.dual_right.map_bddBelow

/-- An antitone map sends a greatest element of a set to a least element of its image. -/
theorem map_isGreatest : IsGreatest s a → IsLeast (f '' s) (f a) :=
  hf.dual_right.map_isGreatest

/-- An antitone map sends a least element of a set to a greatest element of its image. -/
theorem map_isLeast : IsLeast s a → IsGreatest (f '' s) (f a) :=
  hf.dual_right.map_isLeast

end Antitone

section StrictMono

variable [LinearOrder α] [Preorder β] {f : α → β} {a : α} {s : Set α}

lemma StrictMono.mem_upperBounds_image (hf : StrictMono f) :
    f a ∈ upperBounds (f '' s) ↔ a ∈ upperBounds s := by simp [upperBounds, hf.le_iff_le]

lemma StrictMono.mem_lowerBounds_image (hf : StrictMono f) :
    f a ∈ lowerBounds (f '' s) ↔ a ∈ lowerBounds s := by simp [lowerBounds, hf.le_iff_le]

lemma StrictMono.map_isLeast (hf : StrictMono f) : IsLeast (f '' s) (f a) ↔ IsLeast s a := by
  simp [IsLeast, hf.injective.eq_iff, hf.mem_lowerBounds_image]

lemma StrictMono.map_isGreatest (hf : StrictMono f) :
    IsGreatest (f '' s) (f a) ↔ IsGreatest s a := by
  simp [IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

end StrictMono

section StrictAnti

variable [LinearOrder α] [Preorder β] {f : α → β} {a : α} {s : Set α}

lemma StrictAnti.mem_upperBounds_image (hf : StrictAnti f) :
    f a ∈ upperBounds (f '' s) ↔ a ∈ lowerBounds s := by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

lemma StrictAnti.mem_lowerBounds_image (hf : StrictAnti f) :
    f a ∈ lowerBounds (f '' s) ↔ a ∈ upperBounds s := by
  simp [upperBounds, lowerBounds, hf.le_iff_ge]

lemma StrictAnti.map_isLeast (hf : StrictAnti f) : IsLeast (f '' s) (f a) ↔ IsGreatest s a := by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_lowerBounds_image]

lemma StrictAnti.map_isGreatest (hf : StrictAnti f) : IsGreatest (f '' s) (f a) ↔ IsLeast s a := by
  simp [IsLeast, IsGreatest, hf.injective.eq_iff, hf.mem_upperBounds_image]

end StrictAnti

section Image2

variable [Preorder α] [Preorder β] [Preorder γ] {f : α → β → γ} {s : Set α} {t : Set β} {a : α}
  {b : β}

section MonotoneMonotone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

theorem mem_upperBounds_image2 (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2 (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    f a b ∈ lowerBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upperBounds_upperBounds_subset :
    image2 f (upperBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_upperBounds_image2 h₀ h₁ ha hb

theorem image2_lowerBounds_lowerBounds_subset :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦ mem_lowerBounds_image2 h₀ h₁ ha hb

/-- See also `Monotone.map_bddAbove`. -/
protected theorem BddAbove.image2 :
    BddAbove s → BddAbove t → BddAbove (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2 h₀ h₁ ha hb⟩

/-- See also `Monotone.map_bddBelow`. -/
protected theorem BddBelow.image2 :
    BddBelow s → BddBelow t → BddBelow (image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2 h₀ h₁ ha hb⟩

protected theorem IsGreatest.image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsGreatest (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2 h₀ h₁ ha.2 hb.2⟩

protected theorem IsLeast.image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsLeast (image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lowerBounds_image2 h₀ h₁ ha.2 hb.2⟩

end MonotoneMonotone

section MonotoneAntitone

variable (h₀ : ∀ b, Monotone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upperBounds_lowerBounds_subset_upperBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb

theorem image2_lowerBounds_upperBounds_subset_lowerBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha hb

theorem BddAbove.bddAbove_image2_of_bddBelow :
    BddAbove s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

theorem BddBelow.bddBelow_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

theorem IsGreatest.isGreatest_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

theorem IsLeast.isLeast_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

end MonotoneAntitone

section AntitoneAntitone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Antitone (f a))

include h₀ h₁

theorem mem_upperBounds_image2_of_mem_lowerBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2_of_mem_upperBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_upperBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (lowerBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb

theorem image2_lowerBounds_lowerBounds_subset_lowerBounds_image2 :
    image2 f (upperBounds s) (upperBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha hb

theorem BddBelow.image2_bddAbove : BddBelow s → BddBelow t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha hb⟩

theorem BddAbove.image2_bddBelow : BddAbove s → BddAbove t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha hb⟩

theorem IsLeast.isGreatest_image2 (ha : IsLeast s a) (hb : IsLeast t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_upperBounds_image2_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

theorem IsGreatest.isLeast_image2 (ha : IsGreatest s a) (hb : IsGreatest t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1, mem_lowerBounds_image2_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneAntitone

section AntitoneMonotone

variable (h₀ : ∀ b, Antitone (swap f b)) (h₁ : ∀ a, Monotone (f a))

include h₀ h₁

theorem mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds t) : f a b ∈ upperBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds (ha : a ∈ upperBounds s)
    (hb : b ∈ lowerBounds t) : f a b ∈ lowerBounds (image2 f s t) :=
  forall_mem_image2.2 fun _ hx _ hy => (h₀ _ <| ha hx).trans <| h₁ _ <| hb hy

theorem image2_lowerBounds_upperBounds_subset_upperBounds_image2 :
    image2 f (lowerBounds s) (upperBounds t) ⊆ upperBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb

theorem image2_upperBounds_lowerBounds_subset_lowerBounds_image2 :
    image2 f (upperBounds s) (lowerBounds t) ⊆ lowerBounds (image2 f s t) :=
  image2_subset_iff.2 fun _ ha _ hb ↦
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha hb

theorem BddBelow.bddAbove_image2_of_bddAbove :
    BddBelow s → BddAbove t → BddAbove (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha hb⟩

theorem BddAbove.bddBelow_image2_of_bddAbove :
    BddAbove s → BddBelow t → BddBelow (Set.image2 f s t) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨f a b, mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha hb⟩

theorem IsLeast.isGreatest_image2_of_isGreatest (ha : IsLeast s a) (hb : IsGreatest t b) :
    IsGreatest (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_upperBounds_image2_of_mem_upperBounds_of_mem_upperBounds h₀ h₁ ha.2 hb.2⟩

theorem IsGreatest.isLeast_image2_of_isLeast (ha : IsGreatest s a) (hb : IsLeast t b) :
    IsLeast (Set.image2 f s t) (f a b) :=
  ⟨mem_image2_of_mem ha.1 hb.1,
    mem_lowerBounds_image2_of_mem_lowerBounds_of_mem_lowerBounds h₀ h₁ ha.2 hb.2⟩

end AntitoneMonotone

end Image2

section IsCofinalFor
variable {α β : Type*} [Preorder α] [Preorder β] {s t : Set α} {f : α → β}

lemma IsCofinalFor.image_of_monotone (hst : IsCofinalFor s t) (hf : Monotone f) :
    IsCofinalFor (f '' s) (f '' t) := by
  simp only [IsCofinalFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

lemma IsCofinalFor.image_of_antitone (hst : IsCofinalFor s t) (hf : Antitone f) :
    IsCoinitialFor (f '' s) (f '' t) := by
  simp only [IsCoinitialFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hab⟩ := hst ha
  exact ⟨b, hb, hf hab⟩

lemma IsCoinitialFor.image_of_monotone (hst : IsCoinitialFor s t) (hf : Monotone f) :
    IsCoinitialFor (f '' s) (f '' t) := by
  simp only [IsCoinitialFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hst ha
  exact ⟨b, hb, hf hba⟩

lemma IsCoinitialFor.image_of_antitone (hst : IsCoinitialFor s t) (hf : Antitone f) :
    IsCofinalFor (f '' s) (f '' t) := by
  simp only [IsCofinalFor, forall_mem_image, exists_mem_image]
  rintro a ha
  obtain ⟨b, hb, hba⟩ := hst ha
  exact ⟨b, hb, hf hba⟩

end IsCofinalFor

section Prod

variable {α β : Type*} [Preorder α] [Preorder β]

lemma bddAbove_prod {s : Set (α × β)} :
    BddAbove s ↔ BddAbove (Prod.fst '' s) ∧ BddAbove (Prod.snd '' s) :=
  ⟨fun ⟨p, hp⟩ ↦ ⟨⟨p.1, forall_mem_image.2 fun _q hq ↦ (hp hq).1⟩,
    ⟨p.2, forall_mem_image.2 fun _q hq ↦ (hp hq).2⟩⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ ⟨⟨x, y⟩, fun _p hp ↦
      ⟨hx <| mem_image_of_mem _ hp, hy <| mem_image_of_mem _ hp⟩⟩⟩

lemma bddBelow_prod {s : Set (α × β)} :
    BddBelow s ↔ BddBelow (Prod.fst '' s) ∧ BddBelow (Prod.snd '' s) :=
  bddAbove_prod (α := αᵒᵈ) (β := βᵒᵈ)

lemma bddAbove_range_prod {F : ι → α × β} :
    BddAbove (range F) ↔ BddAbove (range <| Prod.fst ∘ F) ∧ BddAbove (range <| Prod.snd ∘ F) := by
  simp only [bddAbove_prod, ← range_comp]

lemma bddBelow_range_prod {F : ι → α × β} :
    BddBelow (range F) ↔ BddBelow (range <| Prod.fst ∘ F) ∧ BddBelow (range <| Prod.snd ∘ F) :=
  bddAbove_range_prod (α := αᵒᵈ) (β := βᵒᵈ)

theorem isLUB_prod {s : Set (α × β)} (p : α × β) :
    IsLUB s p ↔ IsLUB (Prod.fst '' s) p.1 ∧ IsLUB (Prod.snd '' s) p.2 := by
  refine
    ⟨fun H =>
      ⟨⟨monotone_fst.mem_upperBounds_image H.1, fun a ha => ?_⟩,
        ⟨monotone_snd.mem_upperBounds_image H.1, fun a ha => ?_⟩⟩,
      fun H => ⟨?_, ?_⟩⟩
  · suffices h : (a, p.2) ∈ upperBounds s from (H.2 h).1
    exact fun q hq => ⟨ha <| mem_image_of_mem _ hq, (H.1 hq).2⟩
  · suffices h : (p.1, a) ∈ upperBounds s from (H.2 h).2
    exact fun q hq => ⟨(H.1 hq).1, ha <| mem_image_of_mem _ hq⟩
  · exact fun q hq => ⟨H.1.1 <| mem_image_of_mem _ hq, H.2.1 <| mem_image_of_mem _ hq⟩
  · exact fun q hq =>
      ⟨H.1.2 <| monotone_fst.mem_upperBounds_image hq,
        H.2.2 <| monotone_snd.mem_upperBounds_image hq⟩

theorem isGLB_prod {s : Set (α × β)} (p : α × β) :
    IsGLB s p ↔ IsGLB (Prod.fst '' s) p.1 ∧ IsGLB (Prod.snd '' s) p.2 :=
  @isLUB_prod αᵒᵈ βᵒᵈ _ _ _ _

lemma Monotone.upperBounds_image_of_directedOn_prod {γ : Type*} [Preorder γ] {g : α × β → γ}
    (hg : Monotone g) {d : Set (α × β)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (g '' d) = upperBounds (g '' (Prod.fst '' d) ×ˢ (Prod.snd '' d)) := le_antisymm
  (upperBounds_mono_of_isCofinalFor (hd.isCofinalFor_fst_image_prod_snd_image.image_of_monotone hg))
  (upperBounds_mono_set (image_mono subset_fst_image_prod_snd_image))

end Prod


section Pi

variable {π : α → Type*} [∀ a, Preorder (π a)]

lemma bddAbove_pi {s : Set (∀ a, π a)} :
    BddAbove s ↔ ∀ a, BddAbove (Function.eval a '' s) :=
  ⟨fun ⟨f, hf⟩ a ↦ ⟨f a, forall_mem_image.2 fun _ hg ↦ hf hg a⟩,
    fun h ↦ ⟨fun a ↦ (h a).some, fun _ hg a ↦ (h a).some_mem <| mem_image_of_mem _ hg⟩⟩

lemma bddBelow_pi {s : Set (∀ a, π a)} :
    BddBelow s ↔ ∀ a, BddBelow (Function.eval a '' s) :=
  bddAbove_pi (π := fun a ↦ (π a)ᵒᵈ)

lemma bddAbove_range_pi {F : ι → ∀ a, π a} :
    BddAbove (range F) ↔ ∀ a, BddAbove (range fun i ↦ F i a) := by
  simp only [bddAbove_pi, ← range_comp]
  rfl

lemma bddBelow_range_pi {F : ι → ∀ a, π a} :
    BddBelow (range F) ↔ ∀ a, BddBelow (range fun i ↦ F i a) :=
  bddAbove_range_pi (π := fun a ↦ (π a)ᵒᵈ)

theorem isLUB_pi {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsLUB s f ↔ ∀ a, IsLUB (Function.eval a '' s) (f a) := by
  classical
    refine
      ⟨fun H a => ⟨(Function.monotone_eval a).mem_upperBounds_image H.1, fun b hb => ?_⟩, fun H =>
        ⟨?_, ?_⟩⟩
    · suffices h : Function.update f a b ∈ upperBounds s from Function.update_self a b f ▸ H.2 h a
      exact fun g hg => le_update_iff.2 ⟨hb <| mem_image_of_mem _ hg, fun i _ => H.1 hg i⟩
    · exact fun g hg a => (H a).1 (mem_image_of_mem _ hg)
    · exact fun g hg a => (H a).2 ((Function.monotone_eval a).mem_upperBounds_image hg)

theorem isGLB_pi {s : Set (∀ a, π a)} {f : ∀ a, π a} :
    IsGLB s f ↔ ∀ a, IsGLB (Function.eval a '' s) (f a) :=
  @isLUB_pi α (fun a => (π a)ᵒᵈ) _ s f

end Pi

theorem IsGLB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsGLB (f '' s) (f x)) : IsGLB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_lowerBounds_image (fun _ _ => hf.2) hy⟩

theorem IsLUB.of_image [Preorder α] [Preorder β] {f : α → β} (hf : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
    {s : Set α} {x : α} (hx : IsLUB (f '' s) (f x)) : IsLUB s x :=
  ⟨fun _ hy => hf.1 <| hx.1 <| mem_image_of_mem _ hy, fun _ hy =>
    hf.1 <| hx.2 <| Monotone.mem_upperBounds_image (fun _ _ => hf.2) hy⟩

lemma BddAbove.range_mono [Preorder β] {f : α → β} (g : α → β) (h : ∀ a, f a ≤ g a)
    (hbdd : BddAbove (range g)) : BddAbove (range f) := by
  obtain ⟨C, hC⟩ := hbdd
  use C
  rintro - ⟨x, rfl⟩
  exact (h x).trans (hC <| mem_range_self x)

lemma BddBelow.range_mono [Preorder β] (f : α → β) {g : α → β} (h : ∀ a, f a ≤ g a)
    (hbdd : BddBelow (range f)) : BddBelow (range g) :=
  BddAbove.range_mono (β := βᵒᵈ) f h hbdd

lemma BddAbove.range_comp {γ : Type*} [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : BddAbove (range f)) (hg : Monotone g) : BddAbove (range (fun x => g (f x))) := by
  change BddAbove (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddAbove hf

lemma BddBelow.range_comp {γ : Type*} [Preorder β] [Preorder γ] {f : α → β} {g : β → γ}
    (hf : BddBelow (range f)) (hg : Monotone g) : BddBelow (range (fun x => g (f x))) := by
  change BddBelow (range (g ∘ f))
  simpa only [Set.range_comp] using hg.map_bddBelow hf
