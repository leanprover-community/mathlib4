import Mathlib

namespace Set

open Function

variable {α β : Type*}

/-- Without `subset_range_of_surjective`, `image_subset_iff` and `image_preimage_eq` create a simp
  confluence issue. -/
example {f : α → β} (s t : Set β) (h : Surjective f) :
    f '' (f ⁻¹' s) ⊆ t ↔ f '' (f ⁻¹' s) ⊆ t := by
  conv =>
    congr
    · simp [h, -image_preimage_eq, -subset_range_of_surjective]
    · simp [h, -image_subset_iff, -subset_range_of_surjective]
  fail_if_success simpa [h, -subset_range_of_surjective]
  simp [h]

/-- Without `Nonempty.subset_preimage_const`, `image_subset_iff` and `Nonempty.image_const` create a
  simp confluence issue. -/
example {s : Set α} (hs : Set.Nonempty s) (t : Set β) (a : β) :
    (fun _ => a) '' s ⊆ t ↔ (fun _ => a) '' s ⊆ t := by
  conv =>
    congr
    · simp [hs, -Nonempty.image_const, -Nonempty.subset_preimage_const]
    · simp [hs, -image_subset_iff, -Nonempty.subset_preimage_const]
  fail_if_success simpa [hs, -Nonempty.subset_preimage_const]
  simp [hs]

/-- Without `preimage_eq_univ_iff`, `image_subset_iff` and `image_univ` create a
  simp confluence issue. -/
example {f : α → β} (s) : f '' univ ⊆ s ↔ f '' univ ⊆ s := by
  conv =>
    congr
    · simp [-image_univ, -preimage_eq_univ_iff]
    · simp [-image_subset_iff, -preimage_eq_univ_iff]
  fail_if_success simpa [-preimage_eq_univ_iff]
  simp

end Set

namespace EquivLike

/-- Without `memRange_congr_left'`, `range_comp` and `Set.mem_range` create a simp confluence issue.
-/
example {ι : Type*} {ι' : Type*} {E : Type*} [EquivLike E ι ι']
    {α : Type*} (f : ι' → α) (e : E) (x : α) :
    x ∈ Set.range (f ∘ ⇑e) ↔ x ∈ Set.range (f ∘ ⇑e) := by
  conv =>
    congr
    · simp [-range_comp, -memRange_congr_left']
    · simp [-Set.mem_range, -memRange_congr_left']
  fail_if_success simpa [-memRange_congr_left']
  simp

end EquivLike
