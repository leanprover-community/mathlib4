import Mathlib

variable {ι : Sort*} {α β : Type*}

open Set Filter

def cocountable : Filter α := by
  apply ofCountableUnion hc Set.Countable
  · intro _ _ _
    exact hc
  · intro _ _ _ _
    simp_all only [Cardinal.mk_eq_aleph0]

/-- Construct a filter with cardinal intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the cardinal intersection property. -/
def Filter.ofCardinalInter {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) (l : Set (Set α))
    (hp : ∀ S : Set (Set α), (Cardinal.mk S ≤ c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := by
    apply @sInter_empty α ▸ hp _ ?_ (empty_subset _)
    simp_all only [Cardinal.mk_eq_zero, zero_le]
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := by
    apply sInter_pair s t ▸ hp _ (ge_trans hc Cardinal.mk_le_aleph0)
      (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)

def Filter.ofCardinalUnion {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) (p : Set α → Prop)
    (hUnion : ∀ S : Set (Set α), (Cardinal.mk S ≤ c) → (∀ s ∈ S, p s) → p (⋃₀ S))
    (hmono : ∀ t, p t → ∀ s ⊆ t, p s) : Filter α := by
  refine .ofCardinalInter hc {s | p sᶜ} (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_setOf_eq, compl_sInter]
    exact hUnion _ (ge_trans hSc Cardinal.mk_image_le) (ball_image_iff.2 hSp)
  · exact hmono _ ht _ (compl_subset_compl.2 hsub)

-- Of course, this would generalise to CardinalInterFilter under a suitable definition for these.
instance Filter.countableInter_ofCardinalnter {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) (l : Set (Set α))
    (hp : ∀ S : Set (Set α), (Cardinal.mk S ≤ c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCardinalInter hc l hp h_mono) where
  countable_sInter_mem := fun _ hS a ↦ hp _ (ge_trans hc (Countable.le_aleph0 hS)) a

def cocardinal {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : Filter α := by
  apply ofCardinalUnion hc (fun _ ↦ Cardinal.mk _ ≤ c)
  · intro _ _ _
    exact hc
  · intro _ _ _ _
    simp_all only [Cardinal.mk_eq_aleph0]
