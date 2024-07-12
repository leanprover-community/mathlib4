import Mathlib.Computability.Language
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Greedoid.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Finite

section LanguageGreedoid

open Language Finset Set

structure LanguageGreedoid (α : Type*) where
  ground_set : Finset α
  language : Language α
  subset_ground : ∀ ⦃l : List α⦄, l ∈ language → ∀ x ∈ l, x ∈ ground_set 
  language_simple : ∀ ⦃l⦄, l ∈ language → l.Nodup
  contains_nil : [] ∈ language
  contains_suffix : ∀ ⦃l₁ l₂ : List α⦄, l₁ ++ l₂ ∈ language → l₂ ∈ language
  exchange_prop : ∀ ⦃l₁ l₂ : List α⦄, l₁ ∈ language → l₂ ∈ language → l₁.length < l₂.length →
    ∃ x ∈ l₁, x :: l₂ ∈ language

namespace LanguageGreedoid

variable {α : Type*}

/-- TODO: Remove `DecidableEq`. Check Mathlib.Data.Fintype.List.-/
theorem language_Finite [DecidableEq α] {L : LanguageGreedoid α} : L.language.Finite := by
  let s := L.ground_set.powerset.map ⟨λ s ↦ s.val.lists, by
    intro s t h
    simp only at h
    
    sorry⟩
  apply Set.Finite.ofFinset
  · sorry
  · sorry

protected def toGreedoid (L : LanguageGreedoid α) : Greedoid α where
  ground_set := L.ground_set
  feasible_set := @Set.toFinset (Set.image (@Set.univ { l // l ∈ L.language }) λ l ↦ sorry) sorry
  contains_emptyset := sorry
  accessible_property := sorry
  exchange_property := sorry
  subset_ground := sorry

end LanguageGreedoid

end LanguageGreedoid
