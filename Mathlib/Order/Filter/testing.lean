import Mathlib.Order.Filter.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

open Set Filter

open Filter

variable {ι : Sort*} {α β : Type*}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CardinalInterFilter (l : Filter α) {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : Prop where
  /-- For a collection of sets `s ∈ l` with cardinality below c,
  their intersection belongs to `l` as well. -/
  cardinal_sInter_mem : ∀ S : Set (Set α), (Cardinal.mk S < c) → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l

variable {l : Filter α} {c : Cardinal} {hc : Cardinal.aleph0 ≤ c} [CardinalInterFilter l hc]

theorem cardinal_sInter_mem {S : Set (Set α)} (hSc : Cardinal.mk S < c) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l
    := ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ _ hSc⟩

theorem cardinal_iInter_mem [Cardinal.mk ι < c] -- <- this one fails with
  -- application type mismatch
  -- Cardinal.mk ι
  -- argument
  -- ι
  -- has type
  -- Sort u_1 : Type u_1
  -- but is expected to have type
  -- Type ?u.892 : Type (?u.892 + 1)
    {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sorry

theorem cardinal_bInter_mem {ι : Type*} {S : Set ι} (hS : Cardinal.mk S < c) -- <- this one fails with
  -- type mismatch
  -- c
  -- has type
  -- Cardinal.{u_2} : Type (u_2 + 1)
  -- but is expected to have type
  -- Cardinal.{u_4} : Type (u_4 + 1)
    {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := sorry
