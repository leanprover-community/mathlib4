/-
Copyright (c) 2022 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import Mathlib.Topology.Sets.Compacts

#align_import topology.metric_space.baire from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# Second Baire theorem

In this file we prove that a locally compact regular topological space has Baire property.
-/

open TopologicalSpace Set

/-- **Second Baire theorem**: locally compact R₁ spaces are Baire. -/
instance (priority := 100) BaireSpace.of_t2Space_locallyCompactSpace {X : Type*}
    [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X] : BaireSpace X := by
  constructor
  intro f ho hd
  /- To prove that an intersection of open dense subsets is dense, prove that its intersection
    with any open neighbourhood `U` is dense. Define recursively a decreasing sequence `K` of
    compact neighbourhoods: start with some compact neighbourhood inside `U`, then at each step,
    take its interior, intersect with `f n`, then choose a compact neighbourhood inside the
    intersection. -/
  rw [dense_iff_inter_open]
  intro U U_open U_nonempty
  -- Choose an antitone sequence of positive compacts such that `closure (K 0) ⊆ U`
  -- and `closure (K (n + 1)) ⊆ f n` for all `n`
  obtain ⟨K, hK_anti, hKf, hKU⟩ : ∃ K : ℕ → PositiveCompacts X,
      (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, closure ↑(K (n + 1)) ⊆ f n) ∧ closure ↑(K 0) ⊆ U := by
    rcases U_open.exists_positiveCompacts_closure_subset U_nonempty with ⟨K₀, hK₀⟩
    have : ∀ (n) (K : PositiveCompacts X),
        ∃ K' : PositiveCompacts X, closure ↑K' ⊆ f n ∩ interior K := by
      refine fun n K ↦ ((ho n).inter isOpen_interior).exists_positiveCompacts_closure_subset ?_
      rw [inter_comm]
      exact (hd n).inter_open_nonempty _ isOpen_interior K.interior_nonempty
    choose K_next hK_next using this
    -- The next two lines are faster than a single `refine`.
    use Nat.rec K₀ K_next
    refine ⟨fun n ↦ ?_, fun n ↦ (hK_next n _).trans (inter_subset_left _ _), hK₀⟩
    exact subset_closure.trans <| (hK_next _ _).trans <|
      (inter_subset_right _ _).trans interior_subset
  -- Prove that ̀`⋂ n : ℕ, closure (K n)` is inside `U ∩ ⋂ n : ℕ, f n`.
  have hK_subset : (⋂ n, closure (K n) : Set X) ⊆ U ∩ ⋂ n, f n := fun x hx ↦ by
    simp only [mem_iInter, mem_inter_iff] at hx ⊢
    exact ⟨hKU <| hx 0, fun n ↦ hKf n <| hx (n + 1)⟩
  /- Prove that `⋂ n : ℕ, closure (K n)` is not empty, as an intersection of a decreasing sequence
    of nonempty compact closed subsets. -/
  have hK_nonempty : (⋂ n, closure (K n) : Set X).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => closure_mono <| hK_anti n) (fun n => (K n).nonempty.closure)
      (K 0).isCompact.closure fun n => isClosed_closure
  exact hK_nonempty.mono hK_subset
#align baire_category_theorem_locally_compact BaireSpace.of_t2Space_locallyCompactSpace
