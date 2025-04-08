/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.LocalAtTarget

/-!
# Cardinality of connected components under open and closed maps

Let `f : X → Y` be an open and closed map.

## Main results

- `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`: If `Y` is connected,
  the number of connected components of `X` is bounded by the cardinality of the fiber
  of `f` at `y`.
-/

open scoped Function

open ConnectedComponents

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf₁ : IsOpenMap f)
  (hf₂ : IsClosedMap f)

include hf₁ hf₂

/-- If `f : X → Y` is an open and closed map to and `Y` is connected, the number of connected
components of `X` is bounded by the cardinality of the fiber of any point. -/
@[stacks 07VB]
lemma IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton [ConnectedSpace Y]
    (y : Y) : ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard := by
  suffices h : ∀ {n : ℕ} (U : Fin n → Set X) (hU₁ : ∀ i, IsClopen (U i)) (hU₂ : ∀ i, (U i).Nonempty)
      (hU₃ : Pairwise (Disjoint on U)) (hU₄ : ⋃ i, U i = Set.univ),
      n ≤ (f ⁻¹' {y}).encard by
    obtain (hy|hy) := finite_or_infinite (ConnectedComponents X)
    · cases nonempty_fintype (ConnectedComponents X)
      simp only [ENat.card_eq_coe_fintype_card]
      refine h (fun i ↦ ConnectedComponents.mk ⁻¹' {(Fintype.equivFin _).symm i}) (fun i ↦ ?_)
          (fun i ↦ ?_) (fun i j hij ↦ Disjoint.preimage _ (by simp [hij])) ?_
      · exact (isClopen_discrete _).preimage continuous_coe
      · exact (Set.singleton_nonempty _).preimage surjective_coe
      · simp [← Set.preimage_iUnion]
    · simp only [ENat.card_eq_top_of_infinite, top_le_iff, ENat.eq_top_iff_forall_ge]
      intro m
      obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_fun_isClopen_of_infinite X (m + 1) (by simp)
      exact le_trans (by simp) (h U hU1 hU2 hU3 hU4)
  intro n U hU1 hU2 hU3 hU4
  have heq : f ⁻¹' {y} = ⋃ i, (U i ∩ f ⁻¹' {y}) := by
    conv_lhs => rw [← Set.univ_inter (f ⁻¹' {y}), ← hU4, Set.iUnion_inter]
  rw [heq, Set.encard_iUnion fun i j hij ↦ .inter_left _ (.inter_right _ <| hU3 hij)]
  trans ∑ i : Fin n, 1
  · simp
  · rw [finsum_eq_sum_of_fintype]
    refine Fintype.sum_mono fun i ↦ Set.one_le_encard_iff_nonempty.mpr (show y ∈ f '' (U i) from ?_)
    convert Set.mem_univ y
    exact IsClopen.eq_univ ⟨hf₂ _ (hU1 i).1, hf₁ _ (hU1 i).2⟩ ((hU2 i).image f)

lemma IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    [ConnectedSpace Y] {y : Y} (hy : (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) := by
  rw [← ENat.card_lt_top_iff_finite]
  exact lt_of_le_of_lt (hf₁.enatCard_connectedComponents_le_encard_preimage_singleton hf₂ y)
    hy.encard_lt_top

/-- If `f : X → Y` is open and closed with finite fibers and `Y` has finitely many connected
components, so does `X`. -/
lemma IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton
    [Finite (ConnectedComponents Y)] (hfc : Continuous f) (h : ∀ y, (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) := by
  suffices h : ∀ (y : ConnectedComponents Y), Finite (ConnectedComponents (f ⁻¹' (mk ⁻¹' {y}))) by
    refine .of_equiv _ (equivOfIsClopen (U := fun y ↦ f ⁻¹' (mk ⁻¹' {y})) ?_ ?_ ?_).symm
    · exact fun y ↦ (isClopen_discrete {y}).preimage (continuous_coe.comp hfc)
    · exact fun i j hij ↦ (Disjoint.preimage mk (by simpa)).preimage f
    · rw [Set.iUnion_eq_univ_iff]
      exact fun x ↦ ⟨mk (f x), rfl⟩
  intro y
  obtain ⟨y, rfl⟩ := surjective_coe y
  have := isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := y))
  rw [connectedComponents_preimage_singleton]
  refine IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    (hf₁.restrictPreimage (connectedComponent y)) (hf₂.restrictPreimage (connectedComponent y))
    (y := ⟨y, mem_connectedComponent⟩) ?_
  rw [← Set.finite_image_iff Subtype.val_injective.injOn]
  convert h y
  aesop (add safe mem_connectedComponent)

end
