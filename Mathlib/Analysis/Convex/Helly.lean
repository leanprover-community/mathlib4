import Mathlib.Data.Set.Card
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.SubsetProperties
import Mathlib.Tactic.Linarith

open Set
open FiniteDimensional

universe u

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
[FiniteDimensional 𝕜 E]

/-- **Helly's theorem on convex sets**: If `F` is a finite family of convex sets in a vector space
of finite dimension `d`, and any `d + 1` sets of `F` intersect, then all sets of `F` intersect. -/
theorem helly_theorem (F : Set (Set E)) {hF_fin : Set.Finite F}
    (h_card : (finrank 𝕜 E) + 1 ≤ ncard F) (h_convex : ∀ X ∈ F, Convex 𝕜 X)
    (h_inter : ∀ G : Set (Set E), (G ⊆ F) → (ncard G = (finrank 𝕜 E) + 1) →
    Set.Nonempty (sInter (G : Set (Set E)))) : Set.Nonempty (sInter (F : Set (Set E))) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ncard F = n := ⟨ncard F, rfl⟩
  rw [hn] at h_card
  induction' n, h_card using Nat.le_induction with k h_card hk generalizing F
  exact h_inter F (Eq.subset rfl) hn

  have h1 : ∀ X ∈ F, Set.Nonempty (sInter (F \ {X})) := by
    intro X hX
    apply @hk _ (Finite.diff hF_fin {X})
    intro Y hY
    exact h_convex Y (Set.mem_of_mem_diff hY)
    intro G hG_1 hG_2
    exact h_inter G (Set.Subset.trans hG_1 (Set.diff_subset F {X})) hG_2
    rw [Set.ncard_diff_singleton_of_mem hX hF_fin]
    exact Nat.sub_eq_of_eq_add hn

  let a : F → E := fun X => Set.Nonempty.some (h1 X (Subtype.mem X))
  ------------------------------------- I stopped here
  have h2 (X Y : Set E) (hX : X ∈ F) (hY : Y ∈ F) (hneq : X ≠ Y) : a ⟨Y, hY⟩ ∈ X := by
    have ha_aux := Set.Nonempty.some_mem (h1 Y hY)
    fapply Set.mem_of_subset_of_mem
    exact ⋂₀ (F \ {Y})
    apply Set.sInter_subset_of_mem
    rw [Set.mem_diff_singleton]
    constructor; exact hX; exact hneq
    exact ha_aux

  have h3 : ¬AffineIndependent 𝕜 a := by
    have := Set.Finite.fintype hF_fin
    have h3_aux : Fintype.card F = (k - 1) + 2 :=
      calc
        Fintype.card F = Finset.card (Set.Finite.toFinset hF_fin) := by
          rw [←Set.Finite.card_toFinset hF_fin]
        _ = ncard F := by rw [←Set.ncard_eq_toFinset_card F hF_fin]
        _ = k + 1 := hn
        _ = (k - 1) + 1 + 1 := by rw [Nat.sub_add_cancel]; linarith
        _ = (k - 1) + 2 := by simp
    rw [←finrank_vectorSpan_le_iff_not_affineIndependent 𝕜 a h3_aux]
    apply LE.le.trans (Submodule.finrank_le (vectorSpan 𝕜 (Set.range a)))
    exact Nat.le_pred_of_lt h_card

  obtain ⟨I, p, h4_I, h4_Ic⟩ := Convex.radon_partition h3
  use p; simp; intro X hX

  have h5 (I : Set F) (h : ⟨X, hX⟩ ∈ I) : (convexHull 𝕜) (a '' Iᶜ) ⊆ X := by
    rw [Convex.convexHull_subset_iff]
    intro y hy; simp at hy
    rcases hy with ⟨X1, hX1, hX2, hX3⟩
    rw [←hX3]
    apply h2
    exact hX; exact hX1
    by_contra heq
    have h4_aux : (⟨X, hX⟩ : {x // x ∈ F}) = ⟨X1, hX1⟩ := by
      exact SetCoe.ext heq
    rw [h4_aux] at h; contradiction
    exact h_convex X hX

  by_cases (⟨X, hX⟩ ∈ I)
  · exact h5 I h h4_Ic
  · apply h5 Iᶜ h; rwa [compl_compl]

#check helly_theorem
