/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Factorization in the simplex category

-/

open CategoryTheory

namespace SimplexCategory.Truncated

variable {d : ℕ} (W : MorphismProperty (Truncated d)) [W.IsMultiplicative]

lemma morphismProperty_eq_top
    (δ_mem : ∀ (n : ℕ) (hn : n + 1 ≤ d) (i : Fin (n + 2)),
    W (SimplexCategory.δ (n := n) i : ⟨.mk n, by dsimp; omega⟩ ⟶
      ⟨.mk (n + 1), by dsimp; omega⟩))
    (σ_mem : ∀ (n : ℕ) (hn : n + 1 ≤ d) (i : Fin (n + 1)),
    W (SimplexCategory.σ (n := n) i : ⟨.mk (n + 1), by dsimp; omega⟩ ⟶
      ⟨.mk n, by dsimp; omega⟩)) :
    W = ⊤ := by
  ext ⟨a, ha⟩ ⟨b, hb⟩ f
  simp only [MorphismProperty.top_apply, iff_true]
  induction' a using SimplexCategory.rec with a
  induction' b using SimplexCategory.rec with b
  dsimp at ha hb
  generalize h : a + b = c
  induction c generalizing a b with
  | zero =>
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    obtain rfl : f = 𝟙 _ := by
      ext i : 3
      apply Subsingleton.elim (α := Fin 1)
    apply MorphismProperty.id_mem
  | succ c hc =>
    let f' : mk a ⟶ mk b := f
    by_cases h₁ : Function.Surjective f'.toOrderHom; swap
    · obtain _ | b := b
      · exact (h₁ (fun i ↦ ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩)).elim
      · obtain ⟨i, g', hf'⟩ := eq_comp_δ_of_not_surjective _ h₁
        obtain rfl : f = (g' : _ ⟶ ⟨mk b, by dsimp; omega⟩) ≫ δ i := hf'
        exact W.comp_mem _ _ (hc _ _ _ _ _ (by omega))
          (δ_mem _ (by omega) _)
    by_cases h₂ : Function.Injective f'.toOrderHom; swap
    · obtain _ | a := a
      · exact (h₂ (Function.injective_of_subsingleton (α := Fin 1) _)).elim
      · obtain ⟨i, g', hf'⟩ := eq_σ_comp_of_not_injective _ h₂
        obtain rfl : f = (by exact σ i) ≫ (g' : ⟨mk a, by dsimp; omega⟩ ⟶ _) := hf'
        exact W.comp_mem _ _ (σ_mem _ (by omega) _) (hc _ _ _ _ _ (by omega))
    rw [← epi_iff_surjective] at h₁
    rw [← mono_iff_injective] at h₂
    obtain rfl : a = b := le_antisymm (len_le_of_mono h₂) (len_le_of_epi h₁)
    obtain rfl : f = 𝟙 _ := eq_id_of_mono f'
    apply W.id_mem

end SimplexCategory.Truncated
