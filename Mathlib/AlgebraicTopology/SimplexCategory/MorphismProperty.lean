/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Properties of morphisms in the simplex category

In this file, we show that morphisms in the simplex category
are generated by faces and degeneracies. This is stated by
saying that if `W : MorphismProperty SimplexCategory` is
multiplicative, and contains faces and degeneracies, then `W = ⊤`.
This statement is deduced from a similar statement for
the category `SimplexCategory.Truncated d`.

-/

open CategoryTheory

namespace SimplexCategory

lemma Truncated.morphismProperty_eq_top
    {d : ℕ} (W : MorphismProperty (Truncated d)) [W.IsMultiplicative]
    (δ_mem : ∀ (n : ℕ) (hn : n < d) (i : Fin (n + 2)),
    W (SimplexCategory.δ (n := n) i : ⟨.mk n, by dsimp; order⟩ ⟶
      ⟨.mk (n + 1), by dsimp; omega⟩))
    (σ_mem : ∀ (n : ℕ) (hn : n < d) (i : Fin (n + 1)),
    W (SimplexCategory.σ (n := n) i : ⟨.mk (n + 1), by dsimp; omega⟩ ⟶
      ⟨.mk n, by dsimp; order⟩)) :
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
      · exact (h₁ (fun _ ↦ ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩)).elim
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

lemma morphismProperty_eq_top
    (W : MorphismProperty SimplexCategory) [W.IsMultiplicative]
    (δ_mem : ∀ {n : ℕ} (i : Fin (n + 2)), W (SimplexCategory.δ i))
    (σ_mem : ∀ {n : ℕ} (i : Fin (n + 1)), W (SimplexCategory.σ i)) :
    W = ⊤ := by
  have hW (d : ℕ) : W.inverseImage (Truncated.inclusion d) = ⊤ :=
    Truncated.morphismProperty_eq_top _ (fun _ _ i ↦ δ_mem i)
      (fun _ _ i ↦ σ_mem i)
  ext a b f
  simp only [MorphismProperty.top_apply, iff_true]
  change W.inverseImage (Truncated.inclusion _)
    (f : ⟨a, Nat.le_max_left _ _⟩ ⟶ ⟨b, Nat.le_max_right _ _⟩)
  simp only [hW, MorphismProperty.top_apply]

end SimplexCategory
