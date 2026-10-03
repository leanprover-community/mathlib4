/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

/-!
# ...

-/

universe u

@[expose] public section

open CategoryTheory Simplicial

namespace PartialOrder.NonemptyFiniteChains

variable {X : Type u} [LinearOrder X] [Fintype X] [Nontrivial X] (x₀ : X)

def horn : (nerve (NonemptyFiniteChains X)).Subcomplex where
  obj _ := Set.ofPred (fun s ↦ ∀ i, ¬ complSingleton x₀ ≤ s.obj i)
  map _ _ hs _ := hs _

lemma notMem_horn_iff {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∉ (horn x₀).obj _ ↔ complSingleton x₀ ≤ s.obj (Fin.last _) := by
  simp only [horn, nerve_obj, le_iff, Set.mem_ofPred_eq, not_forall, not_not]
  exact ⟨fun ⟨i, hi⟩ ↦ subset_trans hi (s.monotone (Fin.le_last _)), fun h ↦ ⟨_, h⟩⟩

lemma mem_horn_iff {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∈ (horn x₀).obj _ ↔
      ¬ complSingleton x₀ ≤ s.obj (Fin.last n) := by
  rw [← notMem_horn_iff, not_not]

lemma notMem_horn_iff' {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∉ (horn x₀).obj _ ↔
      s.obj (Fin.last _) = complSingleton x₀ ∨ s.obj (Fin.last _) = ⊤ := by
  simp [notMem_horn_iff, NonemptyFiniteChains.ext_iff,
    Finset.compl_singleton_subset_iff]

lemma mem_horn_iff' {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∈ (horn x₀).obj _ ↔
      s.obj (Fin.last _) ≠ complSingleton x₀ ∧ s.obj (Fin.last _) ≠ ⊤ := by
  simp [mem_horn_iff, NonemptyFiniteChains.ext_iff,
    Finset.compl_singleton_subset_iff]

end PartialOrder.NonemptyFiniteChains
