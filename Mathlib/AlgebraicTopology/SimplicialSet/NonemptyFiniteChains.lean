/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Order.NonemptyFiniteChains

/-!
# ...

-/

universe u

@[expose] public section

open CategoryTheory Simplicial

namespace PartialOrder.NonemptyFiniteChains

section

variable {X : Type u} [PartialOrder X]

open Classical in
@[no_expose]
noncomputable def ofS (s : (nerve X).S) : NonemptyFiniteChains X where
  finset := Finset.univ.image s.simplex.obj
  nonempty := ⟨s.simplex.obj 0, by simp⟩
  comparable := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    obtain h | h := le_total i j
    · exact Or.inl (s.simplex.monotone h)
    · exact Or.inr (s.simplex.monotone h)

@[simp]
lemma mem_ofS_iff (s : (nerve X).S) (x : X) :
    x ∈ (ofS s).1 ↔ x ∈ Set.range s.simplex.obj := by
  simp [ofS]

lemma obj_mem_ofS (s : (nerve X).S) (i : Fin (s.dim + 1)) :
    s.simplex.obj i ∈ (ofS s).1 := by simp [ofS]

noncomputable def ofN (s : (nerve X).N) : NonemptyFiniteChains X := ofS s.toS

@[simp]
lemma mem_ofN_iff (s : (nerve X).N) (x : X) :
    x ∈ (ofN s).1 ↔ x ∈ Set.range s.simplex.obj := by
  simp [ofN]

@[simp]
lemma ofN_le_ofN_iff {s t : (nerve X).N} : (ofN s).1 ⊆ (ofN t).1 ↔ s ≤ t := by
  sorry

variable (X) in
lemma bijective_ofN : Function.Bijective (ofN (X := X)) :=
  sorry

@[simps! apply]
noncomputable def nerveNEquiv : (nerve X).N ≃o NonemptyFiniteChains X :=
  (Equiv.ofBijective _ (bijective_ofN X)).toOrderIso
    (fun s t h ↦ by simpa)
    (fun s t h ↦ by
      obtain ⟨s, rfl⟩ := (bijective_ofN _ ).2 s
      obtain ⟨t, rfl⟩ := (bijective_ofN _ ).2 t
      simpa using h)

end

section

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

end

end PartialOrder.NonemptyFiniteChains
