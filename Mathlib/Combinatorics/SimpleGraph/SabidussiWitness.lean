/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.Representation

/-!
# Sabidussi witness helpers

Standalone functions for proving concrete graphs are Sabidussi coset graphs.
Given `k` generators on `Fin n`, apply words (lists of generator/inverse indices),
prove closure membership, and prove the closure preserves adjacency.

## Main definitions

* `genOrInv'` — map word index to generator or inverse
* `applyWord'` — apply a word to get a permutation
* `applyWord'_mem` — word products lie in the generator closure
* `closureGraphAction` — closure elements preserve adjacency (pigeonhole for inverses)
-/

set_option linter.style.nativeDecide false

variable {n k : ℕ}

/-- Given `k` generators, map index `i : Fin (2k)` to a generator or inverse.
Indices `0, ..., k-1` are generators; `k, ..., 2k-1` are their inverses. -/
def genOrInv' (gens : Fin k → Equiv.Perm (Fin n)) (i : Fin (2 * k)) :
    Equiv.Perm (Fin n) :=
  if h : i.val < k then gens ⟨i.val, h⟩
  else (gens ⟨i.val - k, by omega⟩).symm

/-- Apply a word (list of generator/inverse indices) to obtain a permutation. -/
def applyWord' (gens : Fin k → Equiv.Perm (Fin n)) :
    List (Fin (2 * k)) → Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | i :: rest => (genOrInv' gens i).trans (applyWord' gens rest)

/-- Each generator is in the closure of the generator set. -/
private theorem gen_mem_closure' (gens : Fin k → Equiv.Perm (Fin n)) (i : Fin k) :
    gens i ∈ Subgroup.closure (Set.range gens) :=
  Subgroup.subset_closure (Set.mem_range.mpr ⟨i, rfl⟩)

/-- Each generator-or-inverse is in the closure of the generator set. -/
private theorem genOrInv'_mem_closure (gens : Fin k → Equiv.Perm (Fin n))
    (i : Fin (2 * k)) :
    genOrInv' gens i ∈ Subgroup.closure (Set.range gens) := by
  unfold genOrInv'
  split
  · exact gen_mem_closure' gens ⟨_, ‹_›⟩
  · exact Subgroup.inv_mem _ (gen_mem_closure' gens ⟨_, by omega⟩)

/-- Any word product lies in the closure of the generators. -/
theorem applyWord'_mem (gens : Fin k → Equiv.Perm (Fin n))
    (w : List (Fin (2 * k))) :
    applyWord' gens w ∈ Subgroup.closure (Set.range gens) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i rest ih =>
    show (genOrInv' gens i).trans (applyWord' gens rest) ∈ _
    exact Subgroup.mul_mem _ ih (genOrInv'_mem_closure gens i)

/-- If every generator preserves adjacency in `Γ`, then every element of the
closure preserves adjacency. The inverse case uses pigeonhole on directed edges. -/
theorem closureGraphAction {Γ : SimpleGraph (Fin n)}
    (gens : Fin k → Equiv.Perm (Fin n))
    (hgens : ∀ i : Fin k, ∀ u v : Fin n, Γ.Adj u v → Γ.Adj (gens i u) (gens i v))
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ Subgroup.closure (Set.range gens)) :
    ∀ u v : Fin n, Γ.Adj u v → Γ.Adj (σ u) (σ v) := by
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
    exact hgens i
  | one => simp
  | mul x y _ _ ihx ihy =>
    intro u v hadj
    simp only [Equiv.Perm.mul_apply]
    exact ihx _ _ (ihy u v hadj)
  | inv x _ ih =>
    intro u v hadj
    let f : { p : Fin n × Fin n // Γ.Adj p.1 p.2 } →
            { p : Fin n × Fin n // Γ.Adj p.1 p.2 } :=
      fun ⟨⟨a, b⟩, hab⟩ => ⟨⟨x a, x b⟩, ih a b hab⟩
    have hf_surj : Function.Surjective f := Finite.surjective_of_injective (by
      intro ⟨⟨a₁, b₁⟩, _⟩ ⟨⟨a₂, b₂⟩, _⟩ heq
      simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact Subtype.ext (Prod.ext (x.injective heq.1) (x.injective heq.2)))
    obtain ⟨⟨⟨a, b⟩, hab⟩, heq⟩ := hf_surj ⟨⟨u, v⟩, hadj⟩
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at heq
    rw [show a = x⁻¹ u from by rw [← heq.1]; simp,
        show b = x⁻¹ v from by rw [← heq.2]; simp] at hab
    exact hab
