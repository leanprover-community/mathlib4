/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.OfMap

/-!
# fintype instances for sigma types
-/


open Function

open Nat

universe u v

variable {ι α : Type*} {κ : ι → Type*} [Π i, Fintype (κ i)]

open Finset

lemma Set.biUnion_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋃ i ∈ s, ⋃ j, f ⟨i, j⟩ := by aesop

lemma Set.biUnion_finsetSigma_univ' (s : Finset ι) (f : Π i, κ i → Set α) :
    ⋃ i ∈ s, ⋃ j, f i j = ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

lemma Set.biInter_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋂ i ∈ s, ⋂ j, f ⟨i, j⟩ := by aesop

attribute [local simp] Sigma.forall in
lemma Set.biInter_finsetSigma_univ' (s : Finset ι) (f : Π i, κ i → Set α) :
    ⋂ i ∈ s, ⋂ j, f i j = ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

variable [Fintype ι]

instance Sigma.instFintype : Fintype (Σ i, κ i) := ⟨univ.sigma fun _ ↦ univ, by simp⟩
instance PSigma.instFintype : Fintype (Σ' i, κ i) := .ofEquiv _ (Equiv.psigmaEquivSigma _).symm

@[simp] lemma Finset.univ_sigma_univ : univ.sigma (fun _ ↦ univ) = (univ : Finset (Σ i, κ i)) := rfl
