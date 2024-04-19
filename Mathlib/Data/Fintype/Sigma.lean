/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Sigma

#align_import data.fintype.sigma from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# fintype instances for sigma types
-/


open Function

open Nat

universe u v

variable {ι α β γ : Type*} {κ : ι → Type*} [Π i, Fintype (κ i)]

open Finset Function

lemma Set.biUnion_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋃ i ∈ s, ⋃ j, f ⟨i, j⟩ := by aesop

lemma Set.biUnion_finsetSigma_univ' (s : Finset ι) (f : Π i, κ i → Set α) :
    ⋃ i ∈ s, ⋃ j, f i j = ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

lemma Set.biInter_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋂ i ∈ s, ⋂ j, f ⟨i, j⟩ := by aesop

lemma Set.biInter_finsetSigma_univ' (s : Finset ι) (f : Π i, κ i → Set α) :
    ⋂ i ∈ s, ⋂ j, f i j = ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

variable [Fintype ι]

instance Sigma.instFintype : Fintype (Σ i, κ i) := ⟨univ.sigma fun _ ↦ univ, by simp⟩
instance PSigma.instFintype : Fintype (Σ' i, κ i) := .ofEquiv _ (Equiv.psigmaEquivSigma _).symm
#align psigma.fintype PSigma.instFintype

@[simp] lemma Finset.univ_sigma_univ : univ.sigma (fun _ ↦ univ) = (univ : Finset (Σ i, κ i)) := rfl
#align finset.univ_sigma_univ Finset.univ_sigma_univ

instance Infinite.sigma_of_left {α : Type*} {β : α → Type*} [Infinite α] [∀ a, Nonempty (β a)] :
    Infinite ((a : α) × (β a)) :=
  Infinite.of_surjective Sigma.fst Sigma.fst_surjective

theorem Infinite.sigma_of_right {α : Type*} {β : α → Type*} {a : α} [Infinite (β a)] :
    Infinite ((a : α) × (β a)) :=
  Infinite.of_injective (f := fun x ↦ ⟨a,x⟩) fun _ _ ↦ by simp
