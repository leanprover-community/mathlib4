/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sigma

#align_import data.fintype.sigma from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# fintype instances for sigma types
-/


open Function

open Nat

universe u v

variable {ι α β γ : Type*} {κ : ι → Type*} [∀ i, Fintype (κ i)]

open Finset Function

instance {α : Type*} (β : α → Type*) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.sigma fun _ => univ, fun ⟨a, b⟩ => by simp⟩

@[simp]
theorem Finset.univ_sigma_univ {α : Type*} {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)] :
    ((univ : Finset α).sigma fun a => (univ : Finset (β a))) = univ :=
  rfl
#align finset.univ_sigma_univ Finset.univ_sigma_univ

instance PSigma.fintype {α : Type*} {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv _ (Equiv.psigmaEquivSigma _).symm
#align psigma.fintype PSigma.fintype

lemma Set.biUnion_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋃ i ∈ s, ⋃ j, f ⟨i, j⟩ := by aesop

lemma Set.biUnion_finsetSigma_univ' (s : Finset ι) (f : ∀ i, κ i → Set α) :
    ⋃ i ∈ s, ⋃ j, f i j = ⋃ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop

lemma Set.biInter_finsetSigma_univ (s : Finset ι) (f : Sigma κ → Set α) :
    ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij = ⋂ i ∈ s, ⋂ j, f ⟨i, j⟩ := by aesop

lemma Set.biInter_finsetSigma_univ' (s : Finset ι) (f : ∀ i, κ i → Set α) :
    ⋂ i ∈ s, ⋂ j, f i j = ⋂ ij ∈ s.sigma fun _ ↦ Finset.univ, f ij.1 ij.2 := by aesop
