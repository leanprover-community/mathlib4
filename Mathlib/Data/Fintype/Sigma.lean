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

variable {α β γ : Type*}

open Finset Function

instance (β : α → Type*) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.sigma fun _ => univ, fun ⟨a, b⟩ => by simp⟩

@[simp]
theorem Finset.univ_sigma_univ {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)] :
    ((univ : Finset α).sigma fun a => (univ : Finset (β a))) = univ :=
  rfl
#align finset.univ_sigma_univ Finset.univ_sigma_univ

instance PSigma.fintype {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv _ (Equiv.psigmaEquivSigma _).symm
#align psigma.fintype PSigma.fintype

lemma Set.biInter_finsetSigma_univ {β : α → Type*} [∀ a, Fintype (β a)]
    (s : Finset α) (u : Sigma β → Set γ) :
    ⋂ ij ∈ s.sigma (fun _ ↦ Finset.univ), u ij = ⋂ i ∈ s, ⋂ j : β i, u ⟨i, j⟩ :=
  by ext; constructor <;> simp_all

lemma Set.biInter_finsetSigma_univ' {β : α → Type*} [∀ a, Fintype (β a)]
    (s : Finset α) (u : ∀ i, β i → Set γ) :
    ⋂ i ∈ s, ⋂ j : β i, u i j = ⋂ ij ∈ s.sigma (fun _ ↦ Finset.univ), u ij.fst ij.snd :=
  Eq.symm $ Set.biInter_finsetSigma_univ _ _
