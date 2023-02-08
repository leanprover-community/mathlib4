/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.sigma
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sigma

/-!
# fintype instances for sigma types
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

open Finset Function

instance {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.sigma fun _ => univ, fun ⟨a, b⟩ => by simp⟩

@[simp]
theorem Finset.univ_sigma_univ {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    ((univ : Finset α).sigma fun a => (univ : Finset (β a))) = univ :=
  rfl
#align finset.univ_sigma_univ Finset.univ_sigma_univ

instance PSigma.fintype {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (Σ'a, β a) :=
  Fintype.ofEquiv _ (Equiv.psigmaEquivSigma _).symm
#align psigma.fintype PSigma.fintype
