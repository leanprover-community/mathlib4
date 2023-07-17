/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn

! This file was ported from Lean 3 source module init.data.sigma.basic
! leanprover-community/lean commit 87932f1c56b7c05aefd2810d05e69da9500a0064
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Logic

/-!
# Lemmas about `Sigma` from Lean 3 core.
-/

theorem ex_of_psig {p : α → Prop} : (Σ' x, p x) → ∃ x, p x
  | ⟨x, hx⟩ => ⟨x, hx⟩

protected theorem Sigma.eq {β : α → Type v} : ∀ {p₁ p₂ : Σ a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl

protected theorem PSigma.eq {β : α → Sort v} : ∀ {p₁ p₂ : Σ' a, β a} (h₁ : p₁.1 = p₂.1),
    (Eq.recOn h₁ p₁.2 : β p₂.1) = p₂.2 → p₁ = p₂
  | ⟨_, _⟩, _, rfl, rfl => rfl
