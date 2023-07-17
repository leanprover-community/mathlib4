/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.sigma.lex
! leanprover-community/lean commit 9af482290ef68e8aaa5ead01aa7b09b7be7019fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Data.Sigma.Basic

/-!
# Facts about `PSigma.Lex` from Lean 3 core.
-/

universe u v

namespace PSigma

variable {α : Sort u} {β : α → Sort v} {r : α → α → Prop} {s : ∀ a : α, β a → β a → Prop}

-- The lexicographical order of well founded relations is well-founded
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b
#align psigma.lex_wf PSigma.lex_wf

end PSigma
