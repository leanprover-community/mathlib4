/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename

#align_import init.data.sigma.lex from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

/-!
# Well-foundedness of orders of well-founded relations

Porting note: many declarations that were here in mathlib3 have been moved to `Init.WF`
in Lean 4 core. The ones below are all the exceptions.
-/

universe u v

namespace PSigma

section

open WellFounded

variable {α : Sort u} {β : α → Sort v} {r : α → α → Prop} {s : ∀ a : α, β a → β a → Prop}

#align psigma.lex PSigma.Lex
#align psigma.lex_accessible PSigma.lexAccessible

/-- The lexicographical order of well-founded relations is well-founded. -/
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b
#align psigma.lex_wf PSigma.lex_wf

#align psigma.lex_ndep PSigma.lexNdep
#align psigma.lex_ndep_wf PSigma.lexNdepWf

end

section

open WellFounded

variable {α : Sort u} {β : Sort v} {r : α → α → Prop} {s : β → β → Prop}

#align psigma.rev_lex PSigma.RevLex
#align psigma.rev_lex_accessible PSigma.revLexAccessible

theorem revLex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a
#align psigma.rev_lex_wf PSigma.revLex_wf

end

section

#align psigma.skip_left PSigma.SkipLeft

theorem skipLeft_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) :
    WellFounded (SkipLeft α s) :=
  revLex_wf emptyWf.wf hb
#align psigma.skip_left_wf PSigma.skipLeft_wf

#align psigma.mk_skip_left PSigma.mkSkipLeft

end

instance hasWellFounded {α : Type u} {β : α → Type v} [s₁ : WellFoundedRelation α]
    [s₂ : ∀ a, WellFoundedRelation (β a)] : WellFoundedRelation (PSigma β) where
  rel := Lex s₁.rel fun a => (s₂ a).rel
  wf := lex_wf s₁.wf fun a => (s₂ a).wf
#align psigma.has_well_founded PSigma.hasWellFounded

end PSigma
