/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Well-foundedness of orders of well-founded relations

Porting note: many declarations that were here in mathlib3 have been moved to `Init.WF`
in Lean 4 core. The ones below are all the exceptions.
-/

universe u v

namespace PSigma

section

open WellFounded

variable {α : Sort u} {β : α → Sort v} {r : α → α → Prop} {s : ∀ a : α, β a → β a → Prop}

/-- The lexicographical order of well-founded relations is well-founded. -/
theorem lex_wf (ha : WellFounded r) (hb : ∀ x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b

end

section

open WellFounded

variable {α : Sort u} {β : Sort v} {r : α → α → Prop} {s : β → β → Prop}

theorem revLex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a

end

section

theorem skipLeft_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : WellFounded s) :
    WellFounded (SkipLeft α s) :=
  revLex_wf emptyWf.wf hb

end

instance hasWellFounded {α : Type u} {β : α → Type v} [s₁ : WellFoundedRelation α]
    [s₂ : ∀ a, WellFoundedRelation (β a)] : WellFoundedRelation (PSigma β) where
  rel := Lex s₁.rel fun a => (s₂ a).rel
  wf := lex_wf s₁.wf fun a => (s₂ a).wf

end PSigma
