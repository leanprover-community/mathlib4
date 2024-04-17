/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Init.Function

#align_import data.prod.pprod from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Extra facts about `PProd`
-/


open Function

variable {α β γ δ : Sort*}

namespace PProd

@[simp]
theorem mk.eta {p : PProd α β} : PProd.mk p.1 p.2 = p :=
  rfl
#align pprod.mk.eta PProd.mk.eta

@[simp]
theorem «forall» {p : PProd α β → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ :=
  ⟨fun h a b ↦ h ⟨a, b⟩, fun h ⟨a, b⟩ ↦ h a b⟩
#align pprod.forall PProd.forall

@[simp]
theorem «exists» {p : PProd α β → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ :=
  ⟨fun ⟨⟨a, b⟩, h⟩ ↦ ⟨a, b, h⟩, fun ⟨a, b, h⟩ ↦ ⟨⟨a, b⟩, h⟩⟩
#align pprod.exists PProd.exists

theorem forall' {p : α → β → Prop} : (∀ x : PProd α β, p x.1 x.2) ↔ ∀ a b, p a b :=
  PProd.forall
#align pprod.forall' PProd.forall'

theorem exists' {p : α → β → Prop} : (∃ x : PProd α β, p x.1 x.2) ↔ ∃ a b, p a b :=
  PProd.exists
#align pprod.exists' PProd.exists'

end PProd

theorem Function.Injective.pprod_map {f : α → β} {g : γ → δ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x ↦ ⟨f x.1, g x.2⟩ : PProd α γ → PProd β δ) := fun _ _ h ↦
  have A := congr_arg PProd.fst h
  have B := congr_arg PProd.snd h
  congr_arg₂ PProd.mk (hf A) (hg B)
#align function.injective.pprod_map Function.Injective.pprod_map
