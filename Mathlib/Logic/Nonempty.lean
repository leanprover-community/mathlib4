/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Init.ZeroOne
import Mathlib.Init.Function

#align_import logic.nonempty from "leanprover-community/mathlib"@"d2d8742b0c21426362a9dacebc6005db895ca963"

/-!
# Nonempty types

This file proves a few extra facts about `Nonempty`, which is defined in core Lean.

## Main declarations

* `Nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` explicitly.
* `Classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` as an
  instance.
-/

section
variable {α β : Sort*}

@[simp]
theorem Nonempty.forall {α} {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h _ ↦ h _) fun h ⟨a⟩ ↦ h a
#align nonempty.forall Nonempty.forall

@[simp]
theorem Nonempty.exists {α} {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ ↦ ⟨a, h⟩) fun ⟨a, h⟩ ↦ ⟨⟨a⟩, h⟩
#align nonempty.exists Nonempty.exists

theorem exists_true_iff_nonempty {α : Sort*} : (∃ _ : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨a, trivial⟩
#align exists_true_iff_nonempty exists_true_iff_nonempty

@[simp]
theorem nonempty_Prop {p : Prop} : Nonempty p ↔ p :=
  Iff.intro (fun ⟨h⟩ ↦ h) fun h ↦ ⟨h⟩
#align nonempty_Prop nonempty_Prop

theorem Nonempty.imp {α} {p : Prop} : (Nonempty α → p) ↔ (α → p) :=
  Nonempty.forall

theorem not_nonempty_iff_imp_false {α : Sort*} : ¬Nonempty α ↔ α → False :=
  Nonempty.imp
#align not_nonempty_iff_imp_false not_nonempty_iff_imp_false

@[simp]
theorem nonempty_psigma {α} {β : α → Sort*} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ ↦ ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ ↦ ⟨⟨a, c⟩⟩
#align nonempty_psigma nonempty_psigma

@[simp]
theorem nonempty_subtype {α} {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ ↦ ⟨a, h⟩) fun ⟨a, h⟩ ↦ ⟨⟨a, h⟩⟩
#align nonempty_subtype nonempty_subtype

@[simp]
theorem nonempty_pprod {α β} : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ ↦ ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ ↦ ⟨⟨a, b⟩⟩
#align nonempty_pprod nonempty_pprod

@[simp]
theorem nonempty_psum {α β} : Nonempty (PSum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ ↦
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h ↦
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩
#align nonempty_psum nonempty_psum

@[simp]
theorem nonempty_plift {α} : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨⟨a⟩⟩
#align nonempty_plift nonempty_plift

/-- Using `Classical.choice`, lifts a (`Prop`-valued) `Nonempty` instance to a (`Type`-valued)
  `Inhabited` instance. `Classical.inhabited_of_nonempty` already exists, in
  `Init/Classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
noncomputable def Classical.inhabited_of_nonempty' {α} [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩
#align classical.inhabited_of_nonempty' Classical.inhabited_of_nonempty'

/-- Using `Classical.choice`, extracts a term from a `Nonempty` type. -/
protected noncomputable abbrev Nonempty.some {α} (h : Nonempty α) : α :=
  Classical.choice h
#align nonempty.some Nonempty.some

/-- Using `Classical.choice`, extracts a term from a `Nonempty` type. -/
protected noncomputable abbrev Classical.arbitrary (α) [h : Nonempty α] : α :=
  Classical.choice h
#align classical.arbitrary Classical.arbitrary

/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `Nonempty` cannot be a `functor`, because `Functor` is restricted to `Type`. -/
theorem Nonempty.map {α β} (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩
#align nonempty.map Nonempty.map

protected theorem Nonempty.map2 {α β γ : Sort*} (f : α → β → γ) :
    Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩
#align nonempty.map2 Nonempty.map2

protected theorem Nonempty.congr {α β} (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩
#align nonempty.congr Nonempty.congr

theorem Nonempty.elim_to_inhabited {α : Sort*} [h : Nonempty α] {p : Prop} (f : Inhabited α → p) :
    p :=
  h.elim <| f ∘ Inhabited.mk
#align nonempty.elim_to_inhabited Nonempty.elim_to_inhabited

protected instance Prod.instNonempty {α β} [h : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  h.elim fun g ↦ h2.elim fun g2 ↦ ⟨⟨g, g2⟩⟩

protected instance Pi.instNonempty {ι : Sort*} {α : ι → Sort*} [∀ i, Nonempty (α i)] :
    Nonempty (∀ i, α i) :=
  ⟨fun _ ↦ Classical.arbitrary _⟩

theorem Classical.nonempty_pi {ι} {α : ι → Sort*} : Nonempty (∀ i, α i) ↔ ∀ i, Nonempty (α i) :=
  ⟨fun ⟨f⟩ a ↦ ⟨f a⟩, @Pi.instNonempty _ _⟩
#align classical.nonempty_pi Classical.nonempty_pi

theorem subsingleton_of_not_nonempty {α : Sort*} (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x ↦ False.elim <| not_nonempty_iff_imp_false.mp h x⟩
#align subsingleton_of_not_nonempty subsingleton_of_not_nonempty

theorem Function.Surjective.nonempty [h : Nonempty β] {f : α → β} (hf : Function.Surjective f) :
    Nonempty α :=
  let ⟨y⟩ := h
  let ⟨x, _⟩ := hf y
  ⟨x⟩
#align function.surjective.nonempty Function.Surjective.nonempty

end

section
variable {α β : Type*} {γ : α → Type*}

instance (priority := 20) Zero.instNonempty [Zero α] : Nonempty α :=
  ⟨0⟩

instance (priority := 20) One.instNonempty [One α] : Nonempty α :=
  ⟨1⟩

@[simp]
theorem nonempty_sigma : Nonempty (Σa : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ ↦ ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ ↦ ⟨⟨a, c⟩⟩
#align nonempty_sigma nonempty_sigma

@[simp]
theorem nonempty_sum : Nonempty (Sum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ ↦
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h ↦
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩
#align nonempty_sum nonempty_sum

@[simp]
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ ↦ ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ ↦ ⟨⟨a, b⟩⟩
#align nonempty_prod nonempty_prod

@[simp]
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ ↦ ⟨a⟩) fun ⟨a⟩ ↦ ⟨⟨a⟩⟩
#align nonempty_ulift nonempty_ulift

end
