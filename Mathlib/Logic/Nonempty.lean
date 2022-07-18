/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Tactic.NoMatch

/-!
# Nonempty types

This file proves a few extra facts about `Nonempty`, which is defined in core Lean.

## Main declarations

* `Nonempty.some`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` explicitly.
* `Classical.arbitrary`: Extracts a witness of nonemptiness using choice. Takes `Nonempty α` as an
  instance.
-/


theorem exists_true_iff_nonempty {α : Sort _} : (∃ _a : α, True) ↔ Nonempty α :=
  Iff.intro (fun ⟨a, _⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨a, trivial⟩

@[simp]
theorem nonempty_Prop : Nonempty p ↔ p :=
  Iff.intro (fun ⟨h⟩ => h) fun h => ⟨h⟩

theorem not_nonempty_iff_imp_false : ¬Nonempty α ↔ α → False :=
  ⟨fun h a => h ⟨a⟩, fun h ⟨a⟩ => h a⟩

@[simp]
theorem nonempty_sigma {γ : α → Type v} :
    Nonempty (Σ a : α, γ a) ↔ ∃ a : α, Nonempty (γ a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem nonempty_subtype {p : α → Prop} : Nonempty (Subtype p) ↔ ∃ a : α, p a :=
  Iff.intro (fun ⟨⟨a, h⟩⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a, h⟩⟩

@[simp]
theorem nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
theorem nonempty_pprod : Nonempty (PProd α β) ↔ Nonempty α ∧ Nonempty β :=
  Iff.intro (fun ⟨⟨a, b⟩⟩ => ⟨⟨a⟩, ⟨b⟩⟩) fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨⟨a, b⟩⟩

@[simp]
theorem nonempty_sum : Nonempty (Sum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | Sum.inl a => Or.inl ⟨a⟩
      | Sum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨Sum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨Sum.inr b⟩

@[simp]
theorem nonempty_psum : Nonempty (PSum α β) ↔ Nonempty α ∨ Nonempty β :=
  Iff.intro
    (fun ⟨h⟩ =>
      match h with
      | PSum.inl a => Or.inl ⟨a⟩
      | PSum.inr b => Or.inr ⟨b⟩)
    fun h =>
    match h with
    | Or.inl ⟨a⟩ => ⟨PSum.inl a⟩
    | Or.inr ⟨b⟩ => ⟨PSum.inr b⟩

@[simp]
theorem nonempty_psigma {β : α → Sort v} : Nonempty (PSigma β) ↔ ∃ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨⟨a, c⟩⟩ => ⟨a, ⟨c⟩⟩) fun ⟨a, ⟨c⟩⟩ => ⟨⟨a, c⟩⟩

@[simp]
theorem nonempty_empty : ¬Nonempty Empty := fun.

@[simp]
theorem nonempty_ulift : Nonempty (ULift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem nonempty_plift : Nonempty (PLift α) ↔ Nonempty α :=
  Iff.intro (fun ⟨⟨a⟩⟩ => ⟨a⟩) fun ⟨a⟩ => ⟨⟨a⟩⟩

@[simp]
theorem Nonempty.forall {p : Nonempty α → Prop} : (∀ h : Nonempty α, p h) ↔ ∀ a, p ⟨a⟩ :=
  Iff.intro (fun h _ => h _) fun h ⟨a⟩ => h a

@[simp]
theorem Nonempty.exists {p : Nonempty α → Prop} : (∃ h : Nonempty α, p h) ↔ ∃ a, p ⟨a⟩ :=
  Iff.intro (fun ⟨⟨a⟩, h⟩ => ⟨a, h⟩) fun ⟨a, h⟩ => ⟨⟨a⟩, h⟩

theorem Classical.nonempty_pi {β : α → Sort v} : Nonempty (∀ a : α, β a) ↔ ∀ a : α, Nonempty (β a) :=
  Iff.intro (fun ⟨f⟩ a => ⟨f a⟩) fun f => ⟨fun a => Classical.choice $ f a⟩

/-- Using `classical.choice`, lifts a (`Prop`-valued) `Nonempty` instance to a (`Type`-valued)
  `inhabited` instance. `classical.inhabited_of_nonempty` already exists, in
  `core/init/classical.lean`, but the assumption is not a type class argument,
  which makes it unsuitable for some applications. -/
noncomputable def Classical.inhabitedOfNonempty' [h : Nonempty α] : Inhabited α :=
  ⟨Classical.choice h⟩

/-- Using `classical.choice`, extracts a term from a `Nonempty` type. -/
@[reducible]
protected noncomputable def Nonempty.some (h : Nonempty α) : α :=
  Classical.choice h

/-- Using `classical.choice`, extracts a term from a `Nonempty` type. -/
@[reducible]
protected noncomputable def Classical.arbitrary α [h : Nonempty α] : α :=
  Classical.choice h

/-- Given `f : α → β`, if `α` is nonempty then `β` is also nonempty.
  `Nonempty` cannot be a `functor`, because `functor` is restricted to `Type`. -/
theorem Nonempty.map (f : α → β) : Nonempty α → Nonempty β
  | ⟨h⟩ => ⟨f h⟩

protected theorem Nonempty.map2 (f : α → β → γ) : Nonempty α → Nonempty β → Nonempty γ
  | ⟨x⟩, ⟨y⟩ => ⟨f x y⟩

protected theorem Nonempty.congr (f : α → β) (g : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map f, Nonempty.map g⟩

theorem Nonempty.elim_to_inhabited [h : Nonempty α] {p : Prop} (f : Inhabited α → p) : p :=
  h.elim $ f ∘ Inhabited.mk

instance [h : Nonempty α] [h2 : Nonempty β] : Nonempty (α × β) :=
  h.elim $ fun g => h2.elim $ fun g2 => ⟨⟨g, g2⟩⟩

theorem subsingleton_of_not_nonempty (h : ¬Nonempty α) : Subsingleton α :=
  ⟨fun x => False.elim $ not_nonempty_iff_imp_false.mp h x⟩

instance {β : α → Sort v} [∀ a, Nonempty (β a)] : Nonempty (∀ a, β a) :=
  ⟨fun _ => Classical.arbitrary _⟩
