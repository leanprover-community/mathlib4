/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Coe

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `Monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `Antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `MonotoneOn f s`: Same as `Monotone f`, but for all `a, b ∈ s`.
* `AntitoneOn f s`: Same as `Antitone f`, but for all `a, b ∈ s`.
* `StrictMono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `StrictAnti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `StrictMonoOn f s`: Same as `StrictMono f`, but for all `a, b ∈ s`.
* `StrictAntiOn f s`: Same as `StrictAnti f`, but for all `a, b ∈ s`.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists Nat.instLinearOrder Int.instLinearOrder


open Function

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {π : ι → Type*}

section MonotoneDef

variable [Preorder α] [Preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

to_dual_insert_cast Monotone := forall_comm.eq

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

to_dual_insert_cast Antitone := forall_comm.eq

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b

to_dual_insert_cast MonotoneOn := by grind only

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a

to_dual_insert_cast AntitoneOn := by grind only

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

to_dual_insert_cast StrictMono := forall_comm.eq

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a

to_dual_insert_cast StrictAnti := forall_comm.eq

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a < f b

to_dual_insert_cast StrictMonoOn := by grind only

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b < f a

to_dual_insert_cast StrictAntiOn := by grind only

end MonotoneDef

section Decidable

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

instance [i : Decidable (∀ a b, a ≤ b → f a ≤ f b)] : Decidable (Monotone f) := i
instance [i : Decidable (∀ a b, a ≤ b → f b ≤ f a)] : Decidable (Antitone f) := i

instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a ≤ b → f a ≤ f b)] :
    Decidable (MonotoneOn f s) := i

instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a ≤ b → f b ≤ f a)] :
    Decidable (AntitoneOn f s) := i

instance [i : Decidable (∀ a b, a < b → f a < f b)] : Decidable (StrictMono f) := i
instance [i : Decidable (∀ a b, a < b → f b < f a)] : Decidable (StrictAnti f) := i

instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a < b → f a < f b)] :
    Decidable (StrictMonoOn f s) := i

instance [i : Decidable (∀ a ∈ s, ∀ b ∈ s, a < b → f b < f a)] :
    Decidable (StrictAntiOn f s) := i

end Decidable

/-! ### Monotonicity in function spaces -/


section Preorder

variable [Preorder α]

@[to_dual self]
theorem Monotone.comp_le_comp_left
    [Preorder β] {f : β → α} {g h : γ → β} (hf : Monotone f) (le_gh : g ≤ h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) :=
  fun x ↦ hf (le_gh x)

variable [Preorder γ]

theorem monotone_lam {f : α → β → γ} (hf : ∀ b, Monotone fun a ↦ f a b) : Monotone f :=
  fun _ _ h b ↦ hf b h

theorem monotone_app (f : β → α → γ) (b : β) (hf : Monotone fun a b ↦ f b a) : Monotone (f b) :=
  fun _ _ h ↦ hf h b

theorem antitone_lam {f : α → β → γ} (hf : ∀ b, Antitone fun a ↦ f a b) : Antitone f :=
  fun _ _ h b ↦ hf b h

theorem antitone_app (f : β → α → γ) (b : β) (hf : Antitone fun a b ↦ f b a) : Antitone (f b) :=
  fun _ _ h ↦ hf h b

end Preorder

theorem Function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] (i : ι) :
    Monotone (Function.eval i : (∀ i, α i) → α i) := fun _ _ H ↦ H i

/-! ### Monotonicity hierarchy -/


section Preorder

variable [Preorder α]

section Preorder

variable [Preorder β] {f : α → β} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `Monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/

@[to_dual self]
theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b :=
  hf h

@[to_dual self]
theorem Antitone.imp (hf : Antitone f) (h : a ≤ b) : f b ≤ f a :=
  hf h

@[to_dual self]
theorem StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b :=
  hf h

@[to_dual self]
theorem StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f a :=
  hf h

protected theorem Monotone.monotoneOn (hf : Monotone f) (s : Set α) : MonotoneOn f s :=
  fun _ _ _ _ ↦ hf.imp

protected theorem Antitone.antitoneOn (hf : Antitone f) (s : Set α) : AntitoneOn f s :=
  fun _ _ _ _ ↦ hf.imp

@[simp] theorem monotoneOn_univ : MonotoneOn f Set.univ ↔ Monotone f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.monotoneOn _⟩

@[simp] theorem antitoneOn_univ : AntitoneOn f Set.univ ↔ Antitone f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.antitoneOn _⟩

protected theorem StrictMono.strictMonoOn (hf : StrictMono f) (s : Set α) : StrictMonoOn f s :=
  fun _ _ _ _ ↦ hf.imp

protected theorem StrictAnti.strictAntiOn (hf : StrictAnti f) (s : Set α) : StrictAntiOn f s :=
  fun _ _ _ _ ↦ hf.imp

@[simp] theorem strictMonoOn_univ : StrictMonoOn f Set.univ ↔ StrictMono f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.strictMonoOn _⟩

@[simp] theorem strictAntiOn_univ : StrictAntiOn f Set.univ ↔ StrictAnti f :=
  ⟨fun h _ _ ↦ h trivial trivial, fun h ↦ h.strictAntiOn _⟩

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β}

theorem Monotone.strictMono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : StrictMono f :=
  fun _ _ h ↦ (h₁ h.le).lt_of_ne fun H ↦ h.ne <| h₂ H

theorem Antitone.strictAnti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : StrictAnti f :=
  fun _ _ h ↦ (h₁ h.le).lt_of_ne fun H ↦ h.ne <| h₂ H.symm

end PartialOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {f : α → β} {s : Set α}

@[to_dual none]
theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congr fun _ _ ↦
    ⟨fun hf h ↦ hf h.le, fun hf h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).le) hf⟩

@[to_dual none]
theorem antitone_iff_forall_lt : Antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congr fun _ _ ↦
    ⟨fun hf h ↦ hf h.le, fun hf h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).ge) hf⟩

@[to_dual none]
theorem monotoneOn_iff_forall_lt :
    MonotoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a ≤ f b :=
  ⟨fun hf _ ha _ hb h ↦ hf ha hb h.le,
   fun hf _ ha _ hb h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).le) (hf ha hb)⟩

@[to_dual none]
theorem antitoneOn_iff_forall_lt :
    AntitoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b ≤ f a :=
  ⟨fun hf _ ha _ hb h ↦ hf ha hb h.le,
   fun hf _ ha _ hb h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).ge) (hf ha hb)⟩

-- `Preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `StrictMono f` is vacuously true.
protected theorem StrictMonoOn.monotoneOn (hf : StrictMonoOn f s) : MonotoneOn f s :=
  monotoneOn_iff_forall_lt.2 fun _ ha _ hb h ↦ (hf ha hb h).le

protected theorem StrictAntiOn.antitoneOn (hf : StrictAntiOn f s) : AntitoneOn f s :=
  antitoneOn_iff_forall_lt.2 fun _ ha _ hb h ↦ (hf ha hb h).le

protected theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  monotone_iff_forall_lt.2 fun _ _ h ↦ (hf h).le

protected theorem StrictAnti.antitone (hf : StrictAnti f) : Antitone f :=
  antitone_iff_forall_lt.2 fun _ _ h ↦ (hf h).le

end PartialOrder

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorder α] [Preorder β]

protected theorem monotone [Subsingleton α] (f : α → β) : Monotone f :=
  fun _ _ _ ↦ (congr_arg _ <| Subsingleton.elim _ _).le

protected theorem antitone [Subsingleton α] (f : α → β) : Antitone f :=
  fun _ _ _ ↦ (congr_arg _ <| Subsingleton.elim _ _).le

theorem monotone' [Subsingleton β] (f : α → β) : Monotone f :=
  fun _ _ _ ↦ (Subsingleton.elim _ _).le

theorem antitone' [Subsingleton β] (f : α → β) : Antitone f :=
  fun _ _ _ ↦ (Subsingleton.elim _ _).le

protected theorem strictMono [Subsingleton α] (f : α → β) : StrictMono f :=
  fun _ _ h ↦ (h.ne <| Subsingleton.elim _ _).elim

protected theorem strictAnti [Subsingleton α] (f : α → β) : StrictAnti f :=
  fun _ _ h ↦ (h.ne <| Subsingleton.elim _ _).elim

end Subsingleton

/-! ### Miscellaneous monotonicity results -/


theorem monotone_id [Preorder α] : Monotone (id : α → α) := fun _ _ ↦ id

theorem monotoneOn_id [Preorder α] {s : Set α} : MonotoneOn id s := fun _ _ _ _ ↦ id

theorem strictMono_id [Preorder α] : StrictMono (id : α → α) := fun _ _ ↦ id

theorem strictMonoOn_id [Preorder α] {s : Set α} : StrictMonoOn id s := fun _ _ _ _ ↦ id

theorem monotone_const [Preorder α] [Preorder β] {c : β} : Monotone fun _ : α ↦ c :=
  fun _ _ _ ↦ le_rfl

theorem monotoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    MonotoneOn (fun _ : α ↦ c) s :=
  fun _ _ _ _ _ ↦ le_rfl

theorem antitone_const [Preorder α] [Preorder β] {c : β} : Antitone fun _ : α ↦ c :=
  fun _ _ _ ↦ le_refl c

theorem antitoneOn_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    AntitoneOn (fun _ : α ↦ c) s :=
  fun _ _ _ _ _ ↦ le_rfl

@[to_dual self]
theorem strictMono_of_le_iff_le [Preorder α] [Preorder β] {f : α → β}
    (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : StrictMono f :=
  fun _ _ ↦ (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

theorem strictAnti_of_le_iff_le [Preorder α] [Preorder β] {f : α → β}
    (h : ∀ x y, x ≤ y ↔ f y ≤ f x) : StrictAnti f :=
  fun _ _ ↦ (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

@[to_dual none]
theorem Function.Injective.of_lt_imp_ne [LinearOrder α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
    Injective f := by
  grind [Injective]

@[deprecated (since := "2025-12-23")]
alias injective_of_lt_imp_ne := Function.Injective.of_lt_imp_ne

theorem Function.Injective.of_eq_imp_le [PartialOrder α] {f : α → β}
    (h : ∀ {x y}, f x = f y → x ≤ y) : f.Injective :=
  fun _ _ hxy ↦ h hxy |>.antisymm <| h hxy.symm

@[deprecated Injective.of_eq_imp_le (since := "2025-12-23")]
theorem injective_of_le_imp_le [PartialOrder α] [Preorder β] (f : α → β)
    (h : ∀ {x y}, f x ≤ f y → x ≤ y) : Injective f :=
  .of_eq_imp_le (h ·.le)

/-! ### Monotonicity under composition -/


section Composition

variable [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α} {t : Set β}

protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

theorem Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

theorem Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

protected theorem Monotone.iterate {f : α → α} (hf : Monotone f) (n : ℕ) : Monotone f^[n] :=
  Nat.recOn n monotone_id fun _ h ↦ h.comp hf

protected theorem Monotone.comp_monotoneOn (hg : Monotone g) (hf : MonotoneOn f s) :
    MonotoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

theorem Monotone.comp_antitoneOn (hg : Monotone g) (hf : AntitoneOn f s) : AntitoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

protected theorem Antitone.comp_antitoneOn (hg : Antitone g) (hf : AntitoneOn f s) :
    MonotoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

theorem Antitone.comp_monotoneOn (hg : Antitone g) (hf : MonotoneOn f s) : AntitoneOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

protected theorem StrictMono.comp (hg : StrictMono g) (hf : StrictMono f) : StrictMono (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

theorem StrictMono.comp_strictAnti (hg : StrictMono g) (hf : StrictAnti f) : StrictAnti (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

protected theorem StrictAnti.comp (hg : StrictAnti g) (hf : StrictAnti f) : StrictMono (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

theorem StrictAnti.comp_strictMono (hg : StrictAnti g) (hf : StrictMono f) : StrictAnti (g ∘ f) :=
  fun _ _ h ↦ hg (hf h)

protected theorem StrictMono.iterate {f : α → α} (hf : StrictMono f) (n : ℕ) : StrictMono f^[n] :=
  Nat.recOn n strictMono_id fun _ h ↦ h.comp hf

protected theorem StrictMono.comp_strictMonoOn (hg : StrictMono g) (hf : StrictMonoOn f s) :
    StrictMonoOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

theorem StrictMono.comp_strictAntiOn (hg : StrictMono g) (hf : StrictAntiOn f s) :
    StrictAntiOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

protected theorem StrictAnti.comp_strictAntiOn (hg : StrictAnti g) (hf : StrictAntiOn f s) :
    StrictMonoOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

theorem StrictAnti.comp_strictMonoOn (hg : StrictAnti g) (hf : StrictMonoOn f s) :
    StrictAntiOn (g ∘ f) s :=
  fun _ ha _ hb h ↦ hg (hf ha hb h)

lemma MonotoneOn.comp (hg : MonotoneOn g t) (hf : MonotoneOn f s) (hs : Set.MapsTo f s t) :
    MonotoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hx) (hs hy) <| hf hx hy hxy

lemma MonotoneOn.comp_AntitoneOn (hg : MonotoneOn g t) (hf : AntitoneOn f s)
    (hs : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hy) (hs hx) <| hf hx hy hxy

lemma AntitoneOn.comp (hg : AntitoneOn g t) (hf : AntitoneOn f s) (hs : Set.MapsTo f s t) :
    MonotoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hy) (hs hx) <| hf hx hy hxy

lemma AntitoneOn.comp_MonotoneOn (hg : AntitoneOn g t) (hf : MonotoneOn f s)
    (hs : Set.MapsTo f s t) : AntitoneOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hx) (hs hy) <| hf hx hy hxy

lemma StrictMonoOn.comp (hg : StrictMonoOn g t) (hf : StrictMonoOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hx) (hs hy) <| hf hx hy hxy

lemma StrictMonoOn.comp_strictAntiOn (hg : StrictMonoOn g t) (hf : StrictAntiOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hy) (hs hx) <| hf hx hy hxy

lemma StrictAntiOn.comp (hg : StrictAntiOn g t) (hf : StrictAntiOn f s) (hs : Set.MapsTo f s t) :
    StrictMonoOn (g ∘ f) s := fun _x hx _y hy hxy ↦ hg (hs hy) (hs hx) <| hf hx hy hxy

lemma StrictAntiOn.comp_strictMonoOn (hg : StrictAntiOn g t) (hf : StrictMonoOn f s)
    (hs : Set.MapsTo f s t) : StrictAntiOn (g ∘ f) s := fun _x hx _y hy hxy ↦
  hg (hs hx) (hs hy) <| hf hx hy hxy

end Composition

/-! ### Monotonicity in linear orders  -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α → β} {s : Set α}

open Ordering

@[to_dual self]
theorem Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' ↦ h.not_ge (hf h')

@[to_dual self]
theorem Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' ↦ h.not_ge (hf h')

@[to_dual self (reorder := a b, ha hb)]
theorem MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' ↦ h.not_ge <| hf hb ha h'

@[to_dual self (reorder := a b, ha hb)]
theorem AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' ↦ h.not_ge <| hf ha hb h'

end Preorder

end LinearOrder

theorem Subtype.mono_coe [Preorder α] (p : α → Prop) : Monotone ((↑) : Subtype p → α) :=
  fun _ _ ↦ id

theorem Subtype.strictMono_coe [Preorder α] (p : α → Prop) :
    StrictMono ((↑) : Subtype p → α) :=
  fun _ _ ↦ id

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ}

theorem monotone_fst : Monotone (@Prod.fst α β) := fun _ _ ↦ And.left

theorem monotone_snd : Monotone (@Prod.snd α β) := fun _ _ ↦ And.right

theorem monotone_prodMk_iff {f : γ → α} {g : γ → β} :
    Monotone (fun x => (f x, g x)) ↔ Monotone f ∧ Monotone g := by
  simp_rw [Monotone, Prod.mk_le_mk, forall_and]

theorem Monotone.prodMk {f : γ → α} {g : γ → β} (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun x => (f x, g x)) :=
  monotone_prodMk_iff.2 ⟨hf, hg⟩

theorem Monotone.prodMap (hf : Monotone f) (hg : Monotone g) : Monotone (Prod.map f g) :=
  fun _ _ h ↦ ⟨hf h.1, hg h.2⟩

theorem Antitone.prodMap (hf : Antitone f) (hg : Antitone g) : Antitone (Prod.map f g) :=
  fun _ _ h ↦ ⟨hf h.1, hg h.2⟩

lemma monotone_prod_iff {h : α × β → γ} :
    Monotone h ↔ (∀ a, Monotone (fun b => h (a, b))) ∧ (∀ b, Monotone (fun a => h (a, b))) where
  mp h := ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

lemma antitone_prod_iff {h : α × β → γ} :
    Antitone h ↔ (∀ a, Antitone (fun b => h (a, b))) ∧ (∀ b, Antitone (fun a => h (a, b))) where
  mp h := ⟨fun _ _ _ hab => h (Prod.mk_le_mk_iff_right.mpr hab),
    fun _ _ _ hab => h (Prod.mk_le_mk_iff_left.mpr hab)⟩
  mpr h _ _ hab := le_trans (h.1 _ (Prod.mk_le_mk.mp hab).2) (h.2 _ (Prod.mk_le_mk.mp hab).1)

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ}

theorem StrictMono.prodMap (hf : StrictMono f) (hg : StrictMono g) : StrictMono (Prod.map f g) :=
  fun a b ↦ by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)

theorem StrictAnti.prodMap (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti (Prod.map f g) :=
  fun a b ↦ by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.antitone.imp) (And.imp hf.antitone.imp hg.imp)

end PartialOrder

/-! ### Pi types -/

namespace Function

variable [Preorder α] [DecidableEq ι] [∀ i, Preorder (π i)] {f : ∀ i, π i} {i : ι}

-- Porting note: Dot notation breaks in `f.update i`
theorem update_mono : Monotone (update f i) := fun _ _ => update_le_update_iff'.2

theorem update_strictMono : StrictMono (update f i) := fun _ _ => update_lt_update_iff.2

theorem const_mono : Monotone (const β : α → β → α) := fun _ _ h _ ↦ h

theorem const_strictMono [Nonempty β] : StrictMono (const β : α → β → α) :=
  fun _ _ ↦ const_lt_const.2

end Function

section apply
variable {β : ι → Type*} [∀ i, Preorder (β i)] [Preorder α] {f : α → ∀ i, β i}

lemma monotone_iff_apply₂ : Monotone f ↔ ∀ i, Monotone (f · i) := by
  simp [Monotone, Pi.le_def, @forall_comm ι]

lemma antitone_iff_apply₂ : Antitone f ↔ ∀ i, Antitone (f · i) := by
  simp [Antitone, Pi.le_def, @forall_comm ι]

alias ⟨Monotone.apply₂, Monotone.of_apply₂⟩ := monotone_iff_apply₂
alias ⟨Antitone.apply₂, Antitone.of_apply₂⟩ := antitone_iff_apply₂

end apply
