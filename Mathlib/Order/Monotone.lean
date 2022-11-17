/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Order.Basic

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `monotone_on f s`: Same as `monotone f`, but for all `a, b ∈ s`.
* `antitone_on f s`: Same as `antitone f`, but for all `a, b ∈ s`.
* `strict_mono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `strict_anti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `strict_mono_on f s`: Same as `strict_mono f`, but for all `a, b ∈ s`.
* `strict_anti_on f s`: Same as `strict_anti f`, but for all `a, b ∈ s`.

## Main theorems

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strict_mono_nat_of_lt_succ`, `strict_mono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strict_anti_nat_of_succ_lt`, `strict_anti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `has_le α` or `has_lt α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `fin n`... To make that work, we need `succ_order α`
and `succ_archimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} {r : α → α → Prop}

section MonotoneDef

variable [Preorder α] [Preorder β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f a ≤ f b

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a ≤ b → f b ≤ f a

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a < f b

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b < f a

end MonotoneDef

/-! ### Monotonicity in function spaces -/

section Preorder

variable [Preorder α]

theorem Monotone.comp_le_comp_left
    [Preorder β] {f : β → α} {g h : γ → β} (hf : Monotone f) (le_gh : g ≤ h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) :=
  fun x => hf (le_gh x)

variable [Preorder γ]

theorem monotone_lam {f : α → β → γ} (hf : ∀ b, Monotone fun a => f a b) : Monotone f :=
  fun _ _ h b => hf b h

theorem monotone_app (f : β → α → γ) (b : β) (hf : Monotone fun a b => f b a) : Monotone (f b) :=
  fun _ _ h => hf h b

theorem antitone_lam {f : α → β → γ} (hf : ∀ b, Antitone fun a => f a b) : Antitone f :=
  fun _ _ h b => hf b h

theorem antitone_app (f : β → α → γ) (b : β) (hf : Antitone fun a b => f b a) : Antitone (f b) :=
  fun _ _ h => hf h b

end Preorder

theorem Function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, Preorder (α i)] (i : ι) :
    Monotone (Function.eval i : (∀ i, α i) → α i) := fun _ _ H => H i

/-! ### Monotonicity hierarchy -/


section Preorder

variable [Preorder α]

section Preorder

variable [Preorder β] {f : α → β} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/


theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b :=
  hf h

theorem Antitone.imp (hf : Antitone f) (h : a ≤ b) : f b ≤ f a :=
  hf h

theorem StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b :=
  hf h

theorem StrictAnti.imp (hf : StrictAnti f) (h : a < b) : f b < f a :=
  hf h

protected theorem Monotone.monotone_on (hf : Monotone f) (s : Set α) : MonotoneOn f s :=
  fun _ _ _ _ => hf.imp

protected theorem Antitone.antitone_on (hf : Antitone f) (s : Set α) : AntitoneOn f s :=
  fun _ _ _ _ => hf.imp

protected theorem StrictMono.strict_mono_on (hf : StrictMono f) (s : Set α) : StrictMonoOn f s :=
  fun _ _ _ _ => hf.imp

protected theorem StrictAnti.strict_anti_on (hf : StrictAnti f) (s : Set α) : StrictAntiOn f s :=
  fun _ _ _ _ => hf.imp

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β}

theorem Monotone.strict_mono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : StrictMono f :=
  fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne <| h₂ H

theorem Antitone.strict_anti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : StrictAnti f :=
  fun _ _ h => (h₁ h.le).lt_of_ne fun H => h.ne <| h₂ H.symm

end PartialOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {f : α → β} {s : Set α}

theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) hf⟩

theorem antitone_iff_forall_lt : Antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congr fun _ _ =>
    ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) hf⟩

theorem monotone_on_iff_forall_lt :
    MonotoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a ≤ f b :=
  ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) (hf ha hb)⟩

theorem antitone_on_iff_forall_lt :
    AntitoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f b ≤ f a :=
  ⟨fun hf _ ha _ hb h => hf ha hb h.le,
   fun hf _ ha _ hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).ge) (hf ha hb)⟩

-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected theorem StrictMonoOn.monotone_on (hf : StrictMonoOn f s) : MonotoneOn f s :=
  monotone_on_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le

protected theorem StrictAntiOn.antitone_on (hf : StrictAntiOn f s) : AntitoneOn f s :=
  antitone_on_iff_forall_lt.2 fun _ ha _ hb h => (hf ha hb h).le

protected theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  monotone_iff_forall_lt.2 fun _ _ h => (hf h).le

protected theorem StrictAnti.antitone (hf : StrictAnti f) : Antitone f :=
  antitone_iff_forall_lt.2 fun _ _ h => (hf h).le

end PartialOrder

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorder α] [Preorder β]

protected theorem monotone [Subsingleton α] (f : α → β) : Monotone f :=
  fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le

protected theorem antitone [Subsingleton α] (f : α → β) : Antitone f :=
  fun _ _ _ => (congr_arg _ <| Subsingleton.elim _ _).le

theorem monotone' [Subsingleton β] (f : α → β) : Monotone f :=
  fun _ _ _ => (Subsingleton.elim _ _).le

theorem antitone' [Subsingleton β] (f : α → β) : Antitone f :=
  fun _ _ _ => (Subsingleton.elim _ _).le

protected theorem strict_mono [Subsingleton α] (f : α → β) : StrictMono f :=
  fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim

protected theorem strict_anti [Subsingleton α] (f : α → β) : StrictAnti f :=
  fun _ _ h => (h.ne <| Subsingleton.elim _ _).elim

end Subsingleton

/-! ### Miscellaneous monotonicity results -/


theorem monotone_id [Preorder α] : Monotone (id : α → α) := fun _ _ => id

theorem monotone_on_id [Preorder α] {s : Set α} : MonotoneOn id s := fun _ _ _ _ => id

theorem strict_mono_id [Preorder α] : StrictMono (id : α → α) := fun _ _ => id

theorem strict_mono_on_id [Preorder α] {s : Set α} : StrictMonoOn id s := fun _ _ _ _ => id

theorem monotone_const [Preorder α] [Preorder β] {c : β} : Monotone fun _ : α => c :=
  fun _ _ _ => le_rfl

theorem monotone_on_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    MonotoneOn (fun _ : α => c) s :=
  fun _ _ _ _ _ => le_rfl

theorem antitone_const [Preorder α] [Preorder β] {c : β} : Antitone fun _ : α => c :=
  fun _ _ _ => le_refl c

theorem antitone_on_const [Preorder α] [Preorder β] {c : β} {s : Set α} :
    AntitoneOn (fun _ : α => c) s :=
  fun _ _ _ _ _ => le_rfl

theorem injective_of_le_imp_le
    [PartialOrder α] [Preorder β] (f : α → β) (h : ∀ {x y}, f x ≤ f y → x ≤ y) : Injective f :=
  fun _ _ hxy => (h hxy.le).antisymm (h hxy.ge)

/-! ### Monotonicity under composition -/


section Composition

variable [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}

protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) :=
  fun _ _ h => hg (hf h)

theorem Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘ f) :=
  fun _ _ h => hg (hf h)

protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) :=
  fun _ _ h => hg (hf h)

theorem Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘ f) :=
  fun _ _ h => hg (hf h)
