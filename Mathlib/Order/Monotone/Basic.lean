/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Compare
import Mathlib.Order.Max
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Choose

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

## Main theorems

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strictMono_nat_of_lt_succ`, `strictMono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strictAnti_nat_of_succ_lt`, `strictAnti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `LE α` or `LT α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `Preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `Fin n`... To make that work, we need `SuccOrder α`
and `IsSuccArchimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/


open Function OrderDual

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {π : ι → Type*}
  {r : α → α → Prop}

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

lemma monotone_inclusion_le_le_of_le [Preorder α] {k j : α} (hkj : k ≤ j) :
    Monotone (fun ⟨i, hi⟩ => ⟨i, hi.trans hkj⟩ : { i // i ≤ k } → { i // i ≤ j}) :=
  fun _ _ h => h

lemma monotone_inclusion_lt_le_of_le [Preorder α] {k j : α} (hkj : k ≤ j) :
    Monotone (fun ⟨i, hi⟩ => ⟨i, hi.le.trans hkj⟩ : { i // i < k } → { i // i ≤ j}) :=
  fun _ _ h => h

lemma monotone_inclusion_lt_lt_of_le [Preorder α] {k j : α} (hkj : k ≤ j) :
    Monotone (fun ⟨i, hi⟩ => ⟨i, lt_of_lt_of_le hi hkj⟩ : { i // i < k } → { i // i < j}) :=
  fun _ _ h => h

/-! ### Monotonicity on the dual order

Strictly, many of the `*On.dual` lemmas in this section should use `ofDual ⁻¹' s` instead of `s`,
but right now this is not possible as `Set.preimage` is not defined yet, and importing it creates
an import cycle.

Often, you should not need the rewriting lemmas. Instead, you probably want to add `.dual`,
`.dual_left` or `.dual_right` to your `Monotone`/`Antitone` hypothesis.
-/


section OrderDual

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

@[simp]
theorem monotone_comp_ofDual_iff : Monotone (f ∘ ofDual) ↔ Antitone f :=
  forall_swap

@[simp]
theorem antitone_comp_ofDual_iff : Antitone (f ∘ ofDual) ↔ Monotone f :=
  forall_swap

-- Porting note:
-- Here (and below) without the type ascription, Lean is seeing through the
-- defeq `βᵒᵈ = β` and picking up the wrong `Preorder` instance.
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/logic.2Eequiv.2Ebasic.20mathlib4.23631/near/311744939
@[simp]
theorem monotone_toDual_comp_iff : Monotone (toDual ∘ f : α → βᵒᵈ) ↔ Antitone f :=
  Iff.rfl

@[simp]
theorem antitone_toDual_comp_iff : Antitone (toDual ∘ f : α → βᵒᵈ) ↔ Monotone f :=
  Iff.rfl

@[simp]
theorem monotoneOn_comp_ofDual_iff : MonotoneOn (f ∘ ofDual) s ↔ AntitoneOn f s :=
  forall₂_swap

@[simp]
theorem antitoneOn_comp_ofDual_iff : AntitoneOn (f ∘ ofDual) s ↔ MonotoneOn f s :=
  forall₂_swap

@[simp]
theorem monotoneOn_toDual_comp_iff : MonotoneOn (toDual ∘ f : α → βᵒᵈ) s ↔ AntitoneOn f s :=
  Iff.rfl

@[simp]
theorem antitoneOn_toDual_comp_iff : AntitoneOn (toDual ∘ f : α → βᵒᵈ) s ↔ MonotoneOn f s :=
  Iff.rfl

@[simp]
theorem strictMono_comp_ofDual_iff : StrictMono (f ∘ ofDual) ↔ StrictAnti f :=
  forall_swap

@[simp]
theorem strictAnti_comp_ofDual_iff : StrictAnti (f ∘ ofDual) ↔ StrictMono f :=
  forall_swap

@[simp]
theorem strictMono_toDual_comp_iff : StrictMono (toDual ∘ f : α → βᵒᵈ) ↔ StrictAnti f :=
  Iff.rfl

@[simp]
theorem strictAnti_toDual_comp_iff : StrictAnti (toDual ∘ f : α → βᵒᵈ) ↔ StrictMono f :=
  Iff.rfl

@[simp]
theorem strictMonoOn_comp_ofDual_iff : StrictMonoOn (f ∘ ofDual) s ↔ StrictAntiOn f s :=
  forall₂_swap

@[simp]
theorem strictAntiOn_comp_ofDual_iff : StrictAntiOn (f ∘ ofDual) s ↔ StrictMonoOn f s :=
  forall₂_swap

@[simp]
theorem strictMonoOn_toDual_comp_iff : StrictMonoOn (toDual ∘ f : α → βᵒᵈ) s ↔ StrictAntiOn f s :=
  Iff.rfl

@[simp]
theorem strictAntiOn_toDual_comp_iff : StrictAntiOn (toDual ∘ f : α → βᵒᵈ) s ↔ StrictMonoOn f s :=
  Iff.rfl

theorem monotone_dual_iff : Monotone (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ Monotone f := by
  rw [monotone_toDual_comp_iff, antitone_comp_ofDual_iff]

theorem antitone_dual_iff : Antitone (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ Antitone f := by
  rw [antitone_toDual_comp_iff, monotone_comp_ofDual_iff]

theorem monotoneOn_dual_iff : MonotoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ MonotoneOn f s := by
  rw [monotoneOn_toDual_comp_iff, antitoneOn_comp_ofDual_iff]

theorem antitoneOn_dual_iff : AntitoneOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ AntitoneOn f s := by
  rw [antitoneOn_toDual_comp_iff, monotoneOn_comp_ofDual_iff]

theorem strictMono_dual_iff : StrictMono (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ StrictMono f := by
  rw [strictMono_toDual_comp_iff, strictAnti_comp_ofDual_iff]

theorem strictAnti_dual_iff : StrictAnti (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) ↔ StrictAnti f := by
  rw [strictAnti_toDual_comp_iff, strictMono_comp_ofDual_iff]

theorem strictMonoOn_dual_iff :
    StrictMonoOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ StrictMonoOn f s := by
  rw [strictMonoOn_toDual_comp_iff, strictAntiOn_comp_ofDual_iff]

theorem strictAntiOn_dual_iff :
    StrictAntiOn (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ) s ↔ StrictAntiOn f s := by
  rw [strictAntiOn_toDual_comp_iff, strictMonoOn_comp_ofDual_iff]

alias ⟨_, Monotone.dual_left⟩ := antitone_comp_ofDual_iff

alias ⟨_, Antitone.dual_left⟩ := monotone_comp_ofDual_iff

alias ⟨_, Monotone.dual_right⟩ := antitone_toDual_comp_iff

alias ⟨_, Antitone.dual_right⟩ := monotone_toDual_comp_iff

alias ⟨_, MonotoneOn.dual_left⟩ := antitoneOn_comp_ofDual_iff

alias ⟨_, AntitoneOn.dual_left⟩ := monotoneOn_comp_ofDual_iff

alias ⟨_, MonotoneOn.dual_right⟩ := antitoneOn_toDual_comp_iff

alias ⟨_, AntitoneOn.dual_right⟩ := monotoneOn_toDual_comp_iff

alias ⟨_, StrictMono.dual_left⟩ := strictAnti_comp_ofDual_iff

alias ⟨_, StrictAnti.dual_left⟩ := strictMono_comp_ofDual_iff

alias ⟨_, StrictMono.dual_right⟩ := strictAnti_toDual_comp_iff

alias ⟨_, StrictAnti.dual_right⟩ := strictMono_toDual_comp_iff

alias ⟨_, StrictMonoOn.dual_left⟩ := strictAntiOn_comp_ofDual_iff

alias ⟨_, StrictAntiOn.dual_left⟩ := strictMonoOn_comp_ofDual_iff

alias ⟨_, StrictMonoOn.dual_right⟩ := strictAntiOn_toDual_comp_iff

alias ⟨_, StrictAntiOn.dual_right⟩ := strictMonoOn_toDual_comp_iff

alias ⟨_, Monotone.dual⟩ := monotone_dual_iff

alias ⟨_, Antitone.dual⟩ := antitone_dual_iff

alias ⟨_, MonotoneOn.dual⟩ := monotoneOn_dual_iff

alias ⟨_, AntitoneOn.dual⟩ := antitoneOn_dual_iff

alias ⟨_, StrictMono.dual⟩ := strictMono_dual_iff

alias ⟨_, StrictAnti.dual⟩ := strictAnti_dual_iff

alias ⟨_, StrictMonoOn.dual⟩ := strictMonoOn_dual_iff

alias ⟨_, StrictAntiOn.dual⟩ := strictAntiOn_dual_iff

end OrderDual

/-! ### Monotonicity in function spaces -/


section Preorder

variable [Preorder α]

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


theorem Monotone.imp (hf : Monotone f) (h : a ≤ b) : f a ≤ f b :=
  hf h

theorem Antitone.imp (hf : Antitone f) (h : a ≤ b) : f b ≤ f a :=
  hf h

theorem StrictMono.imp (hf : StrictMono f) (h : a < b) : f a < f b :=
  hf h

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

theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congr fun _ _ ↦
    ⟨fun hf h ↦ hf h.le, fun hf h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).le) hf⟩

theorem antitone_iff_forall_lt : Antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congr fun _ _ ↦
    ⟨fun hf h ↦ hf h.le, fun hf h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).ge) hf⟩

theorem monotoneOn_iff_forall_lt :
    MonotoneOn f s ↔ ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s), a < b → f a ≤ f b :=
  ⟨fun hf _ ha _ hb h ↦ hf ha hb h.le,
   fun hf _ ha _ hb h ↦ h.eq_or_lt.elim (fun H ↦ (congr_arg _ H).le) (hf ha hb)⟩

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

theorem strictMono_of_le_iff_le [Preorder α] [Preorder β] {f : α → β}
    (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : StrictMono f :=
  fun _ _ ↦ (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

theorem strictAnti_of_le_iff_le [Preorder α] [Preorder β] {f : α → β}
    (h : ∀ x y, x ≤ y ↔ f y ≤ f x) : StrictAnti f :=
  fun _ _ ↦ (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

-- Porting note: mathlib3 proof uses `contrapose` tactic
theorem injective_of_lt_imp_ne [LinearOrder α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
    Injective f := by
  intro x y hf
  rcases lt_trichotomy x y with (hxy | rfl | hxy)
  · exact absurd hf <| h _ _ hxy
  · rfl
  · exact absurd hf.symm <| h _ _ hxy

theorem injective_of_le_imp_le [PartialOrder α] [Preorder β] (f : α → β)
    (h : ∀ {x y}, f x ≤ f y → x ≤ y) : Injective f :=
  fun _ _ hxy ↦ (h hxy.le).antisymm (h hxy.ge)

section Preorder

variable [Preorder α] [Preorder β] {f g : α → β} {a : α}

theorem StrictMono.isMax_of_apply (hf : StrictMono f) (ha : IsMax (f a)) : IsMax a :=
  of_not_not fun h ↦
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMax ha

theorem StrictMono.isMin_of_apply (hf : StrictMono f) (ha : IsMin (f a)) : IsMin a :=
  of_not_not fun h ↦
    let ⟨_, hb⟩ := not_isMin_iff.1 h
    (hf hb).not_isMin ha

theorem StrictAnti.isMax_of_apply (hf : StrictAnti f) (ha : IsMin (f a)) : IsMax a :=
  of_not_not fun h ↦
    let ⟨_, hb⟩ := not_isMax_iff.1 h
    (hf hb).not_isMin ha

theorem StrictAnti.isMin_of_apply (hf : StrictAnti f) (ha : IsMax (f a)) : IsMin a :=
  of_not_not fun h ↦
    let ⟨_, hb⟩ := not_isMin_iff.1 h
    (hf hb).not_isMax ha

lemma StrictMono.add_le_nat {f : ℕ → ℕ} (hf : StrictMono f) (m n : ℕ) : m + f n ≤ f (m + n)  := by
  rw [Nat.add_comm m, Nat.add_comm m]
  induction m with
  | zero => rw [Nat.add_zero, Nat.add_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, ← Nat.add_assoc, Nat.succ_le]
    exact ih.trans_lt (hf (n + m).lt_succ_self)

protected theorem StrictMono.ite' (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop}
    [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
    StrictMono fun x ↦ if p x then f x else g x := by
  intro x y h
  by_cases hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
  by_cases hx : p x
  · simpa [hx, hy] using hfg hx hy h
  · simpa [hx, hy] using hg h

protected theorem StrictMono.ite (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop}
    [DecidablePred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) :
    StrictMono fun x ↦ if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h ↦ (hf h).trans_le (hfg y)

-- Porting note: `Strict*.dual_right` dot notation is not working here for some reason
protected theorem StrictAnti.ite' (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop}
    [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
    StrictAnti fun x ↦ if p x then f x else g x :=
  StrictMono.ite' (StrictAnti.dual_right hf) (StrictAnti.dual_right hg) hp hfg

protected theorem StrictAnti.ite (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop}
    [DecidablePred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) :
    StrictAnti fun x ↦ if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h ↦ (hfg y).trans_lt (hf h)

end Preorder

/-! ### Monotonicity under composition -/


section Composition

variable [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} {s : Set α}

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

end Composition

namespace List

section Fold

theorem foldl_monotone [Preorder α] {f : α → β → α} (H : ∀ b, Monotone fun a ↦ f a b)
    (l : List β) : Monotone fun a ↦ l.foldl f a :=
  List.recOn l (fun _ _ ↦ id) fun _ _ hl _ _ h ↦ hl (H _ h)

theorem foldr_monotone [Preorder β] {f : α → β → β} (H : ∀ a, Monotone (f a)) (l : List α) :
    Monotone fun b ↦ l.foldr f b := fun _ _ h ↦ List.recOn l h fun i _ hl ↦ H i hl

theorem foldl_strictMono [Preorder α] {f : α → β → α} (H : ∀ b, StrictMono fun a ↦ f a b)
    (l : List β) : StrictMono fun a ↦ l.foldl f a :=
  List.recOn l (fun _ _ ↦ id) fun _ _ hl _ _ h ↦ hl (H _ h)

theorem foldr_strictMono [Preorder β] {f : α → β → β} (H : ∀ a, StrictMono (f a)) (l : List α) :
    StrictMono fun b ↦ l.foldr f b := fun _ _ h ↦ List.recOn l h fun i _ hl ↦ H i hl

end Fold

end List

/-! ### Monotonicity in linear orders  -/


section LinearOrder

variable [LinearOrder α]

section Preorder

variable [Preorder β] {f : α → β} {s : Set α}

open Ordering

theorem Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' ↦ h.not_le (hf h')

theorem Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' ↦ h.not_le (hf h')

theorem MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : f a < f b) : a < b :=
  lt_of_not_ge fun h' ↦ h.not_le <| hf hb ha h'

theorem AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (h : f a < f b) : b < a :=
  lt_of_not_ge fun h' ↦ h.not_le <| hf ha hb h'

theorem StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a ≤ f b ↔ a ≤ b :=
  ⟨fun h ↦ le_of_not_gt fun h' ↦ (hf hb ha h').not_le h, fun h ↦
    h.lt_or_eq_dec.elim (fun h' ↦ (hf ha hb h').le) fun h' ↦ h' ▸ le_rfl⟩

theorem StrictAntiOn.le_iff_le (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a ≤ f b ↔ b ≤ a :=
  hf.dual_right.le_iff_le hb ha

theorem StrictMonoOn.eq_iff_eq (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b ↔ a = b :=
  ⟨fun h ↦ le_antisymm ((hf.le_iff_le ha hb).mp h.le) ((hf.le_iff_le hb ha).mp h.ge), by
    rintro rfl
    rfl⟩

theorem StrictAntiOn.eq_iff_eq (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a = f b ↔ b = a :=
  (hf.dual_right.eq_iff_eq ha hb).trans eq_comm

theorem StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a < f b ↔ a < b := by
  rw [lt_iff_le_not_le, lt_iff_le_not_le, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

theorem StrictAntiOn.lt_iff_lt (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a < f b ↔ b < a :=
  hf.dual_right.lt_iff_lt hb ha

theorem StrictMono.le_iff_le (hf : StrictMono f) {a b : α} : f a ≤ f b ↔ a ≤ b :=
  (hf.strictMonoOn Set.univ).le_iff_le trivial trivial

theorem StrictAnti.le_iff_le (hf : StrictAnti f) {a b : α} : f a ≤ f b ↔ b ≤ a :=
  (hf.strictAntiOn Set.univ).le_iff_le trivial trivial

theorem StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α} : f a < f b ↔ a < b :=
  (hf.strictMonoOn Set.univ).lt_iff_lt trivial trivial

theorem StrictAnti.lt_iff_lt (hf : StrictAnti f) {a b : α} : f a < f b ↔ b < a :=
  (hf.strictAntiOn Set.univ).lt_iff_lt trivial trivial

protected theorem StrictMonoOn.compares (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : ∀ {o : Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
  | Ordering.lt => hf.lt_iff_lt ha hb
  | Ordering.eq => ⟨fun h ↦ ((hf.le_iff_le ha hb).1 h.le).antisymm
                      ((hf.le_iff_le hb ha).1 h.symm.le), congr_arg _⟩
  | Ordering.gt => hf.lt_iff_lt hb ha

protected theorem StrictAntiOn.compares (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) {o : Ordering} : o.Compares (f a) (f b) ↔ o.Compares b a :=
  toDual_compares_toDual.trans <| hf.dual_right.compares hb ha

protected theorem StrictMono.compares (hf : StrictMono f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares a b :=
  (hf.strictMonoOn Set.univ).compares trivial trivial

protected theorem StrictAnti.compares (hf : StrictAnti f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  (hf.strictAntiOn Set.univ).compares trivial trivial

theorem StrictMono.injective (hf : StrictMono f) : Injective f :=
  fun x y h ↦ show Compares eq x y from hf.compares.1 h

theorem StrictAnti.injective (hf : StrictAnti f) : Injective f :=
  fun x y h ↦ show Compares eq x y from hf.compares.1 h.symm

theorem StrictMono.maximal_of_maximal_image (hf : StrictMono f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
    x ≤ a :=
  hf.le_iff_le.mp (hmax (f x))

theorem StrictMono.minimal_of_minimal_image (hf : StrictMono f) {a} (hmin : ∀ p, f a ≤ p) (x : α) :
    a ≤ x :=
  hf.le_iff_le.mp (hmin (f x))

theorem StrictAnti.minimal_of_maximal_image (hf : StrictAnti f) {a} (hmax : ∀ p, p ≤ f a) (x : α) :
    a ≤ x :=
  hf.le_iff_le.mp (hmax (f x))

theorem StrictAnti.maximal_of_minimal_image (hf : StrictAnti f) {a} (hmin : ∀ p, f a ≤ p) (x : α) :
    x ≤ a :=
  hf.le_iff_le.mp (hmin (f x))

end Preorder

section PartialOrder

variable [PartialOrder β] {f : α → β}

theorem Monotone.strictMono_iff_injective (hf : Monotone f) : StrictMono f ↔ Injective f :=
  ⟨fun h ↦ h.injective, hf.strictMono_of_injective⟩

theorem Antitone.strictAnti_iff_injective (hf : Antitone f) : StrictAnti f ↔ Injective f :=
  ⟨fun h ↦ h.injective, hf.strictAnti_of_injective⟩

/-- If a monotone function is equal at two points, it is equal between all of them -/
theorem Monotone.eq_of_le_of_le {a₁ a₂ : α} (h_mon : Monotone f) (h_fa : f a₁ = f a₂) {i : α}
    (h₁ : a₁ ≤ i) (h₂ : i ≤ a₂) : f i = f a₁ := by
  apply le_antisymm
  · rw [h_fa]; exact h_mon h₂
  · exact h_mon h₁

/-- If an antitone function is equal at two points, it is equal between all of them -/
theorem Antitone.eq_of_le_of_le {a₁ a₂ : α} (h_anti : Antitone f) (h_fa : f a₁ = f a₂) {i : α}
    (h₁ : a₁ ≤ i) (h₂ : i ≤ a₂) : f i = f a₁ := by
  apply le_antisymm
  · exact h_anti h₁
  · rw [h_fa]; exact h_anti h₂

end PartialOrder

variable [LinearOrder β] {f : α → β} {s : Set α} {x y : α}

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
lemma not_monotone_not_antitone_iff_exists_le_le :
    ¬ Monotone f ∧ ¬ Antitone f ↔
      ∃ a b c, a ≤ b ∧ b ≤ c ∧ ((f a < f b ∧ f c < f b) ∨ (f b < f a ∧ f b < f c)) := by
  simp_rw [Monotone, Antitone, not_forall, not_le]
  refine Iff.symm ⟨?_, ?_⟩
  · rintro ⟨a, b, c, hab, hbc, ⟨hfab, hfcb⟩ | ⟨hfba, hfbc⟩⟩
    exacts [⟨⟨_, _, hbc, hfcb⟩, _, _, hab, hfab⟩, ⟨⟨_, _, hab, hfba⟩, _, _, hbc, hfbc⟩]
  rintro ⟨⟨a, b, hab, hfba⟩, c, d, hcd, hfcd⟩
  obtain hda | had := le_total d a
  · obtain hfad | hfda := le_total (f a) (f d)
    · exact ⟨c, d, b, hcd, hda.trans hab, Or.inl ⟨hfcd, hfba.trans_le hfad⟩⟩
    · exact ⟨c, a, b, hcd.trans hda, hab, Or.inl ⟨hfcd.trans_le hfda, hfba⟩⟩
  obtain hac | hca := le_total a c
  · obtain hfdb | hfbd := le_or_lt (f d) (f b)
    · exact ⟨a, c, d, hac, hcd, Or.inr ⟨hfcd.trans <| hfdb.trans_lt hfba, hfcd⟩⟩
    obtain hfca | hfac := lt_or_le (f c) (f a)
    · exact ⟨a, c, d, hac, hcd, Or.inr ⟨hfca, hfcd⟩⟩
    obtain hbd | hdb := le_total b d
    · exact ⟨a, b, d, hab, hbd, Or.inr ⟨hfba, hfbd⟩⟩
    · exact ⟨a, d, b, had, hdb, Or.inl ⟨hfac.trans_lt hfcd, hfbd⟩⟩
  · obtain hfdb | hfbd := le_or_lt (f d) (f b)
    · exact ⟨c, a, b, hca, hab, Or.inl ⟨hfcd.trans <| hfdb.trans_lt hfba, hfba⟩⟩
    obtain hfca | hfac := lt_or_le (f c) (f a)
    · exact ⟨c, a, b, hca, hab, Or.inl ⟨hfca, hfba⟩⟩
    obtain hbd | hdb := le_total b d
    · exact ⟨a, b, d, hab, hbd, Or.inr ⟨hfba, hfbd⟩⟩
    · exact ⟨a, d, b, had, hdb, Or.inl ⟨hfac.trans_lt hfcd, hfbd⟩⟩

/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
lemma not_monotone_not_antitone_iff_exists_lt_lt :
    ¬ Monotone f ∧ ¬ Antitone f ↔ ∃ a b c, a < b ∧ b < c ∧
    (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp_rw [not_monotone_not_antitone_iff_exists_le_le, ← and_assoc]
  refine exists₃_congr (fun a b c ↦ and_congr_left <|
    fun h ↦ (Ne.le_iff_lt ?_).and <| Ne.le_iff_lt ?_) <;>
  (rintro rfl; simp at h)

/-!
### Strictly monotone functions and `cmp`
-/


theorem StrictMonoOn.cmp_map_eq (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    cmp (f x) (f y) = cmp x y :=
  ((hf.compares hx hy).2 (cmp_compares x y)).cmp_eq

theorem StrictMono.cmp_map_eq (hf : StrictMono f) (x y : α) : cmp (f x) (f y) = cmp x y :=
  (hf.strictMonoOn Set.univ).cmp_map_eq trivial trivial

theorem StrictAntiOn.cmp_map_eq (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    cmp (f x) (f y) = cmp y x :=
  hf.dual_right.cmp_map_eq hy hx

theorem StrictAnti.cmp_map_eq (hf : StrictAnti f) (x y : α) : cmp (f x) (f y) = cmp y x :=
  (hf.strictAntiOn Set.univ).cmp_map_eq trivial trivial

end LinearOrder

/-! ### Monotonicity in `ℕ` and `ℤ` -/


section Preorder

variable [Preorder α]

theorem Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b < c) :
    r (f b) (f c) := by
  induction hbc with
  | refl => exact h _ hab
  | step b_lt_k r_b_k => exact _root_.trans r_b_k (h _ (hab.trans_lt b_lt_k).le)

theorem Nat.rel_of_forall_rel_succ_of_le_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r]
    {f : ℕ → β} {a : ℕ} (h : ∀ n, a ≤ n → r (f n) (f (n + 1)))
    ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b ≤ c) : r (f b) (f c) :=
  hbc.eq_or_lt.elim (fun h ↦ h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)

theorem Nat.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a < b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ ↦ h n) le_rfl hab

theorem Nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ ↦ h n) le_rfl hab

theorem monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

theorem antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  @monotone_nat_of_le_succ αᵒᵈ _ _ hf

theorem strictMono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf

theorem strictAnti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  @strictMono_nat_of_lt_succ αᵒᵈ _ f hf

namespace Nat

/-- If `α` is a preorder with no maximal elements, then there exists a strictly monotone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strictMono' [NoMaxOrder α] (a : α) : ∃ f : ℕ → α, StrictMono f ∧ f 0 = a := by
  choose g hg using fun x : α ↦ exists_gt x
  exact ⟨fun n ↦ Nat.recOn n a fun _ ↦ g, strictMono_nat_of_lt_succ fun n ↦ hg _, rfl⟩

/-- If `α` is a preorder with no maximal elements, then there exists a strictly antitone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strictAnti' [NoMinOrder α] (a : α) : ∃ f : ℕ → α, StrictAnti f ∧ f 0 = a :=
  exists_strictMono' (OrderDual.toDual a)

variable (α)

/-- If `α` is a nonempty preorder with no maximal elements, then there exists a strictly monotone
function `ℕ → α`. -/
theorem exists_strictMono [Nonempty α] [NoMaxOrder α] : ∃ f : ℕ → α, StrictMono f :=
  let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, _⟩ := exists_strictMono' a
  ⟨f, hf⟩

/-- If `α` is a nonempty preorder with no minimal elements, then there exists a strictly antitone
function `ℕ → α`. -/
theorem exists_strictAnti [Nonempty α] [NoMinOrder α] : ∃ f : ℕ → α, StrictAnti f :=
  exists_strictMono αᵒᵈ

end Nat

theorem Int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) := by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction n with
  | zero => rw [Int.ofNat_one]; apply h
  | succ n ihn => rw [Int.ofNat_succ, ← Int.add_assoc]; exact _root_.trans ihn (h _)

theorem Int.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  hab.eq_or_lt.elim (fun h ↦ h ▸ refl _) fun h' ↦ Int.rel_of_forall_rel_succ_of_lt r h h'

theorem monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

theorem antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≥ ·) hf

theorem strictMono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf

theorem strictAnti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

namespace Int

variable (α)
variable [Nonempty α] [NoMinOrder α] [NoMaxOrder α]

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
monotone function `f : ℤ → α`. -/
theorem exists_strictMono : ∃ f : ℤ → α, StrictMono f := by
  inhabit α
  rcases Nat.exists_strictMono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strictAnti' (default : α) with ⟨g, hg, hg₀⟩
  refine ⟨fun n ↦ Int.casesOn n f fun n ↦ g (n + 1), strictMono_int_of_lt_succ ?_⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
  · show g 1 < f 0
    rw [hf₀, ← hg₀]
    exact hg Nat.zero_lt_one
  · exact hg (Nat.lt_succ_self _)

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
antitone function `f : ℤ → α`. -/
theorem exists_strictAnti : ∃ f : ℤ → α, StrictAnti f :=
  exists_strictMono αᵒᵈ

end Int

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Monotone f) (n : ℕ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Nat.le_of_lt_succ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitone f) (n : ℕ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Nat.le_of_lt_succ <| hf.reflect_lt h1)

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotone f) (n : ℤ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Int.le_of_lt_add_one <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitone f) (n : ℤ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Int.le_of_lt_add_one <| hf.reflect_lt h1)

theorem StrictMono.id_le {φ : ℕ → ℕ} (h : StrictMono φ) : ∀ n, n ≤ φ n := fun n ↦
  Nat.recOn n (Nat.zero_le _) fun n hn ↦ Nat.succ_le_of_lt (hn.trans_lt <| h <| Nat.lt_succ_self n)

end Preorder

theorem Subtype.mono_coe [Preorder α] (t : Set α) : Monotone ((↑) : Subtype t → α) :=
  fun _ _ ↦ id

theorem Subtype.strictMono_coe [Preorder α] (t : Set α) :
    StrictMono ((↑) : Subtype t → α) :=
  fun _ _ ↦ id

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ} {a b : α}

theorem monotone_fst : Monotone (@Prod.fst α β) := fun _ _ ↦ And.left

theorem monotone_snd : Monotone (@Prod.snd α β) := fun _ _ ↦ And.right

theorem Monotone.prod_map (hf : Monotone f) (hg : Monotone g) : Monotone (Prod.map f g) :=
  fun _ _ h ↦ ⟨hf h.1, hg h.2⟩

theorem Antitone.prod_map (hf : Antitone f) (hg : Antitone g) : Antitone (Prod.map f g) :=
  fun _ _ h ↦ ⟨hf h.1, hg h.2⟩

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] [Preorder γ] [Preorder δ] {f : α → γ} {g : β → δ}

theorem StrictMono.prod_map (hf : StrictMono f) (hg : StrictMono g) : StrictMono (Prod.map f g) :=
  fun a b ↦ by
  simp only [Prod.lt_iff]
  exact Or.imp (And.imp hf.imp hg.monotone.imp) (And.imp hf.monotone.imp hg.imp)

theorem StrictAnti.prod_map (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti (Prod.map f g) :=
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
variable {ι α : Type*} {β : ι → Type*} [∀ i, Preorder (β i)] [Preorder α] {f : α → ∀ i, β i}

lemma monotone_iff_apply₂ : Monotone f ↔ ∀ i, Monotone (f · i) := by
  simp [Monotone, Pi.le_def, @forall_swap ι]

lemma antitone_iff_apply₂ : Antitone f ↔ ∀ i, Antitone (f · i) := by
  simp [Antitone, Pi.le_def, @forall_swap ι]

alias ⟨Monotone.apply₂, Monotone.of_apply₂⟩ := monotone_iff_apply₂
alias ⟨Antitone.apply₂, Antitone.of_apply₂⟩ := antitone_iff_apply₂

end apply
