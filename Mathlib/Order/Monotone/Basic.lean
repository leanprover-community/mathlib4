/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Compare
import Mathlib.Order.Max
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Choose

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

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

section WellFounded

variable [Preorder α] [Preorder β] {f : α → β}

theorem StrictMono.wellFoundedLT [WellFoundedLT β] (hf : StrictMono f) : WellFoundedLT α :=
  Subrelation.isWellFounded (InvImage (· < ·) f) @hf

theorem StrictAnti.wellFoundedLT [WellFoundedGT β] (hf : StrictAnti f) : WellFoundedLT α :=
  StrictMono.wellFoundedLT (β := βᵒᵈ) hf

theorem StrictMono.wellFoundedGT [WellFoundedGT β] (hf : StrictMono f) : WellFoundedGT α :=
  StrictMono.wellFoundedLT (α := αᵒᵈ) (β := βᵒᵈ) (fun _ _ h ↦ hf h)

theorem StrictAnti.wellFoundedGT [WellFoundedLT β] (hf : StrictAnti f) : WellFoundedGT α :=
  StrictMono.wellFoundedLT (α := αᵒᵈ) (fun _ _ h ↦ hf h)

end WellFounded

/-! ### Miscellaneous monotonicity results -/

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

protected theorem StrictAnti.ite' (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop}
    [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
    StrictAnti fun x ↦ if p x then f x else g x :=
  StrictMono.ite' hf.dual_right hg.dual_right hp hfg

protected theorem StrictAnti.ite (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop}
    [DecidablePred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) :
    StrictAnti fun x ↦ if p x then f x else g x :=
  (hf.ite' hg hp) fun _ y _ _ h ↦ (hfg y).trans_lt (hf h)

end Preorder

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

theorem StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    f a ≤ f b ↔ a ≤ b :=
  ⟨fun h ↦ le_of_not_gt fun h' ↦ (hf hb ha h').not_ge h, fun h ↦
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
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

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

lemma StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn f := fun x hx y hy hxy ↦
  show Ordering.eq.Compares x y from (hf.compares hx hy).1 hxy

lemma StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn f := hf.dual_left.injOn

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
  · obtain hfdb | hfbd := le_or_gt (f d) (f b)
    · exact ⟨a, c, d, hac, hcd, Or.inr ⟨hfcd.trans <| hfdb.trans_lt hfba, hfcd⟩⟩
    obtain hfca | hfac := lt_or_ge (f c) (f a)
    · exact ⟨a, c, d, hac, hcd, Or.inr ⟨hfca, hfcd⟩⟩
    obtain hbd | hdb := le_total b d
    · exact ⟨a, b, d, hab, hbd, Or.inr ⟨hfba, hfbd⟩⟩
    · exact ⟨a, d, b, had, hdb, Or.inl ⟨hfac.trans_lt hfcd, hfbd⟩⟩
  · obtain hfdb | hfbd := le_or_gt (f d) (f b)
    · exact ⟨c, a, b, hca, hab, Or.inl ⟨hfcd.trans <| hfdb.trans_lt hfba, hfba⟩⟩
    obtain hfca | hfac := lt_or_ge (f c) (f a)
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

theorem exists_strictMono_subsequence {P : ℕ → Prop} (h : ∀ N, ∃ n > N, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  have : NoMaxOrder {n // P n} :=
    ⟨fun n ↦ Exists.intro ⟨(h n.1).choose, (h n.1).choose_spec.2⟩ (h n.1).choose_spec.1⟩
  obtain ⟨f, hf, _⟩ := Nat.exists_strictMono' (⟨(h 0).choose, (h 0).choose_spec.2⟩ : {n // P n})
  exact Exists.intro (fun n ↦ (f n).1) ⟨hf, fun n ↦ (f n).2⟩

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

lemma pow_self_mono : Monotone fun n : ℕ ↦ n ^ n := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [Nat.pow_succ]
  exact (Nat.pow_le_pow_left n.le_succ _).trans (Nat.le_mul_of_pos_right _ n.succ_pos)

lemma pow_monotoneOn : MonotoneOn (fun p : ℕ × ℕ ↦ p.1 ^ p.2) {p | p.1 ≠ 0} := fun _p _ _q hq hpq ↦
  (Nat.pow_le_pow_left hpq.1 _).trans (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hq) hpq.2)

lemma pow_self_strictMonoOn : StrictMonoOn (fun n : ℕ ↦ n ^ n) {n : ℕ | n ≠ 0} :=
  fun _m hm _n hn hmn ↦
    (Nat.pow_lt_pow_left hmn hm).trans_le (Nat.pow_le_pow_right (Nat.pos_iff_ne_zero.2 hn) hmn.le)

end Nat

theorem Int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) := by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction n with
  | zero => rw [Int.ofNat_one]; apply h
  | succ n ihn => rw [Int.natCast_succ, ← Int.add_assoc]; exact _root_.trans ihn (h _)

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
  exact (hf.reflect_lt h1).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitone f) (n : ℕ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Nat.le_of_lt_succ <| hf.reflect_lt h1)

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotone f) (n : ℤ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitone f) (n : ℤ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_ge (Int.le_of_lt_add_one <| hf.reflect_lt h1)

end Preorder

/-- A monotone function `f : ℕ → ℕ` bounded by `b`, which is constant after stabilising for the
first time, stabilises in at most `b` steps. -/
lemma Nat.stabilises_of_monotone {f : ℕ → ℕ} {b n : ℕ} (hfmono : Monotone f) (hfb : ∀ m, f m ≤ b)
    (hfstab : ∀ m, f m = f (m + 1) → f (m + 1) = f (m + 2)) (hbn : b ≤ n) : f n = f b := by
  obtain ⟨m, hmb, hm⟩ : ∃ m ≤ b, f m = f (m + 1) := by
    contrapose! hfb
    let rec strictMono : ∀ m ≤ b + 1, m ≤ f m
    | 0, _ => Nat.zero_le _
    | m + 1, hmb => (strictMono _ <| m.le_succ.trans hmb).trans_lt <| (hfmono m.le_succ).lt_of_ne <|
        hfb _ <| Nat.le_of_succ_le_succ hmb
    exact ⟨b + 1, strictMono _ le_rfl⟩
  replace key : ∀ k : ℕ, f (m + k) = f (m + k + 1) ∧ f (m + k) = f m := fun k =>
    Nat.rec ⟨hm, rfl⟩ (fun k ih => ⟨hfstab _ ih.1, ih.1.symm.trans ih.2⟩) k
  replace key : ∀ k ≥ m, f k = f m := fun k hk =>
    (congr_arg f (Nat.add_sub_of_le hk)).symm.trans (key (k - m)).2
  exact (key n (hmb.trans hbn)).trans (key b hmb).symm

/-- A bounded monotone function `ℕ → ℕ` converges. -/
lemma converges_of_monotone_of_bounded {f : ℕ → ℕ} (mono_f : Monotone f)
    {c : ℕ} (hc : ∀ n, f n ≤ c) : ∃ b N, ∀ n ≥ N, f n = b := by
  induction c with
  | zero => use 0, 0, fun n _ ↦ Nat.eq_zero_of_le_zero (hc n)
  | succ c ih =>
    by_cases h : ∀ n, f n ≤ c
    · exact ih h
    · push_neg at h; obtain ⟨N, hN⟩ := h
      replace hN : f N = c + 1 := by specialize hc N; omega
      use c + 1, N; intro n hn
      specialize mono_f hn; specialize hc n; omega

@[deprecated (since := "2024-11-27")]
alias Group.card_pow_eq_card_pow_card_univ_aux := Nat.stabilises_of_monotone

@[deprecated (since := "2024-11-27")]
alias Group.card_nsmul_eq_card_nsmulpow_card_univ_aux := Nat.stabilises_of_monotone
