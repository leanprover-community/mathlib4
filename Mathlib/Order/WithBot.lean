/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Nontrivial.Basic
public import Mathlib.Order.TypeTags
public import Mathlib.Data.Option.NAry
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Lift
public import Mathlib.Data.Option.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.BoundedOrder.Basic

/-!
# `WithBot`, `WithTop`

Adding a `bot` or a `top` to an order.

## Main declarations

* `With<Top/Bot> α`: Equips `Option α` with the order on `α` plus `none` as the top/bottom element.

-/

@[expose] public section

variable {α β γ δ : Type*}

namespace WithBot

variable {a b : α}

@[to_dual]
instance nontrivial [Nonempty α] : Nontrivial (WithBot α) :=
  inferInstanceAs <| Nontrivial (Option α)

@[to_dual]
instance [IsEmpty α] : Unique (WithBot α) :=
  inferInstanceAs <| Unique (Option α)

open Function

@[to_dual]
theorem coe_injective : Injective ((↑) : α → WithBot α) :=
  Option.some_injective _

@[to_dual (attr := simp, norm_cast)]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

@[to_dual]
protected theorem «forall» {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x :=
  Option.forall

@[to_dual]
protected theorem «exists» {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x :=
  Option.exists

@[to_dual]
theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl

@[to_dual]
theorem some_eq_coe (a : α) : (Option.some a : WithBot α) = (↑a : WithBot α) :=
  rfl

@[to_dual (attr := simp)]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  nofun

@[to_dual (attr := simp)]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  nofun

@[to_dual]
lemma isSome_iff_ne_none (x : WithBot α) : isSome x = true ↔ x ≠ ⊥ := by
  cases x
  · simp
  · simp

@[to_dual (attr := simp)]
theorem isSome_eq_false_iff {x : WithBot α} :
    x.isSome = false ↔ x = ⊥ := by
  cases x <;> simp

/-- Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries. -/
@[to_dual
/-- Specialization of `Option.getD` to values in `WithTop α` that respects API boundaries. -/]
def unbotD (d : α) (x : WithBot α) : α :=
  recBotCoe d id x

@[to_dual (attr := simp)]
theorem unbotD_bot {α} (d : α) : unbotD d ⊥ = d :=
  rfl

@[to_dual (attr := simp)]
theorem unbotD_coe {α} (d x : α) : unbotD d x = x :=
  rfl

@[to_dual]
theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b := coe_inj

@[to_dual]
theorem unbotD_eq_iff {d y : α} {x : WithBot α} : unbotD d x = y ↔ x = y ∨ x = ⊥ ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[to_dual (attr := simp)]
theorem unbotD_eq_self_iff {d : α} {x : WithBot α} : unbotD d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbotD_eq_iff]

@[to_dual]
theorem unbotD_eq_unbotD_iff {d : α} {x y : WithBot α} :
    unbotD d x = unbotD d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
  induction y <;> simp [unbotD_eq_iff, or_comm]

/-- Lift a map `f : α → β` to `WithBot α → WithBot β`. Implemented using `Option.map`. -/
@[to_dual
/-- Lift a map `f : α → β` to `WithTop α → WithTop β`. Implemented using `Option.map`. -/]
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f

@[to_dual (attr := simp)]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl

@[to_dual (attr := simp)]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[to_dual (attr := simp)]
lemma map_eq_bot_iff {f : α → β} {a : WithBot α} :
    map f a = ⊥ ↔ a = ⊥ := Option.map_eq_none_iff

@[to_dual]
theorem map_eq_some_iff {f : α → β} {y : β} {v : WithBot α} :
    WithBot.map f v = .some y ↔ ∃ x, v = .some x ∧ f x = y := Option.map_eq_some_iff

@[to_dual]
theorem some_eq_map_iff {f : α → β} {y : β} {v : WithBot α} :
    .some y = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = y := by
  cases v <;> simp [eq_comm]

@[to_dual (attr := simp)]
theorem map_id : map (id : α → α) = id :=
  Option.map_id

@[to_dual (attr := simp)]
theorem map_map (h : β → γ) (g : α → β) (a : WithBot α) : map h (map g a) = map (h ∘ g) a :=
  Option.map_map h g a

@[to_dual]
theorem comp_map (h : β → γ) (g : α → β) (x : WithBot α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[to_dual (attr := simp)]
theorem map_comp_map (f : α → β) (g : β → γ) :
    WithBot.map g ∘ WithBot.map f = WithBot.map (g ∘ f) :=
  Option.map_comp_map f g

@[to_dual]
theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

@[to_dual]
theorem map_injective {f : α → β} (Hf : Injective f) : Injective (WithBot.map f) :=
  Option.map_injective Hf

/-- The image of a binary function `f : α → β → γ` as a function
`WithBot α → WithBot β → WithBot γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_dual
/-- The image of a binary function `f : α → β → γ` as a function
`WithTop α → WithTop β → WithTop γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
def map₂ : (α → β → γ) → WithBot α → WithBot β → WithBot γ := Option.map₂

@[to_dual] lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl

@[to_dual (attr := simp)]
lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f ⊥ b = ⊥ := rfl
@[to_dual (attr := simp)]
lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a ⊥ = ⊥ := by cases a <;> rfl

@[to_dual (attr := simp)]
lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[to_dual (attr := simp)]
lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by cases a <;> rfl

@[to_dual (attr := simp)]
lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithBot α} {b : WithBot β} :
    map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := Option.map₂_eq_none_iff

/-- Sequencing of `WithBot` computations. -/
@[to_dual /-- Sequencing of `WithTop` computations. -/]
def bind (x : WithBot α) (f : α → WithBot β) : WithBot β := Option.bind x f

@[to_dual (attr := simp)]
lemma bind_bot (f : α → WithBot β) : bind ⊥ f = ⊥ := rfl

@[to_dual (attr := simp)]
lemma bind_some (x : α) (f : α → WithBot β) : bind x f = f x := rfl

@[to_dual]
lemma map_eq_bind (x : WithBot α) (f : α → β) :
    map f x = x.bind (fun y ↦ f y) := by
  cases x <;> simp

@[to_dual]
lemma ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x := Option.ne_none_iff_exists

@[to_dual]
lemma eq_bot_iff_forall_ne {x : WithBot α} : x = ⊥ ↔ ∀ a : α, ↑a ≠ x :=
  Option.eq_none_iff_forall_some_ne

@[to_dual]
theorem forall_ne_bot {p : WithBot α → Prop} : (∀ x ≠ ⊥, p x) ↔ ∀ x : α, p x := by
  simp [ne_bot_iff_exists]

@[to_dual]
theorem exists_ne_bot {p : WithBot α → Prop} : (∃ x ≠ ⊥, p x) ↔ ∃ x : α, p x := by
  simp [ne_bot_iff_exists]

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
@[to_dual
/-- Deconstruct a `x : WithTop α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/]
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α | (x : α), _ => x

@[to_dual (attr := simp)]
lemma coe_unbot : ∀ (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl

@[to_dual (attr := simp)]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl

@[to_dual (attr := simp)]
theorem unbot_dite {p : Prop} {_ : Decidable p} (b : p → α) (w) :
    (if h : p then some (b h) else ⊥).unbot w = b (by simpa using w) := by
  split
  · simp
  · exfalso
    simp at w
    contradiction

@[to_dual (attr := simp)]
theorem unbot_ite {p : Prop} {_ : Decidable p} (h) :
    (if p then some b else ⊥).unbot h = b := by
  simpa using unbot_dite (p := p) (fun _ => b) (by simpa using h)

@[to_dual (attr := simp)]
theorem unbot_dite' {p : Prop} {_ : Decidable p} (b : ¬ p → α) (w) :
    (if h : p then ⊥ else some (b h)).unbot w = b (by simpa using w) := by
  split
  · exfalso
    simp at w
    contradiction
  · simp

@[to_dual (attr := simp)]
theorem unbot_ite' {p : Prop} {_ : Decidable p} (h) :
    (if p then ⊥ else some b).unbot h = b := by
  simpa using unbot_dite' (p := p) (fun _ => b) (by simpa using h)

@[to_dual]
instance canLift : CanLift (WithBot α) α (↑) fun r => r ≠ ⊥ where
  prf x h := ⟨x.unbot h, coe_unbot _ _⟩

@[to_dual]
instance instTop [Top α] : Top (WithBot α) where
  top := (⊤ : α)

@[to_dual (attr := simp, norm_cast)]
lemma coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤ := rfl
@[to_dual (attr := simp, norm_cast)]
lemma coe_eq_top [Top α] {a : α} : (a : WithBot α) = ⊤ ↔ a = ⊤ := coe_eq_coe
@[to_dual (attr := simp, norm_cast)]
lemma top_eq_coe [Top α] {a : α} : ⊤ = (a : WithBot α) ↔ ⊤ = a := coe_eq_coe

@[to_dual]
theorem unbot_eq_iff {a : WithBot α} {b : α} (h : a ≠ ⊥) :
    a.unbot h = b ↔ a = b := by
  induction a
  · simpa using h rfl
  · simp

@[to_dual]
theorem eq_unbot_iff {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a = b.unbot h ↔ a = b := by
  induction b
  · simpa using h rfl
  · simp

@[to_dual]
theorem unbot_inj {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) :
    a.unbot ha = b.unbot hb ↔ a = b := by
  rw [unbot_eq_iff, coe_unbot]

/-- The equivalence between the non-bottom elements of `WithBot α` and `α`. -/
@[to_dual (attr := simps)
/-- The equivalence between the non-top elements of `WithTop α` and `α`. -/]
def _root_.Equiv.withBotSubtypeNe : {y : WithBot α // y ≠ ⊥} ≃ α where
  toFun := fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Function that sends an element of `WithBot α` to `α`,
with an arbitrary default value for `⊥`. -/
@[to_dual
/-- Function that sends an element of `WithTop α` to `α`,
with an arbitrary default value for `⊤`. -/]
noncomputable abbrev unbotA [Nonempty α] : WithBot α → α := unbotD (Classical.arbitrary α)

@[to_dual]
lemma unbotA_eq_unbot [Nonempty α] {a : WithBot α} (ha : a ≠ ⊥) : unbotA a = unbot a ha := by
  cases a with
  | bot => contradiction
  | coe a => simp

end WithBot

namespace Equiv

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithBot e`. -/
@[to_dual (attr := simps apply)
/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithTop e`. -/]
def withBotCongr (e : α ≃ β) : WithBot α ≃ WithBot β where
  toFun := WithBot.map e
  invFun := WithBot.map e.symm
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

attribute [grind =] withBotCongr_apply withTopCongr_apply

@[to_dual (attr := simp)]
theorem withBotCongr_refl : withBotCongr (Equiv.refl α) = Equiv.refl _ :=
  Equiv.ext <| congr_fun WithBot.map_id

@[to_dual (attr := simp, grind =)]
theorem withBotCongr_symm (e : α ≃ β) : withBotCongr e.symm = (withBotCongr e).symm :=
  rfl

@[to_dual (attr := simp)]
theorem withBotCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    withBotCongr (e₁.trans e₂) = (withBotCongr e₁).trans (withBotCongr e₂) := by
  ext x
  simp

end Equiv

-- TODO: do we really need to preserve the def-eq between `LE` on `WithBot` and `WithTop`
-- moving forward? See discussion here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Order.20dual.20tactic/near/562584912

section LE
variable [LE α]

/-- Auxiliary definition for the order on `WithBot`. -/
@[mk_iff le_def_aux]
protected inductive WithBot.LE : WithBot α → WithBot α → Prop
  | protected bot_le (x : WithBot α) : WithBot.LE ⊥ x
  | protected coe_le_coe {a b : α} : a ≤ b → WithBot.LE a b

/-- The order on `WithBot α`, defined by `⊥ ≤ y` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
instance (priority := 10) WithBot.instLE : LE (WithBot α) where le := WithBot.LE

/-- The order on `WithTop α`, defined by `x ≤ ⊤` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ b : α, y = ↑b → ∃ a : α, x = ↑a ∧ a ≤ b`,
see `le_iff_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[to_dual existing]
instance (priority := 10) WithTop.instLE : LE (WithTop α) where le a b := WithBot.LE (α := αᵒᵈ) b a

lemma WithBot.le_def {x y : WithBot α} : x ≤ y ↔ x = ⊥ ∨ ∃ a b : α, a ≤ b ∧ x = a ∧ y = b :=
  le_def_aux ..

@[to_dual existing le_def]
lemma WithTop.le_def' {x y : WithTop α} : x ≤ y ↔ y = ⊤ ∨ ∃ b a : α, a ≤ b ∧ y = b ∧ x = a :=
  WithBot.le_def

@[to_dual le_def']
lemma WithTop.le_def {x y : WithTop α} : x ≤ y ↔ y = ⊤ ∨ ∃ a b : α, a ≤ b ∧ x = a ∧ y = b := by
  grind [WithTop.le_def']

end LE

section LT
variable [LT α]

/-- Auxiliary definition for the order on `WithBot`. -/
@[mk_iff lt_def_aux]
protected inductive WithBot.LT [LT α] : WithBot α → WithBot α → Prop
  | protected bot_lt (b : α) : WithBot.LT ⊥ b
  | protected coe_lt_coe {a b : α} : a < b → WithBot.LT a b

/-- The order on `WithBot α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b`,
see `lt_iff_exists`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
instance (priority := 10) WithBot.instLT : LT (WithBot α) where lt := WithBot.LT

/-- The order on `WithTop α`, defined by `↑a < ⊤` and `a < b → ↑a < ↑b`.

Equivalently, `x < y` can be defined as `∃ a : α, x = ↑a ∧ ∀ b : α, y = ↑b → a < b`,
see `le_if_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[to_dual existing]
instance (priority := 10) WithTop.instLT : LT (WithTop α) where lt a b := WithBot.LT (α := αᵒᵈ) b a

lemma WithBot.lt_def {x y : WithBot α} :
    x < y ↔ (x = ⊥ ∧ ∃ b : α, y = b) ∨ ∃ a b : α, a < b ∧ x = a ∧ y = b :=
  (lt_def_aux ..).trans <| by simp

@[to_dual existing lt_def]
lemma WithTop.lt_def' {x y : WithTop α} :
    x < y ↔ (y = ⊤ ∧ ∃ a : α, x = a) ∨ ∃ b a : α, a < b ∧ y = b ∧ x = a :=
  WithBot.lt_def

@[to_dual lt_def']
lemma WithTop.lt_def {x y : WithTop α} :
    x < y ↔ (∃ a : α, x = ↑a) ∧ y = ⊤ ∨ ∃ a b : α, a < b ∧ x = ↑a ∧ y = ↑b := by
  grind [WithTop.lt_def']

end LT

namespace WithBot

variable {a b : α}

section LE

variable [LE α] {x y : WithBot α}

@[to_dual]
lemma le_iff_forall : x ≤ y ↔ ∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b := by
  cases x <;> cases y <;> simp [le_def]

@[to_dual (attr := simp, norm_cast)]
lemma coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by simp [le_def]

@[to_dual not_top_le_coe]
lemma not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := by simp [le_def]

@[to_dual]
instance instOrderBot : OrderBot (WithBot α) where bot_le := by simp [le_def]

@[to_dual]
instance instOrderTop [OrderTop α] : OrderTop (WithBot α) where
  le_top x := by cases x <;> simp [le_def]

@[to_dual]
instance instBoundedOrder [OrderTop α] : BoundedOrder (WithBot α) where

/-- There is a general version `le_bot_iff`, but this lemma does not require a `PartialOrder`. -/
@[to_dual (attr := simp) top_le_iff
/-- There is a general version `top_le_iff`, but this lemma does not require a `PartialOrder`. -/]
protected theorem le_bot_iff : ∀ {x : WithBot α}, x ≤ ⊥ ↔ x = ⊥
  | (a : α) => by simp [not_coe_le_bot]
  | ⊥ => by simp

@[to_dual le_coe]
theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe

@[to_dual le_coe_iff]
theorem coe_le_iff : a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b := by simp [le_iff_forall]
@[to_dual coe_le_iff]
theorem le_coe_iff : x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b := by simp [le_iff_forall]

@[to_dual]
protected theorem _root_.IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α) :=
  fun x ↦ by cases x <;> simp; simpa using @h _

@[to_dual (attr := simp) untop_le_iff]
lemma le_unbot_iff (hx : x ≠ ⊥) : a ≤ unbot x hx ↔ a ≤ x := by lift x to α using hx; simp
@[to_dual (attr := simp) le_untop_iff]
lemma unbot_le_iff (hx : x ≠ ⊥) : unbot x hx ≤ a ↔ x ≤ a := by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
lemma unbot_le_unbot_iff (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x.unbot hx ≤ y.unbot hy ↔ x ≤ y := by simp

@[to_dual]
alias ⟨_, unbot_mono⟩ := unbot_le_unbot_iff

@[deprecated (since := "2025-12-05")]
alias unbot_le_unbot := unbot_le_unbot_iff

@[to_dual untopD_le_iff]
lemma le_unbotD_iff (hx : x ≠ ⊥) : b ≤ x.unbotD a ↔ b ≤ x := by lift x to α using hx; simp
@[to_dual le_untopD_iff]
lemma unbotD_le_iff (hx : x = ⊥ → a ≤ b) : x.unbotD a ≤ b ↔ x ≤ b := by cases x <;> simp [hx]

@[to_dual]
lemma unbotD_mono (hx : x ≠ ⊥) (h : x ≤ y) : x.unbotD a ≤ y.unbotD a := by
  lift x to α using hx
  cases y <;> simp_all

@[to_dual untopA_le_iff]
lemma le_unbotA_iff [Nonempty α] (hx : x ≠ ⊥) : a ≤ x.unbotA ↔ a ≤ x := le_unbotD_iff hx
@[to_dual le_untopA_iff]
lemma unbotA_le_iff [Nonempty α] (hx : x ≠ ⊥) : x.unbotA ≤ a ↔ x ≤ a := by
  lift x to α using hx; simp

@[to_dual]
lemma unbotA_mono [Nonempty α] (hy : x ≠ ⊥) (h : x ≤ y) : x.unbotA ≤ y.unbotA := unbotD_mono hy h

end LE

section LT

variable [LT α] {x y : WithBot α}

@[to_dual]
lemma lt_iff_exists : x < y ↔ ∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b := by
  cases x <;> cases y <;> simp [lt_def]

@[to_dual (attr := simp, norm_cast)]
lemma coe_lt_coe : (a : WithBot α) < b ↔ a < b := by simp [lt_def]
@[to_dual (attr := simp) coe_lt_top]
lemma bot_lt_coe (a : α) : ⊥ < (a : WithBot α) := by simp [lt_def]
@[to_dual (attr := simp) not_top_lt]
protected lemma not_lt_bot (a : WithBot α) : ¬a < ⊥ := by simp [lt_def]

@[to_dual]
lemma lt_iff_exists_coe : x < y ↔ ∃ b : α, y = b ∧ x < b := by cases y <;> simp

@[to_dual coe_lt_iff]
lemma lt_coe_iff : x < b ↔ ∀ a : α, x = a → a < b := by simp [lt_iff_exists]

/-- A version of `bot_lt_iff_ne_bot` for `WithBot` that only requires `LT α`, not
`PartialOrder α`. -/
@[to_dual lt_top_iff_ne_top
/-- A version of `lt_top_iff_ne_top` for `WithTop` that only requires `LT α`, not
`PartialOrder α`. -/]
protected lemma bot_lt_iff_ne_bot : ⊥ < x ↔ x ≠ ⊥ := by cases x <;> simp

@[to_dual (attr := simp) untop_lt_iff]
lemma lt_unbot_iff (hx : x ≠ ⊥) : a < unbot x hx ↔ a < x := by lift x to α using hx; simp
@[to_dual (attr := simp) lt_untop_iff]
lemma unbot_lt_iff (hx : x ≠ ⊥) : unbot x hx < b ↔ x < b := by lift x to α using hx; simp

@[to_dual (reorder := hx hy)]
lemma unbot_lt_unbot_iff (hx hy) : unbot x hx < unbot y hy ↔ x < y := by simp

@[deprecated (since := "2025-12-05")]
alias unbot_lt_unbot := unbot_lt_unbot_iff

@[to_dual untopD_lt_iff]
lemma lt_unbotD_iff (hx : x ≠ ⊥) : b < x.unbotD a ↔ b < x := by lift x to α using hx; simp
@[to_dual lt_untopD_iff]
lemma unbotD_lt_iff (hx : x = ⊥ → a < b) : x.unbotD a < b ↔ x < b := by cases x <;> simp [hx]

@[to_dual untopA_lt_iff]
lemma lt_unbotA_iff [Nonempty α] (hx : x ≠ ⊥) : a < x.unbotA ↔ a < x := lt_unbotD_iff hx
@[to_dual lt_untopA_iff]
lemma unbotA_lt_iff [Nonempty α] (hx : x ≠ ⊥) : x.unbotA < a ↔ x < a := by
  lift x to α using hx; simp

end LT

@[to_dual]
instance [Preorder α] : Preorder (WithBot α) where
  lt_iff_le_not_ge x y := by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {x y : WithBot α}

@[to_dual]
theorem coe_strictMono : StrictMono (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_lt_coe.2

@[to_dual]
theorem coe_mono : Monotone (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_le_coe.2

@[to_dual]
theorem monotone_iff {f : WithBot α → β} :
    Monotone f ↔ Monotone (fun a ↦ f a : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h ↦ ⟨h.comp WithBot.coe_mono, fun _ ↦ h bot_le⟩, fun h ↦
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[to_dual (attr := simp)]
theorem monotone_map_iff {f : α → β} : Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

@[to_dual]
alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

@[to_dual]
theorem strictMono_iff {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (fun a => f a : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

@[to_dual]
theorem strictAnti_iff {f : WithBot α → β} :
    StrictAnti f ↔ StrictAnti (fun a ↦ f a : α → β) ∧ ∀ x : α, f x < f ⊥ :=
  strictMono_iff (β := βᵒᵈ)

@[to_dual (attr := simp)]
theorem strictMono_map_iff {f : α → β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, bot_lt_coe]

@[to_dual]
alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

@[to_dual]
lemma map_le_iff (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    x.map f ≤ y.map f ↔ x ≤ y := by cases x <;> cases y <;> simp [mono_iff]

@[to_dual coe_untopD_le]
theorem le_coe_unbotD (x : WithBot α) (b : α) : x ≤ x.unbotD b := by cases x <;> simp

@[to_dual (attr := simp) coe_top_lt]
theorem lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥ := by cases x <;> simp

@[to_dual eq_top_iff_forall_gt]
lemma eq_bot_iff_forall_lt : x = ⊥ ↔ ∀ b : α, x < b := by
  cases x <;> simp; simpa using ⟨_, lt_irrefl _⟩

@[to_dual eq_top_iff_forall_ge]
lemma eq_bot_iff_forall_le [NoBotOrder α] : x = ⊥ ↔ ∀ b : α, x ≤ b := by
  refine ⟨by simp +contextual, fun h ↦ (x.eq_bot_iff_forall_ne).2 fun y => ?_⟩
  rintro rfl
  exact not_isBot y fun z => coe_le_coe.1 (h z)

@[to_dual forall_le_coe_iff_le]
lemma forall_coe_le_iff_le [NoBotOrder α] : (∀ a : α, a ≤ x → a ≤ y) ↔ x ≤ y := by
  obtain _ | a := x
  · simpa [WithBot.none_eq_bot, eq_bot_iff_forall_le] using fun a ha ↦ (not_isBot _ ha).elim
  · exact ⟨fun h ↦ h _ le_rfl, fun hay b ↦ hay.trans'⟩

@[to_dual forall_coe_le_iff_le]
lemma forall_le_coe_iff_le [NoBotOrder α] : (∀ a : α, y ≤ a → x ≤ a) ↔ x ≤ y := by
  obtain _ | y := y
  · simp [WithBot.none_eq_bot, eq_bot_iff_forall_le]
  · exact ⟨fun h ↦ h _ le_rfl, fun hmn a ham ↦ hmn.trans ham⟩

@[to_dual (attr := simp) forall_lt_coe]
theorem forall_coe_lt {p : WithBot α → Prop} :
    (∀ x, (a : WithBot α) < x → p x) ↔ ∀ b, a < b → p b := by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_lt_coe]
theorem exists_coe_lt {p : WithBot α → Prop} :
    (∃ x, (a : WithBot α) < x ∧ p x) ↔ ∃ b, a < b ∧ p b := by
  simp [WithBot.exists]

@[to_dual (attr := simp) forall_le_coe]
theorem forall_coe_le {p : WithBot α → Prop} :
    (∀ x, (a : WithBot α) ≤ x → p x) ↔ ∀ b, a ≤ b → p b := by
  simp [WithBot.forall]

@[to_dual (attr := simp) exists_le_coe]
theorem exists_coe_le {p : WithBot α → Prop} :
    (∃ x, (a : WithBot α) ≤ x ∧ p x) ↔ ∃ b, a ≤ b ∧ p b := by
  simp [WithBot.exists]

/- to_dual does not seem able to handle this. -/
lemma isSome_mono : Monotone (fun x : WithBot α ↦ x.isSome) := by
  intro x y h
  cases x <;> cases y <;> simp_all

lemma _root_.WithTop.isSome_mono : Monotone (fun x : WithBot α ↦ x.isSome) := by
  intro x y h
  cases x <;> cases y <;> simp_all

@[to_dual]
lemma bind_mono
    {f : α → WithBot β} (hf : Monotone f)
    {g : α → β → WithBot γ} (hg : Monotone (Function.uncurry g)) :
    Monotone (fun x ↦ (f x).bind (g x)) := by
  intro x₁ x₂ hx
  specialize hf hx
  cases hfx₁ : f x₁
  · simp [hfx₁]
  · cases hfx₂ : f x₂
    · simp [hfx₁, hfx₂] at hf
    · simp only [hfx₁, bind_some, hfx₂]
      simp only [hfx₁, hfx₂, coe_le_coe] at hf
      apply hg (Prod.mk_le_mk.mpr ⟨hx, hf⟩)

end Preorder

@[to_dual]
instance [PartialOrder α] : PartialOrder (WithBot α) where
  le_antisymm x y := by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

section PartialOrder
variable [PartialOrder α] {x y : WithBot α} {a b : α}

@[to_dual untopD_le]
lemma le_unbotD (hy : b ≤ y) : b ≤ y.unbotD a := by
  rwa [le_unbotD_iff]
  exact ne_bot_of_le_ne_bot (by simp) hy

@[to_dual untopA_le]
lemma le_unbotA [Nonempty α] (hy : b ≤ y) : b ≤ y.unbotA := le_unbotD hy

@[to_dual eq_bot_iff_forall_le]
lemma eq_top_iff_forall_ge [Nonempty α] [NoTopOrder α] {x : WithBot (WithTop α)} :
    x = ⊤ ↔ ∀ a : α, a ≤ x := by
  refine ⟨by simp_all, fun H ↦ ?_⟩
  induction x
  · simp at H
  · simpa [WithTop.eq_top_iff_forall_ge] using H

variable [NoBotOrder α]

@[to_dual eq_of_forall_le_coe_iff]
lemma eq_of_forall_coe_le_iff (h : ∀ a : α, a ≤ x ↔ a ≤ y) : x = y :=
  le_antisymm (forall_coe_le_iff_le.mp fun a ↦ (h a).1) (forall_coe_le_iff_le.mp fun a ↦ (h a).2)

@[to_dual eq_of_forall_coe_le_iff]
lemma eq_of_forall_le_coe_iff (h : ∀ a : α, x ≤ a ↔ y ≤ a) : x = y :=
  le_antisymm (forall_le_coe_iff_le.mp fun a ↦ (h a).2) (forall_le_coe_iff_le.mp fun a ↦ (h a).1)

end PartialOrder

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithBot α) where
  sup
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊥, ⊥ => ⊥
    | (a : α), ⊥ => a
    | ⊥, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual existing]
instance _root_.WithTop.semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithTop α) where
  inf
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊤, ⊤ => ⊤
    | (a : α), ⊤ => a
    | ⊤, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊓ b)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

@[to_dual existing]
instance _root_.WithTop.semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithTop α) where
  sup := .map₂ (· ⊔ ·)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

@[to_dual (attr := simp, norm_cast)]
theorem coe_sup [SemilatticeSup α] (a b : α) :
    ((a ⊔ b : α) : WithBot α) = (a : WithBot α) ⊔ b := rfl

@[to_dual (attr := simp, norm_cast)]
theorem coe_inf [SemilatticeInf α] (a b : α) :
    ((a ⊓ b : α) : WithBot α) = (a : WithBot α) ⊓ b := rfl

instance lattice [Lattice α] : Lattice (WithBot α) where

@[to_dual existing]
instance _root_.WithTop.lattice [Lattice α] : Lattice (WithTop α) where

instance distribLattice [DistribLattice α] : DistribLattice (WithBot α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual existing]
instance _root_.WithTop.distribLattice [DistribLattice α] : DistribLattice (WithTop α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← WithTop.coe_inf, ← WithTop.coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

@[to_dual]
instance decidableEq [DecidableEq α] : DecidableEq (WithBot α) :=
  inferInstanceAs <| DecidableEq (Option α)

@[to_dual]
instance decidableLE [LE α] [DecidableLE α] : DecidableLE (WithBot α)
  | ⊥, _ => isTrue <| by simp
  | (a : α), ⊥ => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

@[to_dual]
instance decidableLT [LT α] [DecidableLT α] : DecidableLT (WithBot α)
  | _, ⊥ => isFalse <| by simp
  | ⊥, (a : α) => isTrue <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe

instance total_le [LE α] [@Std.Total α (· ≤ ·)] : @Std.Total (WithBot α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

instance _root_.WithTop.total_le [LE α] [@Std.Total α (· ≤ ·)] :
    @Std.Total (WithTop α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using Std.Total.total ..

instance linearOrder [LinearOrder α] : LinearOrder (WithBot α) := Lattice.toLinearOrder _

@[to_dual existing]
instance _root_.WithTop.linearOrder [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

@[to_dual]
instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithBot α) where
  wf := .intro fun
  | ⊥ => ⟨_, by simp⟩
  | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih ↦ .intro _ fun
    | ⊥, _ => ⟨_, by simp⟩
    | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

@[to_dual]
instance instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) where
  wf := have acc_some (a : α) : @Acc (WithBot α) (· > ·) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih ↦ ⟨_, by simpa [WithBot.forall]⟩
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => ⟨_, by simpa [WithBot.forall]⟩

lemma denselyOrdered_iff [LT α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithBot.coe_lt_coe.mpr hab)
    induction c with
    | bot => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithBot.exists, WithBot.forall, exists_lt] using DenselyOrdered.dense

@[to_dual existing]
lemma _root_.WithTop.denselyOrdered_iff [LT α] [NoMaxOrder α] :
    DenselyOrdered (WithTop α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithTop.coe_lt_coe.mpr hab)
    induction c with
    | top => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithTop.exists, WithTop.forall, exists_gt] using DenselyOrdered.dense

@[to_dual]
instance denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) :=
  denselyOrdered_iff.mpr inferInstance

instance trichotomous.lt [Preorder α] [@Std.Trichotomous α (· < ·)] :
    @Std.Trichotomous (WithBot α) (· < ·) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} ↦ by
    cases x <;> cases y <;> simp [trichotomous]

instance _root_.WithTop.trichotomous.lt [Preorder α] [@Std.Trichotomous α (· < ·)] :
    @Std.Trichotomous (WithTop α) (· < ·) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} ↦ by
    cases x <;> cases y <;> simp [trichotomous]

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedLT`, remove this.
instance IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
  IsWellOrder (WithBot α) (· < ·) where

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedLT`, remove this.
instance _root_.WithTop.IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
  IsWellOrder (WithTop α) (· < ·) where

instance trichotomous.gt [Preorder α] [@Std.Trichotomous α (· > ·)] :
    @Std.Trichotomous (WithBot α) (· > ·) :=
  have : @Std.Trichotomous α (· < ·) := .swap _; .swap _

instance _root_.WithTop.trichotomous.gt [Preorder α] [@Std.Trichotomous α (· > ·)] :
    @Std.Trichotomous (WithTop α) (· > ·) :=
  have : @Std.Trichotomous α (· < ·) := .swap _; .swap _

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedGT`, remove this.
instance IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) where

-- TODO: the hypotheses are equivalent to `LinearOrder` + `WellFoundedGT`, remove this.
instance _root_.WithTop.IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] :
    IsWellOrder (WithTop α) (· > ·) where

section LinearOrder
variable [LinearOrder α] {x y : WithBot α}

@[to_dual]
lemma coe_min (a b : α) : ↑(min a b) = min (a : WithBot α) b := rfl
@[to_dual]
lemma coe_max (a b : α) : ↑(max a b) = max (a : WithBot α) b := rfl

variable [DenselyOrdered α] [NoMinOrder α]

@[to_dual ge_of_forall_gt_iff_ge]
lemma le_of_forall_lt_iff_le : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x := by
  cases x <;> cases y <;> simp [exists_lt, forall_gt_imp_ge_iff_le_of_dense]

@[to_dual le_of_forall_lt_iff_le]
lemma ge_of_forall_gt_iff_ge : (∀ z : α, z < x → z ≤ y) ↔ x ≤ y := by
  cases x <;> cases y <;> simp [exists_lt, forall_lt_imp_le_iff_le_of_dense]

end LinearOrder

@[to_dual lt_iff_exists_coe_btwn']
theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < x ∧ x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

@[to_dual lt_iff_exists_coe_btwn]
theorem lt_iff_exists_coe_btwn' [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, x < b ∧ a < x := by
  rw [lt_iff_exists_coe_btwn]; simp_rw [and_comm]

@[to_dual]
instance noTopOrder [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) where
  exists_not_le := fun
    | ⊥ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_le a; ⟨b, mod_cast hba⟩

@[to_dual]
instance noMaxOrder [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) where
  exists_gt := fun
    | ⊥ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_gt a; ⟨b, mod_cast hba⟩

variable {a b : α}

/-! ### `(WithBot α)ᵒᵈ ≃ WithTop αᵒᵈ`, `(WithTop α)ᵒᵈ ≃ WithBot αᵒᵈ` -/

open Function

/-- `WithBot.toDual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithBot.toDualTopEquiv` for the related order-iso. -/
@[to_dual
/-- `WithTop.toDual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithTop.toDualBotEquiv` for the related order-iso. -/]
protected def toDual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _

/-- `WithBot.ofDual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithBot.ofDualTopEquiv` for the related order-iso.
-/
@[to_dual
/-- `WithTop.ofDual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithTop.toDualBotEquiv` for the related order-iso. -/]
protected def ofDual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _

@[to_dual (attr := simp)]
theorem toDual_symm : WithBot.toDual.symm = WithTop.ofDual (α := α) := rfl

@[to_dual]
theorem toDual_symm_apply (a : WithTop αᵒᵈ) : WithBot.toDual.symm a = WithTop.ofDual a := rfl

attribute [deprecated toDual_symm (since := "2025-12-30")] toDual_symm_apply
attribute [deprecated WithTop.toDual_symm (since := "2025-12-30")] WithTop.toDual_symm_apply

@[to_dual (attr := simp)]
theorem ofDual_symm : WithBot.ofDual.symm = WithTop.toDual (α := α) := rfl

@[to_dual]
theorem ofDual_symm_apply (a : WithTop α) : WithBot.ofDual.symm a = WithTop.toDual a := rfl

attribute [deprecated ofDual_symm (since := "2025-12-30")] ofDual_symm_apply
attribute [deprecated WithTop.ofDual_symm (since := "2025-12-30")] WithTop.ofDual_symm_apply

@[to_dual (attr := simp)]
theorem toDual_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ := rfl

@[deprecated (since := "2025-12-30")] alias toDual_apply_bot := toDual_bot
@[deprecated (since := "2025-12-30")] alias _root_.WithTop.toDual_apply_top := WithTop.toDual_top

@[to_dual (attr := simp)]
theorem ofDual_bot : WithBot.ofDual (⊥ : WithBot αᵒᵈ) = ⊤ := rfl

@[deprecated (since := "2025-12-30")] alias ofDual_apply_bot := ofDual_bot
@[deprecated (since := "2025-12-30")] alias _root_.WithTop.ofDual_apply_top := WithTop.ofDual_top

open OrderDual

@[to_dual (attr := simp)]
theorem toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a := rfl

@[to_dual (attr := simp)]
theorem ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a := rfl

@[to_dual]
theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (toDual ∘ f) :=
  rfl

@[to_dual]
theorem map_ofDual (f : α → β) (a : WithBot αᵒᵈ) :
    map f (WithBot.ofDual a) = a.map (ofDual ∘ f) :=
  rfl

@[to_dual]
theorem toDual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (map f a) = WithTop.map (toDual ∘ f ∘ ofDual) (WithBot.toDual a) :=
  rfl

@[to_dual]
theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (map f a) = WithTop.map (ofDual ∘ f ∘ toDual) (WithBot.ofDual a) :=
  rfl

section LE
variable [LE α]

@[to_dual le_toDual_iff]
lemma toDual_le_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual ≤ y ↔ WithTop.ofDual y ≤ x := by cases x <;> cases y <;> simp [toDual_le]

@[to_dual toDual_le_iff]
lemma le_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x ≤ WithBot.toDual y ↔ y ≤ WithTop.ofDual x := by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]
lemma toDual_le_toDual_iff {x y : WithBot α} :
    x.toDual ≤ y.toDual ↔ y ≤ x := by cases x <;> cases y <;> simp

@[to_dual le_ofDual_iff]
lemma ofDual_le_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x ≤ y ↔ y.toDual ≤ x := by cases x <;> cases y <;> simp [toDual_le]

@[to_dual ofDual_le_iff]
lemma le_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x ≤ WithBot.ofDual y ↔ y ≤ x.toDual := by cases x <;> cases y <;> simp [le_toDual]

@[to_dual (attr := simp)]
lemma ofDual_le_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x ≤ WithBot.ofDual y ↔ y ≤ x := by cases x <;> cases y <;> simp_all

end LE

section LT
variable [LT α]

@[to_dual lt_toDual_iff]
lemma toDual_lt_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual < y ↔ WithTop.ofDual y < x := by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual toDual_lt_iff]
lemma lt_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x < y.toDual ↔ y < WithTop.ofDual x := by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]
lemma toDual_lt_toDual_iff {x y : WithBot α} :
    x.toDual < y.toDual ↔ y < x := by cases x <;> cases y <;> simp

@[to_dual lt_ofDual_iff]
lemma ofDual_lt_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x < y ↔ y.toDual < x := by cases x <;> cases y <;> simp [toDual_lt]

@[to_dual ofDual_lt_iff]
lemma lt_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x < WithBot.ofDual y ↔ y < x.toDual := by cases x <;> cases y <;> simp [lt_toDual]

@[to_dual (attr := simp)]
lemma ofDual_lt_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x < WithBot.ofDual y ↔ y < x := by cases x <;> cases y <;> simp

end LT

end WithBot
