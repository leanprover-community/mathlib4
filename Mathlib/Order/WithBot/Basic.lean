/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Order.TypeTags
import Mathlib.Data.Option.NAry
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Lift
import Mathlib.Data.Option.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# `WithBot`, `WithTop`

Adding a `bot` or a `top` to an order.

## Main declarations

* `With<Top/Bot> α`: Equips `Option α` with the order on `α` plus `none` as the top/bottom element.
> FIX ^
-/

variable {α β γ δ : Type*}
variable {a b : α}

attribute [local grind cases] WithBot

namespace WithBot

instance nontrivial [Nonempty α] : Nontrivial (WithBot α) :=
  ⟨⊥, Classical.arbitrary α, by simp⟩

/-- `WithTop α` is a `Subsingleton` if and only if `α` is empty. -/
theorem subsingleton_iff_isEmpty {α : Type*} : Subsingleton (WithBot α) ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa using h.elim x ⊥⟩,
   fun h ↦ ⟨fun x y ↦ by
     have := IsEmpty.false (α := α)
     cases x <;> cases y <;> solve_by_elim⟩⟩

instance [IsEmpty α] : Unique (WithBot α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)

open Function

/-- Decidable equality with `⊥`. This is not an instance to avoid conflicts with other instances. -/
def instDecidableEqBot : (x : WithBot α) → Decidable (x = ⊥)
  | .bot => isTrue rfl
  | .some _ => isFalse (by simp)

theorem coe_injective : Injective ((↑) : α → WithBot α) := by grind [Injective]

@[simp, norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b := by grind

protected theorem «forall» {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x := by grind

protected theorem «exists» {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x := by grind

@[deprecated bot_eq (since := "2025-08-04")]
theorem none_eq_bot : (bot : WithBot α) = (⊥ : WithBot α) :=
  rfl

@[deprecated "This is now a syntactic identity. " (since := "2025-08-04")]
theorem some_eq_coe (a : α) : (some a : WithBot α) = (↑a : WithBot α) :=
  rfl

@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  nofun

@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  nofun

theorem coe_eq_coe : (a : WithBot α) = (b : WithBot α) ↔ a = b := coe_inj

/-- Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries.
-/
def unbotD (d : α) (x : WithBot α) : α :=
  recBotCoe d id x

@[simp]
theorem unbotD_bot {α} (d : α) : unbotD d ⊥ = d :=
  rfl

@[simp]
theorem unbotD_coe {α} (d x : α) : unbotD d x = x :=
  rfl

theorem unbotD_eq_iff {d y : α} {x : WithBot α} : unbotD d x = y ↔ x = y ∨ x = ⊥ ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[simp]
theorem unbotD_eq_self_iff {d : α} {x : WithBot α} : unbotD d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbotD_eq_iff]

theorem unbotD_eq_unbotD_iff {d : α} {x y : WithBot α} :
    unbotD d x = unbotD d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
  induction y <;> simp [unbotD_eq_iff, or_comm]

/-- Apply a function to non-`⊥` elements, and send `⊥` to `d`. -/
-- (If you think `WithBot` is equivalent to `Option`, this is the equivalent of `Option.elim`.)
def mapD (d : β) (f : α → β) : WithBot α → β
| .bot => d
| .some a => f a

@[simp, grind =]
theorem mapD_bot (d : β) (f : α → β) : mapD d f ⊥ = d :=
  rfl

@[simp, grind =]
theorem mapD_coe (d : β) (f : α → β) (a : α) : mapD d f a = f a :=
  rfl

/-- Lift a map `f : α → β` to `WithBot α → WithBot β`. -/
def map (f : α → β) : WithBot α → WithBot β
| .bot => .bot
| .some a => .some (f a)

@[simp, grind =]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl

@[simp, grind =]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[simp]
lemma map_eq_bot_iff {f : α → β} {a : WithBot α} :
    map f a = ⊥ ↔ a = ⊥ := by grind

theorem map_eq_some_iff {f : α → β} {y : β} {v : WithBot α} :
    WithBot.map f v = .some y ↔ ∃ x, v = .some x ∧ f x = y := by grind

theorem some_eq_map_iff {f : α → β} {y : β} {v : WithBot α} :
    .some y = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = y := by grind

theorem map_id : map (id : α → α) = id := by grind

@[simp]
theorem map_map (h : β → γ) (g : α → β) (a : WithBot α) : map h (map g a) = map (h ∘ g) a := by
  grind

theorem comp_map (h : β → γ) (g : α → β) (x : WithBot α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) :
    WithBot.map g ∘ WithBot.map f = WithBot.map (g ∘ f) := by
  funext x; simp [map_map]

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) := by
  replace h := congrFun h a
  grind

theorem map_injective {f : α → β} (Hf : Injective f) : Injective (WithBot.map f) :=
  fun
  | .bot, .bot, _
  | .bot, .some b, _
  | .some a, .bot, _ => by simp_all
  | .some a, .some b, h => by simp only [map_coe, some.injEq] at h; specialize Hf h; simpa

/-- The image of a binary function `f : α → β → γ` as a function
`WithBot α → WithBot β → WithBot γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (f : α → β → γ) : WithBot α → WithBot β → WithBot γ
  | .bot, .bot => .bot
  | .some _, .bot => .bot
  | .bot, .some _ => .bot
  | .some a, .some b => .some (f a b)

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp, grind =] lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f ⊥ b = ⊥ := by cases b <;> rfl
@[simp, grind =] lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a ⊥ = ⊥ := by cases a <;> rfl
@[simp, grind =] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) :
    map₂ f a b = b.map fun b ↦ f a b := by
  cases b <;> rfl
@[simp, grind =] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) :
    map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithBot α} {b : WithBot β} :
    map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := by grind

@[simp] lemma map₂_eq_coe_iff {f : α → β → γ} {a : WithBot α} {b : WithBot β} {c : γ} :
    map₂ f a b = WithBot.some c ↔ ∃ a' b', a = .some a' ∧ b = .some b' ∧ f a' b' = c :=
  match a, b with
  | .bot, .bot
  | .bot, .some b
  | .some a, .bot
  | .some a, .some b => by simp

lemma ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x := by grind

lemma eq_bot_iff_forall_ne {x : WithBot α} : x = ⊥ ↔ ∀ a : α, ↑a ≠ x := by grind

@[deprecated (since := "2025-03-19")] alias forall_ne_iff_eq_bot := eq_bot_iff_forall_ne

theorem forall_ne_bot {p : WithBot α → Prop} : (∀ x, x ≠ ⊥ → p x) ↔ ∀ x : α, p x := by
  simp [ne_bot_iff_exists]

theorem exists_ne_bot {p : WithBot α → Prop} : (∃ x ≠ ⊥, p x) ↔ ∃ x : α, p x := by
  simp [ne_bot_iff_exists]

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α | (x : α), _ => x

@[simp] lemma coe_unbot : ∀ (x : WithBot α) hx, x.unbot hx = x | (x : α), _ => rfl

@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl

instance canLift : CanLift (WithBot α) α (↑) fun r => r ≠ ⊥ where
  prf x h := ⟨x.unbot h, coe_unbot _ _⟩

instance instTop [Top α] : Top (WithBot α) where
  top := (⊤ : α)

@[simp, norm_cast] lemma coe_top [Top α] : ((⊤ : α) : WithBot α) = ⊤ := rfl
@[simp, norm_cast] lemma coe_eq_top [Top α] {a : α} : (a : WithBot α) = ⊤ ↔ a = ⊤ := coe_eq_coe
@[simp, norm_cast] lemma top_eq_coe [Top α] {a : α} : ⊤ = (a : WithBot α) ↔ ⊤ = a := coe_eq_coe

theorem unbot_eq_iff {a : WithBot α} {b : α} (h : a ≠ ⊥) :
    a.unbot h = b ↔ a = b := by
  induction a
  · simpa using h rfl
  · simp

theorem eq_unbot_iff {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a = b.unbot h ↔ a = b := by
  induction b
  · simpa using h rfl
  · simp

@[simps]
def equivOption : WithBot α ≃ Option α where
  toFun := fun | .bot => none | .some a => Option.some a
  invFun := fun | none => .bot | .some a => WithBot.some a
  left_inv := by grind
  right_inv := by grind

attribute [grind =] equivOption_apply equivOption_symm_apply

theorem equivOption_eq_some {x : WithBot α} {y : α} :
    equivOption x = Option.some y ↔ x = WithBot.some y := by
  grind

theorem equivOption_eq_none {x : WithBot α} :
    equivOption x = none ↔ x = ⊥ := by
  grind

theorem equivOption_symm_eq_coe {x : Option α} {y : α} :
    equivOption.symm x = WithBot.some y ↔ x = Option.some y := by
  grind

theorem equivOption_symm_eq_bot {x : Option α} :
    equivOption.symm x = ⊥ ↔ x = none := by
  grind

/-- The equivalence between the non-bottom elements of `WithBot α` and `α`. -/
@[simps] def _root_.Equiv.withBotSubtypeNe : {y : WithBot α // y ≠ ⊥} ≃ α where
  toFun := fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- Function that sends an element of `WithBot α` to `α`,
with an arbitrary default value for `⊥`. -/
noncomputable
abbrev unbotA [Nonempty α] : WithBot α → α := unbotD (Classical.arbitrary α)

lemma unbotA_eq_unbot [Nonempty α] {a : WithBot α} (ha : a ≠ ⊥) : unbotA a = unbot a ha := by
  cases a with
  | bot => contradiction
  | coe a => simp

end WithBot

namespace Equiv

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithBot e`. -/
@[simps apply]
def withBotCongr (e : α ≃ β) : WithBot α ≃ WithBot β where
  toFun := WithBot.map e
  invFun := WithBot.map e.symm
  left_inv x := by grind
  right_inv x := by grind

attribute [grind =] withBotCongr_apply

@[simp]
theorem withBotCongr_refl : withBotCongr (Equiv.refl α) = Equiv.refl _ :=
  Equiv.ext <| congr_fun WithBot.map_id

@[simp, grind =]
theorem withBotCongr_symm (e : α ≃ β) : withBotCongr e.symm = (withBotCongr e).symm :=
  rfl

@[simp]
theorem withBotCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    withBotCongr (e₁.trans e₂) = (withBotCongr e₁).trans (withBotCongr e₂) := by
  ext x
  simp

end Equiv

namespace WithBot

variable {a b : α}

section LE

variable [LE α] {x y : WithBot α}

/-- The order on `WithBot α`, defined by `⊥ ≤ ⊥`, `⊥ ≤ ↑a` and `a ≤ b → ↑a ≤ ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b`,
see `le_if_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
@[mk_iff le_def_aux]
protected inductive LE : WithBot α → WithBot α → Prop
  | protected bot_le (x : WithBot α) : WithBot.LE ⊥ x
  | protected coe_le_coe {a b : α} : a ≤ b → WithBot.LE a b

instance (priority := 10) instLE : LE (WithBot α) where le := WithBot.LE

lemma le_def : x ≤ y ↔ x = ⊥ ∨ ∃ a b : α, a ≤ b ∧ x = a ∧ y = b := le_def_aux ..

lemma le_iff_forall : x ≤ y ↔ ∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b := by
  cases x <;> cases y <;> simp [le_def]

@[simp, norm_cast] lemma coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by simp [le_def]

lemma not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := by simp [le_def]

instance instOrderBot : OrderBot (WithBot α) where bot_le := by simp [le_def]

instance instBoundedOrder [OrderTop α] : BoundedOrder (WithBot α) where
  le_top x := by cases x <;> simp [le_def]

/-- There is a general version `le_bot_iff`, but this lemma does not require a `PartialOrder`. -/
@[simp]
protected theorem le_bot_iff : ∀ {x : WithBot α}, x ≤ ⊥ ↔ x = ⊥
  | (a : α) => by simp [not_coe_le_bot]
  | ⊥ => by simp

theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ (equivOption.symm o) ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem coe_le_iff : a ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b := by simp [le_iff_forall]
theorem le_coe_iff : x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b := by simp [le_iff_forall]

protected theorem _root_.IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α) :=
  fun x ↦ by cases x <;> simp; simpa using @h _

lemma le_unbot_iff (hy : y ≠ ⊥) : a ≤ unbot y hy ↔ a ≤ y := by lift y to α using id hy; simp
lemma unbot_le_iff (hx : x ≠ ⊥) : unbot x hx ≤ b ↔ x ≤ b := by lift x to α using id hx; simp
lemma unbotD_le_iff (hx : x = ⊥ → a ≤ b) : x.unbotD a ≤ b ↔ x ≤ b := by cases x <;> simp [hx]

@[simp] lemma unbot_le_unbot (hx hy) : unbot x hx ≤ unbot y hy ↔ x ≤ y := by
  lift x to α using hx
  lift y to α using hy
  simp

end LE

section LT

variable [LT α] {x y : WithBot α}

/-- The order on `WithBot α`, defined by `⊥ < ↑a` and `a < b → ↑a < ↑b`.

Equivalently, `x ≤ y` can be defined as `∀ b : α, y = ↑v → ∃ a : α, x = ↑a ∧ a ≤ b`,
see `le_if_forall`. The definition as an inductive predicate is preferred since it
cannot be accidentally unfolded too far. -/
instance (priority := 10) instLT : LT (WithBot α) where
  lt
  | ⊥, ⊥ => False
  | (a : α), ⊥ => False
  | ⊥, (b : α) => True
  | (a : α), (b : α) => a < b

lemma lt_def : x < y ↔ ∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b := by
  cases x <;> cases y <;> simp [LT.lt]

@[simp, norm_cast] lemma coe_lt_coe : (a : WithBot α) < b ↔ a < b := by simp [lt_def]
@[simp] lemma bot_lt_coe (a : α) : ⊥ < (a : WithBot α) := by simp [lt_def]
@[simp] protected lemma not_lt_bot (a : WithBot α) : ¬a < ⊥ := by simp [lt_def]

lemma lt_iff_exists_coe : x < y ↔ ∃ b : α, y = b ∧ x < b := by cases y <;> simp

lemma lt_coe_iff : x < b ↔ ∀ a : α, x = a → a < b := by simp [lt_def]

/-- A version of `bot_lt_iff_ne_bot` for `WithBot` that only requires `LT α`, not
`PartialOrder α`. -/
protected lemma bot_lt_iff_ne_bot : ⊥ < x ↔ x ≠ ⊥ := by cases x <;> simp

lemma lt_unbot_iff (hy : y ≠ ⊥) : a < unbot y hy ↔ a < y := by lift y to α using hy; simp
lemma unbot_lt_iff (hx : x ≠ ⊥) : unbot x hx < b ↔ x < b := by lift x to α using hx; simp
lemma unbotD_lt_iff (hx : x = ⊥ → a < b) : x.unbotD a < b ↔ x < b := by cases x <;> simp [hx]

@[simp] lemma unbot_lt_unbot (hx hy) : unbot x hx < unbot y hy ↔ x < y := by
  lift x to α using hx
  lift y to α using hy
  simp

end LT

instance instPreorder [Preorder α] : Preorder (WithBot α) where
  lt_iff_le_not_ge x y := by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

instance instPartialOrder [PartialOrder α] : PartialOrder (WithBot α) where
  le_antisymm x y := by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

section Preorder

variable [Preorder α] [Preorder β] {x y : WithBot α}

theorem coe_strictMono : StrictMono (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_lt_coe.2

theorem coe_mono : Monotone (fun (a : α) => (a : WithBot α)) := fun _ _ => coe_le_coe.2

theorem monotone_iff {f : WithBot α → β} :
    Monotone f ↔ Monotone (fun a ↦ f a : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h ↦ ⟨h.comp WithBot.coe_mono, fun _ ↦ h bot_le⟩, fun h ↦
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[simp]
theorem monotone_map_iff {f : α → β} : Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

theorem strictMono_iff {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (fun a => f a : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

theorem strictAnti_iff {f : WithBot α → β} :
    StrictAnti f ↔ StrictAnti (fun a ↦ f a : α → β) ∧ ∀ x : α, f x < f ⊥ :=
  strictMono_iff (β := βᵒᵈ)

@[simp]
theorem strictMono_map_iff {f : α → β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, bot_lt_coe]

alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

lemma map_le_iff (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    x.map f ≤ y.map f ↔ x ≤ y := by cases x <;> cases y <;> simp [mono_iff]

theorem le_coe_unbotD (x : WithBot α) (b : α) : x ≤ x.unbotD b := by cases x <;> simp

@[simp]
theorem lt_coe_bot [OrderBot α] : x < (⊥ : α) ↔ x = ⊥ := by cases x <;> simp

lemma eq_bot_iff_forall_lt : x = ⊥ ↔ ∀ b : α, x < b := by
  cases x <;> simp; simpa using ⟨_, lt_irrefl _⟩

lemma eq_bot_iff_forall_le [NoBotOrder α] : x = ⊥ ↔ ∀ b : α, x ≤ b := by
  refine ⟨by simp +contextual, fun h ↦ (x.eq_bot_iff_forall_ne).2 fun y => ?_⟩
  rintro rfl
  exact not_isBot y fun z => coe_le_coe.1 (h z)

@[deprecated (since := "2025-03-19")] alias forall_lt_iff_eq_bot := eq_bot_iff_forall_lt
@[deprecated (since := "2025-03-19")] alias forall_le_iff_eq_bot := eq_bot_iff_forall_le

lemma forall_coe_le_iff_le [NoBotOrder α] : (∀ a : α, a ≤ x → a ≤ y) ↔ x ≤ y := by
  obtain _ | a := x
  · simpa [WithBot.none_eq_bot, eq_bot_iff_forall_le] using fun a ha ↦ (not_isBot _ ha).elim
  · exact ⟨fun h ↦ h _ le_rfl, fun hay b ↦ hay.trans'⟩

lemma forall_le_coe_iff_le [NoBotOrder α] : (∀ a : α, y ≤ a → x ≤ a) ↔ x ≤ y := by
  obtain _ | y := y
  · simp [eq_bot_iff_forall_le]
  · exact ⟨fun h ↦ h _ le_rfl, fun hmn a ham ↦ hmn.trans ham⟩

end Preorder

section PartialOrder
variable [PartialOrder α] [NoBotOrder α] {x y : WithBot α}

lemma eq_of_forall_coe_le_iff (h : ∀ a : α, a ≤ x ↔ a ≤ y) : x = y :=
  le_antisymm (forall_coe_le_iff_le.mp fun a ↦ (h a).1) (forall_coe_le_iff_le.mp fun a ↦ (h a).2)

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

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = (a : WithBot α) ⊔ b :=
  rfl

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) where
  inf := .map₂ (· ⊓ ·)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = (a : WithBot α) ⊓ b :=
  rfl

instance lattice [Lattice α] : Lattice (WithBot α) :=
  { WithBot.semilatticeSup, WithBot.semilatticeInf with }

instance distribLattice [DistribLattice α] : DistribLattice (WithBot α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

instance decidableEq [DecidableEq α] : DecidableEq (WithBot α)
  | ⊥, ⊥ => isTrue rfl
  | ⊥, (b : α) => isFalse <| by simp
  | (a : α), ⊥ => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_eq_coe

instance decidableLE [LE α] [DecidableLE α] : DecidableLE (WithBot α)
  | ⊥, _ => isTrue <| by simp
  | (a : α), ⊥ => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

instance decidableLT [LT α] [DecidableLT α] : DecidableLT (WithBot α)
  | _, ⊥ => isFalse <| by simp
  | ⊥, (a : α) => isTrue <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe

instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using IsTotal.total ..

section LinearOrder
variable [LinearOrder α] {x y : WithBot α}

instance linearOrder : LinearOrder (WithBot α) := Lattice.toLinearOrder _

@[simp, norm_cast] lemma coe_min (a b : α) : ↑(min a b) = min (a : WithBot α) b := rfl
@[simp, norm_cast] lemma coe_max (a b : α) : ↑(max a b) = max (a : WithBot α) b := rfl

variable [DenselyOrdered α] [NoMinOrder α]

lemma le_of_forall_lt_iff_le : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x := by
  cases x <;> cases y <;> simp [exists_lt, forall_gt_imp_ge_iff_le_of_dense]

lemma ge_of_forall_gt_iff_ge : (∀ z : α, z < x → z ≤ y) ↔ x ≤ y := by
  cases x <;> cases y <;> simp [exists_lt, forall_lt_imp_le_iff_le_of_dense]

end LinearOrder

instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithBot α) where
  wf := .intro fun
  | ⊥ => ⟨_, by simp⟩
  | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih ↦ .intro _ fun
    | ⊥, _ => ⟨_, by simp⟩
    | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

instance _root_.WithBot.instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) where
  wf :=
  have acc_some (a : α) : Acc ((· > ·) : WithBot α → WithBot α → Prop) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih =>
      .intro _ fun
        | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => .intro _ fun | (b : α), _ => acc_some b

lemma denselyOrdered_iff [LT α] [NoMinOrder α] :
    DenselyOrdered (WithBot α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (WithBot.coe_lt_coe.mpr hab)
    induction c with
    | bot => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithBot.exists, WithBot.forall, exists_lt] using DenselyOrdered.dense

instance denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  denselyOrdered_iff.mpr inferInstance

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

instance noTopOrder [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) where
  exists_not_le := fun
    | ⊥ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_le a; ⟨b, mod_cast hba⟩

instance noMaxOrder [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) where
  exists_gt := fun
    | ⊥ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_gt a; ⟨b, mod_cast hba⟩

end WithBot

namespace WithTop

variable {a b : α}

/-- Decidable equality with `⊤`. This is not an instance to avoid conflicts with other instances. -/
def instDecidableEqTop : (x : WithTop α) → Decidable (x = ⊤)
  | .bot => isTrue rfl
  | .some _ => isFalse (by rintro ⟨⟩)

instance nontrivial [Nonempty α] : Nontrivial (WithTop α) :=
  WithBot.nontrivial

open Function

theorem coe_injective : Injective ((↑) : α → WithTop α) :=
  WithBot.coe_injective

@[norm_cast]
theorem coe_inj : (a : WithTop α) = b ↔ a = b :=
  WithBot.coe_inj

protected theorem «forall» {p : WithTop α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x :=
  WithBot.forall

protected theorem «exists» {p : WithTop α → Prop} : (∃ x, p x) ↔ p ⊤ ∨ ∃ x : α, p x :=
  WithBot.exists

@[deprecated top_eq (since := "2025-08-04")]
theorem none_eq_top : (top : WithTop α) = (⊤ : WithTop α) :=
  rfl

@[deprecated "This is now a syntactic identity." (since := "2025-08-04")]
theorem some_eq_coe (a : α) : (WithTop.some a : WithTop α) = (↑a : WithTop α) :=
  rfl

@[simp]
theorem top_ne_coe : ⊤ ≠ (a : WithTop α) :=
  nofun

@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  nofun

/-- `WithTop α` is a `Subsingleton` if and only if `α` is empty. -/
theorem subsingleton_iff_isEmpty {α : Type*} : Subsingleton (WithTop α) ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa using h.elim x ⊤⟩,
   fun h ↦ ⟨fun x y ↦ by
     have := IsEmpty.false (α := α)
     cases x <;> cases y <;> solve_by_elim⟩⟩

instance [IsEmpty α] : Unique (WithTop α) :=
  @Unique.mk' _ _ (subsingleton_iff_isEmpty.2 ‹_›)

/-- `WithTop.toDual` is the equivalence sending `⊤` to `⊥` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithTop.toDualBotEquiv` for the related order-iso.
-/
protected def toDual : WithTop α ≃ WithBot αᵒᵈ :=
  Equiv.refl _

/-- `WithTop.ofDual` is the equivalence sending `⊤` to `⊥` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithTop.toDualBotEquiv` for the related order-iso.
-/
protected def ofDual : WithTop αᵒᵈ ≃ WithBot α :=
  Equiv.refl _

/-- `WithBot.toDual` is the equivalence sending `⊥` to `⊤` and any `a : α` to `toDual a : αᵒᵈ`.
See `WithBot.toDual_top_equiv` for the related order-iso.
-/
protected def _root_.WithBot.toDual : WithBot α ≃ WithTop αᵒᵈ :=
  Equiv.refl _

/-- `WithBot.ofDual` is the equivalence sending `⊥` to `⊤` and any `a : αᵒᵈ` to `ofDual a : α`.
See `WithBot.ofDual_top_equiv` for the related order-iso.
-/
protected def _root_.WithBot.ofDual : WithBot αᵒᵈ ≃ WithTop α :=
  Equiv.refl _

@[simp]
theorem toDual_symm_apply (a : WithBot αᵒᵈ) : WithTop.toDual.symm a = WithBot.ofDual a :=
  rfl

@[simp]
theorem ofDual_symm_apply (a : WithBot α) : WithTop.ofDual.symm a = WithBot.toDual a :=
  rfl

@[simp]
theorem toDual_apply_top : WithTop.toDual (⊤ : WithTop α) = ⊥ :=
  rfl

@[simp]
theorem ofDual_apply_top : WithTop.ofDual (⊤ : WithTop α) = ⊥ :=
  rfl

open OrderDual

@[simp]
theorem toDual_apply_coe (a : α) : WithTop.toDual (a : WithTop α) = toDual a :=
  rfl

@[simp]
theorem ofDual_apply_coe (a : αᵒᵈ) : WithTop.ofDual (a : WithTop αᵒᵈ) = ofDual a :=
  rfl

/-- Specialization of `Option.getD` to values in `WithTop α` that respects API boundaries.
-/
def untopD (d : α) (x : WithTop α) : α :=
  recTopCoe d id x

@[simp]
theorem untopD_top {α} (d : α) : untopD d ⊤ = d :=
  rfl

@[simp]
theorem untopD_coe {α} (d x : α) : untopD d x = x :=
  rfl

@[simp, norm_cast]
theorem coe_eq_coe : (a : WithTop α) = b ↔ a = b :=
  WithBot.coe_eq_coe

theorem untopD_eq_iff {d y : α} {x : WithTop α} : untopD d x = y ↔ x = y ∨ x = ⊤ ∧ y = d :=
  WithBot.unbotD_eq_iff

@[simp]
theorem untopD_eq_self_iff {d : α} {x : WithTop α} : untopD d x = d ↔ x = d ∨ x = ⊤ :=
  WithBot.unbotD_eq_self_iff

theorem untopD_eq_untopD_iff {d : α} {x y : WithTop α} :
    untopD d x = untopD d y ↔ x = y ∨ x = d ∧ y = ⊤ ∨ x = ⊤ ∧ y = d :=
  WithBot.unbotD_eq_unbotD_iff

/-- Apply a function to non-`⊥` elements, and send `⊥` to `d`. -/
-- (If you think `WithTop` is equivalent to `Option`, this is the equivalent of `Option.elim`.)
def mapD (d : β) (f : α → β) : WithTop α → β
| .top => d
| .some a => f a

@[simp, grind =]
theorem mapD_bot (d : β) (f : α → β) : mapD d f ⊤ = d :=
  rfl

@[simp, grind =]
theorem mapD_coe (d : β) (f : α → β) (a : α) : mapD d f a = f a :=
  rfl

/-- Lift a map `f : α → β` to `WithTop α → WithTop β`. Implemented using `Option.map`. -/
def map (f : α → β) : WithTop α → WithTop β :=
  WithBot.map f

@[simp, grind =]
theorem map_top (f : α → β) : map f ⊤ = ⊤ :=
  rfl

@[simp, grind =]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[simp]
lemma map_eq_top_iff {f : α → β} {a : WithTop α} :
    map f a = ⊤ ↔ a = ⊤ := WithBot.map_eq_bot_iff

theorem map_eq_some_iff {f : α → β} {y : β} {v : WithTop α} :
    WithTop.map f v = .some y ↔ ∃ x, v = .some x ∧ f x = y := WithBot.map_eq_some_iff

theorem some_eq_map_iff {f : α → β} {y : β} {v : WithTop α} :
    .some y = WithTop.map f v ↔ ∃ x, v = .some x ∧ f x = y := by
  cases v <;> simp [eq_comm]

theorem map_id : map (id : α → α) = id :=
  WithBot.map_id

@[simp]
theorem map_map (h : β → γ) (g : α → β) (a : WithTop α) : map h (map g a) = map (h ∘ g) a :=
  WithBot.map_map h g a

theorem comp_map (h : β → γ) (g : α → β) (x : WithTop α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) :
    WithTop.map g ∘ WithTop.map f = WithTop.map (g ∘ f) := by
  funext x; simp [map_map]

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  WithBot.map_comm h _

theorem map_injective {f : α → β} (Hf : Injective f) : Injective (WithTop.map f) :=
  WithBot.map_injective Hf

/-- The image of a binary function `f : α → β → γ` as a function
`WithTop α → WithTop β → WithTop γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ : (α → β → γ) → WithTop α → WithTop β → WithTop γ := WithBot.map₂

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_top_left (f : α → β → γ) (b) : map₂ f ⊤ b = ⊤ := by cases b <;> rfl
@[simp] lemma map₂_top_right (f : α → β → γ) (a) : map₂ f a ⊤ = ⊤ := by cases a <;> rfl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := by
  cases b <;> rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_top_iff {f : α → β → γ} {a : WithTop α} {b : WithTop β} :
    map₂ f a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithBot.map₂_eq_bot_iff

@[simp] lemma map₂_eq_coe_iff {f : α → β → γ} {a : WithTop α} {b : WithTop β} {c : γ} :
    map₂ f a b = WithTop.some c ↔ ∃ a' b', a = .some a' ∧ b = .some b' ∧ f a' b' = c :=
  WithBot.map₂_eq_coe_iff

theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithBot α) :
    map f (WithBot.toDual a) = a.map (toDual ∘ f) :=
  rfl

theorem map_ofDual (f : α → β) (a : WithBot αᵒᵈ) : map f (WithBot.ofDual a) = a.map (ofDual ∘ f) :=
  rfl

theorem toDual_map (f : α → β) (a : WithTop α) :
    WithTop.toDual (map f a) = WithBot.map (toDual ∘ f ∘ ofDual) (WithTop.toDual a) :=
  rfl

theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithTop αᵒᵈ) :
    WithTop.ofDual (map f a) = WithBot.map (ofDual ∘ f ∘ toDual) (WithTop.ofDual a) :=
  rfl

lemma ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x := WithBot.ne_bot_iff_exists

lemma eq_top_iff_forall_ne {x : WithTop α} : x = ⊤ ↔ ∀ a : α, ↑a ≠ x :=
  WithBot.eq_bot_iff_forall_ne

@[deprecated (since := "2025-03-19")] alias forall_ne_iff_eq_top := eq_top_iff_forall_ne

theorem forall_ne_top {p : WithTop α → Prop} : (∀ x, x ≠ ⊤ → p x) ↔ ∀ x : α, p x := by
  simp [ne_top_iff_exists]

theorem exists_ne_top {p : WithTop α → Prop} : (∃ x ≠ ⊤, p x) ↔ ∃ x : α, p x := by
  simp [ne_top_iff_exists]

/-- Deconstruct a `x : WithTop α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : ∀ x : WithTop α, x ≠ ⊤ → α | (x : α), _ => x

@[simp] lemma coe_untop : ∀ (x : WithTop α) hx, x.untop hx = x | (x : α), _ => rfl

@[simp]
theorem untop_coe (x : α) (h : (x : WithTop α) ≠ ⊤ := coe_ne_top) : (x : WithTop α).untop h = x :=
  rfl

instance canLift : CanLift (WithTop α) α (↑) fun r => r ≠ ⊤ where
  prf x h := ⟨x.untop h, coe_untop _ _⟩

instance instBot [Bot α] : Bot (WithTop α) where
  bot := (⊥ : α)

@[simp, norm_cast] lemma coe_bot [Bot α] : ((⊥ : α) : WithTop α) = ⊥ := rfl
@[simp, norm_cast] lemma coe_eq_bot [Bot α] {a : α} : (a : WithTop α) = ⊥ ↔ a = ⊥ := coe_eq_coe
@[simp, norm_cast] lemma bot_eq_coe [Bot α] {a : α} : (⊥ : WithTop α) = a ↔ ⊥ = a := coe_eq_coe

theorem untop_eq_iff {a : WithTop α} {b : α} (h : a ≠ ⊤) :
    a.untop h = b ↔ a = b :=
  WithBot.unbot_eq_iff (α := αᵒᵈ) h

theorem eq_untop_iff {a : α} {b : WithTop α} (h : b ≠ ⊤) :
    a = b.untop h ↔ a = b :=
  WithBot.eq_unbot_iff (α := αᵒᵈ) h

@[simps]
def equivOption : WithTop α ≃ Option α where
  toFun := fun | .top => none | .some a => Option.some a
  invFun := fun | none => .top | .some a => WithTop.some a
  left_inv x := by cases x <;> grind
  right_inv x := by cases x <;> grind

attribute [grind =] equivOption_apply equivOption_symm_apply

theorem equivOption_eq_none {x : WithTop α} :
    equivOption x = none ↔ x = ⊤ :=
  WithBot.equivOption_eq_none

theorem equivOption_eq_some {x : WithTop α} {y : α} :
    equivOption x = Option.some y ↔ x = WithBot.some y :=
  WithBot.equivOption_eq_some

theorem equivOption_symm_eq_top {x : Option α} :
    equivOption.symm x = ⊤ ↔ x = none :=
  WithBot.equivOption_symm_eq_bot

theorem equivOption_symm_eq_coe {x : Option α} {y : α} :
    equivOption.symm x = WithBot.some y ↔ x = Option.some y :=
  WithBot.equivOption_symm_eq_coe

/-- The equivalence between the non-top elements of `WithTop α` and `α`. -/
@[simps] def _root_.Equiv.withTopSubtypeNe : {y : WithTop α // y ≠ ⊤} ≃ α where
  toFun := fun ⟨x,h⟩ => WithTop.untop x h
  invFun x := ⟨x, WithTop.coe_ne_top⟩
  left_inv _ := by simp
  right_inv _:= by simp

/-- Function that sends an element of `WithTop α` to `α`,
with an arbitrary default value for `⊤`. -/
noncomputable
abbrev untopA [Nonempty α] : WithTop α → α := untopD (Classical.arbitrary α)

lemma untopA_eq_untop [Nonempty α] {a : WithTop α} (ha : a ≠ ⊤) : untopA a = untop a ha := by
  cases a with
  | top => contradiction
  | coe a => simp

end WithTop

namespace Equiv

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv WithTop e`. -/
@[simps apply]
def withTopCongr (e : α ≃ β) : WithTop α ≃ WithTop β where
  toFun := WithTop.map e
  invFun := WithTop.map e.symm
  left_inv x := by cases x <;> grind -- Unfortunately `grind` `cases` doesn't work with synonyms.
  right_inv x := by cases x <;> grind

attribute [grind =] withTopCongr_apply

@[simp]
theorem withTopCongr_refl : withTopCongr (Equiv.refl α) = Equiv.refl _ :=
  Equiv.ext <| congr_fun WithTop.map_id

@[simp, grind =]
theorem withTopCongr_symm (e : α ≃ β) : withTopCongr e.symm = (withTopCongr e).symm :=
  rfl

@[simp]
theorem withTopCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    withTopCongr (e₁.trans e₂) = (withTopCongr e₁).trans (withTopCongr e₂) := by
  ext x
  simp

end Equiv

namespace WithTop

variable {a b : α}

section LE

variable [LE α] {x y : WithTop α}

/-- The order on `WithTop α`, defined by `⊤ ≤ ⊤`, `↑a ≤ ⊤` and `a ≤ b → ↑a ≤ ↑b`. -/
instance (priority := 10) instLE : LE (WithTop α) where le a b := WithBot.LE (α := αᵒᵈ) b a

lemma le_def : x ≤ y ↔ y = ⊤ ∨ ∃ a b : α, a ≤ b ∧ x = a ∧ y = b :=
  WithBot.le_def.trans <| or_congr_right <| exists_swap.trans <| exists₂_congr fun _ _ ↦
    and_congr_right' and_comm

lemma le_iff_forall : x ≤ y ↔ ∀ b : α, y = ↑b → ∃ a : α, x = ↑a ∧ a ≤ b := by
  cases x <;> cases y <;> simp [le_def]

@[simp, norm_cast] lemma coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b := by simp [le_def]

lemma not_top_le_coe (a : α) : ¬ ⊤ ≤ (a : WithTop α) := by simp [le_def]

instance orderTop : OrderTop (WithTop α) where le_top := by simp [le_def]

instance orderBot [OrderBot α] : OrderBot (WithTop α) where bot_le x := by cases x <;> simp [le_def]

instance boundedOrder [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

/-- There is a general version `top_le_iff`, but this lemma does not require a `PartialOrder`. -/
@[simp]
protected theorem top_le_iff : ∀ {a : WithTop α}, ⊤ ≤ a ↔ a = ⊤
  | (a : α) => by simp [not_top_le_coe _]
  | ⊤ => by simp

theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ (equivOption.symm o) b ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem le_coe_iff : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b := by simp [le_iff_forall]
theorem coe_le_iff : ↑a ≤ x ↔ ∀ b : α, x = ↑b → a ≤ b := by simp [le_iff_forall]

protected theorem _root_.IsMin.withTop (h : IsMin a) : IsMin (a : WithTop α) :=
  fun x ↦ by cases x <;> simp; simpa using @h _

lemma untop_le_iff (hx : x ≠ ⊤) : untop x hx ≤ b ↔ x ≤ b := by lift x to α using id hx; simp
lemma le_untop_iff (hy : y ≠ ⊤) : a ≤ untop y hy ↔ a ≤ y := by lift y to α using id hy; simp

lemma untopD_le_iff (hy : y ≠ ⊤) : y.untopD a ≤ b ↔ y ≤ b := by lift y to α using id hy; simp
lemma le_untopD_iff (hy : y = ⊤ → a ≤ b) : a ≤ y.untopD b ↔ a ≤ y := by cases y <;> simp [hy]

lemma untopA_le_iff [Nonempty α] (hy : y ≠ ⊤) : y.untopA ≤ b ↔ y ≤ b := untopD_le_iff hy
lemma le_untopA_iff [Nonempty α] (hy : y ≠ ⊤) : a ≤ y.untopA ↔ a ≤ y := by
  lift y to α using id hy; simp

lemma untop_mono (hx : x ≠ ⊤) (hy : y ≠ ⊤) (h : x ≤ y) :
    x.untop hx ≤ y.untop hy := by
  lift x to α using id hx
  lift y to α using id hy
  simp only [untop_coe]
  exact mod_cast h

lemma untopD_mono (hy : y ≠ ⊤) (h : x ≤ y) :
    x.untopD a ≤ y.untopD a := by
  lift y to α using hy
  cases x with
  | top => simp at h
  | coe a => simp only [WithTop.untopD_coe]; exact mod_cast h

lemma untopA_mono [Nonempty α] (hy : y ≠ ⊤) (h : x ≤ y) :
    x.untopA ≤ y.untopA := untopD_mono hy h

end LE

section LT

variable [LT α] {x y : WithTop α}

/-- The order on `WithTop α`, defined by `↑a < ⊤` and `a < b → ↑a < ↑b`. -/
instance (priority := 10) instLT : LT (WithTop α) where
  -- We match on `b, a` rather than `a, b` to keep the defeq with `WithBot.instLT (α := αᵒᵈ)`
  lt a b := match b, a with
  | ⊤, ⊤ => False
  | (b : α), ⊤ => False
  | ⊤, (a : α) => True
  | (b : α), (a : α) => a < b

lemma lt_def : x < y ↔ ∃ a : α, x = ↑a ∧ ∀ b : α, y = ↑b → a < b := by
  cases x <;> cases y <;> simp [LT.lt]

@[simp, norm_cast] lemma coe_lt_coe : (a : WithTop α) < b ↔ a < b := by simp [lt_def]
@[simp] lemma coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by simp [lt_def]
@[simp] protected lemma not_top_lt (a : WithTop α) : ¬⊤ < a := by simp [lt_def]

lemma lt_iff_exists_coe : x < y ↔ ∃ a : α, x = a ∧ a < y := by cases x <;> simp

lemma coe_lt_iff : a < y ↔ ∀ b : α, y = b → a < b := by simp [lt_def]

/-- A version of `lt_top_iff_ne_top` for `WithTop` that only requires `LT α`, not
`PartialOrder α`. -/
protected lemma lt_top_iff_ne_top : x < ⊤ ↔ x ≠ ⊤ := by cases x <;> simp

@[simp] lemma lt_untop_iff (hy : y ≠ ⊤) : a < y.untop hy ↔ a < y := by lift y to α using id hy; simp
@[simp] lemma untop_lt_iff (hx : x ≠ ⊤) : x.untop hx < b ↔ x < b := by lift x to α using id hx; simp

lemma lt_untopD_iff (hy : y = ⊤ → a < b) : a < y.untopD b ↔ a < y := by cases y <;> simp [hy]
lemma untopD_lt_iff (hx : x ≠ ⊤) : x.untopD a < b ↔ x < b := by
  lift x to α using id hx; simp

lemma lt_untopA_iff [Nonempty α] (hy : y ≠ ⊤) : a < y.untopA ↔ a < y := by
  lift y to α using id hy; simp
lemma untopA_lt_iff [Nonempty α] (hx : x ≠ ⊤) : x.untopA < b ↔ x < b := untopD_lt_iff hx

end LT

instance preorder [Preorder α] : Preorder (WithTop α) where
  lt_iff_le_not_ge x y := by cases x <;> cases y <;> simp [lt_iff_le_not_ge]
  le_refl x := by cases x <;> simp [le_def]
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp [le_def]; simpa using le_trans

instance partialOrder [PartialOrder α] : PartialOrder (WithTop α) where
  le_antisymm x y := by cases x <;> cases y <;> simp [le_def]; simpa using le_antisymm

section Preorder

variable [Preorder α] [Preorder β] {x y : WithTop α}

theorem coe_strictMono : StrictMono (fun a : α => (a : WithTop α)) := fun _ _ => coe_lt_coe.2

theorem coe_mono : Monotone (fun a : α => (a : WithTop α)) := fun _ _ => coe_le_coe.2

theorem monotone_iff {f : WithTop α → β} :
    Monotone f ↔ Monotone (fun (a : α) => f a) ∧ ∀ x : α, f x ≤ f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_mono, fun _ => h le_top⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨fun _ => le_rfl, fun _ h => (not_top_le_coe _ h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[simp]
theorem monotone_map_iff {f : α → β} : Monotone (WithTop.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

alias ⟨_, _root_.Monotone.withTop_map⟩ := monotone_map_iff

theorem strictMono_iff {f : WithTop α → β} :
    StrictMono f ↔ StrictMono (fun (a : α) => f a) ∧ ∀ x : α, f x < f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_strictMono, fun _ => h (coe_lt_top _)⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨flip absurd (lt_irrefl _), fun _ h => (not_top_lt h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

theorem strictAnti_iff {f : WithTop α → β} :
    StrictAnti f ↔ StrictAnti (fun a ↦ f a : α → β) ∧ ∀ x : α, f ⊤ < f x :=
  strictMono_iff (β := βᵒᵈ)

@[simp]
theorem strictMono_map_iff {f : α → β} : StrictMono (WithTop.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, coe_lt_top]

alias ⟨_, _root_.StrictMono.withTop_map⟩ := strictMono_map_iff

theorem map_le_iff (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    x.map f ≤ y.map f ↔ x ≤ y := by cases x <;> cases y <;> simp [mono_iff]

theorem coe_untopD_le (y : WithTop α) (a : α) : y.untopD a ≤ y := by cases y <;> simp

@[simp]
theorem coe_top_lt [OrderTop α] : (⊤ : α) < x ↔ x = ⊤ := by cases x <;> simp

lemma eq_top_iff_forall_gt : y = ⊤ ↔ ∀ a : α, a < y := by
  cases y <;> simp; simpa using ⟨_, lt_irrefl _⟩

lemma eq_top_iff_forall_ge [NoTopOrder α] : y = ⊤ ↔ ∀ a : α, a ≤ y :=
  WithBot.eq_bot_iff_forall_le (α := αᵒᵈ)

@[deprecated (since := "2025-03-19")] alias forall_gt_iff_eq_top := eq_top_iff_forall_gt
@[deprecated (since := "2025-03-19")] alias forall_ge_iff_eq_top := eq_top_iff_forall_ge

lemma forall_coe_le_iff_le [NoTopOrder α] : (∀ a : α, a ≤ x → a ≤ y) ↔ x ≤ y :=
  WithBot.forall_le_coe_iff_le (α := αᵒᵈ)

lemma forall_le_coe_iff_le [NoTopOrder α] : (∀ a : α, y ≤ a → x ≤ a) ↔ x ≤ y :=
  WithBot.forall_coe_le_iff_le (α := αᵒᵈ)

end Preorder

section PartialOrder
variable [PartialOrder α] {x y : WithTop α}

lemma untopD_le (hy : y ≤ b) : y.untopD a ≤ b := by
  rwa [untopD_le_iff]
  exact ne_top_of_le_ne_top (by simp) hy

lemma untopA_le [Nonempty α] (hy : y ≤ b) : y.untopA ≤ b := untopD_le hy

variable [NoTopOrder α]

lemma eq_of_forall_le_coe_iff (h : ∀ a : α, x ≤ a ↔ y ≤ a) : x = y :=
  WithBot.eq_of_forall_coe_le_iff (α := αᵒᵈ) h

lemma eq_of_forall_coe_le_iff (h : ∀ a : α, a ≤ x ↔ a ≤ y) : x = y :=
  WithBot.eq_of_forall_le_coe_iff (α := αᵒᵈ) h

end PartialOrder

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithTop α) where
  inf
    -- note this is `Option.merge`, but with the right defeq when unfolding
    | ⊤, ⊤ => ⊤
    | (a : α), ⊤ => a
    | ⊤, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊓ b)
  inf_le_left x y := by cases x <;> cases y <;> simp
  inf_le_right x y := by cases x <;> cases y <;> simp
  le_inf x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using le_inf

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = (a : WithTop α) ⊓ b :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithTop α) where
  sup := .map₂ (· ⊔ ·)
  le_sup_left x y := by cases x <;> cases y <;> simp
  le_sup_right x y := by cases x <;> cases y <;> simp
  sup_le x y z := by cases x <;> cases y <;> cases z <;> simp; simpa using sup_le

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = (a : WithTop α) ⊔ b :=
  rfl

instance lattice [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance distribLattice [DistribLattice α] : DistribLattice (WithTop α) where
  le_sup_inf x y z := by
    cases x <;> cases y <;> cases z <;> simp [← coe_inf, ← coe_sup]
    simpa [← coe_inf, ← coe_sup] using le_sup_inf

instance decidableEq [DecidableEq α] : DecidableEq (WithTop α) :=
  inferInstanceAs <| DecidableEq (WithBot α)

instance decidableLE [LE α] [DecidableLE α] : DecidableLE (WithTop α)
  | _, ⊤ => isTrue <| by simp
  | ⊤, (a : α) => isFalse <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_le_coe

instance decidableLT [LT α] [DecidableLT α] : DecidableLT (WithTop α)
  | ⊤, _ => isFalse <| by simp
  | (a : α), ⊤ => isTrue <| by simp
  | (a : α), (b : α) => decidable_of_iff' _ coe_lt_coe

instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) where
  total x y := by cases x <;> cases y <;> simp; simpa using IsTotal.total ..

section LinearOrder
variable [LinearOrder α] {x y : WithTop α}

instance linearOrder [LinearOrder α] : LinearOrder (WithTop α) := Lattice.toLinearOrder _

@[simp, norm_cast] lemma coe_min (a b : α) : ↑(min a b) = min (a : WithTop α) b := rfl
@[simp, norm_cast] lemma coe_max (a b : α) : ↑(max a b) = max (a : WithTop α) b := rfl

variable [DenselyOrdered α] [NoMaxOrder α]

lemma le_of_forall_lt_iff_le : (∀ b : α, x < b → y ≤ b) ↔ y ≤ x := by
  cases x <;> cases y <;> simp [exists_gt, forall_gt_imp_ge_iff_le_of_dense]

lemma ge_of_forall_gt_iff_ge : (∀ a : α, a < x → a ≤ y) ↔ x ≤ y := by
  cases x <;> cases y <;> simp [exists_gt, forall_lt_imp_le_iff_le_of_dense]

end LinearOrder

instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithTop α) :=
  inferInstanceAs <| WellFoundedLT (WithBot αᵒᵈ)ᵒᵈ

instance instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithTop α) :=
  inferInstanceAs <| WellFoundedGT (WithBot αᵒᵈ)ᵒᵈ

instance trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithTop α) (· < ·) where
  trichotomous x y := by cases x <;> cases y <;> simp [trichotomous]

instance IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] : IsWellOrder (WithTop α) (· < ·) where

instance trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithTop α) (· > ·) :=
  have : IsTrichotomous α (· < ·) := .swap _; .swap _

instance IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] : IsWellOrder (WithTop α) (· > ·) where

instance _root_.WithBot.trichotomous.lt [Preorder α] [h : IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithBot α) (· < ·) where
  trichotomous x y := by cases x <;> cases y <;> simp [trichotomous]

instance _root_.WithBot.isWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
    IsWellOrder (WithBot α) (· < ·) where

instance _root_.WithBot.trichotomous.gt [Preorder α] [h : IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithBot α) (· > ·) where
  trichotomous x y := by cases x <;> cases y <;> simp; simpa using trichotomous_of (· > ·) ..

instance _root_.WithBot.isWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) where
  trichotomous x y := by cases x <;> cases y <;> simp; simpa using trichotomous_of (· > ·) ..

lemma denselyOrdered_iff [LT α] [NoMaxOrder α] :
    DenselyOrdered (WithTop α) ↔ DenselyOrdered α := by
  constructor <;> intro h <;> constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := exists_between (coe_lt_coe.mpr hab)
    induction c with
    | top => simp at hc
    | coe c => exact ⟨c, by simpa using hc⟩
  · simpa [WithTop.exists, WithTop.forall, exists_gt] using DenselyOrdered.dense

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  denselyOrdered_iff.mpr inferInstance

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

instance noBotOrder [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) where
  exists_not_ge := fun
    | ⊤ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hba⟩ := exists_not_ge a; ⟨b, mod_cast hba⟩

instance noMinOrder [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) where
  exists_lt := fun
    | ⊤ => ‹Nonempty α›.elim fun a ↦ ⟨a, by simp⟩
    | (a : α) => let ⟨b, hab⟩ := exists_lt a; ⟨b, mod_cast hab⟩

end WithTop

section WithBotWithTop

lemma WithBot.eq_top_iff_forall_ge [Preorder α] [Nonempty α] [NoTopOrder α]
    {x : WithBot (WithTop α)} : x = ⊤ ↔ ∀ a : α, a ≤ x := by
  refine ⟨by simp_all, fun H ↦ ?_⟩
  induction x
  · simp at H
  · simpa [WithTop.eq_top_iff_forall_ge] using H

end WithBotWithTop

/-! ### `(WithBot α)ᵒᵈ ≃ WithTop αᵒᵈ`, `(WithTop α)ᵒᵈ ≃ WithBot αᵒᵈ` -/

open OrderDual

namespace WithBot

@[simp]
lemma toDual_symm_apply (a : WithTop αᵒᵈ) : WithBot.toDual.symm a = WithTop.ofDual a :=
  rfl

@[simp]
lemma ofDual_symm_apply (a : WithTop α) : WithBot.ofDual.symm a = WithTop.toDual a :=
  rfl

@[simp] lemma toDual_apply_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ := rfl
@[simp] lemma ofDual_apply_bot : WithBot.ofDual (⊥ : WithBot α) = ⊤ := rfl

@[simp] lemma toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a := rfl
@[simp] lemma ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a := rfl

lemma map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithTop α) :
    WithBot.map f (WithTop.toDual a) = a.map (toDual ∘ f) := rfl

lemma map_ofDual (f : α → β) (a : WithTop αᵒᵈ) :
    WithBot.map f (WithTop.ofDual a) = a.map (ofDual ∘ f) := rfl

lemma toDual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (WithBot.map f a) = map (toDual ∘ f ∘ ofDual) (WithBot.toDual a) := rfl

lemma ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (WithBot.map f a) = map (ofDual ∘ f ∘ toDual) (WithBot.ofDual a) := rfl

end WithBot

section LE
variable [LE α]

lemma WithBot.toDual_le_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual ≤ y ↔ WithTop.ofDual y ≤ x := by
  cases x <;> cases y <;> simp [toDual_le]

lemma WithBot.le_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x ≤ WithBot.toDual y ↔ y ≤ WithTop.ofDual x := by cases x <;> cases y <;> simp [le_toDual]

@[simp]
lemma WithBot.toDual_le_toDual_iff {x y : WithBot α} : x.toDual ≤ y.toDual ↔ y ≤ x := by
  cases x <;> cases y <;> simp

lemma WithBot.ofDual_le_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x ≤ y ↔ y.toDual ≤ x := by cases x <;> cases y <;> simp [toDual_le]

lemma WithBot.le_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x ≤ WithBot.ofDual y ↔ y ≤ x.toDual := by cases x <;> cases y <;> simp [le_toDual]

@[simp]
lemma WithBot.ofDual_le_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x ≤ WithBot.ofDual y ↔ y ≤ x := by cases x <;> cases y <;> simp

lemma WithTop.toDual_le_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x.toDual ≤ y ↔ WithBot.ofDual y ≤ x := by cases x <;> cases y <;> simp [toDual_le]

lemma WithTop.le_toDual_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    x ≤ WithTop.toDual y ↔ y ≤ WithBot.ofDual x := by cases x <;> cases y <;> simp [le_toDual]

@[simp]
lemma WithTop.toDual_le_toDual_iff {x y : WithTop α} : x.toDual ≤ y.toDual ↔ y ≤ x := by
  cases x <;> cases y <;> simp [le_toDual]

lemma WithTop.ofDual_le_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    WithTop.ofDual x ≤ y ↔ y.toDual ≤ x := by cases x <;> cases y <;> simp [toDual_le]

lemma WithTop.le_ofDual_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x ≤ WithTop.ofDual y ↔ y ≤ x.toDual := by cases x <;> cases y <;> simp [le_toDual]

@[simp]
lemma WithTop.ofDual_le_ofDual_iff {x y : WithTop αᵒᵈ} :
    WithTop.ofDual x ≤ WithTop.ofDual y ↔ y ≤ x := by cases x <;> cases y <;> simp

end LE

section LT
variable [LT α]

lemma WithBot.toDual_lt_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x.toDual < y ↔ WithTop.ofDual y < x := by cases x <;> cases y <;> simp [toDual_lt]

lemma WithBot.lt_toDual_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    x < y.toDual ↔ y < WithTop.ofDual x := by cases x <;> cases y <;> simp [lt_toDual]

@[simp]
lemma WithBot.toDual_lt_toDual_iff {x y : WithBot α} : x.toDual < y.toDual ↔ y < x := by
  cases x <;> cases y <;> simp

lemma WithBot.ofDual_lt_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    WithBot.ofDual x < y ↔ y.toDual < x := by cases x <;> cases y <;> simp [toDual_lt]

lemma WithBot.lt_ofDual_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    x < WithBot.ofDual y ↔ y < x.toDual := by cases x <;> cases y <;> simp [lt_toDual]

@[simp]
lemma WithBot.ofDual_lt_ofDual_iff {x y : WithBot αᵒᵈ} :
    WithBot.ofDual x < WithBot.ofDual y ↔ y < x := by cases x <;> cases y <;> simp

lemma WithTop.toDual_lt_iff {x : WithTop α} {y : WithBot αᵒᵈ} :
    WithTop.toDual x < y ↔ WithBot.ofDual y < x := by cases x <;> cases y <;> simp [toDual_lt]

lemma WithTop.lt_toDual_iff {x : WithBot αᵒᵈ} {y : WithTop α} :
    x < WithTop.toDual y ↔ y < WithBot.ofDual x := by cases x <;> cases y <;> simp [lt_toDual]

@[simp]
lemma WithTop.toDual_lt_toDual_iff {x y : WithTop α} :
    WithTop.toDual x < WithTop.toDual y ↔ y < x := by cases x <;> cases y <;> simp

lemma WithTop.ofDual_lt_iff {x : WithTop αᵒᵈ} {y : WithBot α} :
    WithTop.ofDual x < y ↔ WithBot.toDual y < x := by cases x <;> cases y <;> simp [toDual_lt]

lemma WithTop.lt_ofDual_iff {x : WithBot α} {y : WithTop αᵒᵈ} :
    x < WithTop.ofDual y ↔ y < WithBot.toDual x := by cases x <;> cases y <;> simp [lt_toDual]

@[simp]
lemma WithTop.ofDual_lt_ofDual_iff {x y : WithTop αᵒᵈ} :
    WithTop.ofDual x < WithTop.ofDual y ↔ y < x := by cases x <;> cases y <;> simp

end LT
