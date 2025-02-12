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

 -/

variable {α β γ δ : Type*}

namespace WithBot

variable {a b : α}

instance nontrivial [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

open Function

theorem coe_injective : Injective ((↑) : α → WithBot α) :=
  Option.some_injective _

@[simp, norm_cast]
theorem coe_inj : (a : WithBot α) = b ↔ a = b :=
  Option.some_inj

protected theorem «forall» {p : WithBot α → Prop} : (∀ x, p x) ↔ p ⊥ ∧ ∀ x : α, p x :=
  Option.forall

protected theorem «exists» {p : WithBot α → Prop} : (∃ x, p x) ↔ p ⊥ ∨ ∃ x : α, p x :=
  Option.exists

theorem none_eq_bot : (none : WithBot α) = (⊥ : WithBot α) :=
  rfl

theorem some_eq_coe (a : α) : (Option.some a : WithBot α) = (↑a : WithBot α) :=
  rfl

@[simp]
theorem bot_ne_coe : ⊥ ≠ (a : WithBot α) :=
  nofun

@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  nofun

/-- Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries.
-/
def unbot' (d : α) (x : WithBot α) : α :=
  recBotCoe d id x

@[simp]
theorem unbot'_bot {α} (d : α) : unbot' d ⊥ = d :=
  rfl

@[simp]
theorem unbot'_coe {α} (d x : α) : unbot' d x = x :=
  rfl

theorem coe_eq_coe : (a : WithBot α) = b ↔ a = b := coe_inj

theorem unbot'_eq_iff {d y : α} {x : WithBot α} : unbot' d x = y ↔ x = y ∨ x = ⊥ ∧ y = d := by
  induction x <;> simp [@eq_comm _ d]

@[simp] theorem unbot'_eq_self_iff {d : α} {x : WithBot α} : unbot' d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbot'_eq_iff]

theorem unbot'_eq_unbot'_iff {d : α} {x y : WithBot α} :
    unbot' d x = unbot' d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
 induction y <;> simp [unbot'_eq_iff, or_comm]

/-- Lift a map `f : α → β` to `WithBot α → WithBot β`. Implemented using `Option.map`. -/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f

@[simp]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[simp]
lemma map_eq_bot_iff {f : α → β} {a : WithBot α} :
    map f a = ⊥ ↔ a = ⊥ := Option.map_eq_none'

theorem map_eq_some_iff {f : α → β} {y : β} {v : WithBot α} :
    WithBot.map f v = .some y ↔ ∃ x, v = .some x ∧ f x = y := Option.map_eq_some'

theorem some_eq_map_iff {f : α → β} {y : β} {v : WithBot α} :
    .some y = WithBot.map f v ↔ ∃ x, v = .some x ∧ f x = y := by
  cases v <;> simp [eq_comm]

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

/-- The image of a binary function `f : α → β → γ` as a function
`WithBot α → WithBot β → WithBot γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ : (α → β → γ) → WithBot α → WithBot β → WithBot γ := Option.map₂

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f ⊥ b = ⊥ := rfl
@[simp] lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a ⊥ = ⊥ := by cases a <;> rfl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithBot α} {b : WithBot β} :
    map₂ f a b = ⊥ ↔ a = ⊥ ∨ b = ⊥ := Option.map₂_eq_none_iff

lemma ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x := Option.ne_none_iff_exists

lemma forall_ne_iff_eq_bot {x : WithBot α} : (∀ a : α, ↑a ≠ x) ↔ x = ⊥ :=
  Option.forall_some_ne_iff_eq_none

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

/-- The equivalence between the non-bottom elements of `WithBot α` and `α`. -/
@[simps] def _root_.Equiv.withBotSubtypeNe : {y : WithBot α // y ≠ ⊥} ≃ α where
  toFun := fun ⟨x,h⟩ => WithBot.unbot x h
  invFun x := ⟨x, WithBot.coe_ne_bot⟩
  left_inv _ := by simp
  right_inv _ := by simp

section LE

variable [LE α]

instance (priority := 10) le : LE (WithBot α) :=
  ⟨fun o₁ o₂ => ∀ a : α, o₁ = ↑a → ∃ b : α, o₂ = ↑b ∧ a ≤ b⟩

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b := by
  simp [LE.le]

instance orderBot : OrderBot (WithBot α) where
  bot_le _ := fun _ h => Option.noConfusion h

@[simp, deprecated coe_le_coe "Don't mix Option and WithBot" (since := "2024-05-27")]
theorem some_le_some : @LE.le (WithBot α) _ (Option.some a) (Option.some b) ↔ a ≤ b :=
  coe_le_coe

@[simp, deprecated bot_le "Don't mix Option and WithBot" (since := "2024-05-27")]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := bot_le

instance orderTop [OrderTop α] : OrderTop (WithBot α) where
  le_top o a ha := by cases ha; exact ⟨_, rfl, le_top⟩

instance instBoundedOrder [OrderTop α] : BoundedOrder (WithBot α) :=
  { WithBot.orderBot, WithBot.orderTop with }

theorem not_coe_le_bot (a : α) : ¬(a : WithBot α) ≤ ⊥ := fun h =>
  let ⟨_, hb, _⟩ := h _ rfl
  Option.not_mem_none _ hb

/-- There is a general version `le_bot_iff`, but this lemma does not require a `PartialOrder`. -/
@[simp]
protected theorem le_bot_iff : ∀ {a : WithBot α}, a ≤ ⊥ ↔ a = ⊥
  | (a : α) => by simp [not_coe_le_bot _]
  | ⊥ => by simp

theorem coe_le : ∀ {o : Option α}, b ∈ o → ((a : WithBot α) ≤ o ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem coe_le_iff : ∀ {x : WithBot α}, (a : WithBot α) ≤ x ↔ ∃ b : α, x = b ∧ a ≤ b
  | (x : α) => by simp
  | ⊥ => iff_of_false (not_coe_le_bot _) <| by simp

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b
  | (b : α) => by simp
  | ⊥ => by simp

protected theorem _root_.IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α)
  | ⊥, _ => bot_le
  | (_ : α), hb => coe_le_coe.2 <| h <| coe_le_coe.1 hb

theorem le_unbot_iff {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a ≤ unbot b h ↔ (a : WithBot α) ≤ b := by
  match b, h with
  | some _, _ => simp only [unbot_coe, coe_le_coe]

theorem unbot_le_iff {a : WithBot α} (h : a ≠ ⊥) {b : α} :
    unbot a h ≤ b ↔ a ≤ (b : WithBot α) := by
  match a, h with
  | some _, _ => simp only [unbot_coe, coe_le_coe]

theorem unbot'_le_iff {a : WithBot α} {b c : α} (h : a = ⊥ → b ≤ c) :
    a.unbot' b ≤ c ↔ a ≤ c := by
  induction a
  · simpa using h rfl
  · simp

end LE

section LT

variable [LT α]

instance (priority := 10) lt : LT (WithBot α) :=
  ⟨fun o₁ o₂ : WithBot α => ∃ b : α, o₂ = ↑b ∧ ∀ a : α, o₁ = ↑a → a < b⟩

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b := by
  simp [LT.lt]

@[simp]
theorem bot_lt_coe (a : α) : ⊥ < (a : WithBot α) :=
  ⟨a, rfl, fun _ hb => (Option.not_mem_none _ hb).elim⟩

@[simp]
protected theorem not_lt_bot (a : WithBot α) : ¬a < ⊥ :=
  fun ⟨_, h, _⟩ => Option.not_mem_none _ h

@[simp, deprecated coe_lt_coe "Don't mix Option and WithBot" (since := "2024-05-27")]
theorem some_lt_some : @LT.lt (WithBot α) _ (Option.some a) (Option.some b) ↔ a < b :=
  coe_lt_coe

@[simp, deprecated bot_lt_coe "Don't mix Option and WithBot" (since := "2024-05-27")]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) := bot_lt_coe _

@[simp, deprecated not_lt_bot "Don't mix Option and WithBot" (since := "2024-05-27")]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none := WithBot.not_lt_bot _

theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, some b => by simp [coe_eq_coe]
  | a, ⊥ => iff_of_false (WithBot.not_lt_bot _) <| by simp

theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a : α, x = a → a < b
  | (_ : α) => by simp
  | ⊥ => by simp [bot_lt_coe]

/-- A version of `bot_lt_iff_ne_bot` for `WithBot` that only requires `LT α`, not
`PartialOrder α`. -/
protected theorem bot_lt_iff_ne_bot : ∀ {x : WithBot α}, ⊥ < x ↔ x ≠ ⊥
  | ⊥ => iff_of_false (WithBot.not_lt_bot _) <| by simp
  | (x : α) => by simp [bot_lt_coe]

theorem lt_unbot_iff {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a < unbot b h ↔ (a : WithBot α) < b := by
  induction b
  · simpa [bot_lt_coe] using h rfl
  · simp

theorem unbot_lt_iff {a : WithBot α} (h : a ≠ ⊥) {b : α} :
    unbot a h < b ↔ a < (b : WithBot α) := by
  induction a
  · simpa [bot_lt_coe] using h rfl
  · simp

theorem unbot'_lt_iff {a : WithBot α} {b c : α} (h : a = ⊥ → b < c) :
    a.unbot' b < c ↔ a < c := by
  induction a
  · simpa [bot_lt_coe] using h rfl
  · simp

end LT

instance preorder [Preorder α] : Preorder (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros a b
    cases a <;> cases b <;> simp [lt_iff_le_not_le]
  le_refl _ a ha := ⟨a, ha, le_rfl⟩
  le_trans _ _ _ h₁ h₂ a ha :=
    let ⟨b, hb, ab⟩ := h₁ a ha
    let ⟨c, hc, bc⟩ := h₂ b hb
    ⟨c, hc, le_trans ab bc⟩

instance partialOrder [PartialOrder α] : PartialOrder (WithBot α) :=
  { WithBot.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ ↦ by
      cases o₁ with
      | bot =>
        cases o₂ with
        | bot => rfl
        | coe b => obtain ⟨_, ⟨⟩, _⟩ := h₂ b rfl
      | coe a =>
        obtain ⟨b, ⟨⟩, h₁'⟩ := h₁ a rfl
        obtain ⟨_, ⟨⟩, h₂'⟩ := h₂ b rfl
        rw [le_antisymm h₁' h₂'] }

section Preorder

variable [Preorder α] [Preorder β]

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

theorem map_le_iff (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by simp only [map_bot, bot_le]
  | (a : α), ⊥ => by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff

theorem le_coe_unbot' : ∀ (a : WithBot α) (b : α), a ≤ a.unbot' b
  | (a : α), _ => le_rfl
  | ⊥, _ => bot_le

@[simp]
theorem lt_coe_bot [OrderBot α] : ∀ {x : WithBot α}, x < (⊥ : α) ↔ x = ⊥
  | (x : α) => by simp
  | ⊥ => by simp

end Preorder

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithBot α) where
  sup
    -- note this is `Option.liftOrGet`, but with the right defeq when unfolding
    | ⊥, ⊥ => ⊥
    | (a : α), ⊥ => a
    | ⊥, (b : α) => b
    | (a : α), (b : α) => ↑(a ⊔ b)
  le_sup_left := fun o₁ o₂ a ha => by cases ha; cases o₂ <;> simp
  le_sup_right := fun o₁ o₂ a ha => by cases ha; cases o₁ <;> simp
  sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
    cases o₁ with
    | bot =>
      cases o₂ with
      | bot => exact h₁ a ha
      | coe c => exact h₂ a ha
    | coe b =>
      cases o₂ with
      | bot => exact h₁ a ha
      | coe c =>
        cases ha
        obtain ⟨d, ⟨⟩, h₁'⟩ := h₁ b rfl
        simp only [coe_le_coe] at h₂
        exact ⟨d, rfl, sup_le h₁' h₂⟩

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = (a : WithBot α) ⊔ b :=
  rfl

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.partialOrder, @WithBot.orderBot α _ with
    inf := WithBot.map₂ (· ⊓ ·),
    inf_le_left := fun o₁ o₂ a ha => by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩
      exact ⟨_, rfl, inf_le_left⟩,
    inf_le_right := fun o₁ o₂ a ha => by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩
      exact ⟨_, rfl, inf_le_right⟩,
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, le_inf ab ac⟩ }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithBot α) = (a : WithBot α) ⊓ b :=
  rfl

instance lattice [Lattice α] : Lattice (WithBot α) :=
  { WithBot.semilatticeSup, WithBot.semilatticeInf with }

instance distribLattice [DistribLattice α] : DistribLattice (WithBot α) :=
  { WithBot.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊥, ⊥, ⊥ => le_rfl
      | ⊥, ⊥, (a₁ : α) => le_rfl
      | ⊥, (a₁ : α), ⊥ => le_rfl
      | ⊥, (a₁ : α), (a₃ : α) => le_rfl
      | (a₁ : α), ⊥, ⊥ => inf_le_left
      | (a₁ : α), ⊥, (a₃ : α) => inf_le_left
      | (a₁ : α), (a₂ : α), ⊥ => inf_le_right
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

instance decidableEq [DecidableEq α] : DecidableEq (WithBot α) :=
  inferInstanceAs <| DecidableEq (Option α)

instance decidableLE [LE α] [DecidableRel (α := α) (· ≤ ·)] : DecidableRel (α := WithBot α) (· ≤ ·)
  | none, _ => isTrue fun _ h => Option.noConfusion h
  | Option.some x, Option.some y =>
      if h : x ≤ y then isTrue (coe_le_coe.2 h) else isFalse <| by simp [*]
  | Option.some x, none => isFalse fun h => by rcases h x rfl with ⟨y, ⟨_⟩, _⟩

instance decidableLT [LT α] [DecidableRel (α := α) (· < ·)] : DecidableRel (α := WithBot α) (· < ·)
  | none, Option.some x => isTrue <| by exists x, rfl; rintro _ ⟨⟩
  | Option.some x, Option.some y =>
      if h : x < y then isTrue <| by simp [*] else isFalse <| by simp [*]
  | x, none => isFalse <| by rintro ⟨a, ⟨⟨⟩⟩⟩

instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | Option.some x, Option.some y => (total_of (· ≤ ·) x y).imp coe_le_coe.2 coe_le_coe.2⟩

instance linearOrder [LinearOrder α] : LinearOrder (WithBot α) :=
  Lattice.toLinearOrder _

@[simp, norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : ((min x y : α) : WithBot α) = min (x : WithBot α) y :=
  rfl

@[simp, norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : ((max x y : α) : WithBot α) = max (x : WithBot α) y :=
  rfl

instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithBot α) where
  wf :=
  have not_lt_bot : ∀ a : WithBot α, ¬ a < ⊥ := nofun
  have acc_bot := ⟨_, by simp [not_lt_bot]⟩
  .intro fun
    | ⊥ => acc_bot
    | (a : α) => (wellFounded_lt.1 a).rec fun _ _ ih =>
      .intro _ fun
        | ⊥, _ => acc_bot
        | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)

instance _root_.WithBot.instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) where
  wf :=
  have acc_some (a : α) : Acc ((· > ·) : WithBot α → WithBot α → Prop) a :=
    (wellFounded_gt.1 a).rec fun _ _ ih =>
      .intro _ fun
        | (b : α), hlt => ih _ (coe_lt_coe.1 hlt)
        | ⊥, hlt => absurd hlt (WithBot.not_lt_bot _)
  .intro fun
    | (a : α) => acc_some a
    | ⊥ => .intro _ fun
      | (b : α), _ => acc_some b
      | ⊥, hlt => absurd hlt (WithBot.not_lt_bot _)

instance denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  ⟨fun a b =>
    match a, b with
    | a, none => fun h : a < ⊥ => (WithBot.not_lt_bot _ h).elim
    | none, Option.some b => fun _ =>
      let ⟨a, ha⟩ := exists_lt b
      ⟨a, bot_lt_coe a, coe_lt_coe.2 ha⟩
    | Option.some _, Option.some _ => fun h =>
      let ⟨a, ha₁, ha₂⟩ := exists_between (coe_lt_coe.1 h)
      ⟨a, coe_lt_coe.2 ha₁, coe_lt_coe.2 ha₂⟩⟩

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMinOrder α] {a b : WithBot α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.1
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

instance noTopOrder [LE α] [NoTopOrder α] [Nonempty α] : NoTopOrder (WithBot α) :=
  ⟨by
    apply recBotCoe
    · exact ‹Nonempty α›.elim fun a => ⟨a, not_coe_le_bot a⟩

    · intro a
      obtain ⟨b, h⟩ := exists_not_le a
      exact ⟨b, by rwa [coe_le_coe]⟩
      ⟩

instance noMaxOrder [LT α] [NoMaxOrder α] [Nonempty α] : NoMaxOrder (WithBot α) :=
  ⟨by
    apply WithBot.recBotCoe
    · apply ‹Nonempty α›.elim
      exact fun a => ⟨a, WithBot.bot_lt_coe a⟩

    · intro a
      obtain ⟨b, ha⟩ := exists_gt a
      exact ⟨b, coe_lt_coe.mpr ha⟩
      ⟩

end WithBot

namespace WithTop

variable {a b : α}

instance nontrivial [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

open Function

theorem coe_injective : Injective ((↑) : α → WithTop α) :=
  Option.some_injective _

@[norm_cast]
theorem coe_inj : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj

protected theorem «forall» {p : WithTop α → Prop} : (∀ x, p x) ↔ p ⊤ ∧ ∀ x : α, p x :=
  Option.forall

protected theorem «exists» {p : WithTop α → Prop} : (∃ x, p x) ↔ p ⊤ ∨ ∃ x : α, p x :=
  Option.exists

theorem none_eq_top : (none : WithTop α) = (⊤ : WithTop α) :=
  rfl

theorem some_eq_coe (a : α) : (Option.some a : WithTop α) = (↑a : WithTop α) :=
  rfl

@[simp]
theorem top_ne_coe : ⊤ ≠ (a : WithTop α) :=
  nofun

@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  nofun

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
def untop' (d : α) (x : WithTop α) : α :=
  recTopCoe d id x

@[simp]
theorem untop'_top {α} (d : α) : untop' d ⊤ = d :=
  rfl

@[simp]
theorem untop'_coe {α} (d x : α) : untop' d x = x :=
  rfl

@[simp, norm_cast] -- Porting note: added `simp`
theorem coe_eq_coe : (a : WithTop α) = b ↔ a = b :=
  Option.some_inj

theorem untop'_eq_iff {d y : α} {x : WithTop α} : untop' d x = y ↔ x = y ∨ x = ⊤ ∧ y = d :=
  WithBot.unbot'_eq_iff

@[simp] theorem untop'_eq_self_iff {d : α} {x : WithTop α} : untop' d x = d ↔ x = d ∨ x = ⊤ :=
  WithBot.unbot'_eq_self_iff

theorem untop'_eq_untop'_iff {d : α} {x y : WithTop α} :
    untop' d x = untop' d y ↔ x = y ∨ x = d ∧ y = ⊤ ∨ x = ⊤ ∧ y = d :=
  WithBot.unbot'_eq_unbot'_iff

/-- Lift a map `f : α → β` to `WithTop α → WithTop β`. Implemented using `Option.map`. -/
def map (f : α → β) : WithTop α → WithTop β :=
  Option.map f

@[simp]
theorem map_top (f : α → β) : map f ⊤ = ⊤ :=
  rfl

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[simp]
lemma map_eq_top_iff {f : α → β} {a : WithTop α} :
    map f a = ⊤ ↔ a = ⊤ := Option.map_eq_none'

theorem map_eq_some_iff {f : α → β} {y : β} {v : WithTop α} :
    WithTop.map f v = .some y ↔ ∃ x, v = .some x ∧ f x = y := Option.map_eq_some'

theorem some_eq_map_iff {f : α → β} {y : β} {v : WithTop α} :
    .some y = WithTop.map f v ↔ ∃ x, v = .some x ∧ f x = y := by
  cases v <;> simp [eq_comm]

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

/-- The image of a binary function `f : α → β → γ` as a function
`WithTop α → WithTop β → WithTop γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ : (α → β → γ) → WithTop α → WithTop β → WithTop γ := Option.map₂

lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[simp] lemma map₂_top_left (f : α → β → γ) (b) : map₂ f ⊤ b = ⊤ := rfl
@[simp] lemma map₂_top_right (f : α → β → γ) (a) : map₂ f a ⊤ = ⊤ := by cases a <;> rfl
@[simp] lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[simp] lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[simp] lemma map₂_eq_top_iff {f : α → β → γ} {a : WithTop α} {b : WithTop β} :
    map₂ f a b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := Option.map₂_eq_none_iff

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

lemma ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x := Option.ne_none_iff_exists

lemma forall_ne_iff_eq_top {x : WithTop α} : (∀ a : α, ↑a ≠ x) ↔ x = ⊤ :=
  Option.forall_some_ne_iff_eq_none

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

/-- The equivalence between the non-top elements of `WithTop α` and `α`. -/
@[simps] def _root_.Equiv.withTopSubtypeNe : {y : WithTop α // y ≠ ⊤} ≃ α where
  toFun := fun ⟨x,h⟩ => WithTop.untop x h
  invFun x := ⟨x, WithTop.coe_ne_top⟩
  left_inv _ := by simp
  right_inv _:= by simp

section LE

variable [LE α]

instance (priority := 10) le : LE (WithTop α) :=
  ⟨fun o₁ o₂ => ∀ a : α, o₂ = ↑a → ∃ b : α, o₁ = ↑b ∧ b ≤ a⟩

theorem toDual_le_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    WithTop.toDual a ≤ b ↔ WithBot.ofDual b ≤ a :=
  Iff.rfl

theorem le_toDual_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    a ≤ WithTop.toDual b ↔ b ≤ WithBot.ofDual a :=
  Iff.rfl

@[simp]
theorem toDual_le_toDual_iff {a b : WithTop α} : WithTop.toDual a ≤ WithTop.toDual b ↔ b ≤ a :=
  Iff.rfl

theorem ofDual_le_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    WithTop.ofDual a ≤ b ↔ WithBot.toDual b ≤ a :=
  Iff.rfl

theorem le_ofDual_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    a ≤ WithTop.ofDual b ↔ b ≤ WithBot.toDual a :=
  Iff.rfl

@[simp]
theorem ofDual_le_ofDual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a ≤ WithTop.ofDual b ↔ b ≤ a :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe : (a : WithTop α) ≤ b ↔ a ≤ b := by
  simp only [← toDual_le_toDual_iff, toDual_apply_coe, WithBot.coe_le_coe, toDual_le_toDual]

@[simp, deprecated coe_le_coe "Don't mix Option and WithTop" (since := "2024-05-27")]
theorem some_le_some : @LE.le (WithTop α) _ (Option.some a) (Option.some b) ↔ a ≤ b :=
  coe_le_coe

instance orderTop : OrderTop (WithTop α) where
  le_top := fun _ => toDual_le_toDual_iff.mp bot_le

@[simp, deprecated le_top "Don't mix Option and WithTop" (since := "2024-05-27")]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none := le_top

instance orderBot [OrderBot α] : OrderBot (WithTop α) where
  bot_le o a ha := by cases ha; exact ⟨_, rfl, bot_le⟩

instance boundedOrder [OrderBot α] : BoundedOrder (WithTop α) :=
  { WithTop.orderTop, WithTop.orderBot with }

theorem not_top_le_coe (a : α) : ¬(⊤ : WithTop α) ≤ ↑a :=
  WithBot.not_coe_le_bot (toDual a)

/-- There is a general version `top_le_iff`, but this lemma does not require a `PartialOrder`. -/
@[simp]
protected theorem top_le_iff : ∀ {a : WithTop α}, ⊤ ≤ a ↔ a = ⊤
  | (a : α) => by simp [not_top_le_coe _]
  | ⊤ => by simp

theorem le_coe : ∀ {o : Option α}, a ∈ o → (@LE.le (WithTop α) _ o b ↔ a ≤ b)
  | _, rfl => coe_le_coe

theorem le_coe_iff {x : WithTop α} : x ≤ b ↔ ∃ a : α, x = a ∧ a ≤ b :=
  @WithBot.coe_le_iff (αᵒᵈ) _ _ (toDual x)

theorem coe_le_iff {x : WithTop α} : ↑a ≤ x ↔ ∀ b : α, x = ↑b → a ≤ b :=
  @WithBot.le_coe_iff (αᵒᵈ) _ _ (toDual x)

protected theorem _root_.IsMin.withTop (h : IsMin a) : IsMin (a : WithTop α) := by
  -- defeq to is_max_to_dual_iff.mp (is_max.with_bot _), but that breaks API boundary
  intro _ hb
  rw [← toDual_le_toDual_iff] at hb
  simpa [toDual_le_iff] using h.toDual.withBot hb

theorem untop_le_iff {a : WithTop α} {b : α} (h : a ≠ ⊤) :
    untop a h ≤ b ↔ a ≤ (b : WithTop α) :=
  @WithBot.le_unbot_iff αᵒᵈ _ _ _ _

theorem le_untop_iff {a : α} {b : WithTop α} (h : b ≠ ⊤) :
    a ≤ untop b h ↔ (a : WithTop α) ≤ b :=
  @WithBot.unbot_le_iff αᵒᵈ _ _ _ _

theorem le_untop'_iff {a : WithTop α} {b c : α} (h : a = ⊤ → c ≤ b) :
    c ≤ a.untop' b ↔ c ≤ a :=
  WithBot.unbot'_le_iff (α := αᵒᵈ) h

end LE

section LT

variable [LT α]

instance (priority := 10) lt : LT (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₁, ∀ a ∈ o₂, b < a⟩

theorem toDual_lt_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    WithTop.toDual a < b ↔ WithBot.ofDual b < a :=
  Iff.rfl

theorem lt_toDual_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    a < WithTop.toDual b ↔ b < WithBot.ofDual a :=
  Iff.rfl

@[simp]
theorem toDual_lt_toDual_iff {a b : WithTop α} : WithTop.toDual a < WithTop.toDual b ↔ b < a :=
  Iff.rfl

theorem ofDual_lt_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    WithTop.ofDual a < b ↔ WithBot.toDual b < a :=
  Iff.rfl

theorem lt_ofDual_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    a < WithTop.ofDual b ↔ b < WithBot.toDual a :=
  Iff.rfl

@[simp]
theorem ofDual_lt_ofDual_iff {a b : WithTop αᵒᵈ} : WithTop.ofDual a < WithTop.ofDual b ↔ b < a :=
  Iff.rfl

theorem lt_untop_iff {a : α} {b : WithTop α} (h : b ≠ ⊤) :
    a < b.untop h ↔ a < b :=
  WithBot.unbot_lt_iff (α := αᵒᵈ) h

theorem untop_lt_iff {a : WithTop α} {b : α} (h : a ≠ ⊤) :
    a.untop h < b ↔ a < b :=
  WithBot.lt_unbot_iff (α := αᵒᵈ) h

theorem lt_untop'_iff {a : WithTop α} {b c : α} (h : a = ⊤ → c < b) :
    c < a.untop' b ↔ c < a :=
  WithBot.unbot'_lt_iff (α := αᵒᵈ) h

end LT

end WithTop

namespace WithBot

open OrderDual

@[simp]
theorem toDual_symm_apply (a : WithTop αᵒᵈ) : WithBot.toDual.symm a = WithTop.ofDual a :=
  rfl

@[simp]
theorem ofDual_symm_apply (a : WithTop α) : WithBot.ofDual.symm a = WithTop.toDual a :=
  rfl

@[simp]
theorem toDual_apply_bot : WithBot.toDual (⊥ : WithBot α) = ⊤ :=
  rfl

@[simp]
theorem ofDual_apply_bot : WithBot.ofDual (⊥ : WithBot α) = ⊤ :=
  rfl

@[simp]
theorem toDual_apply_coe (a : α) : WithBot.toDual (a : WithBot α) = toDual a :=
  rfl

@[simp]
theorem ofDual_apply_coe (a : αᵒᵈ) : WithBot.ofDual (a : WithBot αᵒᵈ) = ofDual a :=
  rfl

theorem map_toDual (f : αᵒᵈ → βᵒᵈ) (a : WithTop α) :
    WithBot.map f (WithTop.toDual a) = a.map (toDual ∘ f) :=
  rfl

theorem map_ofDual (f : α → β) (a : WithTop αᵒᵈ) :
    WithBot.map f (WithTop.ofDual a) = a.map (ofDual ∘ f) :=
  rfl

theorem toDual_map (f : α → β) (a : WithBot α) :
    WithBot.toDual (WithBot.map f a) = map (toDual ∘ f ∘ ofDual) (WithBot.toDual a) :=
  rfl

theorem ofDual_map (f : αᵒᵈ → βᵒᵈ) (a : WithBot αᵒᵈ) :
    WithBot.ofDual (WithBot.map f a) = map (ofDual ∘ f ∘ toDual) (WithBot.ofDual a) :=
  rfl

lemma forall_lt_iff_eq_bot [Preorder α] {x : WithBot α} :
    (∀ y : α, x < y) ↔ x = ⊥ :=
  ⟨fun h ↦ forall_ne_iff_eq_bot.mp (fun x ↦ (h x).ne'), fun h y ↦ h ▸ bot_lt_coe y⟩

lemma forall_le_iff_eq_bot [Preorder α] [NoMinOrder α] {x : WithBot α} :
    (∀ y : α, x ≤ y) ↔ x = ⊥ := by
  refine ⟨fun h ↦ forall_lt_iff_eq_bot.1 fun y ↦ ?_, fun h _ ↦ h ▸ bot_le⟩
  obtain ⟨w, hw⟩ := exists_lt y
  exact (h w).trans_lt (coe_lt_coe.2 hw)

lemma le_of_forall_lt_iff_le [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    {x y : WithBot α} : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h z x_z ↦ h.trans x_z.le⟩
  induction x with
  | bot => exact le_of_eq <| forall_le_iff_eq_bot.1 fun z ↦ h z (bot_lt_coe z)
  | coe x =>
    rw [le_coe_iff]
    rintro y rfl
    exact le_of_forall_le_of_dense (by exact_mod_cast h)

lemma ge_of_forall_gt_iff_ge [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    {x y : WithBot α} : (∀ z : α, z < x → z ≤ y) ↔ x ≤ y := by
  apply Iff.intro _ (fun h _ x_z ↦ x_z.le.trans h)
  induction y with
  | bot => simpa using forall_le_iff_eq_bot.1
  | coe y =>
    rw [le_coe_iff]
    rintro h x rfl
    exact le_of_forall_ge_of_dense (by exact_mod_cast h)

section LE

variable [LE α]

theorem toDual_le_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    WithBot.toDual a ≤ b ↔ WithTop.ofDual b ≤ a :=
  Iff.rfl

theorem le_toDual_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    a ≤ WithBot.toDual b ↔ b ≤ WithTop.ofDual a :=
  Iff.rfl

@[simp]
theorem toDual_le_toDual_iff {a b : WithBot α} : WithBot.toDual a ≤ WithBot.toDual b ↔ b ≤ a :=
  Iff.rfl

theorem ofDual_le_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    WithBot.ofDual a ≤ b ↔ WithTop.toDual b ≤ a :=
  Iff.rfl

theorem le_ofDual_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    a ≤ WithBot.ofDual b ↔ b ≤ WithTop.toDual a :=
  Iff.rfl

@[simp]
theorem ofDual_le_ofDual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a ≤ WithBot.ofDual b ↔ b ≤ a :=
  Iff.rfl

end LE

section LT

variable [LT α]

theorem toDual_lt_iff {a : WithBot α} {b : WithTop αᵒᵈ} :
    WithBot.toDual a < b ↔ WithTop.ofDual b < a :=
  Iff.rfl

theorem lt_toDual_iff {a : WithTop αᵒᵈ} {b : WithBot α} :
    a < WithBot.toDual b ↔ b < WithTop.ofDual a :=
  Iff.rfl

@[simp]
theorem toDual_lt_toDual_iff {a b : WithBot α} : WithBot.toDual a < WithBot.toDual b ↔ b < a :=
  Iff.rfl

theorem ofDual_lt_iff {a : WithBot αᵒᵈ} {b : WithTop α} :
    WithBot.ofDual a < b ↔ WithTop.toDual b < a :=
  Iff.rfl

theorem lt_ofDual_iff {a : WithTop α} {b : WithBot αᵒᵈ} :
    a < WithBot.ofDual b ↔ b < WithTop.toDual a :=
  Iff.rfl

@[simp]
theorem ofDual_lt_ofDual_iff {a b : WithBot αᵒᵈ} : WithBot.ofDual a < WithBot.ofDual b ↔ b < a :=
  Iff.rfl

end LT

end WithBot

namespace WithTop

section LT

variable [LT α] {a b : α}

open OrderDual

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithTop α) < b ↔ a < b := by
  simp only [← toDual_lt_toDual_iff, toDual_apply_coe, WithBot.coe_lt_coe, toDual_lt_toDual]

@[simp]
theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by
  simp [← toDual_lt_toDual_iff, WithBot.bot_lt_coe]

@[simp]
protected theorem not_top_lt (a : WithTop α) : ¬⊤ < a := by
  rw [← toDual_lt_toDual_iff]
  exact WithBot.not_lt_bot _

@[simp, deprecated coe_lt_coe "Don't mix Option and WithTop" (since := "2024-05-27")]
theorem some_lt_some : @LT.lt (WithTop α) _ (Option.some a) (Option.some b) ↔ a < b := coe_lt_coe

@[simp, deprecated coe_lt_top "Don't mix Option and WithTop" (since := "2024-05-27")]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (Option.some a) none := coe_lt_top a

@[simp, deprecated not_top_lt "Don't mix Option and WithTop" (since := "2024-05-27")]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a := WithTop.not_top_lt _

theorem lt_iff_exists_coe {a b : WithTop α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b := by
  rw [← toDual_lt_toDual_iff, WithBot.lt_iff_exists_coe, OrderDual.exists]
  exact exists_congr fun _ => and_congr_left' Iff.rfl

theorem coe_lt_iff {x : WithTop α} : ↑a < x ↔ ∀ b : α, x = ↑b → a < b :=
  WithBot.lt_coe_iff (α := αᵒᵈ)

/-- A version of `lt_top_iff_ne_top` for `WithTop` that only requires `LT α`, not
`PartialOrder α`. -/
protected theorem lt_top_iff_ne_top {x : WithTop α} : x < ⊤ ↔ x ≠ ⊤ :=
  @WithBot.bot_lt_iff_ne_bot αᵒᵈ _ x

end LT

instance preorder [Preorder α] : Preorder (WithTop α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := @lt_iff_le_not_le (WithBot αᵒᵈ)ᵒᵈ _
  le_refl := @le_refl (WithBot αᵒᵈ)ᵒᵈ _
  le_trans := @le_trans (WithBot αᵒᵈ)ᵒᵈ _

instance partialOrder [PartialOrder α] : PartialOrder (WithTop α) where
  le_antisymm := @le_antisymm (WithBot αᵒᵈ)ᵒᵈ _

section Preorder

variable [Preorder α] [Preorder β]

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

theorem map_le_iff (f : α → β) (a b : WithTop α)
    (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    a.map f ≤ b.map f ↔ a ≤ b := by
  rw [← toDual_le_toDual_iff, toDual_map, toDual_map, WithBot.map_le_iff, toDual_le_toDual_iff]
  simp [mono_iff]

theorem coe_untop'_le (a : WithTop α) (b : α) : a.untop' b ≤ a :=
  WithBot.le_coe_unbot' (α := αᵒᵈ) a b

@[simp]
theorem coe_top_lt [OrderTop α] {x : WithTop α} : (⊤ : α) < x ↔ x = ⊤ :=
  WithBot.lt_coe_bot (α := αᵒᵈ)

lemma forall_gt_iff_eq_top {x : WithTop α} : (∀ y : α, y < x) ↔ x = ⊤ :=
  WithBot.forall_lt_iff_eq_bot (α := αᵒᵈ)

lemma forall_ge_iff_eq_top [NoMaxOrder α] {x : WithTop α} : (∀ y : α, y ≤ x) ↔ x = ⊤ :=
  WithBot.forall_le_iff_eq_bot (α := αᵒᵈ)

end Preorder

lemma le_of_forall_lt_iff_le [LinearOrder α] [DenselyOrdered α] [NoMaxOrder α]
    {x y : WithTop α} : (∀ z : α, x < z → y ≤ z) ↔ y ≤ x :=
  WithBot.ge_of_forall_gt_iff_ge (α := αᵒᵈ)

lemma ge_of_forall_gt_iff_ge [LinearOrder α] [DenselyOrdered α] [NoMaxOrder α]
    {x y : WithTop α} : (∀ z : α, z < x → z ≤ y) ↔ x ≤ y :=
  WithBot.le_of_forall_lt_iff_le (α := αᵒᵈ)

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with
    inf := Option.liftOrGet (· ⊓ ·),
    inf_le_left := @inf_le_left (WithBot αᵒᵈ)ᵒᵈ _
    inf_le_right := @inf_le_right (WithBot αᵒᵈ)ᵒᵈ _
    le_inf := @le_inf (WithBot αᵒᵈ)ᵒᵈ _ }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = (a : WithTop α) ⊓ b :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with
    sup := WithTop.map₂ (· ⊔ ·),
    le_sup_left := @le_sup_left (WithBot αᵒᵈ)ᵒᵈ _
    le_sup_right := @le_sup_right (WithBot αᵒᵈ)ᵒᵈ _
    sup_le := @sup_le (WithBot αᵒᵈ)ᵒᵈ _ }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = (a : WithTop α) ⊔ b :=
  rfl

instance lattice [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance distribLattice [DistribLattice α] : DistribLattice (WithTop α) :=
  { WithTop.lattice with
    le_sup_inf := @le_sup_inf (WithBot αᵒᵈ)ᵒᵈ _ }

instance decidableEq [DecidableEq α] : DecidableEq (WithTop α) :=
  inferInstanceAs <| DecidableEq (Option α)

instance decidableLE [LE α] [DecidableRel (α := α) (· ≤ ·)] :
    DecidableRel (α := WithTop α) (· ≤ ·) := fun _ _ =>
  decidable_of_decidable_of_iff toDual_le_toDual_iff

instance decidableLT [LT α] [DecidableRel (α := α) (· < ·)] :
    DecidableRel (α := WithTop α) (· < ·) := fun _ _ =>
  decidable_of_decidable_of_iff toDual_lt_toDual_iff

instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithTop α) (· ≤ ·) :=
  ⟨fun _ _ => by
    simp_rw [← toDual_le_toDual_iff]
    exact total_of _ _ _⟩

instance linearOrder [LinearOrder α] : LinearOrder (WithTop α) :=
  Lattice.toLinearOrder _

@[simp, norm_cast]
theorem coe_min [LinearOrder α] (x y : α) : (↑(min x y) : WithTop α) = min (x : WithTop α) y :=
  rfl

@[simp, norm_cast]
theorem coe_max [LinearOrder α] (x y : α) : (↑(max x y) : WithTop α) = max (x : WithTop α) y :=
  rfl

instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithTop α) :=
  inferInstanceAs <| WellFoundedLT (WithBot αᵒᵈ)ᵒᵈ

open OrderDual

instance instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithTop α) :=
  inferInstanceAs <| WellFoundedGT (WithBot αᵒᵈ)ᵒᵈ

instance trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithTop α) (· < ·) :=
  ⟨fun
    | (a : α), (b : α) => by simp [trichotomous]
    | ⊤, (b : α) => by simp
    | (a : α), ⊤ => by simp
    | ⊤, ⊤ => by simp⟩

instance IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] : IsWellOrder (WithTop α) (· < ·) where

instance trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithTop α) (· > ·) :=
  have : IsTrichotomous α (· < ·) := .swap _; .swap _

instance IsWellOrder.gt [Preorder α] [IsWellOrder α (· > ·)] : IsWellOrder (WithTop α) (· > ·) where

instance _root_.WithBot.trichotomous.lt [Preorder α] [h : IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithBot α) (· < ·) :=
  @WithTop.trichotomous.gt αᵒᵈ _ h

instance _root_.WithBot.isWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] :
    IsWellOrder (WithBot α) (· < ·) where

instance _root_.WithBot.trichotomous.gt [Preorder α] [h : IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithBot α) (· > ·) :=
  @WithTop.trichotomous.lt αᵒᵈ _ h

instance _root_.WithBot.isWellOrder.gt [Preorder α] [h : IsWellOrder α (· > ·)] :
    IsWellOrder (WithBot α) (· > ·) :=
  @WithTop.IsWellOrder.lt αᵒᵈ _ h

instance [LT α] [DenselyOrdered α] [NoMaxOrder α] : DenselyOrdered (WithTop α) :=
  OrderDual.denselyOrdered (WithBot αᵒᵈ)

theorem lt_iff_exists_coe_btwn [Preorder α] [DenselyOrdered α] [NoMaxOrder α] {a b : WithTop α} :
    a < b ↔ ∃ x : α, a < ↑x ∧ ↑x < b :=
  ⟨fun h =>
    let ⟨_, hy⟩ := exists_between h
    let ⟨x, hx⟩ := lt_iff_exists_coe.1 hy.2
    ⟨x, hx.1 ▸ hy⟩,
    fun ⟨_, hx⟩ => lt_trans hx.1 hx.2⟩

instance noBotOrder [LE α] [NoBotOrder α] [Nonempty α] : NoBotOrder (WithTop α) :=
  @OrderDual.noBotOrder (WithBot αᵒᵈ) _ _

instance noMinOrder [LT α] [NoMinOrder α] [Nonempty α] : NoMinOrder (WithTop α) :=
  @OrderDual.noMinOrder (WithBot αᵒᵈ) _ _

end WithTop
