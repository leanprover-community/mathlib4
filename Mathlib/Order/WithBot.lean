/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Logic.Nontrivial.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Data.Option.NAry
import Mathlib.Tactic.Lift

#align_import order.with_bot from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-!
# `WithBot`, `WithTop`

Adding a `bot` or a `top` to an order.

## Main declarations

* `With<Top/Bot> α`: Equips `Option α` with the order on `α` plus `none` as the top/bottom element.

 -/

variable {α β γ δ : Type*}

/-- Attach `⊥` to a type. -/
def WithBot (α : Type*) :=
  Option α

namespace WithBot

variable {a b : α}

instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithBot α` -/
@[coe, match_pattern] def some : α → WithBot α :=
  Option.some

-- Porting note: changed this from `CoeTC` to `Coe` but I am not 100% confident that's correct.
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

instance bot : Bot (WithBot α) :=
  ⟨none⟩

instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

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
  fun.

@[simp]
theorem coe_ne_bot : (a : WithBot α) ≠ ⊥ :=
  fun.

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim]
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | none => bot
  | Option.some a => coe a

@[simp]
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[simp]
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

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
  induction x using recBotCoe <;> simp [@eq_comm _ d]

@[simp] theorem unbot'_eq_self_iff {d : α} {x : WithBot α} : unbot' d x = d ↔ x = d ∨ x = ⊥ := by
  simp [unbot'_eq_iff]

theorem unbot'_eq_unbot'_iff {d : α} {x y : WithBot α} :
    unbot' d x = unbot' d y ↔ x = y ∨ x = d ∧ y = ⊥ ∨ x = ⊥ ∧ y = d := by
 induction y using recBotCoe <;> simp [unbot'_eq_iff, or_comm]

/-- Lift a map `f : α → β` to `WithBot α → WithBot β`. Implemented using `Option.map`. -/
def map (f : α → β) : WithBot α → WithBot β :=
  Option.map f

@[simp]
theorem map_bot (f : α → β) : map f ⊥ = ⊥ :=
  rfl

@[simp]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) :
    map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

theorem ne_bot_iff_exists {x : WithBot α} : x ≠ ⊥ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

/-- Deconstruct a `x : WithBot α` to the underlying value in `α`, given a proof that `x ≠ ⊥`. -/
def unbot : ∀ x : WithBot α, x ≠ ⊥ → α
  | ⊥, h => absurd rfl h
  | Option.some x, _ => x

@[simp]
theorem coe_unbot (x : WithBot α) (h : x ≠ ⊥) : (x.unbot h : WithBot α) = x := by
  cases x
  exact (h rfl).elim
  rfl

@[simp]
theorem unbot_coe (x : α) (h : (x : WithBot α) ≠ ⊥ := coe_ne_bot) : (x : WithBot α).unbot h = x :=
  rfl

instance canLift : CanLift (WithBot α) α (↑) fun r => r ≠ ⊥ where
  prf x h := ⟨x.unbot h, coe_unbot _ _⟩

section LE

variable [LE α]

instance (priority := 10) le : LE (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b⟩

@[simp]
theorem some_le_some : @LE.le (WithBot α) _ (Option.some a) (Option.some b) ↔ a ≤ b :=
  by simp [LE.le]

@[simp, norm_cast]
theorem coe_le_coe : (a : WithBot α) ≤ b ↔ a ≤ b :=
  some_le_some

@[simp]
theorem none_le {a : WithBot α} : @LE.le (WithBot α) _ none a := fun _ h => Option.noConfusion h

instance orderBot : OrderBot (WithBot α) :=
  { WithBot.bot with bot_le := fun _ => none_le }


instance orderTop [OrderTop α] : OrderTop (WithBot α) where
  top := some ⊤
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
  | Option.some x => by simp [some_eq_coe]
  | none => iff_of_false (not_coe_le_bot _) <| by simp [none_eq_bot]

theorem le_coe_iff : ∀ {x : WithBot α}, x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b
  | Option.some b => by simp [some_eq_coe, coe_eq_coe]
  | none => by simp [none_eq_bot]

protected theorem _root_.IsMax.withBot (h : IsMax a) : IsMax (a : WithBot α)
  | none, _ => bot_le
  | Option.some _, hb => some_le_some.2 <| h <| some_le_some.1 hb

theorem le_unbot_iff {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a ≤ unbot b h ↔ (a : WithBot α) ≤ b := by
  match b, h with
  | some _, _ => simp only [unbot_coe, coe_le_coe]

theorem unbot_le_iff {a : WithBot α} (h : a ≠ ⊥) {b : α} :
    unbot a h ≤ b ↔ a ≤ (b : WithBot α) := by
  match a, h with
  | some _, _ => simp only [unbot_coe, coe_le_coe]

end LE

section LT

variable [LT α]

instance (priority := 10) lt : LT (WithBot α) :=
  ⟨fun o₁ o₂ : Option α => ∃ b ∈ o₂, ∀ a ∈ o₁, a < b⟩

@[simp]
theorem some_lt_some : @LT.lt (WithBot α) _ (Option.some a) (Option.some b) ↔ a < b := by
  simp [LT.lt]

@[simp, norm_cast]
theorem coe_lt_coe : (a : WithBot α) < b ↔ a < b :=
  some_lt_some

@[simp]
theorem none_lt_some (a : α) : @LT.lt (WithBot α) _ none (some a) :=
  ⟨a, rfl, fun _ hb => (Option.not_mem_none _ hb).elim⟩

theorem bot_lt_coe (a : α) : (⊥ : WithBot α) < a :=
  none_lt_some a

@[simp]
theorem not_lt_none (a : WithBot α) : ¬@LT.lt (WithBot α) _ a none :=
  fun ⟨_, h, _⟩ => Option.not_mem_none _ h

theorem lt_iff_exists_coe : ∀ {a b : WithBot α}, a < b ↔ ∃ p : α, b = p ∧ a < p
  | a, Option.some b => by simp [some_eq_coe, coe_eq_coe]
  | a, none => iff_of_false (not_lt_none _) <| by simp [none_eq_bot]

theorem lt_coe_iff : ∀ {x : WithBot α}, x < b ↔ ∀ a, x = ↑a → a < b
  | Option.some b => by simp [some_eq_coe, coe_eq_coe, coe_lt_coe]
  | none => by simp [none_eq_bot, bot_lt_coe]

/-- A version of `bot_lt_iff_ne_bot` for `WithBot` that only requires `LT α`, not
`PartialOrder α`. -/
protected theorem bot_lt_iff_ne_bot : ∀ {x : WithBot α}, ⊥ < x ↔ x ≠ ⊥
  | ⊥ => by simpa using not_lt_none ⊥
  | (x : α) => by simp [bot_lt_coe]

end LT

instance preorder [Preorder α] : Preorder (WithBot α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by
    intros a b
    cases a <;> cases b <;> simp [lt_iff_le_not_le]; simp [LE.le, LT.lt]
  le_refl o a ha := ⟨a, ha, le_rfl⟩
  le_trans o₁ o₂ o₃ h₁ h₂ a ha :=
    let ⟨b, hb, ab⟩ := h₁ a ha
    let ⟨c, hc, bc⟩ := h₂ b hb
    ⟨c, hc, le_trans ab bc⟩

instance partialOrder [PartialOrder α] : PartialOrder (WithBot α) :=
  { WithBot.preorder with
    le_antisymm := fun o₁ o₂ h₁ h₂ => by
      cases' o₁ with a
      · cases' o₂ with b
        · rfl

        rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩

      · rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩
        rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩
        rw [le_antisymm h₁' h₂']
         }

theorem coe_strictMono [Preorder α] : StrictMono (fun (a : α) => (a : WithBot α)) :=
  fun _ _ => coe_lt_coe.2

theorem coe_mono [Preorder α] : Monotone (fun (a : α) => (a : WithBot α)) :=
  fun _ _ => coe_le_coe.2

theorem monotone_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    Monotone f ↔ Monotone (λ a => f a : α → β) ∧ ∀ x : α, f ⊥ ≤ f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_mono, fun _ => h bot_le⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨fun _ => le_rfl, fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_coe_le_bot _ h).elim,
          fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} :
    Monotone (WithBot.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

alias ⟨_, _root_.Monotone.withBot_map⟩ := monotone_map_iff

theorem strictMono_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    StrictMono f ↔ StrictMono (λ a => f a : α → β) ∧ ∀ x : α, f ⊥ < f x :=
  ⟨fun h => ⟨h.comp WithBot.coe_strictMono, fun _ => h (bot_lt_coe _)⟩, fun h =>
    WithBot.forall.2
      ⟨WithBot.forall.2 ⟨flip absurd (lt_irrefl _), fun x _ => h.2 x⟩, fun _ =>
        WithBot.forall.2 ⟨fun h => (not_lt_bot h).elim, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

theorem strictAnti_iff [Preorder α] [Preorder β] {f : WithBot α → β} :
    StrictAnti f ↔ StrictAnti (λ a => f a : α → β) ∧ ∀ x : α, f x < f ⊥ :=
  strictMono_iff (β := βᵒᵈ)

@[simp]
theorem strictMono_map_iff [Preorder α] [Preorder β] {f : α → β} :
    StrictMono (WithBot.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, bot_lt_coe]

alias ⟨_, _root_.StrictMono.withBot_map⟩ := strictMono_map_iff

theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    ∀ a b : WithBot α, a.map f ≤ b.map f ↔ a ≤ b
  | ⊥, _ => by simp only [map_bot, bot_le]
  | (a : α), ⊥ => by simp only [map_coe, map_bot, coe_ne_bot, not_coe_le_bot _]
  | (a : α), (b : α) => by simpa only [map_coe, coe_le_coe] using mono_iff

theorem le_coe_unbot' [Preorder α] : ∀ (a : WithBot α) (b : α), a ≤ a.unbot' b
  | (a : α), _ => le_rfl
  | ⊥, _ => bot_le

theorem unbot'_le_iff [LE α] {a : WithBot α} {b c : α} (h : a = ⊥ → b ≤ c) :
    a.unbot' b ≤ c ↔ a ≤ c := by
  cases a
  · simpa using h rfl
  · simp [some_eq_coe]

theorem unbot'_lt_iff [LT α] {a : WithBot α} {b c : α} (h : a = ⊥ → b < c) :
    a.unbot' b < c ↔ a < c := by
  cases a
  · simpa [bot_lt_coe] using h rfl
  · simp [some_eq_coe]

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithBot α) :=
  { WithBot.partialOrder, @WithBot.orderBot α _ with
    sup := Option.liftOrGet (· ⊔ ·),
    le_sup_left := fun o₁ o₂ a ha => by cases ha; cases o₂ <;> simp [Option.liftOrGet],
    le_sup_right := fun o₁ o₂ a ha => by cases ha; cases o₁ <;> simp [Option.liftOrGet],
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₁ with b <;> cases' o₂ with c <;> cases ha
      · exact h₂ a rfl

      · exact h₁ a rfl

      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, sup_le h₁' h₂⟩
         }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithBot α) = (a : WithBot α) ⊔ b :=
  rfl

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithBot α) :=
  { WithBot.partialOrder, @WithBot.orderBot α _ with
    inf := Option.map₂ (· ⊓ ·),
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

-- porting note: added, previously this was found via unfolding `WithBot`
instance decidableEq [DecidableEq α] : DecidableEq (WithBot α) := instDecidableEqOption

instance decidableLE [LE α] [@DecidableRel α (· ≤ ·)] : @DecidableRel (WithBot α) (· ≤ ·)
  | none, x => isTrue fun a h => Option.noConfusion h
  | Option.some x, Option.some y =>
      if h : x ≤ y then isTrue (some_le_some.2 h) else isFalse <| by simp [*]
  | Option.some x, none => isFalse fun h => by rcases h x rfl with ⟨y, ⟨_⟩, _⟩

instance decidableLT [LT α] [@DecidableRel α (· < ·)] : @DecidableRel (WithBot α) (· < ·)
  | none, Option.some x => isTrue <| by exists x, rfl; rintro _ ⟨⟩
  | Option.some x, Option.some y =>
      if h : x < y then isTrue <| by simp [*] else isFalse <| by simp [*]
  | x, none => isFalse <| by rintro ⟨a, ⟨⟨⟩⟩⟩

instance isTotal_le [LE α] [IsTotal α (· ≤ ·)] : IsTotal (WithBot α) (· ≤ ·) :=
  ⟨fun a b =>
    match a, b with
    | none, _ => Or.inl bot_le
    | _, none => Or.inr bot_le
    | Option.some x, Option.some y => (total_of (· ≤ ·) x y).imp some_le_some.2 some_le_some.2⟩

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
  have not_lt_bot : ∀ a : WithBot α, ¬ a < ⊥ := (fun.)
  have acc_bot := ⟨_, by simp [not_lt_bot]⟩
  .intro fun
    | ⊥ => acc_bot
    | (a : α) => (wellFounded_lt.1 a).rec fun a _ ih =>
      .intro _ fun
        | ⊥, _ => acc_bot
        | (b : α), hlt => ih _ (some_lt_some.1 hlt)

instance denselyOrdered [LT α] [DenselyOrdered α] [NoMinOrder α] : DenselyOrdered (WithBot α) :=
  ⟨fun a b =>
    match a, b with
    | a, none => fun h : a < ⊥ => (not_lt_none _ h).elim
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

--TODO(Mario): Construct using order dual on `WithBot`
/-- Attach `⊤` to a type. -/
def WithTop (α : Type*) :=
  Option α

namespace WithTop

variable {a b : α}

instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

/-- The canonical map from `α` into `WithTop α` -/
@[coe, match_pattern] def some : α → WithTop α :=
  Option.some

instance coeTC : CoeTC α (WithTop α) :=
  ⟨some⟩

instance top : Top (WithTop α) :=
  ⟨none⟩

instance inhabited : Inhabited (WithTop α) :=
  ⟨⊤⟩

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
  fun.

@[simp]
theorem coe_ne_top : (a : WithTop α) ≠ ⊤ :=
  fun.

/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim]
def recTopCoe {C : WithTop α → Sort*} (top : C ⊤) (coe : ∀ a : α, C a) : ∀ n : WithTop α, C n
  | none => top
  | Option.some a => coe a

@[simp]
theorem recTopCoe_top {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) :
    @recTopCoe _ C d f ⊤ = d :=
  rfl

@[simp]
theorem recTopCoe_coe {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
    @recTopCoe _ C d f ↑x = f x :=
  rfl

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

@[simp, norm_cast] -- porting note: added `simp`
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

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ}
    (h : g₁ ∘ f₁ = g₂ ∘ f₂) (a : α) : map g₁ (map f₁ a) = map g₂ (map f₂ a) :=
  Option.map_comm h _

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

theorem ne_top_iff_exists {x : WithTop α} : x ≠ ⊤ ↔ ∃ a : α, ↑a = x :=
  Option.ne_none_iff_exists

/-- Deconstruct a `x : WithTop α` to the underlying value in `α`, given a proof that `x ≠ ⊤`. -/
def untop : ∀ x : WithTop α, x ≠ ⊤ → α :=
  WithBot.unbot

@[simp]
theorem coe_untop (x : WithTop α) (h : x ≠ ⊤) : (x.untop h : WithTop α) = x :=
  WithBot.coe_unbot x h

@[simp]
theorem untop_coe (x : α) (h : (x : WithTop α) ≠ ⊤ := coe_ne_top) : (x : WithTop α).untop h = x :=
  rfl

instance canLift : CanLift (WithTop α) α (↑) fun r => r ≠ ⊤ where
  prf x h := ⟨x.untop h, coe_untop _ _⟩

section LE

variable [LE α]

instance (priority := 10) le : LE (WithTop α) :=
  ⟨fun o₁ o₂ : Option α => ∀ a ∈ o₂, ∃ b ∈ o₁, b ≤ a⟩

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

@[simp]
theorem some_le_some : @LE.le (WithTop α) _ (Option.some a) (Option.some b) ↔ a ≤ b :=
  coe_le_coe

@[simp]
theorem le_none {a : WithTop α} : @LE.le (WithTop α) _ a none :=
  toDual_le_toDual_iff.mp (@WithBot.none_le αᵒᵈ _ _)

instance orderTop : OrderTop (WithTop α) :=
  { WithTop.top with le_top := fun _ => le_none }

instance orderBot [OrderBot α] : OrderBot (WithTop α) where
  bot := some ⊥
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
  simpa [toDual_le_iff] using (IsMax.withBot h : IsMax (toDual a : WithBot αᵒᵈ)) hb

theorem untop_le_iff {a : WithTop α} {b : α} (h : a ≠ ⊤) :
    untop a h ≤ b ↔ a ≤ (b : WithTop α) :=
  @WithBot.le_unbot_iff αᵒᵈ _ _ _ _

theorem le_untop_iff {a : α} {b : WithTop α} (h : b ≠ ⊤) :
    a ≤ untop b h ↔ (a : WithTop α) ≤ b :=
  @WithBot.unbot_le_iff αᵒᵈ _ _ _ _

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

section LE

variable [LE α] {a b : α}

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

variable [LT α] {a b : α}

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
theorem some_lt_some : @LT.lt (WithTop α) _ (Option.some a) (Option.some b) ↔ a < b :=
  coe_lt_coe

theorem coe_lt_top (a : α) : (a : WithTop α) < ⊤ := by
  simp [← toDual_lt_toDual_iff, WithBot.bot_lt_coe]

@[simp]
theorem some_lt_none (a : α) : @LT.lt (WithTop α) _ (Option.some a) none :=
  coe_lt_top a

@[simp]
theorem not_none_lt (a : WithTop α) : ¬@LT.lt (WithTop α) _ none a := by
  rw [← toDual_lt_toDual_iff]
  exact WithBot.not_lt_none _

theorem lt_iff_exists_coe {a b : WithTop α} : a < b ↔ ∃ p : α, a = p ∧ ↑p < b := by
  rw [← toDual_lt_toDual_iff, WithBot.lt_iff_exists_coe, OrderDual.exists]
  exact exists_congr fun _ => and_congr_left' Iff.rfl

theorem coe_lt_iff {x : WithTop α} : ↑a < x ↔ ∀ b, x = ↑b → a < b := by simp

/-- A version of `lt_top_iff_ne_top` for `WithTop` that only requires `LT α`, not
`PartialOrder α`. -/
protected theorem lt_top_iff_ne_top {x : WithTop α} : x < ⊤ ↔ x ≠ ⊤ :=
  @WithBot.bot_lt_iff_ne_bot αᵒᵈ _ x

end LT

instance preorder [Preorder α] : Preorder (WithTop α) where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := by simp [← toDual_lt_toDual_iff, lt_iff_le_not_le]
  le_refl _ := toDual_le_toDual_iff.mp le_rfl
  le_trans _ _ _ := by
    simp_rw [← toDual_le_toDual_iff]
    exact Function.swap le_trans

instance partialOrder [PartialOrder α] : PartialOrder (WithTop α) :=
  { WithTop.preorder with
    le_antisymm := fun _ _ => by
      simp_rw [← toDual_le_toDual_iff]
      exact Function.swap le_antisymm }

theorem coe_strictMono [Preorder α] : StrictMono (fun a : α => (a : WithTop α)) :=
  fun _ _ => some_lt_some.2

theorem coe_mono [Preorder α] : Monotone (fun a : α => (a : WithTop α)) :=
  fun _ _ => coe_le_coe.2

theorem monotone_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    Monotone f ↔ Monotone (fun (a : α) => f a) ∧ ∀ x : α, f x ≤ f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_mono, fun _ => h le_top⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨fun _ => le_rfl, fun _ h => (not_top_le_coe _ h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun _ hle => h.1 (coe_le_coe.1 hle)⟩⟩⟩

@[simp]
theorem monotone_map_iff [Preorder α] [Preorder β] {f : α → β} :
    Monotone (WithTop.map f) ↔ Monotone f :=
  monotone_iff.trans <| by simp [Monotone]

alias ⟨_, _root_.Monotone.withTop_map⟩ := monotone_map_iff

theorem strictMono_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    StrictMono f ↔ StrictMono (fun (a : α) => f a) ∧ ∀ x : α, f x < f ⊤ :=
  ⟨fun h => ⟨h.comp WithTop.coe_strictMono, fun _ => h (coe_lt_top _)⟩, fun h =>
    WithTop.forall.2
      ⟨WithTop.forall.2 ⟨flip absurd (lt_irrefl _), fun _ h => (not_top_lt h).elim⟩, fun x =>
        WithTop.forall.2 ⟨fun _ => h.2 x, fun _ hle => h.1 (coe_lt_coe.1 hle)⟩⟩⟩

theorem strictAnti_iff [Preorder α] [Preorder β] {f : WithTop α → β} :
    StrictAnti f ↔ StrictAnti (λ a => f a : α → β) ∧ ∀ x : α, f ⊤ < f x :=
  strictMono_iff (β := βᵒᵈ)

@[simp]
theorem strictMono_map_iff [Preorder α] [Preorder β] {f : α → β} :
    StrictMono (WithTop.map f) ↔ StrictMono f :=
  strictMono_iff.trans <| by simp [StrictMono, coe_lt_top]

alias ⟨_, _root_.StrictMono.withTop_map⟩ := strictMono_map_iff

theorem map_le_iff [Preorder α] [Preorder β] (f : α → β) (a b : WithTop α)
    (mono_iff : ∀ {a b}, f a ≤ f b ↔ a ≤ b) :
    a.map f ≤ b.map f ↔ a ≤ b := by
  erw [← toDual_le_toDual_iff, toDual_map, toDual_map, WithBot.map_le_iff, toDual_le_toDual_iff]
  simp [mono_iff]

theorem coe_untop'_le [Preorder α] : ∀ (a : WithTop α) (b : α), a.untop' b ≤ a
  | (a : α), _ => le_rfl
  | ⊤, _ => le_top

theorem le_untop'_iff [LE α] {a : WithTop α} {b c : α} (h : a = ⊤ → c ≤ b) :
    c ≤ a.untop' b ↔ c ≤ a := by
  cases a
  · simpa using h rfl
  · simp [some_eq_coe]

theorem lt_untop'_iff [LT α] {a : WithTop α} {b c : α} (h : a = ⊤ → c < b) :
    c < a.untop' b ↔ c < a := by
  cases a
  · simpa [none_eq_top, coe_lt_top] using h rfl
  · simp [some_eq_coe]

instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (WithTop α) :=
  { WithTop.partialOrder with
    inf := Option.liftOrGet (· ⊓ ·),
    inf_le_left := fun o₁ o₂ a ha => by cases ha; cases o₂ <;> simp [Option.liftOrGet],
    inf_le_right := fun o₁ o₂ a ha => by cases ha; cases o₁ <;> simp [Option.liftOrGet],
    le_inf := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases' o₂ with b <;> cases' o₃ with c <;> cases ha
      · exact h₂ a rfl

      · exact h₁ a rfl

      · rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩
        simp at h₂
        exact ⟨d, rfl, le_inf h₁' h₂⟩
         }

theorem coe_inf [SemilatticeInf α] (a b : α) : ((a ⊓ b : α) : WithTop α) = (a : WithTop α) ⊓ b :=
  rfl

instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (WithTop α) :=
  { WithTop.partialOrder with
    sup := Option.map₂ (· ⊔ ·),
    le_sup_left := fun o₁ o₂ a ha => by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩
      exact ⟨_, rfl, le_sup_left⟩,
    le_sup_right := fun o₁ o₂ a ha => by
      rcases Option.mem_map₂_iff.1 ha with ⟨a, b, (rfl : _ = _), (rfl : _ = _), rfl⟩
      exact ⟨_, rfl, le_sup_right⟩,
    sup_le := fun o₁ o₂ o₃ h₁ h₂ a ha => by
      cases ha
      rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩
      rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩
      exact ⟨_, rfl, sup_le ab ac⟩ }

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithTop α) = (a : WithTop α) ⊔ b :=
  rfl

instance lattice [Lattice α] : Lattice (WithTop α) :=
  { WithTop.semilatticeSup, WithTop.semilatticeInf with }

instance distribLattice [DistribLattice α] : DistribLattice (WithTop α) :=
  { WithTop.lattice with
    le_sup_inf := fun o₁ o₂ o₃ =>
      match o₁, o₂, o₃ with
      | ⊤, _, _ => le_rfl
      | (a₁ : α), ⊤, ⊤ => le_rfl
      | (a₁ : α), ⊤, (a₃ : α) => le_rfl
      | (a₁ : α), (a₂ : α), ⊤ => le_rfl
      | (a₁ : α), (a₂ : α), (a₃ : α) => coe_le_coe.mpr le_sup_inf }

-- porting note: added, previously this was found via unfolding `WithTop`
instance decidableEq [DecidableEq α] : DecidableEq (WithTop α) := instDecidableEqOption

instance decidableLE [LE α] [@DecidableRel α (· ≤ ·)] :
    @DecidableRel (WithTop α) (· ≤ ·) := fun _ _ =>
  decidable_of_decidable_of_iff toDual_le_toDual_iff

instance decidableLT [LT α] [@DecidableRel α (· < ·)] :
    @DecidableRel (WithTop α) (· < ·) := fun _ _ =>
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

instance instWellFoundedLT [LT α] [WellFoundedLT α] : WellFoundedLT (WithTop α) where
  wf :=
  have not_top_lt : ∀ a : WithTop α, ¬ ⊤ < a := (fun.)
  have acc_some (a : α) : Acc ((· < ·) : WithTop α → WithTop α → Prop) a :=
    (wellFounded_lt.1 a).rec fun _ _ ih =>
      .intro _ fun
        | (b : α), hlt => ih _ (some_lt_some.1 hlt)
        | ⊤, hlt => nomatch not_top_lt _ hlt
  .intro fun
    | (a : α) => acc_some a
    | ⊤ => .intro _ fun
      | (b : α), _ => acc_some b
      | ⊤, hlt => nomatch not_top_lt _ hlt

open OrderDual

instance instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithTop α) where
  wf := ⟨fun a => by
    -- ideally, use RelHomClass.acc, but that is defined later
    have : Acc (· < ·) (WithTop.toDual a) := wellFounded_lt.apply _
    revert this
    generalize ha : WithBot.toDual a = b
    intro ac
    dsimp at ac
    induction' ac with _ H IH generalizing a
    subst ha
    exact ⟨_, fun a' h => IH (WithTop.toDual a') (toDual_lt_toDual.mpr h) _ rfl⟩⟩

instance _root_.WithBot.instWellFoundedGT [LT α] [WellFoundedGT α] : WellFoundedGT (WithBot α) where
  wf := ⟨fun a => by
    -- ideally, use RelHomClass.acc, but that is defined later
    have : Acc (· < ·) (WithBot.toDual a) := wellFounded_lt.apply _
    revert this
    generalize ha : WithBot.toDual a = b
    intro ac
    dsimp at ac
    induction' ac with _ H IH generalizing a
    subst ha
    exact ⟨_, fun a' h => IH (WithBot.toDual a') (toDual_lt_toDual.mpr h) _ rfl⟩⟩

instance trichotomous.lt [Preorder α] [IsTrichotomous α (· < ·)] :
    IsTrichotomous (WithTop α) (· < ·) :=
  ⟨by
    rintro (a | a) (b | b)
    · simp
    · simp
    · simp
    · simpa [some_eq_coe, IsTrichotomous, coe_eq_coe] using @trichotomous α (· < ·) _ a b⟩

instance IsWellOrder.lt [Preorder α] [IsWellOrder α (· < ·)] : IsWellOrder (WithTop α) (· < ·) where

instance trichotomous.gt [Preorder α] [IsTrichotomous α (· > ·)] :
    IsTrichotomous (WithTop α) (· > ·) :=
  ⟨by
    rintro (a | a) (b | b)
    · simp
    · simp
    · simp
    · simpa [some_eq_coe, IsTrichotomous, coe_eq_coe] using @trichotomous α (· > ·) _ a b⟩

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
