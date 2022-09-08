/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Data.Option.Basic
import Mathlib.Init.Data.Option.Instances
import Mathlib.Init.Function
import Mathlib.Data.Option.Defs
import Mathlib.Logic.Basic

namespace Option

variable {α : Type _} {β : Type _} {γ : Type _}

theorem some_ne_none (x : α) : some x ≠ none :=
  fun h => Option.noConfusion h

protected theorem «forall» {p : Option α → Prop} : (∀ x, p x) ↔ p none ∧ ∀ x, p (some x) :=
  ⟨fun h => ⟨h _, fun _ => h _⟩, fun h x => Option.casesOn x h.1 h.2⟩

protected theorem «exists» {p : Option α → Prop} : (∃ x, p x) ↔ p none ∨ ∃ x, p (some x) :=
  ⟨fun | ⟨none, hx⟩ => Or.inl hx | ⟨some x, hx⟩ => Or.inr ⟨x, hx⟩,
    fun h => h.elim (fun h => ⟨_, h⟩) fun ⟨_, hx⟩ => ⟨_, hx⟩⟩

theorem get_mem : ∀ {o : Option α} (h : isSome o), Option.get h ∈ o
| some _, _ => rfl

theorem get_of_mem {a : α} : ∀ {o : Option α} (h : isSome o), a ∈ o → Option.get h = a
| _, _, rfl => rfl

theorem not_mem_none (a : α) : a ∉ (none : Option α) := fun h => Option.noConfusion h

@[simp] theorem some_get : ∀ {x : Option α} (h : isSome x), some (Option.get h) = x
| some _, _ => rfl

@[simp] theorem get_some (x : α) (h : isSome (some x)) : Option.get h = x := rfl

@[simp] theorem getD_some (x y : α) : Option.getD (some x) y = x := rfl

@[simp] theorem getD_none (x : α) : Option.getD none x = x := rfl

theorem getD_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) : some (x.getD y) = x := by
  cases x; {contradiction}; rw [getD_some]

theorem mem_unique {o : Option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
  Option.some.inj $ ha.symm.trans hb

theorem some_injective (α : Type _) : Function.injective (@some α) :=
  fun _ _ => some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.injective f) : Function.injective (Option.map f)
| none, none, _ => rfl
| some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]

@[ext] theorem ext : ∀ {o₁ o₂ : Option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
| none, none, _ => rfl
| some _, _, H => ((H _).1 rfl).symm
| _, some _, H => (H _).2 rfl

theorem eq_none_iff_forall_not_mem {o : Option α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e a h => by rw [e] at h; (cases h), fun h => ext $ by simp; exact h⟩

@[simp] theorem none_bind (f : α → Option β) : none.bind f = none := rfl

@[simp] theorem some_bind (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

@[simp] theorem bind_some (x : Option α) : x.bind some = x := by cases x <;> rfl

@[simp] theorem bind_eq_some {α β} {x : Option α} {f : α → Option β} {b : β} :
  x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by cases x <;> simp

@[simp] theorem bind_eq_none {o : Option α} {f : α → Option β} :
  o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some]; rfl

theorem bind_comm {α β γ} {f : α → β → Option γ} (a : Option α) (b : Option β) :
  (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl

theorem bind_assoc (x : Option α) (f : α → Option β) (g : β → Option γ) :
  (x.bind f).bind g = x.bind fun y => (f y).bind g := by cases x <;> rfl

theorem join_eq_some {x : Option (Option α)} {a : α} : x.join = some a ↔ x = some (some a) := by
  simp

theorem join_ne_none {x : Option (Option α)} : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp

theorem join_ne_none' {x : Option (Option α)} : ¬x.join = none ↔ ∃ z, x = some (some z) := by
  simp

-- theorem join_eq_none {o : Option (Option α)} : o.join = none ↔ o = none ∨ o = some none := by
--   rcases o with _|_|_; simp

theorem bind_id_eq_join {x : Option (Option α)} : x.bind id = x.join := rfl

@[simp] theorem map_eq_map {α β} {f : α → β} : Functor.map f = Option.map f := rfl

theorem map_none {α β} {f : α → β} : f <$> none = none := rfl

theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] theorem map_none' {f : α → β} : none.map f = none := rfl

@[simp] theorem map_some' {a : α} {f : α → β} : (some a).map f = some (f a) := rfl

theorem map_eq_some {α β} {x : Option α} {f : α → β} {b : β} :
  f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp

@[simp] theorem map_eq_some' {x : Option α} {f : α → β} {b : β} :
  x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by cases x <;> simp

@[simp] theorem map_eq_none' {x : Option α} {f : α → β} : x.map f = none ↔ x = none := by
  cases x <;> simp only [map_none', map_some', eq_self_iff_true]

theorem map_eq_none {α β} {x : Option α} {f : α → β} : f <$> x = none ↔ x = none := map_eq_none'

theorem map_congr {f g : α → β} {x : Option α} (h : ∀ a ∈ x, f a = g a) : x.map f = x.map g := by
  cases x <;> simp only [map_none', map_some', h, mem_def]

@[simp] theorem map_id' : Option.map (@id α) = id := map_id

@[simp] theorem map_map (h : β → γ) (g : α → β) (x : Option α) :
  (x.map g).map h = x.map (h ∘ g) := by
  cases x <;> simp only [map_none', map_some', ·∘·]

theorem comp_map (h : β → γ) (g : α → β) (x : Option α) : x.map (h ∘ g) = (x.map g).map h :=
  (map_map ..).symm

@[simp] theorem map_comp_map (f : α → β) (g : β → γ) :
  Option.map g ∘ Option.map f = Option.map (g ∘ f) := by funext x; simp

theorem mem_map_of_mem {α β : Type _} {a : α} {x : Option α} (g : α → β) (h : a ∈ x) :
  g a ∈ x.map g :=
  mem_def.mpr ((mem_def.mp h).symm ▸ map_some')

theorem bind_map_comm {α β} {x : Option (Option α)} {f : α → β} :
  x.bind (Option.map f) = (x.map (Option.map f)).bind id := by cases x <;> simp

theorem join_map_eq_map_join {f : α → β} {x : Option (Option α)} :
  (x.map (Option.map f)).join = x.join.map f := by
  -- rcases x with (_ | _ | x) <;> simp
  cases x; {simp}; rename_i x; cases x <;> simp

theorem join_join {x : Option (Option (Option α))} : x.join.join = (x.map join).join := by
  (iterate 2 cases x; {simp}; rename_i x); cases x <;> simp
  -- rcases x with (_ | _ | _ | x) <;> simp

theorem mem_of_mem_join {a : α} {x : Option (Option α)} (h : a ∈ x.join) : some a ∈ x :=
  mem_def.mpr ((mem_def.mp h).symm ▸ join_eq_some.mp h)

@[simp] theorem some_orelse (a : α) (x : Option α) : (some a <|> x) = some a := rfl

@[simp] theorem none_orelse (x : Option α) : (none <|> x) = x := by cases x <;> rfl

@[simp] theorem orelse_none (x : Option α) : (x <|> none) = x := by cases x <;> rfl

@[simp] theorem isSome_none : @isSome α none = false := rfl

@[simp] theorem isSome_some {a : α} : isSome (some a) = true := rfl

theorem isSome_iff_exists {x : Option α} : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [isSome] <;> exact ⟨_, rfl⟩

@[simp] theorem isNone_none : @isNone α none = true := rfl

@[simp] theorem isNone_some {a : α} : isNone (some a) = false := rfl

@[simp] theorem not_isSome {a : Option α} : isSome a = false ↔ a.isNone = true := by
  cases a <;> simp

theorem eq_some_iff_get_eq {o : Option α} {a : α} :
  o = some a ↔ ∃ h : o.isSome, Option.get h = a := by cases o <;> simp; intro.

theorem not_isSome_iff_eq_none {o : Option α} : ¬o.isSome ↔ o = none := by
  cases o <;> simp

theorem ne_none_iff_isSome {o : Option α} : o ≠ none ↔ o.isSome := by cases o <;> simp

theorem ne_none_iff_exists {o : Option α} : o ≠ none ↔ ∃ x : α, some x = o := by cases o <;> simp

theorem ne_none_iff_exists' {o : Option α} : o ≠ none ↔ ∃ x : α, o = some x :=
  ne_none_iff_exists.trans $ exists_congr fun _ => eq_comm

theorem bex_ne_none {p : Option α → Prop} : (∃ x, ∃ (_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨get $ ne_none_iff_isSome.1 hx, by rwa [some_get]⟩,
    fun ⟨x, hx⟩ => ⟨some x, some_ne_none x, hx⟩⟩

theorem ball_ne_none {p : Option α → Prop} : (∀ x (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x),
    fun h x hx => by
      have := h (get $ ne_none_iff_isSome.1 hx)
      simp [some_get] at this ⊢
      exact this⟩

@[simp] theorem guard_eq_some {p : α → Prop} [DecidablePred p] {a b : α} :
  guard p a = some b ↔ a = b ∧ p a := by
  by_cases h : p a <;> simp [Option.guard, h]

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
  ∀ o₁ o₂, lift_or_get f o₁ o₂ = o₁ ∨ lift_or_get f o₁ o₂ = o₂
| none, none => Or.inl rfl
| some a, none => Or.inl rfl
| none, some b => Or.inr rfl
| some a, some b => by have := h a b; simp [lift_or_get] at this ⊢; exact this

@[simp] theorem lift_or_get_none_left {f} {b : Option α} : lift_or_get f none b = b := by
  cases b <;> rfl

@[simp] theorem lift_or_get_none_right {f} {a : Option α} : lift_or_get f a none = a := by
  cases a <;> rfl

@[simp] theorem lift_or_get_some_some {f} {a b : α} :
  lift_or_get f (some a) (some b) = f a b := rfl

theorem elim_none (x : β) (f : α → β) : none.elim x f = x := rfl

theorem elim_some (x : β) (f : α → β) (a : α) : (some a).elim x f = f a := rfl

@[simp] theorem getD_map (f : α → β) (x : α) (o : Option α) :
  (o.map f).getD (f x) = f (getD o x) := by cases o <;> rfl

section

attribute [local instance] Classical.propDecidable

/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some (Classical.choice h) else none

theorem choice_eq {α : Type _} [Subsingleton α] (a : α) : choice α = some a := by
  simp [choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  simp; apply Subsingleton.elim

theorem choice_isSome_iff_nonempty {α : Type _} : (choice α).isSome ↔ Nonempty α := by
  constructor
  · intro h
    exact ⟨Option.get h⟩
  · intro h
    simp only [choice]
    rw [dif_pos h]
    exact isSome_some

end

@[simp] theorem to_list_some (a : α) : (a : Option α).toList = [a] := rfl

@[simp] theorem to_list_none (α : Type _) : (none : Option α).toList = [] := rfl
