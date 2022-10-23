/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Logic.IsEmpty
import Mathlib.Tactic.Basic
import Mathlib.Logic.Relator
import Mathlib.Tactic.SimpTrace

/-!
# Option of a type

This file develops the basic theory of option types.

If `α` is a type, then `Option α` can be understood as the type with one more element than `α`.
`Option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `with_bot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `Option` is a monad. We love monads.

`Part` is an alternative to `Option` that can be seen as the type of `True`/`False` values
along with a term `a : α` if the value is `True`.

-/


namespace Option

variable {α β γ δ : Type _}

-- FIXME: do we even need this?
-- theorem coe_def : (coe : α → Option α) = some :=
--   rfl

-- TODO: move to std
/-- Extracts the value `a` from an option if it is `some a`, otherwise use a backup `b`. -/
def getOrElse {α : Type u} : (o : Option α) → α → α
  | some x, _ => x
  | none, b   => b

@[simp]
theorem get_or_else_some (x y : α) : Option.getOrElse (some x) y = x :=
  rfl

@[simp]
theorem get_or_else_none (x : α) : Option.getOrElse none x = x :=
  rfl

@[simp]
theorem get_or_else_coe (x y : α) : Option.getOrElse (↑x) y = x :=
  rfl

theorem get_or_else_of_ne_none {x : Option α} (hx : x ≠ none) (y : α) :
    some (x.getOrElse y) = x := by
  cases x; contradiction; rw [get_or_else_some]

@[simp]
theorem coe_get {o : Option α} (h : o.isSome) : ((Option.get _ h : α) : Option α) = o :=
  Option.some_get h

theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a ∈ o1) (h2 : a ∈ o2) : o1 = o2 :=
  h1.trans h2.symm

theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Option α → Prop) :=
fun _ _ _=> mem_unique

theorem some_injective (α : Type _) : Function.injective (@some α) := fun _ _ => some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.injective f) : Function.injective (Option.map f)
  | none, none, _ => rfl
  | some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]

@[simp]
theorem map_comp_some (f : α → β) : Option.map f ∘ some = some ∘ f :=
  rfl

@[simp]
theorem none_bind' (f : α → Option β) : none.bind f = none :=
  rfl

@[simp]
theorem some_bind' (a : α) (f : α → Option β) : (some a).bind f = f a :=
  rfl

@[simp]
theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
  by cases x <;> simp

@[simp]
theorem bind_eq_none' {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, mem_def, bind_eq_some, not_exists, not_and, iff_self]

-- FIXME: there is no global `mjoin`
-- theorem join_eq_join : mjoin = @join α :=
--   funext fun x => by rw [mjoin, bind_id_eq_join]

theorem bind_eq_bind {α β : Type _} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl

theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl

@[simp]
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl

/-- `option.map` as a function between functions is injective. -/
theorem map_injective' : Function.injective (@Option.map α β) := fun f g h =>
  funext fun x => some_injective _ <| by simp only [← map_some', h]

@[simp]
theorem map_inj {f g : α → β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff

attribute [simp] map_id

@[simp]
theorem map_eq_id {f : α → α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
  (a : α) :
    (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]

section Pmap

variable {p : α → Prop} (f : ∀ a : α, p a → β) (x : Option α)

@[simp]
theorem pbind_eq_bind (f : α → Option β) (x : Option α) : (x.pbind fun a _ => f a) = x.bind f := by
  cases x <;> simp only [pbind, none_bind', some_bind']

theorem map_bind {α β γ} (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x >>= g) = x >>= fun a => Option.map f (g a) := by
  simp only [← map_eq_map, ← bind_pure_comp, LawfulMonad.bind_assoc]

theorem map_bind' (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x.bind g) = x.bind fun a => Option.map f (g a) := by cases x <;> simp

theorem map_pbind (f : β → γ) (x : Option α) (g : ∀ a, a ∈ x → Option β) :
    Option.map f (x.pbind g) = x.pbind fun a H => Option.map f (g a H) := by
  cases x <;> simp only [pbind, map_none']

theorem pbind_map (f : α → β) (x : Option α) (g : ∀ b : β, b ∈ x.map f → Option γ) :
    pbind (Option.map f x) g = x.pbind fun a h => g (f a) (mem_map_of_mem _ h) := by cases x <;> rfl

@[simp]
theorem pmap_none (f : ∀ a : α, p a → β) {H} : pmap f (@none α) H = none :=
  rfl

@[simp]
theorem pmap_some (f : ∀ a : α, p a → β) {x : α} (h : p x) :
    pmap f (some x) = fun _ => some (f x h) :=
  rfl

theorem mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h := by
  rw [mem_def] at ha ⊢
  subst ha
  rfl

theorem pmap_map (g : γ → α) (x : Option γ) (H) :
    pmap f (x.map g) H = pmap (fun a h => f (g a) h) x fun a h => H _ (mem_map_of_mem _ h) := by
  cases x <;> simp only [map_none', map_some', pmap]

theorem map_pmap (g : β → γ) (f : ∀ a, p a → β) (x H) :
    Option.map g (pmap f x H) = pmap (fun a h => g (f a h)) x H :=
  by cases x <;> simp only [map_none', map_some', pmap]

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (x H) :
    @pmap _ _ p (fun a _ => f a) x H = Option.map f x := by
  cases x <;> simp only [map_none', map_some', pmap]

theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a => pmap f (g a) fun b h => H _ (H' a _ h) := by
  cases x <;> simp only [pmap, bind_eq_bind, none_bind, some_bind]

theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h => g (f a (H _ h)) := by
  cases x <;> simp only [pmap, bind_eq_bind, none_bind, some_bind, pbind]

variable {f x}

theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β}
    (h' : ∀ a (H : a ∈ x), f a H = none → x = none) : x.pbind f = none ↔ x = none := by
  cases x
  · simp
  · simp only [pbind, iff_false]
    intro h
    cases h' _ rfl h

theorem pbind_eq_some {f : ∀ a : α, a ∈ x → Option β} {y : β} :
    x.pbind f = some y ↔ ∃ (z : α) (H : z ∈ x), f z H = some y := by
  rcases x with (_|x)
  · simp only [pbind, false_iff, not_exists]
    intro z h
    simp at h
  · simp only [pbind]
    refine ⟨λ h => ⟨x, rfl, h⟩, ?_⟩
    rintro ⟨z, H, hz⟩
    simp only [mem_def, some.injEq] at H
    simpa [H] using hz

@[simp]
theorem pmap_eq_none_iff {h} : pmap f x h = none ↔ x = none := by cases x <;> simp

@[simp]
theorem pmap_eq_some_iff {hf} {y : β} :
    pmap f x hf = some y ↔ ∃ (a : α) (H : x = some a), f a (hf a H) = y := by
  cases x
  · simp only [not_mem_none, exists_false, pmap, not_false_iff, exists_prop_of_false]

  · constructor
    · intro h
      simp only [pmap] at h
      exact ⟨x, rfl, h⟩

    · rintro ⟨a, H, rfl⟩
      simp only [mem_def] at H
      simp only [H, pmap]



@[simp]
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h => H (some a) (mem_of_mem_join h) _ rfl := by
  rcases x with (_ | _ | x) <;> simp

end Pmap

@[simp]
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl

@[simp]
theorem some_orelse' (a : α) (x : Option α) : (some a).orelse x = some a :=
  rfl

@[simp]
theorem some_orelse (a : α) (x : Option α) : (some a <|> x) = some a :=
  rfl

@[simp]
theorem none_orelse' (x : Option α) : none.orelse x = x := by cases x <;> rfl

@[simp]
theorem none_orelse (x : Option α) : (none <|> x) = x :=
  none_orelse' x

@[simp]
theorem orelse_none' (x : Option α) : x.orelse none = x := by cases x <;> rfl

@[simp]
theorem orelse_none (x : Option α) : (x <|> none) = x :=
  orelse_none' x

@[simp]
theorem is_some_none : @isSome α none = ff :=
  rfl

@[simp]
theorem is_some_some {a : α} : isSome (some a) = tt :=
  rfl

theorem is_some_iff_exists {x : Option α} : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [is_some] <;> exact ⟨_, rfl⟩

@[simp]
theorem is_none_none : @isNone α none = tt :=
  rfl

@[simp]
theorem is_none_some {a : α} : isNone (some a) = ff :=
  rfl

@[simp]
theorem not_is_some {a : Option α} : isSome a = ff ↔ a.isNone = tt := by cases a <;> simp

theorem eq_some_iff_get_eq {o : Option α} {a : α} : o = some a ↔ ∃ h : o.isSome, Option.get h = a := by
  cases o <;> simp

theorem not_is_some_iff_eq_none {o : Option α} : ¬o.isSome ↔ o = none := by cases o <;> simp

theorem ne_none_iff_is_some {o : Option α} : o ≠ none ↔ o.isSome := by cases o <;> simp

theorem ne_none_iff_exists {o : Option α} : o ≠ none ↔ ∃ x : α, some x = o := by cases o <;> simp

theorem ne_none_iff_exists' {o : Option α} : o ≠ none ↔ ∃ x : α, o = some x :=
  ne_none_iff_exists.trans <| exists_congr fun _ => eq_comm

-- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x «expr ≠ » none[option.none])
theorem bex_ne_none {p : Option α → Prop} : (∃ (x : _)(_ : x ≠ none), p x) ↔ ∃ x, p (some x) :=
  ⟨fun ⟨x, hx, hp⟩ => ⟨get <| ne_none_iff_is_some.1 hx, by rwa [some_get]⟩, fun ⟨x, hx⟩ => ⟨some x, some_ne_none x, hx⟩⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x «expr ≠ » none[option.none])
theorem ball_ne_none {p : Option α → Prop} : (∀ (x) (_ : x ≠ none), p x) ↔ ∀ x, p (some x) :=
  ⟨fun h x => h (some x) (some_ne_none x), fun h x hx => by
    simpa only [some_get] using h (get <| ne_none_iff_is_some.1 hx)⟩

theorem iget_mem [Inhabited α] : ∀ {o : Option α}, isSome o → o.iget ∈ o
  | some a, _ => rfl

theorem iget_of_mem [Inhabited α] {a : α} : ∀ {o : Option α}, a ∈ o → o.iget = a
  | _, rfl => rfl

theorem get_or_else_default_eq_iget [Inhabited α] (o : Option α) : o.getOrElse default = o.iget := by cases o <;> rfl

@[simp]
theorem guard_eq_some {p : α → Prop} [DecidablePred p] {a b : α} : guard p a = some b ↔ a = b ∧ p a := by
  by_cases p a <;> simp [Option.guard, h] <;> intro <;> contradiction

@[simp]
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : guard p = some u ↔ p := by
  cases u
  by_cases p <;> simp [_root_.guard, h] <;> first |rfl|contradiction

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => Or.inl rfl
  | some a, none => Or.inl rfl
  | none, some b => Or.inr rfl
  | some a, some b => by simpa [lift_or_get] using h a b

@[simp]
theorem lift_or_get_none_left {f} {b : Option α} : liftOrGet f none b = b := by cases b <;> rfl

@[simp]
theorem lift_or_get_none_right {f} {a : Option α} : liftOrGet f a none = a := by cases a <;> rfl

@[simp]
theorem lift_or_get_some_some {f} {a b : α} : liftOrGet f (some a) (some b) = f a b :=
  rfl

/-- Given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def casesOn' : Option α → β → (α → β) → β
  | none, n, s => n
  | some a, n, s => s a

@[simp]
theorem cases_on'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl

@[simp]
theorem cases_on'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl

@[simp]
theorem cases_on'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl

@[simp]
theorem cases_on'_none_coe (f : Option α → β) (o : Option α) : casesOn' o (f none) (f ∘ coe) = f o := by cases o <;> rfl

@[simp]
theorem get_or_else_map (f : α → β) (x : α) (o : Option α) : getOrElse (o.map f) (f x) = f (getOrElse o x) := by
  cases o <;> rfl

theorem orelse_eq_some (o o' : Option α) (x : α) : (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x := by
  cases o
  · simp only [true_and, false_or, eq_self_iff_true, none_orelse]

  · simp only [some_orelse, or_false, false_and]


theorem orelse_eq_some' (o o' : Option α) (x : α) : o.orelse o' = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  Option.orelse_eq_some o o' x

@[simp]
theorem orelse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none := by
  cases o
  · simp only [true_and, none_orelse, eq_self_iff_true]

  · simp only [some_orelse, false_and]


@[simp]
theorem orelse_eq_none' (o o' : Option α) : o.orelse o' = none ↔ o = none ∧ o' = none :=
  Option.orelse_eq_none o o'

section

open Classical

/-- An arbitrary `some a` with `a : α` if `α` is nonempty, and otherwise `none`. -/
noncomputable def choice (α : Type _) : Option α :=
  if h : Nonempty α then some h.some else none

theorem choice_eq {α : Type _} [Subsingleton α] (a : α) : choice α = some a := by
  dsimp [choice]
  rw [dif_pos (⟨a⟩ : Nonempty α)]
  congr

theorem choice_eq_none (α : Type _) [IsEmpty α] : choice α = none :=
  dif_neg (not_nonempty_iff_imp_false.mpr isEmptyElim)

theorem choice_is_some_iff_nonempty {α : Type _} : (choice α).isSome ↔ Nonempty α := by
  fconstructor
  · intro h
    exact ⟨Option.get h⟩

  · intro h
    dsimp only [choice]
    rw [dif_pos h]
    exact is_some_some


end

@[simp]
theorem to_list_some (a : α) : (a : Option α).toList = [a] :=
  rfl

@[simp]
theorem to_list_none (α : Type _) : (none : Option α).toList = [] :=
  rfl

@[simp]
theorem elim_none_some (f : Option α → β) : Option.elim (f none) (f ∘ some) = f :=
  funext fun o => by cases o <;> rfl

end Option
