/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Control.Combinators
import Mathlib.Data.Option.Defs
import Mathlib.Logic.IsEmpty
import Mathlib.Logic.Relator
import Mathlib.Util.CompileInductive
import Aesop

#align_import data.option.basic from "leanprover-community/mathlib"@"f340f229b1f461aa1c8ee11e0a172d0a3b301a4a"

/-!
# Option of a type

This file develops the basic theory of option types.

If `α` is a type, then `Option α` can be understood as the type with one more element than `α`.
`Option α` has terms `some a`, where `a : α`, and `none`, which is the added element.
This is useful in multiple ways:
* It is the prototype of addition of terms to a type. See for example `WithBot α` which uses
  `none` as an element smaller than all others.
* It can be used to define failsafe partial functions, which return `some the_result_we_expect`
  if we can find `the_result_we_expect`, and `none` if there is no meaningful result. This forces
  any subsequent use of the partial function to explicitly deal with the exceptions that make it
  return `none`.
* `Option` is a monad. We love monads.

`Part` is an alternative to `Option` that can be seen as the type of `True`/`False` values
along with a term `a : α` if the value is `True`.

-/

universe u

namespace Option

variable {α β γ δ : Type*}

theorem coe_def : (fun a ↦ ↑a : α → Option α) = some :=
  rfl
#align option.coe_def Option.coe_def

theorem mem_map {f : α → β} {y : β} {o : Option α} : y ∈ o.map f ↔ ∃ x ∈ o, f x = y := by simp
#align option.mem_map Option.mem_map

-- The simpNF linter says that the LHS can be simplified via `Option.mem_def`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {o : Option α} :
    f a ∈ o.map f ↔ a ∈ o := by
  aesop

theorem forall_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∀ y ∈ o.map f, p y) ↔ ∀ x ∈ o, p (f x) := by simp
#align option.forall_mem_map Option.forall_mem_map

theorem exists_mem_map {f : α → β} {o : Option α} {p : β → Prop} :
    (∃ y ∈ o.map f, p y) ↔ ∃ x ∈ o, p (f x) := by simp
#align option.exists_mem_map Option.exists_mem_map

theorem coe_get {o : Option α} (h : o.isSome) : ((Option.get _ h : α) : Option α) = o :=
  Option.some_get h
#align option.coe_get Option.coe_get

theorem eq_of_mem_of_mem {a : α} {o1 o2 : Option α} (h1 : a ∈ o1) (h2 : a ∈ o2) : o1 = o2 :=
  h1.trans h2.symm
#align option.eq_of_mem_of_mem Option.eq_of_mem_of_mem

theorem Mem.leftUnique : Relator.LeftUnique ((· ∈ ·) : α → Option α → Prop) :=
  fun _ _ _=> mem_unique
#align option.mem.left_unique Option.Mem.leftUnique

theorem some_injective (α : Type*) : Function.Injective (@some α) := fun _ _ ↦ some_inj.mp
#align option.some_injective Option.some_injective

/-- `Option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.Injective f) : Function.Injective (Option.map f)
  | none, none, _ => rfl
  | some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]
#align option.map_injective Option.map_injective

@[simp]
theorem map_comp_some (f : α → β) : Option.map f ∘ some = some ∘ f :=
  rfl
#align option.map_comp_some Option.map_comp_some

@[simp]
theorem none_bind' (f : α → Option β) : none.bind f = none :=
  rfl
#align option.none_bind' Option.none_bind'

@[simp]
theorem some_bind' (a : α) (f : α → Option β) : (some a).bind f = f a :=
  rfl
#align option.some_bind' Option.some_bind'

theorem bind_eq_some' {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp
#align option.bind_eq_some' Option.bind_eq_some'

#align option.bind_eq_none' Option.bind_eq_none'

theorem bind_congr {f g : α → Option β} {x : Option α}
    (h : ∀ a ∈ x, f a = g a) : x.bind f = x.bind g := by
  cases x <;> simp only [some_bind, none_bind, mem_def, h]

@[congr]
theorem bind_congr' {f g : α → Option β} {x y : Option α} (hx : x = y)
    (hf : ∀ a ∈ y, f a = g a) : x.bind f = y.bind g :=
  hx.symm ▸ bind_congr hf

theorem joinM_eq_join : joinM = @join α :=
  funext fun _ ↦ rfl
#align option.join_eq_join Option.joinM_eq_join

theorem bind_eq_bind' {α β : Type u} {f : α → Option β} {x : Option α} : x >>= f = x.bind f :=
  rfl
#align option.bind_eq_bind Option.bind_eq_bind'

theorem map_coe {α β} {a : α} {f : α → β} : f <$> (a : Option α) = ↑(f a) :=
  rfl
#align option.map_coe Option.map_coe

@[simp]
theorem map_coe' {a : α} {f : α → β} : Option.map f (a : Option α) = ↑(f a) :=
  rfl
#align option.map_coe' Option.map_coe'

/-- `Option.map` as a function between functions is injective. -/
theorem map_injective' : Function.Injective (@Option.map α β) := fun f g h ↦
  funext fun x ↦ some_injective _ <| by simp only [← map_some', h]
#align option.map_injective' Option.map_injective'

@[simp]
theorem map_inj {f g : α → β} : Option.map f = Option.map g ↔ f = g :=
  map_injective'.eq_iff
#align option.map_inj Option.map_inj

attribute [simp] map_id

@[simp]
theorem map_eq_id {f : α → α} : Option.map f = id ↔ f = id :=
  map_injective'.eq_iff' map_id
#align option.map_eq_id Option.map_eq_id

theorem map_comm {f₁ : α → β} {f₂ : α → γ} {g₁ : β → δ} {g₂ : γ → δ} (h : g₁ ∘ f₁ = g₂ ∘ f₂)
    (a : α) :
    (Option.map f₁ a).map g₁ = (Option.map f₂ a).map g₂ := by rw [map_map, h, ← map_map]
#align option.map_comm Option.map_comm

section pmap

variable {p : α → Prop} (f : ∀ a : α, p a → β) (x : Option α)

-- Porting note: Can't simp tag this anymore because `pbind` simplifies
-- @[simp]
theorem pbind_eq_bind (f : α → Option β) (x : Option α) : (x.pbind fun a _ ↦ f a) = x.bind f := by
  cases x <;> simp only [pbind, none_bind', some_bind']
#align option.pbind_eq_bind Option.pbind_eq_bind

theorem map_bind {α β γ} (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x >>= g) = x >>= fun a ↦ Option.map f (g a) := by
  simp only [← map_eq_map, ← bind_pure_comp, LawfulMonad.bind_assoc]
#align option.map_bind Option.map_bind

theorem map_bind' (f : β → γ) (x : Option α) (g : α → Option β) :
    Option.map f (x.bind g) = x.bind fun a ↦ Option.map f (g a) := by cases x <;> simp
#align option.map_bind' Option.map_bind'

theorem map_pbind (f : β → γ) (x : Option α) (g : ∀ a, a ∈ x → Option β) :
    Option.map f (x.pbind g) = x.pbind fun a H ↦ Option.map f (g a H) := by
  cases x <;> simp only [pbind, map_none']
#align option.map_pbind Option.map_pbind

theorem pbind_map (f : α → β) (x : Option α) (g : ∀ b : β, b ∈ x.map f → Option γ) :
    pbind (Option.map f x) g = x.pbind fun a h ↦ g (f a) (mem_map_of_mem _ h) := by cases x <;> rfl
#align option.pbind_map Option.pbind_map

@[simp]
theorem pmap_none (f : ∀ a : α, p a → β) {H} : pmap f (@none α) H = none :=
  rfl
#align option.pmap_none Option.pmap_none

@[simp]
theorem pmap_some (f : ∀ a : α, p a → β) {x : α} (h : p x) :
    pmap f (some x) = fun _ ↦ some (f x h) :=
  rfl
#align option.pmap_some Option.pmap_some

theorem mem_pmem {a : α} (h : ∀ a ∈ x, p a) (ha : a ∈ x) : f a (h a ha) ∈ pmap f x h := by
  rw [mem_def] at ha ⊢
  subst ha
  rfl
#align option.mem_pmem Option.mem_pmem

theorem pmap_map (g : γ → α) (x : Option γ) (H) :
    pmap f (x.map g) H = pmap (fun a h ↦ f (g a) h) x fun a h ↦ H _ (mem_map_of_mem _ h) := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.pmap_map Option.pmap_map

theorem map_pmap (g : β → γ) (f : ∀ a, p a → β) (x H) :
    Option.map g (pmap f x H) = pmap (fun a h ↦ g (f a h)) x H := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.map_pmap Option.map_pmap

-- Porting note: Can't simp tag this anymore because `pmap` simplifies
-- @[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (x H) :
    @pmap _ _ p (fun a _ ↦ f a) x H = Option.map f x := by
  cases x <;> simp only [map_none', map_some', pmap]
#align option.pmap_eq_map Option.pmap_eq_map

theorem pmap_bind {α β γ} {x : Option α} {g : α → Option β} {p : β → Prop} {f : ∀ b, p b → γ} (H)
    (H' : ∀ (a : α), ∀ b ∈ g a, b ∈ x >>= g) :
    pmap f (x >>= g) H = x >>= fun a ↦ pmap f (g a) fun b h ↦ H _ (H' a _ h) := by
  cases x <;> simp only [pmap, bind_eq_bind, none_bind, some_bind]
#align option.pmap_bind Option.pmap_bind

theorem bind_pmap {α β γ} {p : α → Prop} (f : ∀ a, p a → β) (x : Option α) (g : β → Option γ) (H) :
    pmap f x H >>= g = x.pbind fun a h ↦ g (f a (H _ h)) := by
  cases x <;> simp only [pmap, bind_eq_bind, none_bind, some_bind, pbind]
#align option.bind_pmap Option.bind_pmap

variable {f x}

theorem pbind_eq_none {f : ∀ a : α, a ∈ x → Option β}
    (h' : ∀ a (H : a ∈ x), f a H = none → x = none) : x.pbind f = none ↔ x = none := by
  cases x
  · simp
  · simp only [pbind, iff_false]
    intro h
    cases h' _ rfl h
#align option.pbind_eq_none Option.pbind_eq_none

theorem pbind_eq_some {f : ∀ a : α, a ∈ x → Option β} {y : β} :
    x.pbind f = some y ↔ ∃ (z : α) (H : z ∈ x), f z H = some y := by
  rcases x with (_|x)
  · simp only [pbind, false_iff, not_exists]
    intro z h
    simp at h
  · simp only [pbind]
    refine ⟨fun h ↦ ⟨x, rfl, h⟩, ?_⟩
    rintro ⟨z, H, hz⟩
    simp only [mem_def, Option.some_inj] at H
    simpa [H] using hz
#align option.pbind_eq_some Option.pbind_eq_some

-- Porting note: Can't simp tag this anymore because `pmap` simplifies
-- @[simp]
theorem pmap_eq_none_iff {h} : pmap f x h = none ↔ x = none := by cases x <;> simp
#align option.pmap_eq_none_iff Option.pmap_eq_none_iff

-- Porting note: Can't simp tag this anymore because `pmap` simplifies
-- @[simp]
theorem pmap_eq_some_iff {hf} {y : β} :
    pmap f x hf = some y ↔ ∃ (a : α) (H : x = some a), f a (hf a H) = y := by
  rcases x with (_|x)
  · simp only [not_mem_none, exists_false, pmap, not_false_iff, exists_prop_of_false]
  · constructor
    · intro h
      simp only [pmap, Option.some_inj] at h
      exact ⟨x, rfl, h⟩
    · rintro ⟨a, H, rfl⟩
      simp only [mem_def, Option.some_inj] at H
      simp only [H, pmap]
#align option.pmap_eq_some_iff Option.pmap_eq_some_iff

-- Porting note: Can't simp tag this anymore because `join` and `pmap` simplify
-- @[simp]
theorem join_pmap_eq_pmap_join {f : ∀ a, p a → β} {x : Option (Option α)} (H) :
    (pmap (pmap f) x H).join = pmap f x.join fun a h ↦ H (some a) (mem_of_mem_join h) _ rfl := by
  rcases x with (_ | _ | x) <;> simp
#align option.join_pmap_eq_pmap_join Option.join_pmap_eq_pmap_join

end pmap

@[simp]
theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) :=
  rfl
#align option.seq_some Option.seq_some

@[simp]
theorem some_orElse' (a : α) (x : Option α) : (some a).orElse (fun _ ↦ x) = some a :=
  rfl
#align option.some_orelse' Option.some_orElse'

#align option.some_orelse Option.some_orElse

@[simp]
theorem none_orElse' (x : Option α) : none.orElse (fun _ ↦ x) = x := by cases x <;> rfl
#align option.none_orelse' Option.none_orElse'

#align option.none_orelse Option.none_orElse

@[simp]
theorem orElse_none' (x : Option α) : x.orElse (fun _ ↦ none) = x := by cases x <;> rfl
#align option.orelse_none' Option.orElse_none'

#align option.orelse_none Option.orElse_none

#align option.is_some_none Option.isSome_none

#align option.is_some_some Option.isSome_some

#align option.is_some_iff_exists Option.isSome_iff_exists

#align option.is_none_none Option.isNone_none

#align option.is_none_some Option.isNone_some

#align option.not_is_some Option.not_isSome

#align option.not_is_some_iff_eq_none Option.not_isSome_iff_eq_none

#align option.ne_none_iff_is_some Option.ne_none_iff_isSome

theorem exists_ne_none {p : Option α → Prop} : (∃ x ≠ none, p x) ↔ (∃ x : α, p x) := by
  simp only [← exists_prop, bex_ne_none]

@[simp]
theorem isSome_map (f : α → β) (o : Option α) : isSome (o.map f) = isSome o := by
  cases o <;> rfl

@[simp]
theorem get_map (f : α → β) {o : Option α} (h : isSome (o.map f)) :
    (o.map f).get h = f (o.get (by rwa [← isSome_map])) := by
  cases o <;> [simp at h; rfl]

theorem iget_mem [Inhabited α] : ∀ {o : Option α}, isSome o → o.iget ∈ o
  | some _, _ => rfl
#align option.iget_mem Option.iget_mem

theorem iget_of_mem [Inhabited α] {a : α} : ∀ {o : Option α}, a ∈ o → o.iget = a
  | _, rfl => rfl
#align option.iget_of_mem Option.iget_of_mem

theorem getD_default_eq_iget [Inhabited α] (o : Option α) :
    o.getD default = o.iget := by cases o <;> rfl
#align option.get_or_else_default_eq_iget Option.getD_default_eq_iget

@[simp]
theorem guard_eq_some' {p : Prop} [Decidable p] (u) : _root_.guard p = some u ↔ p := by
  cases u
  by_cases h : p <;> simp [_root_.guard, h]
#align option.guard_eq_some' Option.guard_eq_some'

theorem liftOrGet_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
    ∀ o₁ o₂, liftOrGet f o₁ o₂ = o₁ ∨ liftOrGet f o₁ o₂ = o₂
  | none, none => Or.inl rfl
  | some a, none => Or.inl rfl
  | none, some b => Or.inr rfl
  | some a, some b => by simpa [liftOrGet] using h a b
#align option.lift_or_get_choice Option.liftOrGet_choice

#align option.lift_or_get_none_left Option.liftOrGet_none_left

#align option.lift_or_get_none_right Option.liftOrGet_none_right

#align option.lift_or_get_some_some Option.liftOrGet_some_some

/-- Given an element of `a : Option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def casesOn' : Option α → β → (α → β) → β
  | none, n, _ => n
  | some a, _, s => s a
#align option.cases_on' Option.casesOn'

@[simp]
theorem casesOn'_none (x : β) (f : α → β) : casesOn' none x f = x :=
  rfl
#align option.cases_on'_none Option.casesOn'_none

@[simp]
theorem casesOn'_some (x : β) (f : α → β) (a : α) : casesOn' (some a) x f = f a :=
  rfl
#align option.cases_on'_some Option.casesOn'_some

@[simp]
theorem casesOn'_coe (x : β) (f : α → β) (a : α) : casesOn' (a : Option α) x f = f a :=
  rfl
#align option.cases_on'_coe Option.casesOn'_coe

-- Porting note: Left-hand side does not simplify.
-- @[simp]
theorem casesOn'_none_coe (f : Option α → β) (o : Option α) :
    casesOn' o (f none) (f ∘ (fun a ↦ ↑a)) = f o := by cases o <;> rfl
#align option.cases_on'_none_coe Option.casesOn'_none_coe

lemma casesOn'_eq_elim (b : β) (f : α → β) (a : Option α) :
    Option.casesOn' a b f = Option.elim a b f := by cases a <;> rfl

-- porting note: workaround for leanprover/lean4#2049
compile_inductive% Option

theorem orElse_eq_some (o o' : Option α) (x : α) :
    (o <|> o') = some x ↔ o = some x ∨ o = none ∧ o' = some x := by
  cases o
  · simp only [true_and, false_or, eq_self_iff_true, none_orElse]
  · simp only [some_orElse, or_false, false_and]
#align option.orelse_eq_some Option.orElse_eq_some


theorem orElse_eq_some' (o o' : Option α) (x : α) :
    o.orElse (fun _ ↦ o') = some x ↔ o = some x ∨ o = none ∧ o' = some x :=
  Option.orElse_eq_some o o' x
#align option.orelse_eq_some' Option.orElse_eq_some'

@[simp]
theorem orElse_eq_none (o o' : Option α) : (o <|> o') = none ↔ o = none ∧ o' = none := by
  cases o
  · simp only [true_and, none_orElse, eq_self_iff_true]
  · simp only [some_orElse, false_and]
#align option.orelse_eq_none Option.orElse_eq_none

@[simp]
theorem orElse_eq_none' (o o' : Option α) : o.orElse (fun _ ↦ o') = none ↔ o = none ∧ o' = none :=
  Option.orElse_eq_none o o'
#align option.orelse_eq_none' Option.orElse_eq_none'

section

open scoped Classical

theorem choice_eq_none (α : Type*) [IsEmpty α] : choice α = none :=
  dif_neg (not_nonempty_iff_imp_false.mpr isEmptyElim)
#align option.choice_eq_none Option.choice_eq_none

#align option.choice_is_some_iff_nonempty Option.choice_isSome_iff_nonempty

end

-- Porting note: Can't simp tag this anymore because `elim` simplifies
-- @[simp]
theorem elim_none_some (f : Option α → β) : (fun x ↦ Option.elim x (f none) (f ∘ some)) = f :=
  funext fun o ↦ by cases o <;> rfl
#align option.elim_none_some Option.elim_none_some

theorem elim_comp (h : α → β) {f : γ → α} {x : α} {i : Option γ} :
    (i.elim (h x) fun j => h (f j)) = h (i.elim x f) := by cases i <;> rfl

theorem elim_comp₂ (h : α → β → γ) {f : γ → α} {x : α} {g : γ → β} {y : β}
    {i : Option γ} : (i.elim (h x y) fun j => h (f j) (g j)) = h (i.elim x f) (i.elim y g) := by
  cases i <;> rfl

theorem elim_apply {f : γ → α → β} {x : α → β} {i : Option γ} {y : α} :
    i.elim x f y = i.elim (x y) fun j => f j y := by rw [elim_comp fun f : α → β => f y]

@[simp]
lemma bnot_isSome (a : Option α) : (! a.isSome) = a.isNone := by
  funext
  cases a <;> simp

@[simp]
lemma bnot_comp_isSome : (! ·) ∘ @Option.isSome α = Option.isNone := by
  funext
  simp

@[simp]
lemma bnot_isNone (a : Option α) : (! a.isNone) = a.isSome := by
  funext
  cases a <;> simp

@[simp]
lemma bnot_comp_isNone : (! ·) ∘ @Option.isNone α = Option.isSome := by
  funext x
  simp

@[simp]
lemma isNone_eq_false_iff (a : Option α) : Option.isNone a = false ↔ Option.isSome a := by
  cases a <;> simp

lemma eq_none_or_eq_some (a : Option α) : a = none ∨ ∃ x, a = some x :=
  Option.exists.mp exists_eq'

end Option
