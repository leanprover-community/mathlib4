/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import Mathlib.Data.Set.Subsingleton
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.Defs

#align_import data.part from "leanprover-community/mathlib"@"80c43012d26f63026d362c3aba28f3c3bafb07e6"

/-!
# Partial values of a type
This file defines `Part α`, the partial values of a type.
`o : Part α` carries a proposition `o.Dom`, its domain, along with a function `get : o.Dom → α`, its
value. The rule is then that every partial value has a value but, to access it, you need to provide
a proof of the domain.
`Part α` behaves the same as `Option α` except that `o : Option α` is decidably `none` or `some a`
for some `a : α`, while the domain of `o : Part α` doesn't have to be decidable. That means you can
translate back and forth between a partial value with a decidable domain and an option, and
`Option α` and `Part α` are classically equivalent. In general, `Part α` is bigger than `Option α`.
In current mathlib, `Part ℕ`, aka `PartENat`, is used to move decidability of the order to
decidability of `PartENat.find` (which is the smallest natural satisfying a predicate, or `∞` if
there's none).
## Main declarations
`Option`-like declarations:
* `Part.none`: The partial value whose domain is `False`.
* `Part.some a`: The partial value whose domain is `True` and whose value is `a`.
* `Part.ofOption`: Converts an `Option α` to a `Part α` by sending `none` to `none` and `some a` to
  `some a`.
* `Part.toOption`: Converts a `Part α` with a decidable domain to an `Option α`.
* `Part.equivOption`: Classical equivalence between `Part α` and `Option α`.
Monadic structure:
* `Part.bind`: `o.bind f` has value `(f (o.get _)).get _` (`f o` morally) and is defined when `o`
  and `f (o.get _)` are defined.
* `Part.map`: Maps the value and keeps the same domain.
Other:
* `Part.restrict`: `Part.restrict p o` replaces the domain of `o : Part α` by `p : Prop` so long as
  `p → o.Dom`.
* `Part.assert`: `assert p f` appends `p` to the domains of the values of a partial function.
* `Part.unwrap`: Gets the value of a partial value regardless of its domain. Unsound.
## Notation
For `a : α`, `o : Part α`, `a ∈ o` means that `o` is defined and equal to `a`. Formally, it means
`o.Dom` and `o.get _ = a`.
-/

open Function

/-- `Part α` is the type of "partial values" of type `α`. It
  is similar to `Option α` except the domain condition can be an
  arbitrary proposition, not necessarily decidable. -/
structure Part.{u} (α : Type u) : Type u where
  /-- The domain of a partial value -/
  Dom : Prop
  /-- Extract a value from a partial value given a proof of `Dom` -/
  get : Dom → α
#align part Part

namespace Part

variable {α : Type*} {β : Type*} {γ : Type*}

/-- Convert a `Part α` with a decidable domain to an option -/
def toOption (o : Part α) [Decidable o.Dom] : Option α :=
  if h : Dom o then some (o.get h) else none
#align part.to_option Part.toOption

@[simp] lemma toOption_isSome (o : Part α) [Decidable o.Dom] : o.toOption.isSome ↔ o.Dom := by
  by_cases h : o.Dom <;> simp [h, toOption]
#align part.to_option_is_some Part.toOption_isSome

@[simp] lemma toOption_isNone (o : Part α) [Decidable o.Dom] : o.toOption.isNone ↔ ¬o.Dom := by
  by_cases h : o.Dom <;> simp [h, toOption]
#align part.to_option_is_none Part.toOption_isNone

/-- `Part` extensionality -/
theorem ext' : ∀ {o p : Part α}, (o.Dom ↔ p.Dom) → (∀ h₁ h₂, o.get h₁ = p.get h₂) → o = p
  | ⟨od, o⟩, ⟨pd, p⟩, H1, H2 => by
    have t : od = pd := propext H1
    cases t; rw [show o = p from funext fun p => H2 p p]
#align part.ext' Part.ext'

/-- `Part` eta expansion -/
@[simp]
theorem eta : ∀ o : Part α, (⟨o.Dom, fun h => o.get h⟩ : Part α) = o
  | ⟨_, _⟩ => rfl
#align part.eta Part.eta

/-- `a ∈ o` means that `o` is defined and equal to `a` -/
protected def Mem (a : α) (o : Part α) : Prop :=
  ∃ h, o.get h = a
#align part.mem Part.Mem

instance : Membership α (Part α) :=
  ⟨Part.Mem⟩

theorem mem_eq (a : α) (o : Part α) : (a ∈ o) = ∃ h, o.get h = a :=
  rfl
#align part.mem_eq Part.mem_eq

theorem dom_iff_mem : ∀ {o : Part α}, o.Dom ↔ ∃ y, y ∈ o
  | ⟨_, f⟩ => ⟨fun h => ⟨f h, h, rfl⟩, fun ⟨_, h, rfl⟩ => h⟩
#align part.dom_iff_mem Part.dom_iff_mem

theorem get_mem {o : Part α} (h) : get o h ∈ o :=
  ⟨_, rfl⟩
#align part.get_mem Part.get_mem

@[simp]
theorem mem_mk_iff {p : Prop} {o : p → α} {a : α} : a ∈ Part.mk p o ↔ ∃ h, o h = a :=
  Iff.rfl
#align part.mem_mk_iff Part.mem_mk_iff

/-- `Part` extensionality -/
@[ext]
theorem ext {o p : Part α} (H : ∀ a, a ∈ o ↔ a ∈ p) : o = p :=
  (ext' ⟨fun h => ((H _).1 ⟨h, rfl⟩).fst, fun h => ((H _).2 ⟨h, rfl⟩).fst⟩) fun _ _ =>
    ((H _).2 ⟨_, rfl⟩).snd
#align part.ext Part.ext

/-- The `none` value in `Part` has a `False` domain and an empty function. -/
def none : Part α :=
  ⟨False, False.rec⟩
#align part.none Part.none

instance : Inhabited (Part α) :=
  ⟨none⟩

@[simp]
theorem not_mem_none (a : α) : a ∉ @none α := fun h => h.fst
#align part.not_mem_none Part.not_mem_none

/-- The `some a` value in `Part` has a `True` domain and the
  function returns `a`. -/
def some (a : α) : Part α :=
  ⟨True, fun _ => a⟩
#align part.some Part.some

@[simp]
theorem some_dom (a : α) : (some a).Dom :=
  trivial
#align part.some_dom Part.some_dom

theorem mem_unique : ∀ {a b : α} {o : Part α}, a ∈ o → b ∈ o → a = b
  | _, _, ⟨_, _⟩, ⟨_, rfl⟩, ⟨_, rfl⟩ => rfl
#align part.mem_unique Part.mem_unique

theorem Mem.left_unique : Relator.LeftUnique ((· ∈ ·) : α → Part α → Prop) := fun _ _ _ =>
  mem_unique
#align part.mem.left_unique Part.Mem.left_unique

theorem get_eq_of_mem {o : Part α} {a} (h : a ∈ o) (h') : get o h' = a :=
  mem_unique ⟨_, rfl⟩ h
#align part.get_eq_of_mem Part.get_eq_of_mem

protected theorem subsingleton (o : Part α) : Set.Subsingleton { a | a ∈ o } := fun _ ha _ hb =>
  mem_unique ha hb
#align part.subsingleton Part.subsingleton

@[simp]
theorem get_some {a : α} (ha : (some a).Dom) : get (some a) ha = a :=
  rfl
#align part.get_some Part.get_some

theorem mem_some (a : α) : a ∈ some a :=
  ⟨trivial, rfl⟩
#align part.mem_some Part.mem_some

@[simp]
theorem mem_some_iff {a b} : b ∈ (some a : Part α) ↔ b = a :=
  ⟨fun ⟨_, e⟩ => e.symm, fun e => ⟨trivial, e.symm⟩⟩
#align part.mem_some_iff Part.mem_some_iff

theorem eq_some_iff {a : α} {o : Part α} : o = some a ↔ a ∈ o :=
  ⟨fun e => e.symm ▸ mem_some _, fun ⟨h, e⟩ => e ▸ ext' (iff_true_intro h) fun _ _ => rfl⟩
#align part.eq_some_iff Part.eq_some_iff

theorem eq_none_iff {o : Part α} : o = none ↔ ∀ a, a ∉ o :=
  ⟨fun e => e.symm ▸ not_mem_none, fun h => ext (by simpa)⟩
#align part.eq_none_iff Part.eq_none_iff

theorem eq_none_iff' {o : Part α} : o = none ↔ ¬o.Dom :=
  ⟨fun e => e.symm ▸ id, fun h => eq_none_iff.2 fun _ h' => h h'.fst⟩
#align part.eq_none_iff' Part.eq_none_iff'

@[simp]
theorem not_none_dom : ¬(none : Part α).Dom :=
  id
#align part.not_none_dom Part.not_none_dom

@[simp]
theorem some_ne_none (x : α) : some x ≠ none := by
  intro h
  exact true_ne_false (congr_arg Dom h)
#align part.some_ne_none Part.some_ne_none

@[simp]
theorem none_ne_some (x : α) : none ≠ some x :=
  (some_ne_none x).symm
#align part.none_ne_some Part.none_ne_some

theorem ne_none_iff {o : Part α} : o ≠ none ↔ ∃ x, o = some x := by
  constructor
  · rw [Ne, eq_none_iff', not_not]
    exact fun h => ⟨o.get h, eq_some_iff.2 (get_mem h)⟩
  · rintro ⟨x, rfl⟩
    apply some_ne_none
#align part.ne_none_iff Part.ne_none_iff

theorem eq_none_or_eq_some (o : Part α) : o = none ∨ ∃ x, o = some x :=
  or_iff_not_imp_left.2 ne_none_iff.1
#align part.eq_none_or_eq_some Part.eq_none_or_eq_some

theorem some_injective : Injective (@Part.some α) := fun _ _ h =>
  congr_fun (eq_of_heq (Part.mk.inj h).2) trivial
#align part.some_injective Part.some_injective

@[simp]
theorem some_inj {a b : α} : Part.some a = some b ↔ a = b :=
  some_injective.eq_iff
#align part.some_inj Part.some_inj

@[simp]
theorem some_get {a : Part α} (ha : a.Dom) : Part.some (Part.get a ha) = a :=
  Eq.symm (eq_some_iff.2 ⟨ha, rfl⟩)
#align part.some_get Part.some_get

theorem get_eq_iff_eq_some {a : Part α} {ha : a.Dom} {b : α} : a.get ha = b ↔ a = some b :=
  ⟨fun h => by simp [h.symm], fun h => by simp [h]⟩
#align part.get_eq_iff_eq_some Part.get_eq_iff_eq_some

theorem get_eq_get_of_eq (a : Part α) (ha : a.Dom) {b : Part α} (h : a = b) :
    a.get ha = b.get (h ▸ ha) := by
  congr
#align part.get_eq_get_of_eq Part.get_eq_get_of_eq

theorem get_eq_iff_mem {o : Part α} {a : α} (h : o.Dom) : o.get h = a ↔ a ∈ o :=
  ⟨fun H => ⟨h, H⟩, fun ⟨_, H⟩ => H⟩
#align part.get_eq_iff_mem Part.get_eq_iff_mem

theorem eq_get_iff_mem {o : Part α} {a : α} (h : o.Dom) : a = o.get h ↔ a ∈ o :=
  eq_comm.trans (get_eq_iff_mem h)
#align part.eq_get_iff_mem Part.eq_get_iff_mem

@[simp]
theorem none_toOption [Decidable (@none α).Dom] : (none : Part α).toOption = Option.none :=
  dif_neg id
#align part.none_to_option Part.none_toOption

@[simp]
theorem some_toOption (a : α) [Decidable (some a).Dom] : (some a).toOption = Option.some a :=
  dif_pos trivial
#align part.some_to_option Part.some_toOption

instance noneDecidable : Decidable (@none α).Dom :=
  instDecidableFalse
#align part.none_decidable Part.noneDecidable

instance someDecidable (a : α) : Decidable (some a).Dom :=
  instDecidableTrue
#align part.some_decidable Part.someDecidable

/-- Retrieves the value of `a : Part α` if it exists, and return the provided default value
otherwise. -/
def getOrElse (a : Part α) [Decidable a.Dom] (d : α) :=
  if ha : a.Dom then a.get ha else d
#align part.get_or_else Part.getOrElse

theorem getOrElse_of_dom (a : Part α) (h : a.Dom) [Decidable a.Dom] (d : α) :
    getOrElse a d = a.get h :=
  dif_pos h
#align part.get_or_else_of_dom Part.getOrElse_of_dom

theorem getOrElse_of_not_dom (a : Part α) (h : ¬a.Dom) [Decidable a.Dom] (d : α) :
    getOrElse a d = d :=
  dif_neg h
#align part.get_or_else_of_not_dom Part.getOrElse_of_not_dom

@[simp]
theorem getOrElse_none (d : α) [Decidable (none : Part α).Dom] : getOrElse none d = d :=
  none.getOrElse_of_not_dom not_none_dom d
#align part.get_or_else_none Part.getOrElse_none

@[simp]
theorem getOrElse_some (a : α) (d : α) [Decidable (some a).Dom] : getOrElse (some a) d = a :=
  (some a).getOrElse_of_dom (some_dom a) d
#align part.get_or_else_some Part.getOrElse_some

-- Porting note: removed `simp`
theorem mem_toOption {o : Part α} [Decidable o.Dom] {a : α} : a ∈ toOption o ↔ a ∈ o := by
  unfold toOption
  by_cases h : o.Dom <;> simp [h]
  · exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  · exact mt Exists.fst h
#align part.mem_to_option Part.mem_toOption

-- Porting note (#10756): new theorem, like `mem_toOption` but with LHS in `simp` normal form
@[simp]
theorem toOption_eq_some_iff {o : Part α} [Decidable o.Dom] {a : α} :
    toOption o = Option.some a ↔ a ∈ o := by
  rw [← Option.mem_def, mem_toOption]

protected theorem Dom.toOption {o : Part α} [Decidable o.Dom] (h : o.Dom) : o.toOption = o.get h :=
  dif_pos h
#align part.dom.to_option Part.Dom.toOption

theorem toOption_eq_none_iff {a : Part α} [Decidable a.Dom] : a.toOption = Option.none ↔ ¬a.Dom :=
  Ne.dite_eq_right_iff fun _ => Option.some_ne_none _
#align part.to_option_eq_none_iff Part.toOption_eq_none_iff

/- Porting TODO: Removed `simp`. Maybe add `@[simp]` later if `@[simp]` is taken off definition of
`Option.elim` -/
theorem elim_toOption {α β : Type*} (a : Part α) [Decidable a.Dom] (b : β) (f : α → β) :
    a.toOption.elim b f = if h : a.Dom then f (a.get h) else b := by
  split_ifs with h
  · rw [h.toOption]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    rfl
#align part.elim_to_option Part.elim_toOption

/-- Converts an `Option α` into a `Part α`. -/
@[coe]
def ofOption : Option α → Part α
  | Option.none => none
  | Option.some a => some a
#align part.of_option Part.ofOption

@[simp]
theorem mem_ofOption {a : α} : ∀ {o : Option α}, a ∈ ofOption o ↔ a ∈ o
  | Option.none => ⟨fun h => h.fst.elim, fun h => Option.noConfusion h⟩
  | Option.some _ => ⟨fun h => congr_arg Option.some h.snd, fun h => ⟨trivial, Option.some.inj h⟩⟩
#align part.mem_of_option Part.mem_ofOption

@[simp]
theorem ofOption_dom {α} : ∀ o : Option α, (ofOption o).Dom ↔ o.isSome
  | Option.none => by simp [ofOption, none]
  | Option.some a => by simp [ofOption]
#align part.of_option_dom Part.ofOption_dom

theorem ofOption_eq_get {α} (o : Option α) : ofOption o = ⟨_, @Option.get _ o⟩ :=
  Part.ext' (ofOption_dom o) fun h₁ h₂ => by
    cases o
    · simp at h₂
    · rfl
#align part.of_option_eq_get Part.ofOption_eq_get

instance : Coe (Option α) (Part α) :=
  ⟨ofOption⟩

theorem mem_coe {a : α} {o : Option α} : a ∈ (o : Part α) ↔ a ∈ o :=
  mem_ofOption
#align part.mem_coe Part.mem_coe

@[simp]
theorem coe_none : (@Option.none α : Part α) = none :=
  rfl
#align part.coe_none Part.coe_none

@[simp]
theorem coe_some (a : α) : (Option.some a : Part α) = some a :=
  rfl
#align part.coe_some Part.coe_some

@[elab_as_elim]
protected theorem induction_on {P : Part α → Prop} (a : Part α) (hnone : P none)
    (hsome : ∀ a : α, P (some a)) : P a :=
  (Classical.em a.Dom).elim (fun h => Part.some_get h ▸ hsome _) fun h =>
    (eq_none_iff'.2 h).symm ▸ hnone
#align part.induction_on Part.induction_on

instance ofOptionDecidable : ∀ o : Option α, Decidable (ofOption o).Dom
  | Option.none => Part.noneDecidable
  | Option.some a => Part.someDecidable a
#align part.of_option_decidable Part.ofOptionDecidable

@[simp]
theorem to_ofOption (o : Option α) : toOption (ofOption o) = o := by cases o <;> rfl
#align part.to_of_option Part.to_ofOption

@[simp]
theorem of_toOption (o : Part α) [Decidable o.Dom] : ofOption (toOption o) = o :=
  ext fun _ => mem_ofOption.trans mem_toOption
#align part.of_to_option Part.of_toOption

/-- `Part α` is (classically) equivalent to `Option α`. -/
noncomputable def equivOption : Part α ≃ Option α :=
  haveI := Classical.dec
  ⟨fun o => toOption o, ofOption, fun o => of_toOption o, fun o =>
    Eq.trans (by dsimp; congr) (to_ofOption o)⟩
#align part.equiv_option Part.equivOption

/-- We give `Part α` the order where everything is greater than `none`. -/
instance : PartialOrder (Part
        α) where
  le x y := ∀ i, i ∈ x → i ∈ y
  le_refl x y := id
  le_trans x y z f g i := g _ ∘ f _
  le_antisymm x y f g := Part.ext fun z => ⟨f _, g _⟩

instance : OrderBot (Part α) where
  bot := none
  bot_le := by rintro x _ ⟨⟨_⟩, _⟩

theorem le_total_of_le_of_le {x y : Part α} (z : Part α) (hx : x ≤ z) (hy : y ≤ z) :
    x ≤ y ∨ y ≤ x := by
  rcases Part.eq_none_or_eq_some x with (h | ⟨b, h₀⟩)
  · rw [h]
    left
    apply OrderBot.bot_le _
  right; intro b' h₁
  rw [Part.eq_some_iff] at h₀
  have hx := hx _ h₀; have hy := hy _ h₁
  have hx := Part.mem_unique hx hy; subst hx
  exact h₀
#align part.le_total_of_le_of_le Part.le_total_of_le_of_le

/-- `assert p f` is a bind-like operation which appends an additional condition
  `p` to the domain and uses `f` to produce the value. -/
def assert (p : Prop) (f : p → Part α) : Part α :=
  ⟨∃ h : p, (f h).Dom, fun ha => (f ha.fst).get ha.snd⟩
#align part.assert Part.assert

/-- The bind operation has value `g (f.get)`, and is defined when all the
  parts are defined. -/
protected def bind (f : Part α) (g : α → Part β) : Part β :=
  assert (Dom f) fun b => g (f.get b)
#align part.bind Part.bind

/-- The map operation for `Part` just maps the value and maintains the same domain. -/
@[simps]
def map (f : α → β) (o : Part α) : Part β :=
  ⟨o.Dom, f ∘ o.get⟩
#align part.map Part.map
#align part.map_dom Part.map_Dom
#align part.map_get Part.map_get

theorem mem_map (f : α → β) {o : Part α} : ∀ {a}, a ∈ o → f a ∈ map f o
  | _, ⟨_, rfl⟩ => ⟨_, rfl⟩
#align part.mem_map Part.mem_map

@[simp]
theorem mem_map_iff (f : α → β) {o : Part α} {b} : b ∈ map f o ↔ ∃ a ∈ o, f a = b :=
  ⟨fun hb => match b, hb with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩, rfl⟩,
    fun ⟨_, h₁, h₂⟩ => h₂ ▸ mem_map f h₁⟩
#align part.mem_map_iff Part.mem_map_iff

@[simp]
theorem map_none (f : α → β) : map f none = none :=
  eq_none_iff.2 fun a => by simp
#align part.map_none Part.map_none

@[simp]
theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) :=
  eq_some_iff.2 <| mem_map f <| mem_some _
#align part.map_some Part.map_some

theorem mem_assert {p : Prop} {f : p → Part α} : ∀ {a} (h : p), a ∈ f h → a ∈ assert p f
  | _, x, ⟨h, rfl⟩ => ⟨⟨x, h⟩, rfl⟩
#align part.mem_assert Part.mem_assert

@[simp]
theorem mem_assert_iff {p : Prop} {f : p → Part α} {a} : a ∈ assert p f ↔ ∃ h : p, a ∈ f h :=
  ⟨fun ha => match a, ha with
    | _, ⟨_, rfl⟩ => ⟨_, ⟨_, rfl⟩⟩,
    fun ⟨_, h⟩ => mem_assert _ h⟩
#align part.mem_assert_iff Part.mem_assert_iff

theorem assert_pos {p : Prop} {f : p → Part α} (h : p) : assert p f = f h := by
  dsimp [assert]
  cases h' : f h
  simp only [h', mk.injEq, h, exists_prop_of_true, true_and]
  apply Function.hfunext
  · simp only [h, h', exists_prop_of_true]
  · aesop
#align part.assert_pos Part.assert_pos

theorem assert_neg {p : Prop} {f : p → Part α} (h : ¬p) : assert p f = none := by
  dsimp [assert, none]; congr
  · simp only [h, not_false_iff, exists_prop_of_false]
  · apply Function.hfunext
    · simp only [h, not_false_iff, exists_prop_of_false]
    simp at *
#align part.assert_neg Part.assert_neg

theorem mem_bind {f : Part α} {g : α → Part β} : ∀ {a b}, a ∈ f → b ∈ g a → b ∈ f.bind g
  | _, _, ⟨h, rfl⟩, ⟨h₂, rfl⟩ => ⟨⟨h, h₂⟩, rfl⟩
#align part.mem_bind Part.mem_bind

@[simp]
theorem mem_bind_iff {f : Part α} {g : α → Part β} {b} : b ∈ f.bind g ↔ ∃ a ∈ f, b ∈ g a :=
  ⟨fun hb => match b, hb with
    | _, ⟨⟨_, _⟩, rfl⟩ => ⟨_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩,
    fun ⟨_, h₁, h₂⟩ => mem_bind h₁ h₂⟩
#align part.mem_bind_iff Part.mem_bind_iff

protected theorem Dom.bind {o : Part α} (h : o.Dom) (f : α → Part β) : o.bind f = f (o.get h) := by
  ext b
  simp only [Part.mem_bind_iff, exists_prop]
  refine ⟨?_, fun hb => ⟨o.get h, Part.get_mem _, hb⟩⟩
  rintro ⟨a, ha, hb⟩
  rwa [Part.get_eq_of_mem ha]
#align part.dom.bind Part.Dom.bind

theorem Dom.of_bind {f : α → Part β} {a : Part α} (h : (a.bind f).Dom) : a.Dom :=
  h.1
#align part.dom.of_bind Part.Dom.of_bind

@[simp]
theorem bind_none (f : α → Part β) : none.bind f = none :=
  eq_none_iff.2 fun a => by simp
#align part.bind_none Part.bind_none

@[simp]
theorem bind_some (a : α) (f : α → Part β) : (some a).bind f = f a :=
  ext <| by simp
#align part.bind_some Part.bind_some

theorem bind_of_mem {o : Part α} {a : α} (h : a ∈ o) (f : α → Part β) : o.bind f = f a := by
  rw [eq_some_iff.2 h, bind_some]
#align part.bind_of_mem Part.bind_of_mem

theorem bind_some_eq_map (f : α → β) (x : Part α) : x.bind (some ∘ f) = map f x :=
  ext <| by simp [eq_comm]
#align part.bind_some_eq_map Part.bind_some_eq_map

theorem bind_toOption (f : α → Part β) (o : Part α) [Decidable o.Dom] [∀ a, Decidable (f a).Dom]
    [Decidable (o.bind f).Dom] :
    (o.bind f).toOption = o.toOption.elim Option.none fun a => (f a).toOption := by
  by_cases h : o.Dom
  · simp_rw [h.toOption, h.bind]
    rfl
  · rw [Part.toOption_eq_none_iff.2 h]
    exact Part.toOption_eq_none_iff.2 fun ho => h ho.of_bind
#align part.bind_to_option Part.bind_toOption

theorem bind_assoc {γ} (f : Part α) (g : α → Part β) (k : β → Part γ) :
    (f.bind g).bind k = f.bind fun x => (g x).bind k :=
  ext fun a => by
    simp only [mem_bind_iff]
    exact ⟨fun ⟨_, ⟨_, h₁, h₂⟩, h₃⟩ => ⟨_, h₁, _, h₂, h₃⟩,
           fun ⟨_, h₁, _, h₂, h₃⟩ => ⟨_, ⟨_, h₁, h₂⟩, h₃⟩⟩
#align part.bind_assoc Part.bind_assoc

@[simp]
theorem bind_map {γ} (f : α → β) (x) (g : β → Part γ) :
    (map f x).bind g = x.bind fun y => g (f y) := by rw [← bind_some_eq_map, bind_assoc]; simp
#align part.bind_map Part.bind_map

@[simp]
theorem map_bind {γ} (f : α → Part β) (x : Part α) (g : β → γ) :
    map g (x.bind f) = x.bind fun y => map g (f y) := by
  rw [← bind_some_eq_map, bind_assoc]; simp [bind_some_eq_map]
#align part.map_bind Part.map_bind

theorem map_map (g : β → γ) (f : α → β) (o : Part α) : map g (map f o) = map (g ∘ f) o := by
  erw [← bind_some_eq_map, bind_map, bind_some_eq_map]
#align part.map_map Part.map_map

instance : Monad Part where
  pure := @some
  map := @map
  bind := @Part.bind

instance : LawfulMonad
      Part where
  bind_pure_comp := @bind_some_eq_map
  id_map f := by cases f; rfl
  pure_bind := @bind_some
  bind_assoc := @bind_assoc
  map_const := by simp [Functor.mapConst, Functor.map]
  --Porting TODO : In Lean3 these were automatic by a tactic
  seqLeft_eq x y := ext'
    (by simp [SeqLeft.seqLeft, Part.bind, assert, Seq.seq, const, (· <$> ·), and_comm])
    (fun _ _ => rfl)
  seqRight_eq x y := ext'
    (by simp [SeqRight.seqRight, Part.bind, assert, Seq.seq, const, (· <$> ·), and_comm])
    (fun _ _ => rfl)
  pure_seq x y := ext'
    (by simp [Seq.seq, Part.bind, assert, (· <$> ·), pure])
    (fun _ _ => rfl)
  bind_map x y := ext'
    (by simp [(· >>= ·), Part.bind, assert, Seq.seq, get, (· <$> ·)] )
    (fun _ _ => rfl)

theorem map_id' {f : α → α} (H : ∀ x : α, f x = x) (o) : map f o = o := by
  rw [show f = id from funext H]; exact id_map o
#align part.map_id' Part.map_id'

@[simp]
theorem bind_some_right (x : Part α) : x.bind some = x := by
  erw [bind_some_eq_map]; simp [map_id']
#align part.bind_some_right Part.bind_some_right

@[simp]
theorem pure_eq_some (a : α) : pure a = some a :=
  rfl
#align part.pure_eq_some Part.pure_eq_some

@[simp]
theorem ret_eq_some (a : α) : (return a : Part α) = some a :=
  rfl
#align part.ret_eq_some Part.ret_eq_some

@[simp]
theorem map_eq_map {α β} (f : α → β) (o : Part α) : f <$> o = map f o :=
  rfl
#align part.map_eq_map Part.map_eq_map

@[simp]
theorem bind_eq_bind {α β} (f : Part α) (g : α → Part β) : f >>= g = f.bind g :=
  rfl
#align part.bind_eq_bind Part.bind_eq_bind

theorem bind_le {α} (x : Part α) (f : α → Part β) (y : Part β) :
    x >>= f ≤ y ↔ ∀ a, a ∈ x → f a ≤ y := by
  constructor <;> intro h
  · intro a h' b
    have h := h b
    simp only [and_imp, exists_prop, bind_eq_bind, mem_bind_iff, exists_imp] at h
    apply h _ h'
  · intro b h'
    simp only [exists_prop, bind_eq_bind, mem_bind_iff] at h'
    rcases h' with ⟨a, h₀, h₁⟩
    apply h _ h₀ _ h₁
#align part.bind_le Part.bind_le

-- Porting note: No MonadFail in Lean4 yet
-- instance : MonadFail Part :=
--   { Part.monad with fail := fun _ _ => none }

/-- `restrict p o h` replaces the domain of `o` with `p`, and is well defined when
  `p` implies `o` is defined. -/
def restrict (p : Prop) (o : Part α) (H : p → o.Dom) : Part α :=
  ⟨p, fun h => o.get (H h)⟩
#align part.restrict Part.restrict

@[simp]
theorem mem_restrict (p : Prop) (o : Part α) (h : p → o.Dom) (a : α) :
    a ∈ restrict p o h ↔ p ∧ a ∈ o := by
  dsimp [restrict, mem_eq]; constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨h₀, ⟨_, h₁⟩⟩
  rintro ⟨h₀, _, h₂⟩; exact ⟨h₀, h₂⟩
#align part.mem_restrict Part.mem_restrict

/-- `unwrap o` gets the value at `o`, ignoring the condition. This function is unsound. -/
unsafe def unwrap (o : Part α) : α :=
  o.get lcProof
#align part.unwrap Part.unwrap

theorem assert_defined {p : Prop} {f : p → Part α} : ∀ h : p, (f h).Dom → (assert p f).Dom :=
  Exists.intro
#align part.assert_defined Part.assert_defined

theorem bind_defined {f : Part α} {g : α → Part β} :
    ∀ h : f.Dom, (g (f.get h)).Dom → (f.bind g).Dom :=
  assert_defined
#align part.bind_defined Part.bind_defined

@[simp]
theorem bind_dom {f : Part α} {g : α → Part β} : (f.bind g).Dom ↔ ∃ h : f.Dom, (g (f.get h)).Dom :=
  Iff.rfl
#align part.bind_dom Part.bind_dom

section Instances

/-!
We define several instances for constants and operations on `Part α` inherited from `α`.

This section could be moved to a separate file to avoid the import of `Mathlib.Algebra.Group.Defs`.
-/

@[to_additive]
instance [One α] : One (Part α) where one := pure 1

@[to_additive]
instance [Mul α] : Mul (Part α) where mul a b := (· * ·) <$> a <*> b

@[to_additive]
instance [Inv α] : Inv (Part α) where inv := map Inv.inv

@[to_additive]
instance [Div α] : Div (Part α) where div a b := (· / ·) <$> a <*> b

instance [Mod α] : Mod (Part α) where mod a b := (· % ·) <$> a <*> b

instance [Append α] : Append (Part α) where append a b := (· ++ ·) <$> a <*> b

instance [Inter α] : Inter (Part α) where inter a b := (· ∩ ·) <$> a <*> b

instance [Union α] : Union (Part α) where union a b := (· ∪ ·) <$> a <*> b

instance [SDiff α] : SDiff (Part α) where sdiff a b := (· \ ·) <$> a <*> b

section
-- Porting note (#10756): new theorems to unfold definitions
theorem mul_def [Mul α] (a b : Part α) : a * b = bind a fun y ↦ map (y * ·) b := rfl
theorem one_def [One α] : (1 : Part α) = some 1 := rfl
theorem inv_def [Inv α] (a : Part α) : a⁻¹ = Part.map (· ⁻¹) a := rfl
theorem div_def [Div α] (a b : Part α) : a / b = bind a fun y => map (y / ·) b := rfl
theorem mod_def [Mod α] (a b : Part α) : a % b = bind a fun y => map (y % ·) b := rfl
theorem append_def [Append α] (a b : Part α) : a ++ b = bind a fun y => map (y ++ ·) b := rfl
theorem inter_def [Inter α] (a b : Part α) : a ∩ b = bind a fun y => map (y ∩ ·) b := rfl
theorem union_def [Union α] (a b : Part α) : a ∪ b = bind a fun y => map (y ∪ ·) b := rfl
theorem sdiff_def [SDiff α] (a b : Part α) : a \ b = bind a fun y => map (y \ ·) b := rfl

end

@[to_additive]
theorem one_mem_one [One α] : (1 : α) ∈ (1 : Part α) :=
  ⟨trivial, rfl⟩
#align part.one_mem_one Part.one_mem_one
#align part.zero_mem_zero Part.zero_mem_zero

@[to_additive]
theorem mul_mem_mul [Mul α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma * mb ∈ a * b := ⟨⟨ha.1, hb.1⟩, by simp only [← ha.2, ← hb.2]; rfl⟩
#align part.mul_mem_mul Part.mul_mem_mul
#align part.add_mem_add Part.add_mem_add

@[to_additive]
theorem left_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : a.Dom := hab.1
#align part.left_dom_of_mul_dom Part.left_dom_of_mul_dom
#align part.left_dom_of_add_dom Part.left_dom_of_add_dom

@[to_additive]
theorem right_dom_of_mul_dom [Mul α] {a b : Part α} (hab : Dom (a * b)) : b.Dom := hab.2
#align part.right_dom_of_mul_dom Part.right_dom_of_mul_dom
#align part.right_dom_of_add_dom Part.right_dom_of_add_dom

@[to_additive (attr := simp)]
theorem mul_get_eq [Mul α] (a b : Part α) (hab : Dom (a * b)) :
    (a * b).get hab = a.get (left_dom_of_mul_dom hab) * b.get (right_dom_of_mul_dom hab) := rfl
#align part.mul_get_eq Part.mul_get_eq
#align part.add_get_eq Part.add_get_eq

@[to_additive]
theorem some_mul_some [Mul α] (a b : α) : some a * some b = some (a * b) := by simp [mul_def]
#align part.some_mul_some Part.some_mul_some
#align part.some_add_some Part.some_add_some

@[to_additive]
theorem inv_mem_inv [Inv α] (a : Part α) (ma : α) (ha : ma ∈ a) : ma⁻¹ ∈ a⁻¹ := by
  simp [inv_def]; aesop
#align part.inv_mem_inv Part.inv_mem_inv
#align part.neg_mem_neg Part.neg_mem_neg

@[to_additive]
theorem inv_some [Inv α] (a : α) : (some a)⁻¹ = some a⁻¹ :=
  rfl
#align part.inv_some Part.inv_some
#align part.neg_some Part.neg_some

@[to_additive]
theorem div_mem_div [Div α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma / mb ∈ a / b := by simp [div_def]; aesop
#align part.div_mem_div Part.div_mem_div
#align part.sub_mem_sub Part.sub_mem_sub

@[to_additive]
theorem left_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : a.Dom := hab.1
#align part.left_dom_of_div_dom Part.left_dom_of_div_dom
#align part.left_dom_of_sub_dom Part.left_dom_of_sub_dom

@[to_additive]
theorem right_dom_of_div_dom [Div α] {a b : Part α} (hab : Dom (a / b)) : b.Dom := hab.2
#align part.right_dom_of_div_dom Part.right_dom_of_div_dom
#align part.right_dom_of_sub_dom Part.right_dom_of_sub_dom

@[to_additive (attr := simp)]
theorem div_get_eq [Div α] (a b : Part α) (hab : Dom (a / b)) :
    (a / b).get hab = a.get (left_dom_of_div_dom hab) / b.get (right_dom_of_div_dom hab) := by
  simp [div_def]; aesop
#align part.div_get_eq Part.div_get_eq
#align part.sub_get_eq Part.sub_get_eq

@[to_additive]
theorem some_div_some [Div α] (a b : α) : some a / some b = some (a / b) := by simp [div_def]
#align part.some_div_some Part.some_div_some
#align part.some_sub_some Part.some_sub_some

theorem mod_mem_mod [Mod α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma % mb ∈ a % b := by simp [mod_def]; aesop
#align part.mod_mem_mod Part.mod_mem_mod

theorem left_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : a.Dom := hab.1
#align part.left_dom_of_mod_dom Part.left_dom_of_mod_dom

theorem right_dom_of_mod_dom [Mod α] {a b : Part α} (hab : Dom (a % b)) : b.Dom := hab.2
#align part.right_dom_of_mod_dom Part.right_dom_of_mod_dom

@[simp]
theorem mod_get_eq [Mod α] (a b : Part α) (hab : Dom (a % b)) :
    (a % b).get hab = a.get (left_dom_of_mod_dom hab) % b.get (right_dom_of_mod_dom hab) := by
  simp [mod_def]; aesop
#align part.mod_get_eq Part.mod_get_eq

theorem some_mod_some [Mod α] (a b : α) : some a % some b = some (a % b) := by simp [mod_def]
#align part.some_mod_some Part.some_mod_some

theorem append_mem_append [Append α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma ++ mb ∈ a ++ b := by simp [append_def]; aesop
#align part.append_mem_append Part.append_mem_append

theorem left_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : a.Dom := hab.1
#align part.left_dom_of_append_dom Part.left_dom_of_append_dom

theorem right_dom_of_append_dom [Append α] {a b : Part α} (hab : Dom (a ++ b)) : b.Dom := hab.2
#align part.right_dom_of_append_dom Part.right_dom_of_append_dom

@[simp]
theorem append_get_eq [Append α] (a b : Part α) (hab : Dom (a ++ b)) : (a ++ b).get hab =
    a.get (left_dom_of_append_dom hab) ++ b.get (right_dom_of_append_dom hab) := by
  simp [append_def]; aesop
#align part.append_get_eq Part.append_get_eq

theorem some_append_some [Append α] (a b : α) : some a ++ some b = some (a ++ b) := by
  simp [append_def]
#align part.some_append_some Part.some_append_some

theorem inter_mem_inter [Inter α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma ∩ mb ∈ a ∩ b := by simp [inter_def]; aesop
#align part.inter_mem_inter Part.inter_mem_inter

theorem left_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a ∩ b)) : a.Dom := hab.1
#align part.left_dom_of_inter_dom Part.left_dom_of_inter_dom

theorem right_dom_of_inter_dom [Inter α] {a b : Part α} (hab : Dom (a ∩ b)) : b.Dom := hab.2
#align part.right_dom_of_inter_dom Part.right_dom_of_inter_dom

@[simp]
theorem inter_get_eq [Inter α] (a b : Part α) (hab : Dom (a ∩ b)) :
    (a ∩ b).get hab = a.get (left_dom_of_inter_dom hab) ∩ b.get (right_dom_of_inter_dom hab) := by
  simp [inter_def]; aesop
#align part.inter_get_eq Part.inter_get_eq

theorem some_inter_some [Inter α] (a b : α) : some a ∩ some b = some (a ∩ b) := by
  simp [inter_def]
#align part.some_inter_some Part.some_inter_some

theorem union_mem_union [Union α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma ∪ mb ∈ a ∪ b := by simp [union_def]; aesop
#align part.union_mem_union Part.union_mem_union

theorem left_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a ∪ b)) : a.Dom := hab.1
#align part.left_dom_of_union_dom Part.left_dom_of_union_dom

theorem right_dom_of_union_dom [Union α] {a b : Part α} (hab : Dom (a ∪ b)) : b.Dom := hab.2
#align part.right_dom_of_union_dom Part.right_dom_of_union_dom

@[simp]
theorem union_get_eq [Union α] (a b : Part α) (hab : Dom (a ∪ b)) :
    (a ∪ b).get hab = a.get (left_dom_of_union_dom hab) ∪ b.get (right_dom_of_union_dom hab) := by
  simp [union_def]; aesop
#align part.union_get_eq Part.union_get_eq

theorem some_union_some [Union α] (a b : α) : some a ∪ some b = some (a ∪ b) := by simp [union_def]
#align part.some_union_some Part.some_union_some

theorem sdiff_mem_sdiff [SDiff α] (a b : Part α) (ma mb : α) (ha : ma ∈ a) (hb : mb ∈ b) :
    ma \ mb ∈ a \ b := by simp [sdiff_def]; aesop
#align part.sdiff_mem_sdiff Part.sdiff_mem_sdiff

theorem left_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : a.Dom := hab.1
#align part.left_dom_of_sdiff_dom Part.left_dom_of_sdiff_dom

theorem right_dom_of_sdiff_dom [SDiff α] {a b : Part α} (hab : Dom (a \ b)) : b.Dom := hab.2
#align part.right_dom_of_sdiff_dom Part.right_dom_of_sdiff_dom

@[simp]
theorem sdiff_get_eq [SDiff α] (a b : Part α) (hab : Dom (a \ b)) :
    (a \ b).get hab = a.get (left_dom_of_sdiff_dom hab) \ b.get (right_dom_of_sdiff_dom hab) := by
  simp [sdiff_def]; aesop
#align part.sdiff_get_eq Part.sdiff_get_eq

theorem some_sdiff_some [SDiff α] (a b : α) : some a \ some b = some (a \ b) := by simp [sdiff_def]
#align part.some_sdiff_some Part.some_sdiff_some

end Instances

end Part
