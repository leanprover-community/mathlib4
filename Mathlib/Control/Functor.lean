/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Basic
import Mathlib.Init.Set
import Mathlib.Tactic.Basic
import Std.Tactic.Lint

#align_import control.functor from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Functors

This module provides additional lemmas, definitions, and instances for `Functor`s.

## Main definitions

* `Functor.Const α` is the functor that sends all types to `α`.
* `Functor.AddConst α` is `Functor.Const α` but for when `α` has an additive structure.
* `Functor.Comp F G` for functors `F` and `G` is the functor composition of `F` and `G`.
* `Liftp` and `Liftr` respectively lift predicates and relations on a type `α`
  to `F α`.  Terms of `F α` are considered to, in some sense, contain values of type `α`.

## Tags

functor, applicative
-/

universe u v w

section Functor

variable {F : Type u → Type v}

variable {α β γ : Type u}

variable [Functor F] [LawfulFunctor F]

theorem Functor.map_id : (· <$> ·) id = (id : F α → F α) := funext id_map
#align functor.map_id Functor.map_id

theorem Functor.map_comp_map (f : α → β) (g : β → γ) :
    ((· <$> ·) g ∘ (· <$> ·) f : F α → F γ) = (· <$> ·) (g ∘ f) :=
  funext <| fun _ => (comp_map _ _ _).symm
  -- porting note: was `apply funext <;> intro <;> rw [comp_map]` but `rw` failed?
#align functor.map_comp_map Functor.map_comp_map

theorem Functor.ext {F} :
    ∀ {F1 : Functor F} {F2 : Functor F} [@LawfulFunctor F F1] [@LawfulFunctor F F2],
    (∀ (α β) (f : α → β) (x : F α), @Functor.map _ F1 _ _ f x = @Functor.map _ F2 _ _ f x) →
    F1 = F2
  | ⟨m, mc⟩, ⟨m', mc'⟩, H1, H2, H => by
    cases show @m = @m' by funext α β f x; apply H
    -- ⊢ { map := m, mapConst := mc } = { map := m, mapConst := mc' }
    congr
    -- ⊢ mc = mc'
    funext α β
    -- ⊢ mc = mc'
    have E1 := @map_const _ ⟨@m, @mc⟩ H1
    -- ⊢ mc = mc'
    have E2 := @map_const _ ⟨@m, @mc'⟩ H2
    -- ⊢ mc = mc'
    exact E1.trans E2.symm
    -- 🎉 no goals
#align functor.ext Functor.ext

end Functor

/-- Introduce `id` as a quasi-functor. (Note that where a lawful `Monad` or
`Applicative` or `Functor` is needed, `Id` is the correct definition). -/
def id.mk {α : Sort u} : α → id α :=
  id
#align id.mk id.mk

namespace Functor

/-- `Const α` is the constant functor, mapping every type to `α`. When
`α` has a monoid structure, `Const α` has an `Applicative` instance.
(If `α` has an additive monoid structure, see `Functor.AddConst`.) -/
@[nolint unusedArguments]
def Const (α : Type*) (_β : Type*) :=
  α
#align functor.const Functor.Const

/-- `Const.mk` is the canonical map `α → Const α β` (the identity), and
it can be used as a pattern to extract this value. -/
@[match_pattern]
def Const.mk {α β} (x : α) : Const α β :=
  x
#align functor.const.mk Functor.Const.mk

/-- `Const.mk'` is `Const.mk` but specialized to map `α` to
`Const α PUnit`, where `PUnit` is the terminal object in `Type*`. -/
def Const.mk' {α} (x : α) : Const α PUnit :=
  x
#align functor.const.mk' Functor.Const.mk'

/-- Extract the element of `α` from the `Const` functor. -/
def Const.run {α β} (x : Const α β) : α :=
  x
#align functor.const.run Functor.Const.run

namespace Const

protected theorem ext {α β} {x y : Const α β} (h : x.run = y.run) : x = y :=
  h
#align functor.const.ext Functor.Const.ext

/-- The map operation of the `Const γ` functor. -/
@[nolint unusedArguments]
protected def map {γ α β} (_f : α → β) (x : Const γ β) : Const γ α :=
  x
#align functor.const.map Functor.Const.map

instance functor {γ} : Functor (Const γ) where map := @Const.map γ

instance lawfulFunctor {γ} : LawfulFunctor (Const γ) := by constructor <;> intros <;> rfl
                                                                           -- ⊢ mapConst = map ∘ Function.const β✝
                                                                           -- ⊢ id <$> x✝ = x✝
                                                                           -- ⊢ (h✝ ∘ g✝) <$> x✝ = h✝ <$> g✝ <$> x✝
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals

instance {α β} [Inhabited α] : Inhabited (Const α β) :=
  ⟨(default : α)⟩

end Const

/-- `AddConst α` is a synonym for constant functor `Const α`, mapping
every type to `α`. When `α` has an additive monoid structure,
`AddConst α` has an `Applicative` instance. (If `α` has a
multiplicative monoid structure, see `Functor.Const`.) -/
def AddConst (α : Type*) :=
  Const α
#align functor.add_const Functor.AddConst

/-- `AddConst.mk` is the canonical map `α → AddConst α β`, which is the identity,
where `AddConst α β = Const α β`. It can be used as a pattern to extract this value. -/
@[match_pattern]
def AddConst.mk {α β} (x : α) : AddConst α β :=
  x
#align functor.add_const.mk Functor.AddConst.mk

/-- Extract the element of `α` from the constant functor. -/
def AddConst.run {α β} : AddConst α β → α :=
  id
#align functor.add_const.run Functor.AddConst.run

instance AddConst.functor {γ} : Functor (AddConst γ) :=
  @Const.functor γ
#align functor.add_const.functor Functor.AddConst.functor

instance AddConst.lawfulFunctor {γ} : LawfulFunctor (AddConst γ) :=
  @Const.lawfulFunctor γ
#align functor.add_const.is_lawful_functor Functor.AddConst.lawfulFunctor

instance {α β} [Inhabited α] : Inhabited (AddConst α β) :=
  ⟨(default : α)⟩

/-- `Functor.Comp` is a wrapper around `Function.Comp` for types.
    It prevents Lean's type class resolution mechanism from trying
    a `Functor (Comp F id)` when `Functor F` would do. -/
def Comp (F : Type u → Type w) (G : Type v → Type u) (α : Type v) : Type w :=
  F <| G α
#align functor.comp Functor.Comp

/-- Construct a term of `Comp F G α` from a term of `F (G α)`, which is the same type.
Can be used as a pattern to extract a term of `F (G α)`. -/
@[match_pattern]
def Comp.mk {F : Type u → Type w} {G : Type v → Type u} {α : Type v} (x : F (G α)) : Comp F G α :=
  x
#align functor.comp.mk Functor.Comp.mk

/-- Extract a term of `F (G α)` from a term of `Comp F G α`, which is the same type. -/
def Comp.run {F : Type u → Type w} {G : Type v → Type u} {α : Type v} (x : Comp F G α) : F (G α) :=
  x
#align functor.comp.run Functor.Comp.run

namespace Comp

variable {F : Type u → Type w} {G : Type v → Type u}

protected theorem ext {α} {x y : Comp F G α} : x.run = y.run → x = y :=
  id
#align functor.comp.ext Functor.Comp.ext

instance {α} [Inhabited (F (G α))] : Inhabited (Comp F G α) :=
  ⟨(default : F (G α))⟩

variable [Functor F] [Functor G]

/-- The map operation for the composition `Comp F G` of functors `F` and `G`. -/
protected def map {α β : Type v} (h : α → β) : Comp F G α → Comp F G β
  | Comp.mk x => Comp.mk ((· <$> ·) h <$> x)
#align functor.comp.map Functor.Comp.map

instance functor : Functor (Comp F G) where map := @Comp.map F G _ _

@[functor_norm]
theorem map_mk {α β} (h : α → β) (x : F (G α)) : h <$> Comp.mk x = Comp.mk ((· <$> ·) h <$> x) :=
  rfl
#align functor.comp.map_mk Functor.Comp.map_mk

@[simp]
protected theorem run_map {α β} (h : α → β) (x : Comp F G α) :
    (h <$> x).run = (· <$> ·) h <$> x.run :=
  rfl
#align functor.comp.run_map Functor.Comp.run_map

variable [LawfulFunctor F] [LawfulFunctor G]

variable {α β γ : Type v}

protected theorem id_map : ∀ x : Comp F G α, Comp.map id x = x
  | Comp.mk x => by simp [Comp.map, Functor.map_id]; rfl
                    -- ⊢ mk (mk x) = mk x
                                                     -- 🎉 no goals
  -- porting note: `rfl` wasn't needed in mathlib3
#align functor.comp.id_map Functor.Comp.id_map

protected theorem comp_map (g' : α → β) (h : β → γ) :
    ∀ x : Comp F G α, Comp.map (h ∘ g') x = Comp.map h (Comp.map g' x)
  | Comp.mk x => by simp [Comp.map, Comp.mk, Functor.map_comp_map, functor_norm]
                    -- 🎉 no goals
  -- porting note: `Comp.mk` wasn't needed in mathlib3
#align functor.comp.comp_map Functor.Comp.comp_map

instance lawfulFunctor : LawfulFunctor (Comp F G) where
  map_const := rfl
  id_map := @Comp.id_map F G _ _ _ _
  comp_map := @Comp.comp_map F G _ _ _ _

-- porting note: had to use switch to `Id` from `id` because this has the `Functor` instance.
theorem functor_comp_id {F} [AF : Functor F] [LawfulFunctor F] :
    @Comp.functor F Id _ _ = AF :=
  @Functor.ext F _ AF (@Comp.lawfulFunctor F Id _ _ _ _) _ fun _ _ _ _ => rfl
#align functor.comp.functor_comp_id Functor.Comp.functor_comp_id

-- porting note: had to use switch to `Id` from `id` because this has the `Functor` instance.
theorem functor_id_comp {F} [AF : Functor F] [LawfulFunctor F] : @Comp.functor Id F _ _ = AF :=
  @Functor.ext F _ AF (@Comp.lawfulFunctor Id F _ _ _ _) _ fun _ _ _ _ => rfl
#align functor.comp.functor_id_comp Functor.Comp.functor_id_comp

end Comp

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u → Type w} {G : Type v → Type u}

variable [Applicative F] [Applicative G]

/-- The `<*>` operation for the composition of applicative functors. -/
protected def seq {α β : Type v} : Comp F G (α → β) → (Unit → Comp F G α) → Comp F G β
  | Comp.mk f, g => match g () with
    | Comp.mk x => Comp.mk <| (· <*> ·) <$> f <*> x
#align functor.comp.seq Functor.Comp.seqₓ
-- `ₓ` because the type of `Seq.seq` doesn't match `has_seq.seq`

instance : Pure (Comp F G) :=
  ⟨fun x => Comp.mk <| pure <| pure x⟩

instance : Seq (Comp F G) :=
  ⟨fun f x => Comp.seq f x⟩

@[simp]
protected theorem run_pure {α : Type v} : ∀ x : α, (pure x : Comp F G α).run = pure (pure x)
  | _ => rfl
#align functor.comp.run_pure Functor.Comp.run_pure

@[simp]
protected theorem run_seq {α β : Type v} (f : Comp F G (α → β)) (x : Comp F G α) :
    (f <*> x).run = (· <*> ·) <$> f.run <*> x.run :=
  rfl
#align functor.comp.run_seq Functor.Comp.run_seq

instance instApplicativeComp : Applicative (Comp F G) :=
  { map := @Comp.map F G _ _, seq := @Comp.seq F G _ _ }

end Comp

variable {F : Type u → Type u} [Functor F]

/-- If we consider `x : F α` to, in some sense, contain values of type `α`,
predicate `Liftp p x` holds iff every value contained by `x` satisfies `p`. -/
def Liftp {α : Type u} (p : α → Prop) (x : F α) : Prop :=
  ∃ u : F (Subtype p), Subtype.val <$> u = x
#align functor.liftp Functor.Liftp

/-- If we consider `x : F α` to, in some sense, contain values of type `α`, then
`Liftr r x y` relates `x` and `y` iff (1) `x` and `y` have the same shape and
(2) we can pair values `a` from `x` and `b` from `y` so that `r a b` holds. -/
def Liftr {α : Type u} (r : α → α → Prop) (x y : F α) : Prop :=
  ∃ u : F { p : α × α // r p.fst p.snd },
    (fun t : { p : α × α // r p.fst p.snd } => t.val.fst) <$> u = x ∧
      (fun t : { p : α × α // r p.fst p.snd } => t.val.snd) <$> u = y
#align functor.liftr Functor.Liftr

/-- If we consider `x : F α` to, in some sense, contain values of type `α`, then
`supp x` is the set of values of type `α` that `x` contains. -/
def supp {α : Type u} (x : F α) : Set α :=
  { y : α | ∀ ⦃p⦄, Liftp p x → p y }
#align functor.supp Functor.supp

theorem of_mem_supp {α : Type u} {x : F α} {p : α → Prop} (h : Liftp p x) : ∀ y ∈ supp x, p y :=
  fun _ hy => hy h
#align functor.of_mem_supp Functor.of_mem_supp

/-- If `f` is a functor, if `fb : f β` and `a : α`, then `mapConstRev fb a` is the result of
  applying `f.map` to the constant function `β → α` sending everything to `a`, and then
  evaluating at `fb`. In other words it's `const a <$> fb`. -/
@[reducible] def mapConstRev {f : Type u → Type v} [Functor f] {α β : Type u} :
    f β → α → f α :=
  fun a b => Functor.mapConst b a
#align functor.map_const_rev Functor.mapConstRev
/-- If `f` is a functor, if `fb : f β` and `a : α`, then `mapConstRev fb a` is the result of
  applying `f.map` to the constant function `β → α` sending everything to `a`, and then
  evaluating at `fb`. In other words it's `const a <$> fb`. -/
infix:100 " $> " => Functor.mapConstRev

end Functor
