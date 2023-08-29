/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.Option.Defs

#align_import control.traversable.basic from "leanprover-community/mathlib"@"1fc36cc9c8264e6e81253f88be7fb2cb6c92d76a"

/-!
# Traversable type class

Type classes for traversing collections. The concepts and laws are taken from
<http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html>

Traversable collections are a generalization of functors. Whereas
functors (such as `List`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email → IO response`
that takes an email address, sends an email and waits for a
response. If we have a list `guests : List email`, using calling
`invite` using `map` gives us the following:
`map invite guests : List (IO response)`.  It is not what we need. We need something of
type `IO (List response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : IO (List response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `IO` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
<https://en.wikibooks.org/wiki/Haskell/Traversable>

## Main definitions
  * `Traversable` type class - exposes the `traverse` function
  * `sequence` - based on `traverse`,
    turns a collection of effects into an effect returning a collection
  * `LawfulTraversable` - laws for a traversable functor
  * `ApplicativeTransformation` - the notion of a natural transformation for applicative functors

## Tags

traversable iterator functor applicative

## References

 * "Applicative Programming with Effects", by Conor McBride and Ross Paterson,
   Journal of Functional Programming 18:1 (2008) 1-13, online at
   <http://www.soi.city.ac.uk/~ross/papers/Applicative.html>
 * "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira,
   in Mathematically-Structured Functional Programming, 2006, online at
   <http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator>
 * "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek,
   in Mathematically-Structured Functional Programming, 2012,
   online at <http://arxiv.org/pdf/1202.2919>
-/

open Function hiding comp

universe u v w

section ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

variable (G : Type u → Type w) [Applicative G] [LawfulApplicative G]

/-- A transformation between applicative functors.  It is a natural
transformation such that `app` preserves the `Pure.pure` and
`Functor.map` (`<*>`) operations. See
`ApplicativeTransformation.preserves_map` for naturality. -/
structure ApplicativeTransformation : Type max (u + 1) v w where
  /-- The function on objects defined by an `ApplicativeTransformation`. -/
  app : ∀ α : Type u, F α → G α
  /-- An `ApplicativeTransformation` preserves `pure`. -/
  preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x
  /-- An `ApplicativeTransformation` intertwines `seq`. -/
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y
#align applicative_transformation ApplicativeTransformation

end ApplicativeTransformation

namespace ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F] [LawfulApplicative F]

variable (G : Type u → Type w) [Applicative G] [LawfulApplicative G]

instance : CoeFun (ApplicativeTransformation F G) fun _ => ∀ {α}, F α → G α :=
  ⟨λ η => η.app _⟩

variable {F G}

@[simp]
theorem app_eq_coe (η : ApplicativeTransformation F G) : η.app = η :=
  rfl
#align applicative_transformation.app_eq_coe ApplicativeTransformation.app_eq_coe

@[simp]
theorem coe_mk (f : ∀ α : Type u, F α → G α) (pp ps) :
  (ApplicativeTransformation.mk f @pp @ps) = f :=
  rfl
#align applicative_transformation.coe_mk ApplicativeTransformation.coe_mk

protected theorem congr_fun (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u}
    (x : F α) : η x = η' x :=
  congrArg (fun η'' : ApplicativeTransformation F G => η'' x) h
#align applicative_transformation.congr_fun ApplicativeTransformation.congr_fun

protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
    (h : x = y) : η x = η y :=
  congrArg (fun z : F α => η z) h
#align applicative_transformation.congr_arg ApplicativeTransformation.congr_arg

theorem coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : ∀ α, F α → G α) = η') :
    η = η' := by
  cases η
  -- ⊢ { app := app✝, preserves_pure' := preserves_pure'✝, preserves_seq' := preser …
  cases η'
  -- ⊢ { app := app✝¹, preserves_pure' := preserves_pure'✝¹, preserves_seq' := pres …
  congr
  -- 🎉 no goals
#align applicative_transformation.coe_inj ApplicativeTransformation.coe_inj

@[ext]
theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) :
    η = η' := by
  apply coe_inj
  -- ⊢ (fun {α} => app η α) = fun {α} => app η' α
  ext1 α
  -- ⊢ app η α = app η' α
  exact funext (h α)
  -- 🎉 no goals
#align applicative_transformation.ext ApplicativeTransformation.ext

theorem ext_iff {η η' : ApplicativeTransformation F G} :
    η = η' ↔ ∀ (α : Type u) (x : F α), η x = η' x :=
  ⟨fun h _ _ => h ▸ rfl, fun h => ext h⟩
#align applicative_transformation.ext_iff ApplicativeTransformation.ext_iff

section Preserves

variable (η : ApplicativeTransformation F G)

@[functor_norm]
theorem preserves_pure {α} : ∀ x : α, η (pure x) = pure x :=
  η.preserves_pure'
#align applicative_transformation.preserves_pure ApplicativeTransformation.preserves_pure

@[functor_norm]
theorem preserves_seq {α β : Type u} : ∀ (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
  η.preserves_seq'
#align applicative_transformation.preserves_seq ApplicativeTransformation.preserves_seq

@[functor_norm]
theorem preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y := by
  rw [← pure_seq, η.preserves_seq, preserves_pure, pure_seq]
  -- 🎉 no goals
#align applicative_transformation.preserves_map ApplicativeTransformation.preserves_map

theorem preserves_map' {α β} (x : α → β) : @η _ ∘ Functor.map x = Functor.map x ∘ @η _ := by
  ext y
  -- ⊢ ((fun {α} => app η α) ∘ Functor.map x) y = (Functor.map x ∘ fun {α} => app η …
  exact preserves_map η x y
  -- 🎉 no goals
#align applicative_transformation.preserves_map' ApplicativeTransformation.preserves_map'

end Preserves

/-- The identity applicative transformation from an applicative functor to itself. -/
def idTransformation : ApplicativeTransformation F F where
  app α := id
  preserves_pure' := by simp
                        -- 🎉 no goals
  preserves_seq' x y := by simp
                           -- 🎉 no goals
#align applicative_transformation.id_transformation ApplicativeTransformation.idTransformation

instance : Inhabited (ApplicativeTransformation F F) :=
  ⟨idTransformation⟩

universe s t

variable {H : Type u → Type s} [Applicative H] [LawfulApplicative H]

/-- The composition of applicative transformations. -/
def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
    ApplicativeTransformation F H where
  app α x := η' (η x)
  -- Porting note: something has gone wrong with `simp [functor_norm]`,
  -- which should suffice for the next two.
  preserves_pure' x := by simp only [preserves_pure]
                          -- 🎉 no goals
  preserves_seq' x y := by simp only [preserves_seq]
                           -- 🎉 no goals
#align applicative_transformation.comp ApplicativeTransformation.comp

@[simp]
theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
    {α : Type u} (x : F α) : η'.comp η x = η' (η x) :=
  rfl
#align applicative_transformation.comp_apply ApplicativeTransformation.comp_apply

-- porting note: in mathlib3 we also had the assumption `[LawfulApplicative I]` because
-- this was assumed
theorem comp_assoc {I : Type u → Type t} [Applicative I]
    (η'' : ApplicativeTransformation H I) (η' : ApplicativeTransformation G H)
    (η : ApplicativeTransformation F G) : (η''.comp η').comp η = η''.comp (η'.comp η) :=
  rfl
#align applicative_transformation.comp_assoc ApplicativeTransformation.comp_assoc

@[simp]
theorem comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η :=
  ext fun _ _ => rfl
#align applicative_transformation.comp_id ApplicativeTransformation.comp_id

@[simp]
theorem id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η :=
  ext fun _ _ => rfl
#align applicative_transformation.id_comp ApplicativeTransformation.id_comp

end ApplicativeTransformation

open ApplicativeTransformation

/-- A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `List` and `m` is the applicative functor
`IO`, then given a function `f : α → IO β`, the function `Functor.map f` is
`List α → List (IO β)`, but `traverse f` is `List α → IO (List β)`. -/
class Traversable (t : Type u → Type u) extends Functor t where
  /-- The function commuting a traversable functor `t` with an arbitrary applicative functor `m`. -/
  traverse : ∀ {m : Type u → Type u} [Applicative m] {α β}, (α → m β) → t α → m (t β)
#align traversable Traversable

open Functor

export Traversable (traverse)

section Functions

variable {t : Type u → Type u}

variable {m : Type u → Type v} [Applicative m]

variable {α β : Type u}

variable {f : Type u → Type u} [Applicative f]

/-- A traversable functor commutes with all applicative functors. -/
def sequence [Traversable t] : t (f α) → f (t α) :=
  traverse id
#align sequence sequence

end Functions

/-- A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `pure : α → Id α` to `pure`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `fun x ↦ f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations. -/
class LawfulTraversable (t : Type u → Type u) [Traversable t] extends LawfulFunctor t :
    Prop where
  /-- `traverse` plays well with `pure` of the identity monad-/
  id_traverse : ∀ {α} (x : t α), traverse (pure : α → Id α) x = x
  /-- `traverse` plays well with composition of applicative functors. -/
  comp_traverse :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α β γ}
      (f : β → F γ) (g : α → G β) (x : t α),
      traverse (Functor.Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
  /-- An axiom for `traverse` involving `pure : β → Id β`. -/
  traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α),
    traverse ((pure : β → Id β) ∘ f) x = id.mk (f <$> x)
  /-- The naturality axiom explaining how lawful traversable functors should play with
  lawful applicative functors. -/
  naturality :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α β} (f : α → F β) (x : t α),
      η (traverse f x) = traverse (@η _ ∘ f) x
#align is_lawful_traversable LawfulTraversable

instance : Traversable Id :=
  ⟨id⟩

instance : LawfulTraversable Id := by refine' { .. } <;> intros <;> rfl
                                                         -- ⊢ mapConst = map ∘ const β✝
                                                         -- ⊢ id <$> x✝ = x✝
                                                         -- ⊢ (h✝ ∘ g✝) <$> x✝ = h✝ <$> g✝ <$> x✝
                                                         -- ⊢ traverse pure x✝ = x✝
                                                         -- ⊢ traverse (Comp.mk ∘ map f✝ ∘ g✝) x✝ = Comp.mk (traverse f✝ <$> traverse g✝ x✝)
                                                         -- ⊢ traverse (pure ∘ f✝) x✝ = id.mk (f✝ <$> x✝)
                                                         -- ⊢ (fun {α} => ApplicativeTransformation.app η✝ α) (traverse f✝ x✝) = traverse  …
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals

section

variable {F : Type u → Type v} [Applicative F]

instance : Traversable Option :=
  ⟨@Option.traverse⟩

instance : Traversable List :=
  ⟨@List.traverse⟩

end

namespace Sum

variable {σ : Type u}

variable {F : Type u → Type u}

variable [Applicative F]

-- porting note: this was marked as a dubious translation but the only issue seems to be
-- a universe issue; this may be a bug in mathlib3port. I've carefully checked the universes
-- in mathlib3 and mathlib4 and they seem to match up exactly. Discussion here
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/why.20dubious.3F/

/- warning: sum.traverse -> Sum.traverse is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u}} {F : Type.{u} -> Type.{u}} [_inst_1 : Applicative.{u u} F]
    {α : Type.{u_1}} {β : Type.{u}}, (α -> (F β)) -> (Sum.{u u_1} σ α) ->
    (F (Sum.{u u} σ β))
but is expected to have type
  forall {σ : Type.{u}} {F : Type.{u} -> Type.{u}} [_inst_1 : Applicative.{u u} F]
    {α : Type.{_aux_param_0}} {β : Type.{u}}, (α -> (F β)) -> (Sum.{u _aux_param_0} σ α) ->
    (F (Sum.{u u} σ β))
Case conversion may be inaccurate. Consider using '#align sum.traverse Sum.traverseₓ'. -/

/-- Defines a `traverse` function on the second component of a sum type.
This is used to give a `Traversable` instance for the functor `σ ⊕ -`. -/
protected def traverse {α β} (f : α → F β) : Sum σ α → F (Sum σ β)
  | Sum.inl x => pure (Sum.inl x)
  | Sum.inr x => Sum.inr <$> f x
#align sum.traverse Sum.traverse

end Sum

instance {σ : Type u} : Traversable.{u} (Sum σ) :=
  ⟨@Sum.traverse _⟩
