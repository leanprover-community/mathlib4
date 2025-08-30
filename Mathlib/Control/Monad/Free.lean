/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Eric Wieser
-/
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.SimpRw

/-!
# Free Monad

This file defines a general `FreeM` monad construction.

The `FreeM` monad generates a free monad from any type constructor `f : Type → Type`, without
requiring `f` to be a `Functor`. This implementation uses the "freer monad" approach as the
traditional free monad is not safely definable in Lean due to termination checking.

In this construction, computations are represented as **trees of effects**.
Each node (`FreeM.liftBind`) represents a request to perform an effect, accompanied by a
continuation specifying how the computation proceeds after the effect.
The leaves (`FreeM.pure`) represent completed computations with final results.

A key insight is that `FreeM F` satisfies the **universal property of free monads**: for any monad
`M` and effect handler `f : F → M`, there exists a unique way to interpret `FreeM F` computations
in `M` that respects the effect semantics given by `f`.
This unique interpreter is `FreeM.liftM f`, which acts as the canonical **fold** for free monads.


## Main Definitions

- `FreeM`: The free monad construction
- `FreeM.liftM`: The canonical fold/interpreter satisfying the universal property
- `FreeM.liftM_unique`: Proof of the universal property

See the Haskell [freer-simple](https://hackage.haskell.org/package/freer-simple) library for the
Haskell implementation that inspired this approach.

## Implementation Notes

The `FreeM` monad is defined using an inductive type with constructors `.pure` and `.liftBind`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.

For now we choose to make the constructors the simp-normal form, as opposed to the standard
monad notation.

In a downstream file, the monads `FreeState`, `FreeWriter`, and `FreeCont` are built by supplying
appropriate effect type constructors to the `FreeM` constructor.
They are equipped with interpreters and helper functions.

## References

* [Oleg Kiselyov, Hiromi Ishii. *Freer Monads, More Extensible Effects*][Kiselyov2015]
* [Bartosz Milewski. *The Dao of Functional Programming*][MilewskiDao]

## Tags

Free monad, state monad
-/

/-- The Free monad over a type constructor `F`.

A `FreeM F a` is a tree of operations from the type constructor `F`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for
representing an operation from `F` followed by a continuation.

This construction provides a free monad for any type constructor `F`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional free monad,
this does not require `F` to be a functor. -/
inductive FreeM.{u, v, w} (F : Type u → Type v) (α : Type w) where
  /-- The action that does nothing and returns `a`. -/
  | protected pure (a : α) : FreeM F α
  /-- Invoke the operation `op` with contuation `cont`.

  Note that Lean's inductive types prevent us splitting this into separate bind and lift
  constructors. -/
  | liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

universe u v w w' w''

namespace FreeM
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''}

instance : Pure (FreeM F) where pure := .pure

@[simp]
theorem pure_eq_pure : (pure : α → FreeM F α) = FreeM.pure := rfl

/-- Bind operation for the `FreeM` monad. -/
protected def bind (x : FreeM F α) (f : α → FreeM F β) : FreeM F β :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op fun z => FreeM.bind (cont z) f

protected theorem bind_assoc (x : FreeM F α) (f : α → FreeM F β) (g : β → FreeM F γ) :
    (x.bind f).bind g = x.bind (fun x => (f x).bind g) := by
  induction x with
  | pure a => rfl
  | liftBind op cont ih =>
    simp [FreeM.bind,  ← pure_eq_pure] at *
    simp [ih]

instance : Bind (FreeM F) where bind := .bind

@[simp]
theorem bind_eq_bind {α β : Type w} : Bind.bind = (FreeM.bind : FreeM F α → _ → FreeM F β) := rfl

/-- Map a function over a `FreeM` monad. -/
@[simp]
def map (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op fun z => FreeM.map f (cont z)

@[simp]
theorem id_map : ∀ x : FreeM F α, map id x = x
  | .pure a => rfl
  | .liftBind op cont => by simp_all [map, id_map]

theorem comp_map (h : β → γ) (g : α → β) : ∀ x : FreeM F α, map (h ∘ g) x = map h (map g x)
  | .pure a => rfl
  | .liftBind op cont => by simp_all [map, comp_map]

instance : Functor (FreeM F) where
  map := .map

@[simp]
theorem map_eq_map {α β : Type w} : Functor.map = FreeM.map (F := F) (α := α) (β := β) := rfl

/-- Lift an operation from the effect signature `F` into the `FreeM F` monad. -/
def lift (op : F ι) : FreeM F ι :=
  .liftBind op .pure

/-- Rewrite `lift` to the constructor form so that simplification stays in constructor normal
form. -/
@[simp]
lemma lift_def (op : F ι) :
    (lift op : FreeM F ι) = liftBind op .pure := rfl

@[simp]
lemma map_lift (f : ι → α) (op : F ι) :
    map f (lift op : FreeM F ι) = liftBind op (fun z => (.pure (f z) : FreeM F α)) := rfl

/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma pure_bind (a : α) (f : α → FreeM F β) : (.pure a : FreeM F α).bind f = f a := rfl

@[simp]
lemma bind_pure : ∀ x : FreeM F α, x.bind (.pure) = x
  | .pure a => rfl
  | liftBind op k => by simp [FreeM.bind, bind_pure]

@[simp]
lemma bind_pure_comp (f : α → β) : ∀ x : FreeM F α, x.bind (.pure ∘ f) = map f x
  | .pure a => rfl
  | liftBind op k => by simp only [FreeM.bind, map, bind_pure_comp]

/-- Collapse a `.bind` that follows a `liftBind` into a single `liftBind` -/
@[simp]
lemma liftBind_bind (op : F ι) (cont : ι → FreeM F α) (f : α → FreeM F β) :
    (liftBind op cont).bind f = liftBind op fun x => (cont x).bind f := rfl

instance : LawfulFunctor (FreeM F) where
  map_const := rfl
  id_map := id_map
  comp_map _ _ := comp_map _ _

instance : Monad (FreeM F) where

instance : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := bind_pure_comp)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := FreeM.bind_assoc)

section liftM
variable {m : Type u → Type w} [Monad m] {α β : Type u}

/--
Interpret a `FreeM F` computation into any monad `m` by providing an interpretation
function for the effect signature `F`.

This function defines the *canonical interpreter* from the free monad `FreeM F` into the target
monad `m`. It is the unique monad morphism that extends the effect handler
`interp : ∀ {β}, F β → m β` via the universal property of `FreeM`.
-/
protected def liftM (interp : {ι : Type u} → F ι → m ι) : FreeM F α → m α
  | .pure a => pure a
  | .liftBind op cont => interp op >>= fun result => (cont result).liftM interp

@[simp]
lemma liftM_pure (interp : {ι : Type u} → F ι → m ι) (a : α) :
    (.pure a : FreeM F α).liftM interp = pure a := rfl

@[simp]
lemma liftM_liftBind (interp : {ι : Type u} → F ι → m ι) (op : F β) (cont : β → FreeM F α) :
    (liftBind op cont).liftM interp = (do let b ← interp op; (cont b).liftM interp) := by
  rfl

lemma liftM_lift [LawfulMonad m] (interp : {ι : Type u} → F ι → m ι) (op : F β) :
    (lift op).liftM interp = interp op := by
  simp_rw [lift_def, liftM_liftBind, liftM_pure, _root_.bind_pure]

@[simp]
lemma liftM_bind [LawfulMonad m]
    (interp : {ι : Type u} → F ι → m ι) (x : FreeM F α) (f : α → FreeM F β) :
    (x.bind f : FreeM F β).liftM interp = (do let a ← x.liftM interp; (f a).liftM interp) := by
  induction x generalizing f with
  | pure a => simp only [pure_bind, liftM_pure, LawfulMonad.pure_bind]
  | liftBind op cont ih =>
    rw [FreeM.bind, liftM_liftBind, liftM_liftBind, bind_assoc]
    simp_rw [ih]

/--
A predicate stating that `interp : FreeM F α → m α` is an interpreter for the effect
handler `handler : ∀ {α}, F α → m α`.

This means that `interp` is a monad morphism from the free monad `FreeM F` to the
monad `m`, and that it extends the interpretation of individual operations
given by `f`.

Formally, `interp` satisfies the two equations:
- `interp (pure a) = pure a`
- `interp (liftBind op k) = handler op >>= fun x => interp (k x)`
-/
structure Interprets (handler : {ι : Type u} → F ι → m ι) (interp : FreeM F α → m α) : Prop where
  apply_pure (a : α) : interp (.pure a) = pure a
  apply_liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) :
    interp (liftBind op cont) = handler op >>= fun x => interp (cont x)

theorem Interprets.eq {handler : {ι : Type u} → F ι → m ι} {interp : FreeM F α → m α}
    (h : Interprets handler interp) :
    interp = (·.liftM @handler) := by
  ext x
  induction x with
  | pure a => exact h.apply_pure a
  | liftBind op cont ih =>
    rw [liftM_liftBind, h.apply_liftBind]
    simp [ih]

theorem interprets_liftM (handler : {ι : Type u} → F ι → m ι) :
    Interprets handler (·.liftM handler : FreeM F α → _) where
  apply_pure _ := rfl
  apply_liftBind _ _ := rfl

/--
The universal property of the free monad `FreeM`.

That is, `liftM handler` is the unique interpreter that extends the effect handler `handler` to
interpret `FreeM F` computations in a monad `m`.
-/
theorem interprets_iff (handler : {ι : Type u} → F ι → m ι) (interp : FreeM F α → m α) :
    Interprets handler interp ↔ interp = (·.liftM handler) :=
  ⟨(·.eq), fun h => h ▸ interprets_liftM _⟩

end liftM

end FreeM
