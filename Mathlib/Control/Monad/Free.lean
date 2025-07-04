/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Control.Monad.Writer
import Mathlib.Tactic.Cases

/-!
# Free Monad

This file defines a general `FreeM` monad construction.

The `FreeM` monad generates a free monad from any type constructor `f : Type → Type`, without
requiring `f` to be a `Functor`. This implementation uses the "freer monad" approach as the
traditional free monad is not safely definable in Lean due to termination checking.

In this construction, computations are represented as **trees of effects**. Each node (`liftBind`)
represents a request to perform an effect, accompanied by a continuation specifying how the
computation proceeds after the effect. The leaves (`pure`) represent completed computations with
final results.

A key insight is that `FreeM F` satisfies the **universal property of free monads**: for any monad
`M` and effect handler `f : F → M`, there exists a unique way to interpret `FreeM F` computations
in `M` that respects the effect semantics given by `f`. This unique interpreter is `liftM f`, which
acts as the canonical **fold** for free monads.


## Main Definitions

- `FreeM`: The free monad construction
- `liftM`: The canonical fold/interpreter satisfying the universal property
- `liftM_unique`: Proof of the universal property

See the Haskell [freer-simple](https://hackage.haskell.org/package/freer-simple) library for the
Haskell implementation that inspired this approach.

## Implementation Notes

The `FreeM` monad is defined using an inductive type with constructors `pure` and `liftBind`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.

The monads `FreeState`, `FreeWriter`, and `FreeCont` are built by supplying appropriate
effect type constructors to the `FreeM` constructor. They are equipped with interpreters
and helper functions.

## References

* [Oleg Kiselyov, Hiromi Ishii. *Freer Monads, More Extensible Effects*][Kiselyov2015]
* [Bartosz Milewski. *The Dao of Functional Programming*][MilewskiDao]

## Tags

Free monad, state monad
-/

/-- The Free monad over a type constructor `f`.

A `FreeM f a` is a tree of operations from the type constructor `f`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for
representing an operation from `f` followed by a continuation.

This construction provides a free monad for any type constructor `f`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional free monad,
this does not require `f` to be a functor. -/
inductive FreeM.{u, v, w} (f : Type u → Type v) (α : Type w) where
  | protected pure : α → FreeM f α
  | liftBind {ι : Type u} (op : f ι) (cont : ι → FreeM f α) : FreeM f α

/-
Disable simpNF lints for auto-generated constructor lemmas, as they don't follow simp normal
form patterns. The LHS of these lemmas use `FreeM.pure` which simplifies to `pure` via
`pure_eq_pure`.
-/
attribute [nolint simpNF] FreeM.pure.sizeOf_spec FreeM.pure.injEq FreeM.liftBind.sizeOf_spec
FreeM.liftBind.injEq

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
theorem bind_eq_bind {α β : Type w} :
    Bind.bind = (FreeM.bind : FreeM F α → _ → FreeM F β) := rfl

/-- Map a function over a `FreeM` monad. -/
def map (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op fun z => FreeM.map f (cont z)

instance: Functor (FreeM F) where
  map := .map

@[simp]
theorem map_eq_map {α β : Type w} : Functor.map = FreeM.map (F := F) (α := α) (β := β) := rfl

/-- Lift an operation from the effect signature `f` into the `FreeM f` monad. -/
def lift (op : F ι) : FreeM F ι :=
  .liftBind op pure

/-- Rewrite `lift` to the constructor form so that simplification stays in constructor
normal form. -/
@[simp]
lemma lift_def (op : F ι) :
    (lift op : FreeM F ι) = liftBind op pure := rfl

@[simp]
lemma map_lift {ι : Type u} {β : Type u} (f : ι → β) (op : F ι) :
    (f <$> (lift op : FreeM F ι)) = liftBind op (fun z => (pure (f z) : FreeM F β))
  := rfl

/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma bind_pure_left (a : α) (f : α → FreeM F β) :
    (.pure a : FreeM F α).bind f = f a := rfl

@[simp]
lemma bind_pure_right {α : Type u} (x : FreeM F α) :
    x.bind (.pure) = x := by
  induction x with
  | pure a => rfl
  | liftBind op k ih =>
      simp [FreeM.bind, ih]

/-- Collapse a `.bind` that follows a `liftBind` into a single `liftBind` -/
@[simp]
lemma bind_liftBind_dot {α β γ : Type u} (op : F α) (cont : α → FreeM F β)
    (f : β → FreeM F γ) :
    (liftBind op cont).bind f = liftBind op fun x => (cont x).bind f := rfl

instance : LawfulFunctor (FreeM F) where
  map_const := rfl
  id_map x := by
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp_all [map_eq_map, lift_def, map, ih]
  comp_map g h x := by
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp_all [map_eq_map, lift_def, map, ih]

instance : Monad (FreeM F) where

instance : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := fun f x => by
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp only [FreeM.bind, bind_eq_bind, map_eq_map, pure_eq_pure, map] at *
      simp only [ih]
  )
  (id_map := id_map)
  (pure_bind := fun x f => rfl)
  (bind_assoc := FreeM.bind_assoc)

/--
Interpret a `FreeM f` computation into any monad `m` by providing an interpretation
function for the effect signature `f`.

This function defines the *canonical interpreter* from the free monad `FreeM f` into the target
monad `m`. It is the unique monad morphism that extends the effect handler
`interp : ∀ {β}, F β → M β` via the universal property of `FreeM`.
-/
protected def liftM {M : Type u → Type w} [Monad M] {α : Type u} :
    FreeM F α → ({β : Type u} → F β → M β) → M α
  | .pure a, _ => pure a
  | .liftBind op cont, interp => interp op >>= fun result => (cont result).liftM interp

@[simp]
lemma liftM_pure {M : Type u → Type w} [Monad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (a : α) :
    pure a = (pure a : FreeM F α).liftM interp := rfl

@[simp]
lemma liftM_liftBind {M : Type u → Type w} [Monad M] {α β : Type u}
    (interp : {γ : Type u} → F γ → M γ) (op : F β) (cont : β → FreeM F α) :
    (do let b ← interp op; (cont b).liftM interp) = (liftBind op cont).liftM interp := by
  rfl

@[simp]
lemma liftM_bind {M : Type u → Type w} [Monad M] [LawfulMonad M] {α β : Type u}
    (interp : {β : Type u} → F β → M β) (x : FreeM F α) (f : α → FreeM F β) :
    (do let a ← x.liftM interp; (f a).liftM interp) = (x >>= f : FreeM F β).liftM interp := by
  induction x generalizing f with
  | pure a => simp only [← pure_eq_pure, ← liftM_pure, pure_bind, bind, FreeM.bind]
  | liftBind op cont ih =>
    simp_rw [bind_eq_bind] at *
    rw [FreeM.bind, ← liftM_liftBind, ← liftM_liftBind, bind_assoc]
    simp_rw [ih]

@[simp]
lemma liftM_liftBind_pure {M : Type u → Type w} [Monad M] [LawfulMonad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (op : F α) :
    (FreeM.liftBind op .pure).liftM interp = interp op := by
  simp [← pure_eq_pure, ← liftM_liftBind, ← liftM_pure]

/--
A predicate stating that `g : FreeM F α → M α` is an interpreter for the effect
handler `f : ∀ {α}, F α → M α`.

This means that `g` is a monad morphism from the free monad `FreeM F` to the
monad `M`, and that it extends the interpretation of individual operations
given by `f`.

Formally, `g` satisfies the two equations:
- `g (pure a) = pure a`
- `g (liftBind op k) = f op >>= fun x => g (k x)`
-/
structure ExtendsHandler {M : Type u → Type w} [Monad M] {α : Type u}
    (f : {ι : Type u} → F ι → M ι)
    (g : FreeM F α → M α) : Prop where
  apply_pure : ∀ a, g (pure a) = pure a
  apply_liftBind : ∀ {ι} (op : F ι) (k : ι → FreeM F α),
    g (liftBind op k) = f op >>= fun x => g (k x)

/--
The universal property of the free monad `FreeM`. That is, `liftM f` is the unique interpreter that
extends the effect handler `f` to interpret `FreeM F` computations in monad `M`.
-/
theorem extendsHandler_iff {F : Type u → Type v} {m : Type u → Type w} [Monad m] {α : Type u}
    (f : {ι : Type u} → F ι → m ι) (g : FreeM F α → m α) :
    ExtendsHandler @f g ↔ g = (·.liftM @f) := by
  refine ⟨fun h => funext fun x => ?_, fun h => ?_⟩
  · induction x with
    | pure a => exact h.apply_pure a
    | liftBind op cont ih =>
      rw [← liftM_liftBind, h.apply_liftBind]
      simp [ih]
  · subst h
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

end FreeM
