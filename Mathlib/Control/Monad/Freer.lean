/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Control.Monad.Writer
import Mathlib.Control.Monad.Cont
import Mathlib.Tactic.Cases

/-!
# Freer Monad and Common Instances

This file defines a general `Freer` monad construction and several canonical instances:
`State`, `Writer`, and `Continuation` monads implemented via this construction.

The "Freer" monad (as in, "more free") is an alternative representation of free monads
that doesn't require the underlying type constructor to be a `Functor`. Unlike the traditional
`Free` monad which generates a monad from a functor, `Freer` works with any type constructor
`f : Type → Type`, making it more general and easier to use with algebraic effects. The traditional
free monad is not safely definable in Lean due to strict positivity, so `Freer` is both a workaround
and a generalization.

In this construction, computations are represented as **trees of effects**. Each node (`impure`)
represents a request to perform an effect, accompanied by a continuation specifying how the
computation proceeds after the effect.
The leaves (`pure`) represent completed computations with final results.
To execute or interpret these computations, an interpreter walks this tree, handling effects
step-by-step.

See the Haskell [freer-simple](https://hackage.haskell.org/package/freer-simple) library for the
Haskell implementation.

## Main Definitions

- `Freer`: The general Freer monad.
- `FreerState`: State monad using the `Freer` construction.
- `FreerWriter`: Writer monad using the `Freer` construction.
- `FreerCont`: Continuation monad using the `Freer` construction.

## Implementation Notes

The `Freer` monad is defined using an inductive type with constructors `pure` and `impure`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.

The monads `FreerState`, `FreerWriter`, and `FreerCont` are built by supplying appropriate
effect type constructors to the `Freer` constructor. They are equipped with interpreters
and helper functions.

## References

* [Kiselyov2015] Oleg Kiselyov, Hiromi Ishii. *Freer Monads, More Extensible Effects*.
  Haskell Symposium 2015.

## Tags

Free monad, freer monad, state monad, writer monad, continuation monad
-/

/-- The Freer monad over a type constructor `f`.

A `Freer f a` is a tree of operations from the type constructor `f`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `impure` for
representing an operation from `f` followed by a continuation.

This construction provides a free monad for any type constructor `f`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional Free monad,
this does not require `f` to be a functor. -/
inductive Freer.{u, v, w} (f : Type u → Type v) (α : Type w) where
  | protected pure : α → Freer f α
  | impure {ι : Type u} (op : f ι) (cont : ι → Freer f α) : Freer f α

universe u v w

namespace Freer

/-- Map a function over a `Freer` monad. -/
def map {α β : Type _} (F : Type u → Type v) (f : α → β) : Freer F α → Freer F β :=
fun FFa =>
  match FFa with
  | .pure a => .pure (f a)
  | .impure op cont => .impure op (fun z => Freer.map F f (cont z))

instance {F : Type u → Type v} : Functor (Freer F) where
  map := Freer.map F

instance {F : Type u → Type v} : LawfulFunctor (Freer F) where
  map_const {α β} := by
    simp [Functor.mapConst, Functor.map]
  id_map x := by
    simp [Functor.map]
    induction' x with a b op cont ih
    · simp [map]
    · simp [map, ih]
  comp_map g h x := by
    simp [Functor.map]
    induction x
    case pure a => simp [Freer.map]
    case impure op cont ih => simp [Freer.map, ih]

/-- Bind operation for the `Freer` monad. -/
protected def bind {a b : Type _} (F : Type u → Type v) (x : Freer F a) (f : a → Freer F b) :
Freer F b :=
  match x with
  | .pure a => f a
  | .impure op cont => .impure op (fun z => Freer.bind F (cont z) f)

instance {F : Type u → Type v} : Monad (Freer F) where
  pure := Freer.pure
  bind := Freer.bind F

instance FreeLawfulMonad {F : Type u → Type v} : LawfulMonad (Freer F) := by
  apply LawfulMonad.mk'
  · intro x y; induction' y with a b op cont ih'; all_goals {simp}
  · intro _ _ x f; simp only [bind, Freer.bind]
  · intro _ _ _ x f g; induction' x with a b op cont ih;
    · simp only [bind, Freer.bind]
    · simp only [bind, Freer.bind, ih] at *; simp [ih]
  · intro _ _ x y; simp [Functor.map, Functor.mapConst]
  · intro _ _ x y; simp [bind, SeqLeft.seqLeft, Pure.pure]
  · intro _ _ x y; simp [bind, SeqRight.seqRight]
  · intro _ _ f x; induction' x with a b op cont ih;
    · simp [bind, Freer.bind, Functor.map, Pure.pure, map]
    · simp only [Functor.map, bind, Freer.bind, map, Pure.pure, map] at *; simp [ih]
  · intro _ _ f x; simp [bind, Freer.bind, Functor.map, Seq.seq]

/-! ### State Monad via `Freer` -/

/-- Type constructor for state operations. -/
inductive StateF (σ : Type u) : Type u → Type _ where
  /-- Get the current state. -/
  | get : StateF σ σ
  /-- Set the state. -/
  | set : σ → StateF σ PUnit

/-- State monad via the `Freer` monad. -/
abbrev FreerState (σ : Type u) := Freer (StateF σ)

namespace FreerState

instance {σ : Type u} : Monad (FreerState σ) := inferInstance
instance {σ : Type u} : LawfulMonad (FreerState σ) := inferInstance

instance {σ : Type u} : MonadStateOf σ (FreerState σ) where
  get := Freer.impure StateF.get Freer.pure
  set newState := Freer.impure (StateF.set newState) (fun _ => Freer.pure PUnit.unit)
  modifyGet f :=
    Freer.impure StateF.get (fun s =>
      let (a, s') := f s
      Freer.impure (StateF.set s') (fun _ => Freer.pure a))

instance {σ : Type u} : MonadState σ (FreerState σ) := inferInstance

/-- Run a state computation, returning both the result and final state. -/
def runState {σ : Type u} {α : Type v} (comp : FreerState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .impure StateF.get k     => runState (k s₀) s₀
  | .impure (StateF.set s') k => runState (k PUnit.unit) s'

/-- Run a state computation, returning only the result. -/
def evalState {σ : Type u} {α : Type v} (c : FreerState σ α) (s₀ : σ) : α :=
  (runState c s₀).1

/-- Run a state computation, returning only the final state. -/
def execState {σ : Type u} {α : Type v} (c : FreerState σ α) (s₀ : σ) : σ :=
  (runState c s₀).2

end FreerState

/-! ### Writer Monad via `Freer` -/

/--
Type constructor for writer operations. Writer has a single effect, so the definition has just one
constructor, `tell`, which writes a value to the log.
-/
inductive WriterF (ω : Type u) : Type u → Type u
  | tell : ω → WriterF ω PUnit

/-- Writer monad implemented via the `Freer` monad construction. This provides a more efficient
implementation than the traditional `WriterT` transformer, as it avoids buffering the log. -/
abbrev FreerWriter (ω : Type u) := Freer (WriterF ω)

namespace FreerWriter

open WriterF

instance {ω : Type u} : Monad (FreerWriter ω) := inferInstance
instance {ω : Type u} : LawfulMonad (FreerWriter ω) := inferInstance

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
def tell {ω : Type u} (w : ω) : FreerWriter ω PUnit :=
  Freer.impure  (WriterF.tell w) Freer.pure

/--
Interprets a `FreerWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
def run {ω : Type u} [Monoid ω] {α} : FreerWriter ω α → α × ω
  | .pure a => (a, 1)
  | .impure (WriterF.tell w) k =>
      let (a, w') := run (k PUnit.unit)
      (a, w * w')

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
def listen {ω : Type u} [Monoid ω] {α : Type v} : FreerWriter ω α → FreerWriter ω (α × ω)
  | .pure a => .pure (a, 1)
  | .impure (WriterF.tell w) k =>
      Freer.impure (WriterF.tell w) fun _ =>
        listen (k PUnit.unit) >>= fun (a, w') =>
          pure (a, w * w')

/--
`pass` allows a subcomputation to modify its own log. After traversing the computation and
accumulating its log, the resulting function is applied to rewrite the accumulated log
before re-emission.
-/
def pass {ω : Type u} [Monoid ω] {α} (m : FreerWriter ω (α × (ω → ω))) : FreerWriter ω α :=
  let ((a, f), w) := run m
  Freer.impure (WriterF.tell (f w)) (fun _ => .pure a)

instance {ω : Type u} [Monoid ω] : MonadWriter ω (FreerWriter ω) where
  tell w := Freer.impure (WriterF.tell w) (fun _ => .pure PUnit.unit)
  listen := listen
  pass := pass

/--
Evaluate a writer computation, returning the final result and discarding the log.
-/
def eval {ω : Type u} [Monoid ω] {α : Type v} (comp : FreerWriter ω α) : α :=
  (run comp).1

/--
Execute a writer computation, returning only the accumulated log and discarding the result.
-/
def exec {ω : Type u} {α : Type v} [Monoid ω] (comp : FreerWriter ω α) : ω :=
  (run comp).2

end FreerWriter


/-! ### Continuation Monad via `Freer` -/

/-- Type constructor for continuation operations. -/
inductive ContF (r : Type u) (α : Type v) where
  /-- Call with current continuation: provides access to the current continuation. -/
  | callCC : ((α → r) → r) → ContF r α

instance {r : Type u} : Functor (ContF r) where
  map f
  | .callCC g => .callCC (fun k => g (k ∘ f))

/-- Continuation monad via the `Freer` monad. -/
abbrev FreerCont (r : Type u) := Freer (ContF r)

namespace FreerCont

instance {r : Type u} : Monad (FreerCont r) := inferInstance
instance {r : Type u} : LawfulMonad (FreerCont r) := inferInstance

/-- Run a continuation computation with the given continuation. -/
def run {r : Type u} {α : Type v} : FreerCont r α → (α → r) → r
  | .pure a, k => k a
  | .impure (ContF.callCC g) cont, k => g (fun a => run (cont a) k)

/-- Call with current continuation for the Freer continuation monad. -/
def callCC {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreerCont r) β → FreerCont r α) :
FreerCont r α :=
  Freer.impure (ContF.callCC (fun k =>
    run (f ⟨fun x => Freer.impure (ContF.callCC (fun _ => k x)) Freer.pure⟩) k
  )) Freer.pure

instance {r : Type u} : MonadCont (FreerCont r) where
  callCC := FreerCont.callCC

end FreerCont

end Freer
