/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Control.Monad.Writer
import Mathlib.Control.Monad.Cont
import Mathlib.Algebra.Group.Nat.Defs

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
computationproceeds after the effect.
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
  | pure : α → Freer f α
  | impure (ι : Type u) (op : f ι) (cont : ι → Freer f α) : Freer f α

universe u v w

namespace Freer

/-- Map a function over a `Freer` monad. -/
def map {α β : Type _} (F : Type u → Type v) (f : α → β) : Freer F α → Freer F β :=
fun FFa =>
  match FFa with
  | .pure a => .pure (f a)
  | .impure ι op cont => .impure ι op (fun z => Freer.map F f (cont z))

instance {F : Type u → Type v} : Functor (Freer F) where
  map := Freer.map F

instance {F : Type u → Type v} : LawfulFunctor (Freer F) where
  map_const {α β} := by
    simp [Functor.mapConst, Functor.map]
  id_map x := by
    simp [Functor.map]
    induction x
    case pure a => simp [Freer.map]
    case impure ι op cont ih => simp [Freer.map, ih]
  comp_map g h x := by
    simp [Functor.map]
    induction x
    case pure a => simp [Freer.map]
    case impure ι op cont ih => simp [Freer.map, ih]

/-- Bind operation for the `Freer` monad. -/
def bindFree {a b : Type _} (F : Type u → Type v) (x : Freer F a) (f : a → Freer F b) : Freer F b :=
  match x with
  | .pure a => f a
  | .impure ι op cont => .impure ι op (fun z => bindFree F (cont z) f)

instance {F : Type u → Type v} : Monad (Freer F) where
  pure := Freer.pure
  bind := bindFree F

instance FreeLawfulMonad {F : Type u → Type v} : LawfulMonad (Freer F) where
  bind_pure_comp x y := by
    simp [Functor.map, bind, pure]; induction y
    · case pure a => simp [bindFree, map, Pure.pure]
    · case impure X Fx k ih => simp [bindFree, Freer.map, ih]
  bind_map f x := by
    simp [bind, Seq.seq]
  pure_bind a f := by
    simp [bind, pure, bindFree]
  bind_assoc x f g := by
    simp [bind]; induction x
    case pure a => simp [bindFree, Freer.map]
    case impure X Fx k ih => simp [bindFree, Freer.map, ih]
  seqLeft_eq x y := by
    simp [Functor.map, SeqLeft.seqLeft, Seq.seq]; induction x
    case pure a =>
      simp [bindFree, Freer.map]
      induction y
      case pure b => simp [bindFree, Freer.map]
      case impure X Fy k ih => simp [bindFree, Freer.map, ih]
    case impure X Fx k ih => simp [bindFree, Freer.map, ih]
  seqRight_eq x y := by
    simp [Functor.map, bindFree, Freer.map]; induction x
    case pure a =>
      simp [bindFree, Freer.map]
      induction y
      case pure b => simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Freer.map]
      case impure X Fy k ih =>
        simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Freer.map, ih] at ih ⊢
        apply funext; exact ih
    case impure X Fx k ih =>
      simp [Freer.map, Seq.seq, bindFree, Functor.map, SeqRight.seqRight] at ih ⊢
      apply funext; exact ih
  pure_seq f x := by
    simp [Seq.seq, Functor.map, pure, bindFree]

/-! ### State Monad via `Freer` -/

/-- Type constructor for state operations. -/
inductive StateF (σ : Type u) : Type u → Type _ where
  | get : StateF σ σ                   -- get the current state
  | set : σ → StateF σ PUnit           -- set the state

/-- State monad via the `Freer` monad. -/
abbrev FreerState (σ : Type u) := Freer (StateF σ)

namespace FreerState

instance {σ : Type u} : Monad (FreerState σ) := inferInstance
instance {σ : Type u} : LawfulMonad (FreerState σ) := inferInstance

instance {σ : Type u} : MonadStateOf σ (FreerState σ) where
  get := Freer.impure σ (StateF.get) Freer.pure
  set newState := Freer.impure PUnit (StateF.set newState) (fun _ => Freer.pure PUnit.unit)
  modifyGet f :=
    Freer.impure σ StateF.get (fun s =>
      let (a, s') := f s
      Freer.impure PUnit (StateF.set s') (fun _ => Freer.pure a))

instance {σ : Type u} : MonadState σ (FreerState σ) := inferInstance

/-- Run a state computation, returning both the result and final state. -/
def runState {σ : Type u} {α : Type v} (comp : FreerState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .impure _ StateF.get k     => runState (k s₀) s₀
  | .impure _ (StateF.set s') k => runState (k PUnit.unit) s'

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
inductive WriterF (ω : Type u) : Type u → Type _ where
  | tell : ω → WriterF ω PUnit

abbrev FreerWriter (ω : Type u) := Freer (WriterF ω)

namespace FreerWriter

open WriterF

instance {ω : Type u} : Monad (FreerWriter ω) := inferInstance
instance {ω : Type u} : LawfulMonad (FreerWriter ω) := inferInstance

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
def tell {ω : Type u} (w : ω) : FreerWriter ω PUnit :=
  Freer.impure _ (WriterF.tell w) Freer.pure

/--
Interprets a `FreerWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
def run {ω : Type u} [Monoid ω] {α} : FreerWriter ω α → α × ω
  | .pure a => (a, 1)
  | .impure _ (WriterF.tell w) k =>
      let (a, w') := run (k PUnit.unit)
      (a, w * w')

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
def listen {ω : Type u} [Monoid ω] {α} (m : FreerWriter ω α) : FreerWriter ω (α × ω) :=
  let (a, w) := run m
  Freer.impure _ (WriterF.tell w) (fun _ => .pure (a, w))

/--
`pass` allows a subcomputation to modify its own log. After traversing the computation and
accumulating its log, the resulting function is applied to rewrite the accumulated log
before re-emission.
-/
def pass {ω : Type u} [Monoid ω] {α} (m : FreerWriter ω (α × (ω → ω))) : FreerWriter ω α :=
  let ((a, f), w) := run m
  Freer.impure _ (WriterF.tell (f w)) (fun _ => .pure a)

instance {ω : Type u} [Monoid ω] : MonadWriter ω (FreerWriter ω) where
  tell w := Freer.impure _ (WriterF.tell w) (fun _ => .pure PUnit.unit)
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
  | .impure _ (ContF.callCC g) cont, k => g (fun a => run (cont a) k)

/-- Call with current continuation for the Freer continuation monad. -/
def callCC {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreerCont r) β → FreerCont r α) :
FreerCont r α :=
  Freer.impure _ (ContF.callCC (fun k =>
    run (f ⟨fun x => Freer.impure _ (ContF.callCC (fun _ => k x)) Freer.pure⟩) k
  )) Freer.pure

instance {r : Type u} : MonadCont (FreerCont r) where
  callCC := FreerCont.callCC

end FreerCont

/-! ### Basic Examples -/

-- Example FreerState computations
example : FreerState.evalState (do
  let s ← get
  set (s + 1)
  return s : FreerState Nat Nat) 5 = 5 := rfl

example : FreerState.execState (do
  let s ← get
  set (s + 1)
  return s : FreerState Nat Nat) 5 = 6 := rfl

example : FreerState.runState (do
  let s ← get
  set (s + 1)
  return s : FreerState Nat Nat) 5 = (5, 6) := rfl

-- Example FreerWriter computations
example : FreerWriter.run (do
  FreerWriter.tell (21 : Nat)
  FreerWriter.tell 3
  return 42) = (42, 63) := rfl

example : FreerWriter.run (do
  let (x, captured) ← FreerWriter.listen (do
    FreerWriter.tell 2
    FreerWriter.tell 3
    return 42)
  FreerWriter.tell 2
  return (x, captured)) = ((42, 6), 12) := rfl

example : FreerWriter.run (FreerWriter.pass (do
  FreerWriter.tell 3
  return (42, fun log => log * 2))) = (42, 6) := rfl

-- Example FreerCont computations
example : FreerCont.run (do
  FreerCont.callCC (fun k => do
    k.1 42
    return 100)
  : FreerCont Nat Nat) id = 42 := rfl

example : FreerCont.run (do
  let x ← FreerCont.callCC (fun k => do
    if true then k.1 42 else return 100)
  return x + 1
  : FreerCont Nat Nat) id = 43 := rfl

end Freer
