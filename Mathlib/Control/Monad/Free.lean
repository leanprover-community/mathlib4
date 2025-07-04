/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Control.Monad.Writer
import Mathlib.Tactic.Cases

/-!
# Free Monad and Common Instances

This file defines a general `FreeM` monad construction and several canonical instances:
`State`, `Writer`, and `Continuation` monads implemented via this construction.

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

## Implementation

To execute or interpret these computations, we provide two approaches:
1. **Hand-written interpreters** (`FreeState.run`, `FreeWriter.run`, `FreeCont.run`) that directly
  pattern-match on the tree structure
2. **Canonical interpreters** (`FreeState.toStateM`, `FreeWriter.toWriterT`, `FreeCont.toContT`)
  derived from the universal property via `liftM`

We prove that these approaches are equivalent, demonstrating that the implementation aligns with
the theory. We also provide uniqueness theorems for the canonical interpreters, which follow from
the universal property.

## Main Definitions

- `FreeM`: The free monad construction
- `liftM`: The canonical fold/interpreter satisfying the universal property
- `FreeState`, `FreeWriter`, `FreeCont`: Specific effect monads with both hand-written and
  canonical interpreters
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

Free monad, state monad, writer monad, continuation monad
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
theorem extendsHandler_iff
{F : Type u → Type v} {m : Type u → Type w} [Monad m] {α : Type u}
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

/-! ### State Monad via `FreeM` -/

/-- Type constructor for state operations. -/
inductive StateF (σ : Type u) : Type u → Type u where
  /-- Get the current state. -/
  | get : StateF σ σ
  /-- Set the state. -/
  | set : σ → StateF σ PUnit

/-- State monad via the `FreeM` monad. -/
abbrev FreeState (σ : Type u) := FreeM (StateF σ)

namespace FreeState

instance {σ : Type u} : Monad (FreeState σ) := inferInstance
instance {σ : Type u} : LawfulMonad (FreeState σ) := inferInstance

instance {σ : Type u} : MonadStateOf σ (FreeState σ) where
  get := .lift .get
  set newState := .liftBind (.set newState) (fun _ => .pure PUnit.unit)
  modifyGet f :=
    .liftBind .get (fun s =>
      let (a, s') := f s
      .liftBind (.set s') (fun _ => .pure a))

@[simp]
lemma get_def {σ : Type u} : (get : FreeState σ σ) = .lift .get := rfl

@[simp]
lemma set_def {σ : Type u} (s : σ) :
  (set s : FreeState σ PUnit) = .liftBind (.set s) (fun _ => .pure PUnit.unit) := rfl

instance {σ : Type u} : MonadState σ (FreeState σ) := inferInstance

@[simp]
lemma bind_pure {α β : Type u} (a : α) (f : α → FreeM F β) :
    .pure a >>= f = f a := rfl

@[simp] lemma map_pure {α β : Type u} (f : α → β) (a : α) :
    f <$> (.pure a : FreeM F α) = .pure (f a) := rfl

@[simp]
lemma bind_liftBind {α β γ : Type u} (op : F α) (cont : α → FreeM F β)
  (f : β → FreeM F γ) :
    liftBind op cont >>= f = liftBind op (fun x => cont x >>= f) := rfl

@[simp]
lemma map_liftBind {α β γ : Type u} (f : β → γ) (op : F α) (cont : α → FreeM F β) :
    f <$> liftBind op cont = liftBind op fun x => f <$> cont x := rfl

/-- Interpret `StateF` operations into `StateM`. -/
def stateInterp {σ : Type u} : {α : Type u} → StateF σ α → StateM σ α
  | _, .get => MonadStateOf.get
  | _, .set s => MonadStateOf.set s

/-- Convert a `FreeState` computation into a `StateM` computation. This is the canonical
interpreter derived from `liftM`. -/
def toStateM {σ α : Type u} (comp : FreeState σ α) : StateM σ α :=
  comp.liftM stateInterp

/-- `toStateM` is the unique interpreter extending `stateInterp`. -/
theorem toStateM_unique {σ α : Type u} (g : FreeState σ α → StateM σ α)
    (h : ExtendsHandler stateInterp g) : g = toStateM :=
    (extendsHandler_iff stateInterp g).mp h

/-- Run a state computation, returning both the result and final state. -/
def run {σ : Type u} {α : Type v} (comp : FreeState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .liftBind StateF.get k => run (k s₀) s₀
  | .liftBind (StateF.set s') k => run (k PUnit.unit) s'

/--
The canonical interpreter `toStateM` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeState`.
-/
@[simp]
theorem toStateM_eq_run {σ α : Type u} (comp : FreeState σ α) (s₀ : σ) :
    toStateM comp s₀ = run comp s₀ := by
  induction comp generalizing s₀ with
  | pure a => rfl
  | liftBind op cont ih =>
    cases op <;> apply ih

@[simp]
lemma run_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    run (.pure a : FreeState σ α) s₀ = (a, s₀) := rfl

@[simp]
lemma run_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    run (liftBind .get k) s₀ = run (k s₀) s₀ := rfl

@[simp]
lemma run_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    run (liftBind (.set s') k) s₀ = run (k .unit) s' := rfl

/-- Run a state computation, returning only the result. -/
def evalState {σ : Type u} {α : Type v} (c : FreeState σ α) (s₀ : σ) : α :=
  (run c s₀).1

@[simp]
lemma evalState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    evalState (.pure a : FreeState σ α) s₀ = a := rfl

@[simp]
lemma evalState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    evalState (liftBind .get k) s₀ = evalState (k s₀) s₀ := rfl

@[simp]
lemma evalState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    evalState (liftBind (.set s') k) s₀ = evalState (k .unit) s' := rfl

/-- Run a state computation, returning only the final state. -/
def runState {σ : Type u} {α : Type v} (c : FreeState σ α) (s₀ : σ) : σ :=
  (run c s₀).2

@[simp]
lemma runState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    runState (.pure a : FreeState σ α) s₀ = s₀ := rfl

@[simp]
lemma runState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    runState (liftBind .get k) s₀ = runState (k s₀) s₀ := rfl

@[simp]
lemma runState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    runState (liftBind (.set s') k) s₀ = runState (k .unit) s' := rfl


end FreeState

/-! ### Writer Monad via `FreeM` -/

/--
Type constructor for writer operations. Writer has a single effect, so the definition has just one
constructor, `tell`, which writes a value to the log.
-/
inductive WriterF (ω : Type u) : Type u → Type u
  | tell : ω → WriterF ω PUnit

/-- Writer monad implemented via the `FreeM` monad construction. This provides a more efficient
implementation than the traditional `WriterT` transformer, as it avoids buffering the log. -/
abbrev FreeWriter (ω : Type u) := FreeM (WriterF ω)

namespace FreeWriter

open WriterF

instance {ω : Type u} : Monad (FreeWriter ω) := inferInstance
instance {ω : Type u} : LawfulMonad (FreeWriter ω) := inferInstance

/-- Interpret `WriterF` operations into `WriterT`. -/
def writerInterp {ω : Type u} : {α : Type u} → WriterF ω α → WriterT ω Id α
  | _, .tell w => MonadWriter.tell w

/-- Convert a `FreeWriter` computation into a `WriterT` computation. This is the canonical
interpreter derived from `liftM`. -/
def toWriterT {ω α : Type u} [Monoid ω] (comp : FreeWriter ω α) : WriterT ω Id α :=
  comp.liftM writerInterp

/-- `toWriterT` is the unique interpreter extending `writerInterp`. -/
theorem toWriterT_unique {ω α : Type u} [Monoid ω] (g : FreeWriter ω α → WriterT ω Id α)
    (h : ExtendsHandler writerInterp g) : g = toWriterT := (extendsHandler_iff writerInterp g).mp h

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
def tell {ω : Type u} (w : ω) : FreeWriter ω PUnit :=
  lift (.tell w)

@[simp]
lemma tell_def {ω : Type u} (w : ω) :
    tell w = .lift (.tell w) := rfl

/--
Interprets a `FreeWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
def run {ω : Type u} [Monoid ω] {α} : FreeWriter ω α → α × ω
  | .pure a => (a, 1)
  | .liftBind (.tell w) k =>
      let (a, w') := run (k .unit)
      (a, w * w')

/--
The canonical interpreter `toWriterT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeWriter`.
-/
@[simp]
theorem toWriterT_eq_run {ω : Type u} [Monoid ω] {α} (comp : FreeWriter ω α) :
    toWriterT comp = run comp := by
  induction' comp with a b op cont ih
  · simp only [toWriterT, FreeM.liftM, pure, run, WriterT.run]
  · simp only [toWriterT, FreeM.liftM] at *
    rcases op
    simp only [run] at *
    rw [←ih PUnit.unit]
    congr

@[simp]
lemma run_pure {ω : Type u} [Monoid ω] {α} (a : α) :
    run (.pure a : FreeWriter ω α) = (a, 1) := rfl

@[simp]
lemma run_liftBind_tell {ω : Type u} [Monoid ω] {α} (w : ω) (k : PUnit → FreeWriter ω α) :
    run (liftBind (.tell w) k) = (let (a, w') := run (k .unit); (a, w * w')) := rfl

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
def listen {ω : Type u} [Monoid ω] {α : Type v} : FreeWriter ω α → FreeWriter ω (α × ω)
  | .pure a => .pure (a, 1)
  | .liftBind (.tell w) k =>
      liftBind (.tell w) fun _ =>
        listen (k .unit) >>= fun (a, w') =>
          pure (a, w * w')

@[simp]
lemma listen_pure {ω : Type u} [Monoid ω] {α} (a : α) :
    listen (.pure a : FreeWriter ω α) = .pure (a, 1) := rfl

@[simp]
lemma listen_liftBind_tell {ω : Type u} [Monoid ω] {α} (w : ω)
    (k : PUnit → FreeWriter ω α) :
    listen (liftBind (.tell w) k) =
      liftBind (.tell w) (fun _ =>
        listen (k .unit) >>= fun (a, w') =>
          pure (a, w * w')) := by
  rfl

/--
`pass` allows a subcomputation to modify its own log. After traversing the computation and
accumulating its log, the resulting function is applied to rewrite the accumulated log
before re-emission.
-/
def pass {ω : Type u} [Monoid ω] {α} (m : FreeWriter ω (α × (ω → ω))) : FreeWriter ω α :=
  let ((a, f), w) := run m
  liftBind (.tell (f w)) (fun _ => .pure a)

@[simp]
lemma pass_def {ω : Type u} [Monoid ω] {α} (m : FreeWriter ω (α × (ω → ω))) :
    pass m = let ((a, f), w) := run m; liftBind (.tell (f w)) fun _ => .pure a := rfl

instance {ω : Type u} [Monoid ω] : MonadWriter ω (FreeWriter ω) where
  tell := tell
  listen := listen
  pass := pass

/--
Evaluate a writer computation, returning the final result and discarding the log.
-/
def eval {ω : Type u} [Monoid ω] {α : Type v} (comp : FreeWriter ω α) : α :=
  (run comp).1

/--
Execute a writer computation, returning only the accumulated log and discarding the result.
-/
def exec {ω : Type u} {α : Type v} [Monoid ω] (comp : FreeWriter ω α) : ω :=
  (run comp).2

end FreeWriter

/-! ### Continuation Monad via `FreeM` -/

/-- Type constructor for continuation operations. -/
inductive ContF (r : Type u) (α : Type v) where
  /-- Call with current continuation: provides access to the current continuation. -/
  | callCC : ((α → r) → r) → ContF r α

instance {r : Type u} : Functor (ContF r) where
  map f
  | .callCC g => .callCC fun k => g (k ∘ f)

/-- Continuation monad via the `FreeM` monad. -/
abbrev FreeCont (r : Type u) := FreeM (ContF r)

namespace FreeCont

instance {r : Type u} : Monad (FreeCont r) := inferInstance
instance {r : Type u} : LawfulMonad (FreeCont r) := inferInstance

/-- Interpret `ContF r` operations into `ContT r Id`. -/
def contInterp {r : Type u} {α : Type v} : ContF r α → ContT r Id α
  | .callCC g, k => pure (g fun a => (k a).run)

/-- Convert a `FreeCont` computation into a `ContT` computation. This is the canonical
interpreter derived from `liftM`. -/
def toContT {r α : Type u} (comp : FreeCont r α) : ContT r Id α :=
  comp.liftM contInterp

/-- `toContT` is the unique interpreter extending `contInterp`. -/
theorem toContT_unique {r α : Type u} (g : FreeCont r α → ContT r Id α)
    (h : ExtendsHandler contInterp g) : g = toContT := (extendsHandler_iff contInterp g).mp h

/-- Run a continuation computation with the given continuation. -/
def run {r : Type u} {α : Type v} : FreeCont r α → (α → r) → r
  | .pure a, k => k a
  | .liftBind (.callCC g) cont, k => g (fun a => run (cont a) k)

/--
The canonical interpreter `toContT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeCont`.
-/
@[simp]
theorem toContT_eq_run {r α : Type u} (comp : FreeCont r α) (k : α → r) :
    toContT comp k = run comp k := by
  induction comp with
  | pure a => rfl
  | liftBind op cont ih =>
    simp only [toContT, FreeM.liftM]
    cases op
    simp only [run, bind]
    congr with x
    apply ih

@[simp]
lemma run_pure {r : Type u} {α : Type v} (a : α) (k : α → r) :
    run (.pure a : FreeCont r α) k = k a := rfl

@[simp]
lemma run_liftBind_callCC {r : Type u} {α β : Type v} (g : (α → r) → r)
    (cont : α → FreeCont r β) (k : β → r) :
    run (liftBind (.callCC g) cont) k = g (fun a => run (cont a) k) := rfl

/-- Call with current continuation for the Free continuation monad. -/
def callCC {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    FreeCont r α :=
  liftBind (.callCC fun k => run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k) pure

@[simp]
lemma callCC_def {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    callCC f =
    liftBind (.callCC fun k => run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k) pure :=
  rfl

instance {r : Type u} : MonadCont (FreeCont r) where
  callCC := .callCC

/-- `run` of a `callCC` node simplifies to running the handler with the current continuation. -/
@[simp]
lemma run_callCC {r : Type u} {α β : Type v}
    (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) (k : α → r) :
  run (callCC f) k = run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k := by
  simp [callCC, run_liftBind_callCC]

end FreeCont
end FreeM
