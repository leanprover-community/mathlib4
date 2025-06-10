/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Control.Monad.Writer
import Mathlib.Control.Monad.Cont
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
in `M` that respects the effect semantics given by `f`. This unique interpreter is `mapM f`, which
acts as the canonical **fold** (catamorphism) for free monads.

## Implementation

To execute or interpret these computations, we provide two approaches:
1. **Hand-written interpreters** (`FreeState.run`, `FreeWriter.run`, `FreeCont.run`) that directly
pattern-match on the tree structure
2. **Canonical interpreters** (`FreeState.toStateM`, `FreeWriter.toWriterT`, `FreeCont.toContT`)
derived from the universal property via `mapM`

We prove that these approaches are equivalent, demonstrating that the implementation aligns with
the theory. We also provide uniqueness theorems for the canonical interpreters, which follow from
the universal property.

## Main Definitions

- `FreeM`: The free monad construction
- `mapM`: The canonical fold/interpreter satisfying the universal property
- `FreeState`, `FreeWriter`, `FreeCont`: Specific effect monads with both hand-written and
canonical interpreters
- `mapM_unique`: Proof of the universal property

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

* [Kiselyov2015] Oleg Kiselyov, Hiromi Ishii. *Freer Monads, More Extensible Effects*.
  Haskell Symposium 2015.
* [MilewskiDao] Bartosz Milewski. *The Dao of Functional Programming*. 2025.

## Tags

Free monad, state monad, writer monad, continuation monad
-/

/-- The Free monad over a type constructor `f`.

A `FreeM f a` is a tree of operations from the type constructor `f`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for
representing an operation from `f` followed by a continuation.

This construction provides a free monad for any type constructor `f`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional Free monad,
this does not require `f` to be a functor. -/
inductive FreeM.{u, v, w} (f : Type u → Type v) (α : Type w) where
  | protected pure : α → FreeM f α
  | liftBind {ι : Type u} (op : f ι) (cont : ι → FreeM f α) : FreeM f α

universe u v w

namespace FreeM

/-- Map a function over a `FreeM` monad. -/
def map {α β : Type _} (F : Type u → Type v) (f : α → β) : FreeM F α → FreeM F β :=
fun FFa =>
  match FFa with
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op (fun z => FreeM.map F f (cont z))

instance {F : Type u → Type v} : Functor (FreeM F) where
  map := FreeM.map F

instance {F : Type u → Type v} : LawfulFunctor (FreeM F) where
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
    case pure a => simp [FreeM.map]
    case liftBind op cont ih => simp [FreeM.map, ih]

/-- Bind operation for the `FreeM` monad. -/
protected def bind {a b : Type _} (F : Type u → Type v) (x : FreeM F a) (f : a → FreeM F b) :
FreeM F b :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op (fun z => FreeM.bind F (cont z) f)

/-- Lift an operation from the effect signature `f` into the `FreeM f` monad. -/
@[simp]
def lift {F : Type u → Type v} {ι : Type u} (op : F ι) : FreeM F ι :=
  FreeM.liftBind op FreeM.pure

instance {F : Type u → Type v} : Monad (FreeM F) where
  pure := FreeM.pure
  bind := FreeM.bind F

@[simp]
lemma pure_eq_pure {F : Type u → Type v} {α : Type w} (a : α) :
    (FreeM.pure a : FreeM F α) = pure a := rfl

/-- The `liftBind` constructor is semantically equivalent to `(lift op) >>= cont`. -/
lemma liftBind_eq_lift_bind {F : Type u → Type v} {ι : Type u} {α : Type u}
    (op : F ι) (cont : ι → FreeM F α) :
    FreeM.liftBind op cont = (lift op) >>= cont := by
    simp [lift, bind, FreeM.bind]

instance {F : Type u → Type v} : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := by {
    intro _ _ f x;
    induction' x with a b op cont ih
    · simp only [bind, FreeM.bind, Functor.map, Pure.pure, map]
    · simp only [Functor.map, bind, FreeM.bind, map, Pure.pure, map] at *; simp only [ih]
  })
  (id_map := by intro x y; induction' y with a b op cont ih'; all_goals {simp})
  (pure_bind := by
    intro α β x f
    simp [bind, FreeM.bind])
  (bind_assoc := by
    intro _ _ _ x f g; induction' x with a b op cont ih;
    · simp only [bind, FreeM.bind]
    · simp only [bind, FreeM.bind, ih] at *; simp [ih])


/--
Interpret a `FreeM f` computation into any monad `m` by providing an interpretation
function for the effect signature `f`.

This function defines the *canonical interpreter* (also known as a *fold* or *catamorphism*)
from the free monad `FreeM f` into the target monad `m`. It is the unique monad morphism that
extends the effect handler `interp : ∀ {β}, F β → M β` via the universal property of `FreeM` -/

protected def mapM {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u} :
    FreeM F α → ({β : Type u} → F β → M β) → M α
  | .pure a, _ => pure a
  | .liftBind op cont, interp => interp op >>= fun result => (cont result).mapM interp

@[simp]
lemma mapM_pure {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (a : α) :
    (pure a : FreeM F α).mapM interp = pure a := by simp [FreeM.mapM]

@[simp]
lemma mapM_liftBind {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α β : Type u}
    (interp : {γ : Type u} → F γ → M γ) (op : F β) (cont : β → FreeM F α) :
    (FreeM.liftBind op cont).mapM interp = interp op >>=
    fun result => (cont result).mapM interp := by simp [FreeM.mapM]

lemma mapM_lift {F : Type u → Type v} {M : Type u → Type w} [Monad M] [LawfulMonad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (op : F α) :
    (lift op).mapM interp = interp op := by
  simp [FreeM.mapM, lift]

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
def ExtendsHandler
    {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u}
    (f : {ι : Type u} → F ι → M ι)
    (g : FreeM F α → M α) : Prop :=
  (∀ a, g (pure a) = pure a) ∧
  (∀ {ι} (op : F ι) (k : ι → FreeM F α),
    g (FreeM.liftBind op k) = f op >>= fun x => g (k x))

/--
The universal property of the free monad `FreeM`. That is, `mapM f` is the unique interpreter that
extends the effect handler `f` to interpret `FreeM F` computations in monad `M`.
-/
theorem extendsHandler_iff
{F : Type u → Type v} {m : Type u → Type w} [Monad m] {α : Type u}
    (f : {ι : Type u} → F ι → m ι)
    (g : FreeM F α → m α) :
    ExtendsHandler f g ↔ g = (·.mapM f) := by
  constructor
  · intro h
    apply funext
    intro x
    induction' x with a b op cont ih
    · simp only [FreeM.mapM]
      exact h.1 a
    · simp only [FreeM.mapM]
      rw [h.2]
      congr 1
      ext x
      apply ih x
  · intro h
    constructor
    · intro a
      simp [h]
    · intro ι op k
      simp only [FreeM.mapM, bind, FreeM.bind]
      rw [h]
      congr 1

/-! ### State Monad via `FreeM` -/

/-- Type constructor for state operations. -/
inductive StateF (σ : Type u) : Type u → Type _ where
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
  get := FreeM.lift StateF.get
  set newState := FreeM.liftBind (StateF.set newState) (fun _ => FreeM.pure PUnit.unit)
  modifyGet f :=
    FreeM.liftBind StateF.get (fun s =>
      let (a, s') := f s
      FreeM.liftBind (StateF.set s') (fun _ => FreeM.pure a))

@[simp]
lemma get_def {σ : Type u} : (get : FreeState σ σ) = FreeM.lift StateF.get := by
simp [get, getThe, MonadStateOf.get]

@[simp]
lemma set_def {σ : Type u} (s : σ) : (set s : FreeState σ PUnit) =
    FreeM.liftBind (StateF.set s) (fun _ => FreeM.pure PUnit.unit) := by
    simp [set, MonadStateOf.set]

instance {σ : Type u} : MonadState σ (FreeState σ) := inferInstance

lemma bind_pure {F : Type u → Type v} {α β : Type u} (a : α) (f : α → FreeM F β) :
    (pure a >>= f) = f a := by simp only [pure_bind]

@[simp]
lemma bind_liftBind {F : Type u → Type v} {α β γ : Type u} (op : F α) (cont : α → FreeM F β)
(f : β → FreeM F γ) :
    (FreeM.liftBind op cont >>= f) = FreeM.liftBind op (fun x => cont x >>= f) := by
    simp [bind, FreeM.bind]

lemma map_pure {F : Type u → Type v} {α β : Type u} (f : α → β) (a : α) :
    (f <$> pure a : FreeM F β) = FreeM.pure (f a) := by
    simp [Functor.map, map]

@[simp]
lemma map_liftBind {F : Type u → Type v} {α β γ : Type u} (f : β → γ) (op : F α)
(cont : α → FreeM F β) :
    (f <$> FreeM.liftBind op cont : FreeM F γ) = FreeM.liftBind op (fun x => f <$> cont x)
    := by simp [Functor.map, map]

/-- Interpret `StateF` operations into `StateM`. -/
def stateInterp {σ : Type u} : {α : Type u} → StateF σ α → StateM σ α
  | _, StateF.get => MonadStateOf.get
  | _, StateF.set s => MonadStateOf.set s

/-- Convert a `FreeState` computation into a `StateM` computation. This is the canonical
interpreter derived from `mapM`. -/
def toStateM {σ α : Type u} (comp : FreeState σ α) : StateM σ α :=
  comp.mapM stateInterp

/-- `toStateM` is the unique interpreter extending `stateInterp`. -/
theorem toStateM_unique {σ α : Type u} (g : FreeState σ α → StateM σ α)
    (h : ExtendsHandler stateInterp g) : g = toStateM := (extendsHandler_iff stateInterp g).mp h

/-- Run a state computation, returning both the result and final state. -/
def run {σ : Type u} {α : Type v} (comp : FreeState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .liftBind StateF.get k     => run (k s₀) s₀
  | .liftBind (StateF.set s') k => run (k PUnit.unit) s'

/--
The canonical interpreter `toStateM` derived from `mapM` agrees with the hand-written
recursive interpreter `run` for `FreeState`.
-/
@[simp]
theorem toStateM_eq_run {σ α : Type u} (comp : FreeState σ α) (s₀ : σ) :
    toStateM comp s₀ = run comp s₀ := by
  induction' comp with a b op cont ih generalizing s₀
  · simp [toStateM, FreeM.mapM, pure, run, StateT.pure]
  · simp only [run, FreeM.mapM, stateInterp] at *
    rcases op
    · simp only [MonadStateOf.get, bind, StateT.bind, StateT.get, run] at *
      apply ih
    · simp only [MonadStateOf.set, bind, StateT.bind, StateT.set, run, PUnit.unit] at *
      apply ih

@[simp]
lemma run_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    run (pure a : FreeState σ α) s₀ = (a, s₀) := by simp [run]

@[simp]
lemma run_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    run (.liftBind StateF.get k) s₀ = run (k s₀) s₀ := by simp [run]

@[simp]
lemma run_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    run (.liftBind (StateF.set s') k) s₀ = run (k PUnit.unit) s' := by simp [run]

/-- Run a state computation, returning only the result. -/
def evalState {σ : Type u} {α : Type v} (c : FreeState σ α) (s₀ : σ) : α :=
  (run c s₀).1

@[simp]
lemma evalState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    evalState (pure a : FreeState σ α) s₀ = a := by simp [evalState]

@[simp]
lemma evalState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    evalState (.liftBind StateF.get k) s₀ = evalState (k s₀) s₀ := by simp [evalState]

@[simp]
lemma evalState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    evalState (.liftBind (StateF.set s') k) s₀ = evalState (k PUnit.unit) s' := by simp [evalState]

/-- Run a state computation, returning only the final state. -/
def execState {σ : Type u} {α : Type v} (c : FreeState σ α) (s₀ : σ) : σ :=
  (run c s₀).2

@[simp]
lemma execState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    execState (pure a : FreeState σ α) s₀ = s₀ := by simp [execState]

@[simp]
lemma execState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    execState (.liftBind StateF.get k) s₀ = execState (k s₀) s₀ := by simp [execState]

@[simp]
lemma execState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    execState (.liftBind (StateF.set s') k) s₀ = execState (k PUnit.unit) s' := by simp [execState]


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
  | _, WriterF.tell w => MonadWriter.tell w

/-- Convert a `FreeWriter` computation into a `WriterT` computation. This is the canonical
interpreter derived from `mapM`. -/
def toWriterT {ω α : Type u} [Monoid ω] (comp : FreeWriter ω α) : WriterT ω Id α :=
  comp.mapM writerInterp

/-- `toWriterT` is the unique interpreter extending `writerInterp`. -/
theorem toWriterT_unique {ω α : Type u} [Monoid ω] (g : FreeWriter ω α → WriterT ω Id α)
    (h : ExtendsHandler writerInterp g) : g = toWriterT := (extendsHandler_iff writerInterp g).mp h

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
def tell {ω : Type u} (w : ω) : FreeWriter ω PUnit :=
  FreeM.lift (WriterF.tell w)

@[simp]
lemma tell_def {ω : Type u} (w : ω) :
    tell w = FreeM.lift (WriterF.tell w) := by simp [tell]

/--
Interprets a `FreeWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
def run {ω : Type u} [Monoid ω] {α} : FreeWriter ω α → α × ω
  | .pure a => (a, 1)
  | .liftBind (WriterF.tell w) k =>
      let (a, w') := run (k PUnit.unit)
      (a, w * w')

/--
The canonical interpreter `toWriterT` derived from `mapM` agrees with the hand-written
recursive interpreter `run` for `FreeWriter`.
-/
@[simp]
theorem toWriterT_eq_run {ω : Type u} [Monoid ω] {α} (comp : FreeWriter ω α) :
    toWriterT comp = run comp := by
  induction' comp with a b op cont ih
  · simp only [toWriterT, FreeM.mapM, pure, run, WriterT.run]
  · simp only [toWriterT, FreeM.mapM] at *
    rcases op
    · simp only [run] at *
      rw [←ih PUnit.unit]
      congr

@[simp]
lemma run_pure {ω : Type u} [Monoid ω] {α} (a : α) :
    run (pure a : FreeWriter ω α) = (a, 1) := by simp [run]

@[simp]
lemma run_liftBind_tell {ω : Type u} [Monoid ω] {α} (w : ω) (k : PUnit → FreeWriter ω α) :
    run (.liftBind (WriterF.tell w) k) =
    let (a, w') := run (k PUnit.unit)
    (a, w * w') := by simp [run]

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
def listen {ω : Type u} [Monoid ω] {α : Type v} : FreeWriter ω α → FreeWriter ω (α × ω)
  | .pure a => .pure (a, 1)
  | .liftBind (WriterF.tell w) k =>
      FreeM.liftBind (WriterF.tell w) fun _ =>
        listen (k PUnit.unit) >>= fun (a, w') =>
          pure (a, w * w')

@[simp]
lemma listen_pure {ω : Type u} [Monoid ω] {α} (a : α) :
    listen (pure a : FreeWriter ω α) = .pure (a, 1) := by simp [listen]

@[simp]
lemma listen_liftBind_tell {ω : Type u} [Monoid ω] {α} (w : ω)
    (k : PUnit → FreeWriter ω α) :
    listen (.liftBind (WriterF.tell w) k) =
      FreeM.liftBind (WriterF.tell w) (fun _ =>
        listen (k PUnit.unit) >>= fun (a, w') =>
          pure (a, w * w')) := by
  simp [listen]

/--
`pass` allows a subcomputation to modify its own log. After traversing the computation and
accumulating its log, the resulting function is applied to rewrite the accumulated log
before re-emission.
-/
def pass {ω : Type u} [Monoid ω] {α} (m : FreeWriter ω (α × (ω → ω))) : FreeWriter ω α :=
  let ((a, f), w) := run m
  FreeM.liftBind (WriterF.tell (f w)) (fun _ => .pure a)

@[simp]
lemma pass_def {ω : Type u} [Monoid ω] {α} (m : FreeWriter ω (α × (ω → ω))) :
    pass m =
    let ((a, f), w) := run m
    FreeM.liftBind (WriterF.tell (f w)) (fun _ => .pure a) := by simp [pass]

instance {ω : Type u} [Monoid ω] : MonadWriter ω (FreeWriter ω) where
  tell w := FreeM.liftBind (WriterF.tell w) (fun _ => .pure PUnit.unit)
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
  | .callCC g => .callCC (fun k => g (k ∘ f))

/-- Continuation monad via the `FreeM` monad. -/
abbrev FreeCont (r : Type u) := FreeM (ContF r)

namespace FreeCont

instance {r : Type u} : Monad (FreeCont r) := inferInstance
instance {r : Type u} : LawfulMonad (FreeCont r) := inferInstance

/-- Interpret `ContF r` operations into `ContT r Id`. -/
def contInterp {r : Type u} {α : Type v} : ContF r α → ContT r Id α
  | ContF.callCC g => fun k => g (fun a => k a)

/-- Convert a `FreeCont` computation into a `ContT` computation. This is the canonical
interpreter derived from `mapM`. -/
def toContT {r α : Type u} (comp : FreeCont r α) : ContT r Id α :=
  comp.mapM contInterp

/-- `toContT` is the unique interpreter extending `contInterp`. -/
theorem toContT_unique {r α : Type u} (g : FreeCont r α → ContT r Id α)
    (h : ExtendsHandler contInterp g) : g = toContT := (extendsHandler_iff contInterp g).mp h

/-- Run a continuation computation with the given continuation. -/
def run {r : Type u} {α : Type v} : FreeCont r α → (α → r) → r
  | .pure a, k => k a
  | .liftBind (ContF.callCC g) cont, k => g (fun a => run (cont a) k)

/--
The canonical interpreter `toContT` derived from `mapM` agrees with the hand-written
recursive interpreter `run` for `FreeCont`.
-/
@[simp]
theorem toContT_eq_run {r α : Type u} (comp : FreeCont r α) (k : α → r) :
    toContT comp k = run comp k := by
  induction' comp with a b op cont ih
  · simp [toContT, FreeM.mapM, pure, run]
  · simp only [toContT, FreeM.mapM] at *
    rcases op
    · simp only [run, bind] at *
      congr
      funext x
      apply ih

@[simp]
lemma run_pure {r : Type u} {α : Type v} (a : α) (k : α → r) :
    run (pure a : FreeCont r α) k = k a := by simp [run]

@[simp]
lemma run_liftBind_callCC {r : Type u} {α β : Type v} (g : (α → r) → r)
(cont : α → FreeCont r β) (k : β → r) :
    run (.liftBind (ContF.callCC g) cont) k = g (fun a => run (cont a) k) := by simp [run]

/-- Call with current continuation for the Free continuation monad. -/
def callCC {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
FreeCont r α :=
  FreeM.liftBind (ContF.callCC (fun k =>
    run (f ⟨fun x => FreeM.liftBind (ContF.callCC (fun _ => k x)) FreeM.pure⟩) k
  )) FreeM.pure

@[simp]
lemma callCC_def {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    callCC f =
    FreeM.liftBind (ContF.callCC (fun k =>
      run (f ⟨fun x => FreeM.liftBind (ContF.callCC (fun _ => k x)) FreeM.pure⟩) k
    )) FreeM.pure := by simp [callCC]

instance {r : Type u} : MonadCont (FreeCont r) where
  callCC := FreeCont.callCC

end FreeCont

attribute [nolint simpNF] pure.sizeOf_spec pure.injEq

end FreeM
