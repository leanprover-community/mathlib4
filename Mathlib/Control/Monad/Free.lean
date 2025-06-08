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

The `FreeM` monad generates a monad from any type constructor `f : Type → Type`, without requiring
`f` to be a `Functor`. This implementation uses the "freer monad" approach as the traditional
free monad is not safely definable in Lean due to termination checking.

In this construction, computations are represented as **trees of effects**. Each node (`liftBind`)
represents a request to perform an effect, accompanied by a continuation specifying how the
computation proceeds after the effect.
The leaves (`pure`) represent completed computations with final results.
To execute or interpret these computations, an interpreter walks this tree, handling effects
step-by-step.

See the Haskell [freer-simple](https://hackage.haskell.org/package/freer-simple) library for the
Haskell implementation that inspired this approach.

## Main Definitions

- `FreeM`: The free monad.
- `FreeState`: State monad using the `FreeM` construction.
- `FreeWriter`: Writer monad using the `FreeM` construction.
- `FreeCont`: Continuation monad using the `FreeM` construction.

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

/-- The `liftBind` constructor is semantically equivalent to `(lift op) >>= cont`. -/
lemma liftBind_eq_lift_bind {F : Type u → Type v} {ι : Type u} {α : Type u}
    (op : F ι) (cont : ι → FreeM F α) :
    FreeM.liftBind op cont = (lift op) >>= cont := by
    simp [lift, bind, FreeM.bind]

instance {F : Type u → Type v} : LawfulMonad (FreeM F) := by
  apply LawfulMonad.mk'
  · intro x y; induction' y with a b op cont ih'; all_goals {simp}
  · intro _ _ x f; simp only [bind, FreeM.bind]
  · intro _ _ _ x f g; induction' x with a b op cont ih;
    · simp only [bind, FreeM.bind]
    · simp only [bind, FreeM.bind, ih] at *; simp [ih]
  · intro _ _ x y; simp [Functor.map, Functor.mapConst]
  · intro _ _ x y; simp [bind, SeqLeft.seqLeft, Pure.pure]
  · intro _ _ x y; simp [bind, SeqRight.seqRight]
  · intro _ _ f x; induction' x with a b op cont ih;
    · simp [bind, FreeM.bind, Functor.map, Pure.pure, map]
    · simp only [Functor.map, bind, FreeM.bind, map, Pure.pure, map] at *; simp [ih]
  · intro _ _ f x; simp [bind, FreeM.bind, Functor.map, Seq.seq]

/-- Interpret a `FreeM f` computation into any monad `m` by providing an interpretation
function for the effect signature `f`. This is the key operation that makes free monads useful
for describing and then interpreting effectful computations. -/
@[simp]
protected def mapM {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u} :
    FreeM F α → ({β : Type u} → F β → M β) → M α
  | .pure a, _ => pure a
  | .liftBind op cont, interp => interp op >>= fun result => (cont result).mapM interp

@[simp]
lemma mapM_pure {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (a : α) :
    (FreeM.pure a : FreeM F α).mapM interp = pure a := by simp [FreeM.mapM]

@[simp]
lemma mapM_liftBind {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α β : Type u}
    (interp : {γ : Type u} → F γ → M γ) (op : F β) (cont : β → FreeM F α) :
    (FreeM.liftBind op cont).mapM interp = interp op >>=
    fun result => (cont result).mapM interp := by simp [FreeM.mapM]

lemma mapM_lift {F : Type u → Type v} {M : Type u → Type w} [Monad M] [LawfulMonad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (op : F α) :
    (lift op).mapM interp = interp op := by
  simp [lift, FreeM.mapM]

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

@[simp]
lemma bind_pure {F : Type u → Type v} {α β : Type u} (a : α) (f : α → FreeM F β) :
    (FreeM.pure a >>= f) = f a := by simp [bind, FreeM.bind]

@[simp]
lemma bind_liftBind {F : Type u → Type v} {α β γ : Type u} (op : F α) (cont : α → FreeM F β)
(f : β → FreeM F γ) :
    (FreeM.liftBind op cont >>= f) = FreeM.liftBind op (fun x => cont x >>= f) := by
    simp [bind, FreeM.bind]

@[simp]
lemma map_pure {F : Type u → Type v} {α β : Type u} (f : α → β) (a : α) :
    (f <$> FreeM.pure a : FreeM F β) = FreeM.pure (f a) := by
    simp [Functor.map, map]

@[simp]
lemma map_liftBind {F : Type u → Type v} {α β γ : Type u} (f : β → γ) (op : F α)
(cont : α → FreeM F β) :
    (f <$> FreeM.liftBind op cont : FreeM F γ) = FreeM.liftBind op (fun x => f <$> cont x)
    := by simp [Functor.map, map]

/-- Run a state computation, returning both the result and final state. -/
def runState {σ : Type u} {α : Type v} (comp : FreeState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .liftBind StateF.get k     => runState (k s₀) s₀
  | .liftBind (StateF.set s') k => runState (k PUnit.unit) s'

@[simp]
lemma runState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    runState (.pure a : FreeState σ α) s₀ = (a, s₀) := by simp [runState]

@[simp]
lemma runState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    runState (.liftBind StateF.get k) s₀ = runState (k s₀) s₀ := by simp [runState]

@[simp]
lemma runState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    runState (.liftBind (StateF.set s') k) s₀ = runState (k PUnit.unit) s' := by simp [runState]

/-- Run a state computation, returning only the result. -/
@[simp]
def evalState {σ : Type u} {α : Type v} (c : FreeState σ α) (s₀ : σ) : α :=
  (runState c s₀).1

lemma evalState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    evalState (.pure a : FreeState σ α) s₀ = a := by simp [evalState]

lemma evalState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    evalState (.liftBind StateF.get k) s₀ = evalState (k s₀) s₀ := by simp [evalState]

lemma evalState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    evalState (.liftBind (StateF.set s') k) s₀ = evalState (k PUnit.unit) s' := by simp [evalState]

/-- Run a state computation, returning only the final state. -/
@[simp]
def execState {σ : Type u} {α : Type v} (c : FreeState σ α) (s₀ : σ) : σ :=
  (runState c s₀).2

lemma execState_pure {σ : Type u} {α : Type v} (a : α) (s₀ : σ) :
    execState (.pure a : FreeState σ α) s₀ = s₀ := by simp [execState]

lemma execState_get {σ : Type u} {α : Type v} (k : σ → FreeState σ α) (s₀ : σ) :
    execState (.liftBind StateF.get k) s₀ = execState (k s₀) s₀ := by simp [execState]

lemma execState_set {σ : Type u} {α : Type v} (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    execState (.liftBind (StateF.set s') k) s₀ = execState (k PUnit.unit) s' := by simp [execState]

/-- Interpret `StateF` operations into `StateM`. -/
def stateInterp {σ : Type u} : {α : Type u} → StateF σ α → StateM σ α
  | _, StateF.get => MonadStateOf.get
  | _, StateF.set s => MonadStateOf.set s

/-- Convert a `FreeState` computation into a `StateM` computation. -/
def toStateM {σ α : Type u} (comp : FreeState σ α) : StateM σ α :=
  comp.mapM stateInterp

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

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
@[simp]
def tell {ω : Type u} (w : ω) : FreeWriter ω PUnit :=
  FreeM.lift (WriterF.tell w)

/--
Interprets a `FreeWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
@[simp]
def run {ω : Type u} [Monoid ω] {α} : FreeWriter ω α → α × ω
  | .pure a => (a, 1)
  | .liftBind (WriterF.tell w) k =>
      let (a, w') := run (k PUnit.unit)
      (a, w * w')

lemma run_lift_tell {ω : Type u} [Monoid ω] (w : ω) :
    run (FreeM.lift (WriterF.tell w) : FreeWriter ω PUnit) = (PUnit.unit, w) := by
  simp

lemma run_tell_pure {ω : Type u} [Monoid ω] {α} (w : ω) (a : α) :
    run (FreeWriter.tell w >>= fun _ => FreeM.pure a) = (a, w) := by
  simp

lemma run_tell_bind {ω : Type u} [Monoid ω] {α} (w : ω) (k : FreeWriter ω α) :
    run (FreeM.lift (WriterF.tell w) >>= fun _ => k) =
    let (a, w') := run k
    (a, w * w') := by
  simp

lemma run_tell_return {ω : Type u} [Monoid ω] {α} (w : ω) (a : α) :
    run (FreeWriter.tell w >>= fun _ => FreeM.pure a) = (a, w) := by
  simp

lemma run_tell_map {ω : Type u} [Monoid ω] {α} (w : ω) (f : PUnit → α) :
    run (f <$> FreeWriter.tell w) = (f PUnit.unit, w) := by
  simp

lemma run_tell_tell_return {ω : Type u} [Monoid ω] {α} (w1 w2 : ω) (a : α) :
    run (FreeWriter.tell w1 >>= fun _ => FreeWriter.tell w2 >>= fun _ => FreeM.pure a) =
    (a, w1 * w2) := by
  simp

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
@[simp]
def listen {ω : Type u} [Monoid ω] {α : Type v} : FreeWriter ω α → FreeWriter ω (α × ω)
  | .pure a => .pure (a, 1)
  | .liftBind (WriterF.tell w) k =>
      FreeM.liftBind (WriterF.tell w) fun _ =>
        listen (k PUnit.unit) >>= fun (a, w') =>
          pure (a, w * w')

/--
`pass` allows a subcomputation to modify its own log. After traversing the computation and
accumulating its log, the resulting function is applied to rewrite the accumulated log
before re-emission.
-/
@[simp]
def pass {ω : Type u} [Monoid ω] {α} (m : FreeWriter ω (α × (ω → ω))) : FreeWriter ω α :=
  let ((a, f), w) := run m
  FreeM.liftBind (WriterF.tell (f w)) (fun _ => .pure a)

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

/-- Interpret `WriterF` operations into `WriterT`. -/
def writerInterp {ω : Type u} : {α : Type u} → WriterF ω α → WriterT ω Id α
  | _, WriterF.tell w => MonadWriter.tell w

/-- Convert a `FreeWriter` computation into a `WriterT` computation. -/
def toWriterT {ω α : Type u} [Monoid ω] (comp : FreeWriter ω α) : WriterT ω Id α :=
  comp.mapM writerInterp

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

/-- Run a continuation computation with the given continuation. -/
@[simp]
def run {r : Type u} {α : Type v} : FreeCont r α → (α → r) → r
  | .pure a, k => k a
  | .liftBind (ContF.callCC g) cont, k => g (fun a => run (cont a) k)

lemma run_callCC {r : Type u} {α β : Type v} (g : (α → r) → r)
(cont : α → FreeCont r β) (k : β → r) :
    run (.liftBind (ContF.callCC g) cont) k = g (fun a => run (cont a) k) := by simp

/-- Call with current continuation for the Free continuation monad. -/
@[simp]
def callCC {r : Type u} {α β : Type v} (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
FreeCont r α :=
  FreeM.liftBind (ContF.callCC (fun k =>
    run (f ⟨fun x => FreeM.liftBind (ContF.callCC (fun _ => k x)) FreeM.pure⟩) k
  )) FreeM.pure

instance {r : Type u} : MonadCont (FreeCont r) where
  callCC := FreeCont.callCC

lemma run_map_callCC_apply {α β : Type v} (f : α → β) (a : α) :
    run (f <$> FreeCont.callCC (fun k => k.apply a)) id = f a := by
  simp

/-- Interpret `ContF r` operations into `ContT r Id`. -/
def contInterp {r : Type u} : {α : Type u} → ContF r α → ContT r Id α
  | _, ContF.callCC g => fun k => g (fun a => k a)

/-- Convert a `FreeCont` computation into a `ContT` computation. -/
def toContT {r α : Type u} (comp : FreeCont r α) : ContT r Id α :=
  comp.mapM contInterp

end FreeCont

end FreeM
