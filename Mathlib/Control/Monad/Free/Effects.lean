/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Control.Monad.Free
import Mathlib.Control.Monad.Writer

/-!
# Free Monad

This file defines several canonical instances on the free monad.

## Main definitions

- `FreeState`, `FreeWriter`, `FreeCont`: Specific effect monads with both hand-written and
  canonical interpreters

## Implementation

To execute or interpret these computations, we provide two approaches:
1. **Hand-written interpreters** (`FreeState.run`, `FreeWriter.run`, `FreeCont.run`) that directly
  pattern-match on the tree structure
2. **Canonical interpreters** (`FreeState.toStateM`, `FreeWriter.toWriterT`, `FreeCont.toContT`)
  derived from the universal property via `liftM`

We prove that these approaches are equivalent, demonstrating that the implementation aligns with
the theory. We also provide uniqueness theorems for the canonical interpreters, which follow from
the universal property.

## Tags

Free monad, state monad, writer monad, continuation monad
-/

namespace FreeM
universe u v w w' w''

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
variable {σ : Type u} {α : Type v}

instance : Monad (FreeState σ) := inferInstance
instance : LawfulMonad (FreeState σ) := inferInstance

instance : MonadStateOf σ (FreeState σ) where
  get := .lift .get
  set newState := .liftBind (.set newState) (fun _ => .pure PUnit.unit)
  modifyGet f :=
    .liftBind .get (fun s =>
      let (a, s') := f s
      .liftBind (.set s') (fun _ => .pure a))

@[simp]
lemma get_def : (get : FreeState σ σ) = .lift .get := rfl

@[simp]
lemma set_def (s : σ) : (set s : FreeState σ PUnit) = .lift (.set s) := rfl

instance : MonadState σ (FreeState σ) := inferInstance

/-- Interpret `StateF` operations into `StateM`. -/
def stateInterp {α : Type u} : StateF σ α → StateM σ α
  | .get => MonadStateOf.get
  | .set s => MonadStateOf.set s

/-- Convert a `FreeState` computation into a `StateM` computation. This is the canonical
interpreter derived from `liftM`. -/
def toStateM {α : Type u} (comp : FreeState σ α) : StateM σ α :=
  comp.liftM stateInterp

/-- `toStateM` is the unique interpreter extending `stateInterp`. -/
theorem toStateM_unique {α : Type u} (g : FreeState σ α → StateM σ α)
    (h : Interprets stateInterp g) : g = toStateM := h.eq

/-- Run a state computation, returning both the result and final state. -/
def run (comp : FreeState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .liftBind StateF.get k => run (k s₀) s₀
  | .liftBind (StateF.set s') k => run (k PUnit.unit) s'

/--
The canonical interpreter `toStateM` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeState`.
-/
@[simp]
theorem run_toStateM {α : Type u} (comp : FreeState σ α) :
    (toStateM comp).run = run comp := by
  ext s₀ : 1
  induction comp generalizing s₀ with
  | pure a => rfl
  | liftBind op cont ih =>
    cases op <;> apply ih

@[simp]
lemma run_pure (a : α) (s₀ : σ) :
    run (.pure a : FreeState σ α) s₀ = (a, s₀) := rfl

@[simp]
lemma run_get (k : σ → FreeState σ α) (s₀ : σ) :
    run (liftBind .get k) s₀ = run (k s₀) s₀ := rfl

@[simp]
lemma run_set (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    run (liftBind (.set s') k) s₀ = run (k .unit) s' := rfl

/-- Run a state computation, returning only the result. -/
def run' (c : FreeState σ α) (s₀ : σ) : α := (run c s₀).1

@[simp]
theorem run'_toStateM {α : Type u} (comp : FreeState σ α) :
    (toStateM comp).run' = run' comp := by
  ext s₀ : 1
  rw [run', ← run_toStateM]
  rfl

@[simp]
lemma run'_pure (a : α) (s₀ : σ) :
    run' (.pure a : FreeState σ α) s₀ = a := rfl

@[simp]
lemma run'_get (k : σ → FreeState σ α) (s₀ : σ) :
    run' (liftBind .get k) s₀ = run' (k s₀) s₀ := rfl

@[simp]
lemma run'_set (s' : σ) (k : PUnit → FreeState σ α) (s₀ : σ) :
    run' (liftBind (.set s') k) s₀ = run' (k .unit) s' := rfl

end FreeState

/-! ### Writer Monad via `FreeM` -/

/--
Type constructor for writer operations. Writer has a single effect, so the definition has just one
constructor.
-/
inductive WriterF (ω : Type u) : Type v → Type u
  /-- Write a value to the log. -/
  | tell : ω → WriterF ω PUnit

/-- Writer monad implemented via the `FreeM` monad construction. This provides a more efficient
implementation than the traditional `WriterT` transformer, as it avoids buffering the log. -/
abbrev FreeWriter (ω : Type u) := FreeM (WriterF ω)

namespace FreeWriter

open WriterF
variable {ω : Type u} {α : Type v}

instance : Monad (FreeWriter ω) := inferInstance
instance : LawfulMonad (FreeWriter ω) := inferInstance

/-- Interpret `WriterF` operations into `WriterT`. -/
def writerInterp {α : Type u} : WriterF ω α → WriterT ω Id α
  | .tell w => MonadWriter.tell w

/-- Convert a `FreeWriter` computation into a `WriterT` computation. This is the canonical
interpreter derived from `liftM`. -/
def toWriterT {α : Type u} [Monoid ω] (comp : FreeWriter ω α) : WriterT ω Id α :=
  comp.liftM writerInterp

/-- `toWriterT` is the unique interpreter extending `writerInterp`. -/
theorem toWriterT_unique {α : Type u} [Monoid ω] (g : FreeWriter ω α → WriterT ω Id α)
    (h : Interprets writerInterp g) : g = toWriterT := h.eq

/--
Writes a log entry. This creates an effectful node in the computation tree.
-/
abbrev tell (w : ω) : FreeWriter ω PUnit :=
  lift (.tell w)

@[simp]
lemma tell_def (w : ω) :
    tell w = .lift (.tell w) := rfl

/--
Interprets a `FreeWriter` computation by recursively traversing the tree, accumulating
log entries with the monoid operation, and returns the final value paired with the accumulated log.
-/
def run [Monoid ω] : FreeWriter ω α → α × ω
  | .pure a => (a, 1)
  | .liftBind (.tell w) k =>
      let (a, w') := run (k .unit)
      (a, w * w')

@[simp]
lemma run_pure [Monoid ω] (a : α) :
    run (.pure a : FreeWriter ω α) = (a, 1) := rfl

@[simp]
lemma run_liftBind_tell [Monoid ω] (w : ω) (k : PUnit → FreeWriter ω α) :
    run (liftBind (.tell w) k) = (let (a, w') := run (k .unit); (a, w * w')) := rfl

/--
The canonical interpreter `toWriterT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeWriter`.
-/
@[simp]
theorem run_toWriterT {α: Type u} [Monoid ω] :
    ∀ comp : FreeWriter ω α, (toWriterT comp).run = run comp
  | .pure _ => by simp only [toWriterT, liftM_pure, run_pure, pure, WriterT.run]
  | liftBind (.tell w) cont => by
    simp only [toWriterT, liftM_liftBind, run_liftBind_tell] at *
    rw [← run_toWriterT]
    congr

/--
`listen` captures the log produced by a subcomputation incrementally. It traverses the computation,
emitting log entries as encountered, and returns the accumulated log as a result.
-/
def listen [Monoid ω] : FreeWriter ω α → FreeWriter ω (α × ω)
  | .pure a => .pure (a, 1)
  | .liftBind (.tell w) k =>
      liftBind (.tell w) fun _ =>
        listen (k .unit) >>= fun (a, w') =>
          pure (a, w * w')

@[simp]
lemma listen_pure [Monoid ω] (a : α) :
    listen (.pure a : FreeWriter ω α) = .pure (a, 1) := rfl

@[simp]
lemma listen_liftBind_tell [Monoid ω] (w : ω)
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
def pass [Monoid ω] (m : FreeWriter ω (α × (ω → ω))) : FreeWriter ω α :=
  let ((a, f), w) := run m
  liftBind (.tell (f w)) (fun _ => .pure a)

@[simp]
lemma pass_def [Monoid ω] (m : FreeWriter ω (α × (ω → ω))) :
    pass m = let ((a, f), w) := run m; liftBind (.tell (f w)) fun _ => .pure a := rfl

instance [Monoid ω] : MonadWriter ω (FreeWriter ω) where
  tell := tell
  listen := listen
  pass := pass

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
variable {r : Type u} {α : Type v} {β : Type w}

instance : Monad (FreeCont r) := inferInstance
instance : LawfulMonad (FreeCont r) := inferInstance

/-- Interpret `ContF r` operations into `ContT r Id`. -/
def contInterp : ContF r α → ContT r Id α
  | .callCC g, k => pure (g fun a => (k a).run)

/-- Convert a `FreeCont` computation into a `ContT` computation. This is the canonical
interpreter derived from `liftM`. -/
def toContT {α : Type u} (comp : FreeCont r α) : ContT r Id α :=
  comp.liftM contInterp

/-- `toContT` is the unique interpreter extending `contInterp`. -/
theorem toContT_unique {α : Type u} (g : FreeCont r α → ContT r Id α)
    (h : Interprets contInterp g) : g = toContT := h.eq

/-- Run a continuation computation with the given continuation. -/
def run : FreeCont r α → (α → r) → r
  | .pure a, k => k a
  | .liftBind (.callCC g) cont, k => g (fun a => run (cont a) k)

/--
The canonical interpreter `toContT` derived from `liftM` agrees with the hand-written
recursive interpreter `run` for `FreeCont`.
-/
@[simp]
theorem run_toContT {α : Type u} (comp : FreeCont r α) :
    (toContT comp).run = run comp := by
  ext k
  induction comp with
  | pure a => rfl
  | liftBind op cont ih =>
    simp only [toContT, FreeM.liftM]
    cases op
    simp only [run, bind, ContT.run, id]
    congr with x
    apply ih

@[simp]
lemma run_pure (a : α) (k : α → r) :
    run (.pure a : FreeCont r α) k = k a := rfl

@[simp]
lemma run_liftBind_callCC (g : (α → r) → r)
    (cont : α → FreeCont r β) (k : β → r) :
    run (liftBind (.callCC g) cont) k = g (fun a => run (cont a) k) := rfl

/-- Call with current continuation for the Free continuation monad. -/
def callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    FreeCont r α :=
  liftBind (.callCC fun k => run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k) pure

@[simp]
lemma callCC_def (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    callCC f =
      liftBind (.callCC fun k => run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k) pure :=
  rfl

instance : MonadCont (FreeCont r) where
  callCC := .callCC

/-- `run` of a `callCC` node simplifies to running the handler with the current continuation. -/
@[simp]
lemma run_callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) (k : α → r) :
  run (callCC f) k = run (f ⟨fun x => liftBind (.callCC fun _ => k x) pure⟩) k := by
  simp [callCC, run_liftBind_callCC]

end FreeCont

end FreeM
