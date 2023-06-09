/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, E.W.Ayers
-/
import Mathlib.Algebra.Group.Defs

/-!
# Writer monads

This file introduces monads for managing immutable, appendable state.
Common applications are logging monads where the monad logs messages as the
computation progresses.

## References
- https://hackage.haskell.org/package/mtl-2.2.1/docs/Control-Monad-Writer-Class.html
- [Original Mark P Jones article introducing `Writer`](https://web.cecs.pdx.edu/~mpj/pubs/springschool.html)

-/

def WriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type v :=
  M (α × ω)

@[reducible]
def Writer ω := WriterT ω Id

class MonadWriter (ω : outParam (Type u)) (M : Type u → Type v) where
  tell : ω → M PUnit
  listen {α} : M α → M (α × ω)
  pass {α} : M (α × (ω → ω)) → M α

export MonadWriter (tell listen pass)

variable {M : Type u → Type v} [Monad M]

instance [MonadWriter ω M] : MonadWriter ω (ReaderT ρ M) where
  tell w :=  (tell w : M _)
  listen x r := listen <| x r
  pass x r := pass <| x r

instance [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  tell w := (tell w : M _)
  listen x s := (fun ((a,w), s) ↦ ((a,s), w)) <$> listen (x s)
  pass x s := pass <| (fun ((a, f), s) ↦ ((a, s), f)) <$> (x s)

namespace WriterT

@[inline]
protected def mk {ω : Type u} (cmd :  M (α × ω)) : WriterT ω M α:= cmd
@[inline]
protected def run {ω : Type u} (cmd : WriterT ω M α) : M (α × ω) := cmd
@[inline]
protected def runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω) := cmd

@[ext]
protected theorem ext {ω : Type u} (x x' : WriterT ω M α) (h : x.run = x'.run) : x = x' := h

variable {ω : Type u} {α β : Type u}

/-- Creates an instance of Monad, with an explicitly given empty and append operation.

Previously, this would have used an instance of `[Monoid ω]` as input.
In practice, however, WriterT is used for logging and creating lists so restricting to
monoids with `Mul` and `One` can make `WriterT` cumbersome to use.

This is used to derive instances for both `[EmptyCollection ω] [Append ω]` and `[Monoid ω]`.
-/
@[reducible, inline]
def monad (empty : ω) (append : ω → ω → ω) : Monad (WriterT ω M) where
  map := fun f (cmd : M _) ↦ WriterT.mk $ (fun (a,w) ↦ (f a, w)) <$> cmd
  pure := fun a ↦ pure (f := M) (a, empty)
  bind := fun (cmd : M _) f ↦
    WriterT.mk $ cmd >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, append w₁ w₂)) <$> (f a)

/-- Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit. -/
@[inline]
protected def liftTell (empty : ω) : MonadLift M (WriterT ω M) where
  monadLift := fun cmd ↦ WriterT.mk $ (fun a ↦ (a, empty)) <$> cmd

instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅
instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
instance [Monoid ω] : MonadLift M (WriterT ω M) := WriterT.liftTell 1

instance [Monoid ω] [LawfulMonad M] : LawfulMonad (WriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := by
    intros; simp [Bind.bind, Functor.map, Pure.pure, WriterT.mk, bind_pure_comp])
  (id_map := by intros; simp [Functor.map, WriterT.mk])
  (pure_bind := by intros; simp [Bind.bind, Pure.pure, WriterT.mk])
  (bind_assoc := by intros; simp [Bind.bind, mul_assoc, WriterT.mk, ← bind_pure_comp])

instance : MonadWriter ω (WriterT ω M) where
  tell := fun w ↦ WriterT.mk $ pure (⟨⟩, w)
  listen := fun cmd ↦ WriterT.mk $ (fun (a,w) ↦ ((a,w), w)) <$> cmd
  pass := fun cmd ↦ WriterT.mk $ (fun ((a,f), w) ↦ (a, f w)) <$> cmd

instance [MonadExcept ε M] : MonadExcept ε (WriterT ω M) where
  throw := fun e ↦ WriterT.mk $ throw e
  tryCatch := fun cmd c ↦ WriterT.mk $ tryCatch cmd fun e ↦ (c e).run

instance [MonadLiftT M (WriterT ω M)] : MonadControl M (WriterT ω M) where
  stM := fun α ↦ α × ω
  liftWith f := liftM <| f fun x ↦ x.run
  restoreM := WriterT.mk

instance : MonadFunctor M (WriterT ω M) where
  monadMap := fun k (w : M _) ↦ WriterT.mk $ k w

@[inline] protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') :
    WriterT ω M α → WriterT ω' M α :=
  fun cmd ↦ WriterT.mk $ Prod.map id f <$> cmd

end WriterT

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `MonadFunctor`.

Note: This class can be seen as a simplification of the more "principled" definition
```
class MonadReaderFunctor (ρ ρ' : outParam (Type u)) (n n' : Type u → Type u) where
  map {α : Type u} :
    (∀ {m : Type u → Type u} [Monad m], ReaderT ρ m α → ReaderT ρ' m α) → n α → n' α
```
-/
class MonadWriterAdapter (ω ω' : outParam (Type u)) (m m' : Type u → Type v) where
  adaptWriter {α : Type u} : (ω → ω') → m α → m' α

export MonadWriterAdapter (adaptWriter)

/-- Transitivity.

This instance generates the type-class problem with a metavariable argument (which is why this
is marked as `[nolint dangerousInstance]`).
Currently that is not a problem, as there are almost no instances of `monad_functor` or
`monad_writer_adapter`.

see Note [lower instance priority] -/
@[nolint dangerous_instance]
instance (priority := 100) monadWriterAdapterTrans {n n' : Type u → Type v}
  [MonadWriterAdapter ω ω' m m'] [MonadTransFunctor m m' n n'] : monad_writer_adapter ω ω' n n' :=
⟨fun α f ↦ monad_map (fun α ↦ (adapt_writer f : m α → m' α))⟩
