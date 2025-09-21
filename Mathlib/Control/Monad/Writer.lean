/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Edward Ayers
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Defs

/-!
# Writer monads

This file introduces monads for managing immutable, appendable state.
Common applications are logging monads where the monad logs messages as the
computation progresses.

## References
- https://hackage.haskell.org/package/mtl-2.2.1/docs/Control-Monad-Writer-Class.html
- [Original Mark P Jones article introducing `Writer`](https://web.cecs.pdx.edu/~mpj/pubs/springschool.html)

-/

universe u v

/-- Adds a writable output of type `ω` to a monad.

The instances on this type assume that either `[Monoid ω]` or `[EmptyCollection ω] [Append ω]`.

Use `WriterT.run` to obtain the final value of this output. -/
def WriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type v :=
  M (α × ω)

abbrev Writer ω := WriterT ω Id

class MonadWriter (ω : outParam (Type u)) (M : Type u → Type v) where
  /-- Emit an output `w`. -/
  tell (w : ω) : M PUnit
  /-- Capture the output produced by `f`, without intercepting. -/
  listen {α} (f : M α) : M (α × ω)
  /-- Buffer the output produced by `f` as `w`, then emit `(← f).2 w` in its place. -/
  pass {α} (f : M (α × (ω → ω))) : M α

export MonadWriter (tell listen pass)

variable {M : Type u → Type v} {α ω ρ σ : Type u}

instance [MonadWriter ω M] : MonadWriter ω (ReaderT ρ M) where
  tell w := (tell w : M _)
  listen x r := listen <| x r
  pass x r := pass <| x r

instance [Monad M] [MonadWriter ω M] : MonadWriter ω (StateT σ M) where
  tell w := (tell w : M _)
  listen x s := (fun ((a,w), s) ↦ ((a,s), w)) <$> listen (x s)
  pass x s := pass <| (fun ((a, f), s) ↦ ((a, s), f)) <$> (x s)

namespace WriterT

@[inline]
protected def mk {ω : Type u} (cmd : M (α × ω)) : WriterT ω M α := cmd
@[inline]
protected def run {ω : Type u} (cmd : WriterT ω M α) : M (α × ω) := cmd
@[inline]
protected def runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω) := cmd

@[ext]
protected theorem ext {ω : Type u} (x x' : WriterT ω M α) (h : x.run = x'.run) : x = x' := h

variable [Monad M]

/-- Creates an instance of `Monad`, with explicitly given `empty` and `append` operations.

Previously, this would have used an instance of `[Monoid ω]` as input.
In practice, however, `WriterT` is used for logging and creating lists so restricting to
monoids with `Mul` and `One` can make `WriterT` cumbersome to use.

This is used to derive instances for both `[EmptyCollection ω] [Append ω]` and `[Monoid ω]`.
-/
@[reducible, inline]
def monad (empty : ω) (append : ω → ω → ω) : Monad (WriterT ω M) where
  map := fun f (cmd : M _) ↦ WriterT.mk <| (fun (a,w) ↦ (f a, w)) <$> cmd
  pure := fun a ↦ pure (f := M) (a, empty)
  bind := fun (cmd : M _) f ↦
    WriterT.mk <| cmd >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, append w₁ w₂)) <$> (f a)

/-- Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit. -/
@[inline]
protected def liftTell (empty : ω) : MonadLift M (WriterT ω M) where
  monadLift := fun cmd ↦ WriterT.mk <| (fun a ↦ (a, empty)) <$> cmd

instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅
instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
instance [Monoid ω] : MonadLift M (WriterT ω M) := WriterT.liftTell 1

instance [Monoid ω] [LawfulMonad M] : LawfulMonad (WriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := by
    simp [Bind.bind, Functor.map, Pure.pure, WriterT.mk, bind_pure_comp])
  (id_map := by simp [Functor.map, WriterT.mk])
  (pure_bind := by simp [Bind.bind, Pure.pure, WriterT.mk])
  (bind_assoc := by simp [Bind.bind, mul_assoc, WriterT.mk, ← bind_pure_comp])

instance : MonadWriter ω (WriterT ω M) where
  tell := fun w ↦ WriterT.mk <| pure (⟨⟩, w)
  listen := fun cmd ↦ WriterT.mk <| (fun (a,w) ↦ ((a,w), w)) <$> cmd
  pass := fun cmd ↦ WriterT.mk <| (fun ((a,f), w) ↦ (a, f w)) <$> cmd

instance {ε : Type*} [MonadExcept ε M] : MonadExcept ε (WriterT ω M) where
  throw := fun e ↦ WriterT.mk <| throw e
  tryCatch := fun cmd c ↦ WriterT.mk <| tryCatch cmd fun e ↦ (c e).run

instance [MonadLiftT M (WriterT ω M)] : MonadControl M (WriterT ω M) where
  stM := fun α ↦ α × ω
  liftWith f := liftM <| f fun x ↦ x.run
  restoreM := WriterT.mk

instance : MonadFunctor M (WriterT ω M) where
  monadMap := fun k (w : M _) ↦ WriterT.mk <| k w

@[inline] protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') :
    WriterT ω M α → WriterT ω' M α :=
  fun cmd ↦ WriterT.mk <| Prod.map id f <$> cmd

end WriterT

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `MonadFunctor`.
-/
class MonadWriterAdapter (ω : outParam (Type u)) (m : Type u → Type v) where
  adaptWriter {α : Type u} : (ω → ω) → m α → m α

export MonadWriterAdapter (adaptWriter)

variable {m : Type u → Type*}
/-- Transitivity.

see Note [lower instance priority] -/
instance (priority := 100) monadWriterAdapterTrans {n : Type u → Type v}
    [MonadWriterAdapter ω m] [MonadFunctor m n] : MonadWriterAdapter ω n where
  adaptWriter f := monadMap (fun {α} ↦ (adaptWriter f : m α → m α))

instance [Monad m] : MonadWriterAdapter ω (WriterT ω m) where
  adaptWriter := WriterT.adapt

universe u₀ u₁ v₀ v₁ in
/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
def WriterT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
    {α₁ ω₁ : Type u₀} {α₂ ω₂ : Type u₁} (F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))) :
    WriterT ω₁ m₁ α₁ ≃ WriterT ω₂ m₂ α₂ where
  toFun (f : m₁ _) := WriterT.mk <| F f
  invFun (f : m₂ _) := WriterT.mk <| F.symm f
  left_inv (f : m₁ _) := congr_arg WriterT.mk <| F.left_inv f
  right_inv (f : m₂ _) := congr_arg WriterT.mk <| F.right_inv f
