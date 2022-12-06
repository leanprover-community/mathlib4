/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

The writer monad transformer for passing immutable state.
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Equiv.Defs

universe u v w u₀ u₁ v₀ v₁

-- structure WriterT (ω : Type u) (m : Type u → Type v) (α : Type u) : Type max u v where
--   run : m (α × ω)
-- #align writer_t WriterTₓ

/-
@[reducible]
def Writer (ω : Type u) :=
  WriterT ω id
#align writer Writer
-/

-- TODO -- check if this is a thing in Lean 4
--attribute [pp_using_anonymous_constructor] WriterT


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

protected def mk {ω : Type u} (cmd :  M (α × ω)) : WriterT ω M α:= cmd
protected def run {ω : Type u} (cmd : WriterT ω M α) : M (α × ω) := cmd
protected def runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω) := cmd

variable {ω : Type u} {α β : Type u}

/-- Creates an instance of Monad, with an explicitly given empty and append operation.

Previously, this would have used an instance of `[Monoid ω]` as input.
In practice, however, WriterT is used for logging and creating lists so restricting to
monoids with `Mul` and `One` can make `WriterT` cumbersome to use.

This is used to derive instances for both `[EmptyCollection ω] [Append ω]` and `[Monoid ω]`.
-/
def monad (empty : ω) (append : ω → ω → ω) : Monad (WriterT ω M) where
  map := fun f (cmd : M _) ↦ WriterT.mk $ (fun (a,w) ↦ (f a, w)) <$> cmd
  pure := fun a ↦ pure (f := M) (a, empty)
  bind := fun (cmd : M _) f ↦
    WriterT.mk $ cmd >>= fun (a, w₁) ↦
      (fun (b, w₂) ↦ (b, append w₁ w₂)) <$> (f a)

/-- Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit. -/
protected def liftTell (empty : ω) : MonadLift M (WriterT ω M) where
  monadLift := fun cmd ↦ WriterT.mk $ (fun a ↦ (a, empty)) <$> cmd

instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅
instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
instance [Monoid ω] : MonadLift M (WriterT ω M) := WriterT.liftTell 1

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

section

variable {ω : Type u}

variable {m : Type u → Type v}

variable [Monad m]

variable {α β : Type u}

open Function

@[ext]
protected theorem ext (x x' : WriterT ω m α) (h : x.run = x'.run) : x = x' := by
  simp [WriterT.run] at h; assumption
#align writer_t.ext WriterTₓ.ext

instance [One ω] [Mul ω] : Monad (WriterT ω m) := WriterT.monad 1 Mul.mul
--
instance [Monoid ω] [LawfulMonad m] :
    LawfulMonad
      (WriterT ω
        m) where
  id_map := by
    intros
    cases x
    simp [(· <$> ·), WriterT.bind, WriterT.pure]
  pure_bind := by
    intros
    simp [Pure.pure, WriterT.pure, (· >>= ·), WriterT.bind]
    ext <;> rfl
  bind_assoc := by
    intros
    simp [(· >>= ·), WriterT.bind, mul_assoc, functor_norm]

@[inline]
protected def lift [One ω] (a : m α) : WriterT ω m α :=
  ⟨flip Prod.mk 1 <$> a⟩
#align writer_t.lift WriterTₓ.lift

instance (m) [Monad m] [One ω] : HasMonadLift m (WriterT ω m) :=
  ⟨fun α => WriterT.lift⟩

@[inline]
protected def monadMap {m m'} [Monad m] [Monad m'] {α} (f : ∀ {α}, m α → m' α) :
    WriterT ω m α → WriterT ω m' α := fun x => ⟨f x.run⟩
#align writer_t.monad_map WriterTₓ.monadMap

instance (m m') [Monad m] [Monad m'] : MonadFunctor m m' (WriterT ω m) (WriterT ω m') :=
  ⟨@WriterT.monadMap ω m m' _ _⟩

@[inline]
protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') : WriterT ω m α → WriterT ω' m α :=
  fun x => ⟨Prod.map id f <$> x.run⟩
#align writer_t.adapt WriterTₓ.adapt

instance (ε) [One ω] [Monad m] [MonadExcept ε m] :
    MonadExcept ε (WriterT ω
        m) where
  throw α := WriterT.lift ∘ throw
  catch α x c := ⟨catch x.run fun e => (c e).run⟩

end

end WriterT

#print MonadWriter /-
/-- An implementation of [MonadReader](
https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
It does not contain `local` because this function cannot be lifted using `monad_lift`.
Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
(lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
```
-/
class MonadWriter (ω : outParam (Type u)) (m : Type u → Type v) where
  tell (w : ω) : m PUnit
  listen {α} : m α → m (α × ω)
  pass {α : Type u} : m (α × (ω → ω)) → m α
#align monad_writer MonadWriter
-/

export MonadWriter ()

instance {ω : Type u} {m : Type u → Type v} [Monad m] :
    MonadWriter ω (WriterT ω m) where
  tell := WriterT.tell
  listen α := WriterT.listen
  pass α := WriterT.pass

instance {ω ρ : Type u} {m : Type u → Type v} [Monad m] [MonadWriter ω m] :
    MonadWriter ω (ReaderT ρ
        m) where
  tell x := monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨fun r => listen (cmd r)⟩
  pass := fun α ⟨cmd⟩ => ⟨fun r => pass (cmd r)⟩

def swapRight {α β γ} : (α × β) × γ → (α × γ) × β
  | ⟨⟨x, y⟩, z⟩ => ((x, z), y)
#align swap_right swapRight

instance {ω σ : Type u} {m : Type u → Type v} [Monad m] [MonadWriter ω m] :
    MonadWriter ω (StateT σ
        m) where
  tell x := monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨fun r => swapRight <$> listen (cmd r)⟩
  pass := fun α ⟨cmd⟩ => ⟨fun r => pass (swapRight <$> cmd r)⟩

open Function

def ExceptT.passAux {ε α ω} : Except ε (α × (ω → ω)) → Except ε α × (ω → ω)
  | Except.error a => (Except.error a, id)
  | Except.ok (x, y) => (Except.ok x, y)
#align except_t.pass_aux ExceptTₓ.passAux

instance {ω ε : Type u} {m : Type u → Type v} [Monad m] [MonadWriter ω m] :
    MonadWriter ω (ExceptT ε
        m) where
  tell x := monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨(uncurry fun x y => flip Prod.mk y <$> x) <$> listen cmd⟩
  pass := fun α ⟨cmd⟩ => ⟨pass (ExceptT.passAux <$> cmd)⟩

def OptionT.passAux {α ω} : Option (α × (ω → ω)) → Option α × (ω → ω)
  | none => (none, id)
  | some (x, y) => (some x, y)
#align option_t.pass_aux OptionTₓ.passAux

instance {ω : Type u} {m : Type u → Type v} [Monad m] [MonadWriter ω m] :
    MonadWriter ω (OptionT
        m) where
  tell x := monadLift (tell x : m PUnit)
  listen := fun α ⟨cmd⟩ => ⟨(uncurry fun x y => flip Prod.mk y <$> x) <$> listen cmd⟩
  pass := fun α ⟨cmd⟩ => ⟨pass (OptionT.passAux <$> cmd)⟩

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to
[Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `monad_functor`.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
(map {α : Type u} :
  (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
```
-/
class MonadWriterAdapter (ω ω' : outParam (Type u)) (m m' : Type u → Type v) where
  adaptWriter {α : Type u} : (ω → ω') → m α → m' α
#align monad_writer_adapter MonadWriterAdapter

export MonadWriterAdapter (adaptWriter)

section

variable {ω ω' : Type u} {m m' : Type u → Type v}

/-- Transitivity.

This instance generates the type-class problem with a metavariable argument (which is why this
is marked as `[nolint dangerous_instance]`).
Currently that is not a problem, as there are almost no instances of `monad_functor` or
`monad_writer_adapter`.

see Note [lower instance priority] -/
@[nolint dangerous_instance]
instance (priority := 100) monadWriterAdapterTrans {n n' : Type u → Type v}
    [MonadWriterAdapter ω ω' m m'] [MonadFunctor m m' n n'] : MonadWriterAdapter ω ω' n n' :=
  ⟨fun α f => monadMap fun α => (adaptWriter f : m α → m' α)⟩
#align monad_writer_adapter_trans monadWriterAdapterTrans

instance [Monad m] : MonadWriterAdapter ω ω' (WriterT ω m) (WriterT ω' m) :=
  ⟨fun α => WriterT.adapt⟩

end

instance (ω : Type u) (m out) [MonadRun out m] : MonadRun (fun α => out (α × ω)) (WriterT ω m) :=
  ⟨fun α x => run <| x.run⟩

/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
def WriterT.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ ω₁ : Type u₀}
    {α₂ ω₂ : Type u₁} (F : m₁ (α₁ × ω₁) ≃ m₂ (α₂ × ω₂)) :
    WriterT ω₁ m₁ α₁ ≃ WriterT ω₂ m₂
        α₂ where
  toFun := fun ⟨f⟩ => ⟨F f⟩
  invFun := fun ⟨f⟩ => ⟨F.symm f⟩
  left_inv := fun ⟨f⟩ => congr_arg WriterT.mk <| F.left_inv _
  right_inv := fun ⟨f⟩ => congr_arg WriterT.mk <| F.right_inv _
#align writer_t.equiv WriterTₓ.equiv
