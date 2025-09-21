/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Monad.Basic
import Mathlib.Control.Monad.Cont
import Mathlib.Control.Monad.Writer
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Functor
import Mathlib.Control.Lawful

/-!
# Universe lifting for type families

Some functors such as `Option` and `List` are universe polymorphic. Unlike
type polymorphism where `Option α` is a function application and reasoning and
generalizations that apply to functions can be used, `Option.{u}` and `Option.{v}`
are not one function applied to two universe names but one polymorphic definition
instantiated twice. This means that whatever works on `Option.{u}` is hard
to transport over to `Option.{v}`. `ULiftable` is an attempt at improving the situation.

`ULiftable Option.{u} Option.{v}` gives us a generic and composable way to use
`Option.{u}` in a context that requires `Option.{v}`. It is often used in tandem with
`ULift` but the two are purposefully decoupled.


## Main definitions
* `ULiftable` class

## Tags

universe polymorphism functor

-/


universe v u₀ u₁ v₀ v₁ v₂ w w₀ w₁

variable {s : Type u₀} {s' : Type u₁} {r r' w w' : Type*}

/-- Given a universe polymorphic type family `M.{u} : Type u₁ → Type
u₂`, this class convert between instantiations, from
`M.{u} : Type u₁ → Type u₂` to `M.{v} : Type v₁ → Type v₂` and back.

`f` is an outParam, because `g` can almost always be inferred from the current monad.
At any rate, the lift should be unique, as the intent is to only lift the same constants with
different universe parameters. -/
class ULiftable (f : outParam (Type u₀ → Type u₁)) (g : Type v₀ → Type v₁) where
  congr {α β} : α ≃ β → f α ≃ g β

namespace ULiftable

/-- Not an instance as it is incompatible with `outParam`. In practice it seems not to be needed
anyway. -/
abbrev symm (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) [ULiftable f g] : ULiftable g f where
  congr e := (ULiftable.congr e.symm).symm

instance refl (f : Type u₀ → Type u₁) [Functor f] [LawfulFunctor f] : ULiftable f f where
  congr e := Functor.mapEquiv _ e

/-- The most common practical use `ULiftable` (together with `down`), the function `up.{v}` takes
`x : M.{u} α` and lifts it to `M.{max u v} (ULift.{v} α)` -/
abbrev up {f : Type u₀ → Type u₁} {g : Type max u₀ v → Type v₁} [ULiftable f g] {α} :
    f α → g (ULift.{v} α) :=
  (ULiftable.congr Equiv.ulift.symm).toFun

/-- The most common practical use of `ULiftable` (together with `up`), the function `down.{v}` takes
`x : M.{max u v} (ULift.{v} α)` and lowers it to `M.{u} α` -/
abbrev down {f : Type u₀ → Type u₁} {g : Type max u₀ v → Type v₁} [ULiftable f g] {α} :
    g (ULift.{v} α) → f α :=
  (ULiftable.congr Equiv.ulift.symm).invFun

/-- convenient shortcut to avoid manipulating `ULift` -/
def adaptUp (F : Type v₀ → Type v₁) (G : Type max v₀ u₀ → Type u₁) [ULiftable F G] [Monad G] {α β}
    (x : F α) (f : α → G β) : G β :=
  up x >>= f ∘ ULift.down.{u₀}

/-- convenient shortcut to avoid manipulating `ULift` -/
def adaptDown {F : Type max u₀ v₀ → Type u₁} {G : Type v₀ → Type v₁} [L : ULiftable G F] [Monad F]
    {α β} (x : F α) (f : α → G β) : G β :=
  @down.{max u₀ v₀} G F L β <| x >>= @up.{max u₀ v₀} G F L β ∘ f

/-- map function that moves up universes -/
def upMap {F : Type u₀ → Type u₁} {G : Type max u₀ v₀ → Type v₁} [ULiftable F G] [Functor G]
    {α β} (f : α → β) (x : F α) : G β :=
  Functor.map (f ∘ ULift.down.{v₀}) (up x)

/-- map function that moves down universes -/
def downMap {F : Type max u₀ v₀ → Type u₁} {G : Type u₀ → Type v₁} [ULiftable G F]
    [Functor F] {α β} (f : α → β) (x : F α) : G β :=
  down (Functor.map (ULift.up.{v₀} ∘ f) x : F (ULift β))

/-- A version of `up` for a `PUnit` return type. -/
abbrev up' {f : Type u₀ → Type u₁} {g : Type v₀ → Type v₁} [ULiftable f g] :
    f PUnit → g PUnit :=
  ULiftable.congr Equiv.punitEquivPUnit

/-- A version of `down` for a `PUnit` return type. -/
abbrev down' {f : Type u₀ → Type u₁} {g : Type v₀ → Type v₁} [ULiftable f g] :
    g PUnit → f PUnit :=
  (ULiftable.congr Equiv.punitEquivPUnit).symm

theorem up_down {f : Type u₀ → Type u₁} {g : Type max u₀ v₀ → Type v₁} [ULiftable f g] {α}
    (x : g (ULift.{v₀} α)) : up (down x : f α) = x :=
  (ULiftable.congr Equiv.ulift.symm).right_inv _

theorem down_up {f : Type u₀ → Type u₁} {g : Type max u₀ v₀ → Type v₁} [ULiftable f g] {α}
    (x : f α) : down (up x : g (ULift.{v₀} α)) = x :=
  (ULiftable.congr Equiv.ulift.symm).left_inv _

end ULiftable

open ULift

instance instULiftableId : ULiftable Id Id where
  congr F := F

/-- for specific state types, this function helps to create a uliftable instance -/
def StateT.uliftable' {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁} [ULiftable m m']
    (F : s ≃ s') : ULiftable (StateT s m) (StateT s' m') where
  congr G :=
    StateT.equiv <| Equiv.piCongr F fun _ => ULiftable.congr <| Equiv.prodCongr G F

instance {m m'} [ULiftable m m'] : ULiftable (StateT s m) (StateT (ULift s) m') :=
  StateT.uliftable' Equiv.ulift.symm

instance StateT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (StateT (ULift.{max v₀ u₀} s) m) (StateT (ULift.{max v₁ u₀} s) m') :=
  StateT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

/-- for specific reader monads, this function helps to create a uliftable instance -/
def ReaderT.uliftable' {m m'} [ULiftable m m'] (F : s ≃ s') :
    ULiftable (ReaderT s m) (ReaderT s' m') where
  congr G := ReaderT.equiv <| Equiv.piCongr F fun _ => ULiftable.congr G

instance {m m'} [ULiftable m m'] : ULiftable (ReaderT s m) (ReaderT (ULift s) m') :=
  ReaderT.uliftable' Equiv.ulift.symm

instance ReaderT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ReaderT (ULift.{max v₀ u₀} s) m) (ReaderT (ULift.{max v₁ u₀} s) m') :=
  ReaderT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

/-- for specific continuation passing monads, this function helps to create a uliftable instance -/
def ContT.uliftable' {m m'} [ULiftable m m'] (F : r ≃ r') :
    ULiftable (ContT r m) (ContT r' m') where
  congr := ContT.equiv (ULiftable.congr F)

instance {s m m'} [ULiftable m m'] : ULiftable (ContT s m) (ContT (ULift s) m') :=
  ContT.uliftable' Equiv.ulift.symm

instance ContT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ContT (ULift.{max v₀ u₀} s) m) (ContT (ULift.{max v₁ u₀} s) m') :=
  ContT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

/-- for specific writer monads, this function helps to create a uliftable instance -/
def WriterT.uliftable' {m m'} [ULiftable m m'] (F : w ≃ w') :
    ULiftable (WriterT w m) (WriterT w' m') where
  congr G := WriterT.equiv <| ULiftable.congr <| Equiv.prodCongr G F

instance {m m'} [ULiftable m m'] : ULiftable (WriterT s m) (WriterT (ULift s) m') :=
  WriterT.uliftable' Equiv.ulift.symm

instance WriterT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (WriterT (ULift.{max v₀ u₀} s) m) (WriterT (ULift.{max v₁ u₀} s) m') :=
  WriterT.uliftable' <| Equiv.ulift.trans Equiv.ulift.symm

instance Except.instULiftable {ε : Type u₀} : ULiftable (Except.{u₀,v₁} ε) (Except.{u₀,v₂} ε) where
  congr e :=
    { toFun := Except.map e
      invFun := Except.map e.symm
      left_inv := fun f => by cases f <;> simp [Except.map]
      right_inv := fun f => by cases f <;> simp [Except.map] }

instance Option.instULiftable : ULiftable Option.{u₀} Option.{u₁} where
  congr e :=
    { toFun := Option.map e
      invFun := Option.map e.symm
      left_inv := fun f => by cases f <;> simp
      right_inv := fun f => by cases f <;> simp }
