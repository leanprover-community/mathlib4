/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers

This should be replaced eventually with Simon Hudon's mathlib3 version.
-/
import Mathlib.Data.Prod

class Traversable (T : Type u → Type u) extends Functor T :=
  (traverse ⦃M : Type u → Type u⦄ [Applicative M] {α β} : (α → M β) → T α → M (T β))

variable {T : Type u → Type u} [Traversable T]
variable {M : Type u → Type u} [Applicative M]

export Traversable (traverse)
def sequence : T (M α) → M (T α) := traverse id

class Distributive (R : Type u → Type u) where
  distribute : ∀ ⦃F⦄ [Functor F] {A}, F (R A) → R (F A)

def Distributive.distReader {ρ α : Type u} [Distributive R]: (ρ → R α) → (R (ρ → α))
  | (f : Reader ρ (R α)) => Distributive.distribute f

instance : Traversable Prod.Square where
  traverse := fun _ _ _ _ f (a1,a2) => Prod.mk <$> f a1 <*> f a2
