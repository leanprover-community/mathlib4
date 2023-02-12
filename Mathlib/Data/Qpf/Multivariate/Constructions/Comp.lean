/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon

! This file was ported from Lean 3 source module data.qpf.multivariate.constructions.comp
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pfunctor.Multivariate.Basic
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/


universe u

namespace Mvqpf

open MvFunctor

variable {n m : ℕ} (F : TypeVec.{u} n → Type _) [fF : MvFunctor F] [q : Mvqpf F]
  (G : Fin2 n → TypeVec.{u} m → Type u) [fG : ∀ i, MvFunctor <| G i] [q' : ∀ i, Mvqpf <| G i]

/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin2 n => G i v
#align mvqpf.comp Mvqpf.Comp

namespace Comp

open MvFunctor Mvpfunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

instance [I : Inhabited (F fun i : Fin2 n => G i α)] : Inhabited (Comp F G α) :=
  I

/-- Constructor for functor composition -/
protected def mk (x : F fun i => G i α) : (Comp F G) α :=
  x
#align mvqpf.comp.mk Mvqpf.Comp.mk

/-- Destructor for functor composition -/
protected def get (x : (Comp F G) α) : F fun i => G i α :=
  x
#align mvqpf.comp.get Mvqpf.Comp.get

@[simp]
protected theorem mk_get (x : (Comp F G) α) : Comp.mk (Comp.get x) = x :=
  rfl
#align mvqpf.comp.mk_get Mvqpf.Comp.mk_get

@[simp]
protected theorem get_mk (x : F fun i => G i α) : Comp.get (Comp.mk x) = x :=
  rfl
#align mvqpf.comp.get_mk Mvqpf.Comp.get_mk

include fG

/-- map operation defined on a vector of functors -/
protected def map' : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β := fun i => map f
#align mvqpf.comp.map' Mvqpf.Comp.map'

include fF

/-- The composition of functors is itself functorial -/
protected def map : (Comp F G) α → (Comp F G) β :=
  (map fun i => map f : (F fun i => G i α) → F fun i => G i β)
#align mvqpf.comp.map Mvqpf.Comp.map

instance : MvFunctor (Comp F G) where map α β := Comp.map

theorem map_mk (x : F fun i => G i α) :
    f <$$> Comp.mk x = Comp.mk ((fun i (x : G i α) => f <$$> x) <$$> x) :=
  rfl
#align mvqpf.comp.map_mk Mvqpf.Comp.map_mk

theorem get_map (x : Comp F G α) :
    Comp.get (f <$$> x) = (fun i (x : G i α) => f <$$> x) <$$> Comp.get x :=
  rfl
#align mvqpf.comp.get_map Mvqpf.Comp.get_map

include q q'

instance : Mvqpf (Comp F G)
    where
  p := Mvpfunctor.comp (p F) fun i => p <| G i
  abs α := Comp.mk ∘ (map fun i => abs) ∘ abs ∘ Mvpfunctor.comp.get
  repr α :=
    Mvpfunctor.comp.mk ∘
      repr ∘ (map fun i => (repr : G i α → (fun i : Fin2 n => Obj (p (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp [(· ∘ ·), MvFunctor.map_map, (· ⊚ ·), abs_repr]
  abs_map := by
    intros
    simp [(· ∘ ·)]
    rw [← abs_map]
    simp [MvFunctor.id_map, (· ⊚ ·), map_mk, Mvpfunctor.comp.get_map, abs_map, MvFunctor.map_map,
      abs_repr]

end Comp

end Mvqpf

