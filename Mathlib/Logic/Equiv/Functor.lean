/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison

! This file was ported from Lean 3 source module logic.equiv.functor
! leanprover-community/mathlib commit 9407b03373c8cd201df99d6bc5514fc2db44054f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Bifunctor
import Mathbin.Logic.Equiv.Defs

/-!
# Functor and bifunctors can be applied to `equiv`s.

We define
```lean
def functor.map_equiv (f : Type u → Type v) [functor f] [is_lawful_functor f] :
  α ≃ β → f α ≃ f β
```
and
```lean
def bifunctor.map_equiv (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] :
  α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/


universe u v w

variable {α β : Type u}

open Equiv

namespace Functor

variable (f : Type u → Type v) [Functor f] [LawfulFunctor f]

/-- Apply a functor to an `equiv`. -/
def mapEquiv (h : α ≃ β) : f α ≃ f β where
  toFun := map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]
#align functor.map_equiv Functor.mapEquiv

@[simp]
theorem mapEquiv_apply (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map h x :=
  rfl
#align functor.map_equiv_apply Functor.mapEquiv_apply

@[simp]
theorem mapEquiv_symm_apply (h : α ≃ β) (y : f β) :
    (mapEquiv f h : f α ≃ f β).symm y = map h.symm y :=
  rfl
#align functor.map_equiv_symm_apply Functor.mapEquiv_symm_apply

@[simp]
theorem mapEquiv_refl : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) :=
  by
  ext x
  simp only [map_equiv_apply, refl_apply]
  exact LawfulFunctor.id_map x
#align functor.map_equiv_refl Functor.mapEquiv_refl

end Functor

namespace Bifunctor

variable {α' β' : Type v} (F : Type u → Type v → Type w) [Bifunctor F] [IsLawfulBifunctor F]

/-- Apply a bifunctor to a pair of `equiv`s. -/
def mapEquiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β'
    where
  toFun := bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv x := by simp [bimap_bimap, id_bimap]
  right_inv x := by simp [bimap_bimap, id_bimap]
#align bifunctor.map_equiv Bifunctor.mapEquiv

@[simp]
theorem mapEquiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
    (mapEquiv F h h' : F α α' ≃ F β β') x = bimap h h' x :=
  rfl
#align bifunctor.map_equiv_apply Bifunctor.mapEquiv_apply

@[simp]
theorem mapEquiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
    (mapEquiv F h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y :=
  rfl
#align bifunctor.map_equiv_symm_apply Bifunctor.mapEquiv_symm_apply

@[simp]
theorem mapEquiv_refl_refl : mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.refl (F α α') :=
  by
  ext x
  simp [id_bimap]
#align bifunctor.map_equiv_refl_refl Bifunctor.mapEquiv_refl_refl

end Bifunctor

