/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module control.equiv_functor.instances
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Control.EquivFunctor

/-!
# `EquivFunctor` instances

We derive some `EquivFunctor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equiv

instance equivFunctorUnique : EquivFunctor Unique where
  map e := Equiv.uniqueCongr e
  map_refl' α := by simp
  map_trans' := by simp
#align equiv_functor_unique equivFunctorUnique

instance equivFunctorPerm : EquivFunctor Perm where
  map e p := (e.symm.trans p).trans e
  map_refl' α := by ext; simp
  map_trans' := sorry
#align equiv_functor_perm equivFunctorPerm

-- There is a classical instance of `IsLawfulFunctor Finset` available,
-- but we provide this computable alternative separately.
instance equivFunctorFinset : EquivFunctor Finset where
  map e s := s.map e.toEmbedding
  map_refl' α := by ext; simp
  map_trans' := sorry
#align equiv_functor_finset equivFunctorFinset

instance equivFunctorFintype : EquivFunctor Fintype where
  map e s := Fintype.ofBijective e e.bijective
  map_refl' α := by ext; simp
  map_trans' := by simp
#align equiv_functor_fintype equivFunctorFintype
