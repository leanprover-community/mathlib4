/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Category.Pointed.Basic

/-!
# Forgetful functors from Grp to the category of pointed types

In this file, we define the forgetful functor from `Grp`, `AddGrp`, `CommGrp`, `AddCommGrp` to the
category `Pointed` of pointed types.
-/
open CategoryTheory

universe u

@[to_additive (attr := simps)]
def Grp.forgetToPointed : Grp.{u} ⥤ Pointed.{u} where
  obj X := ⟨X, 1⟩
  map f := ⟨f, f.hom.map_one⟩

@[to_additive (attr := simps)]
def CommGrp.forgetToPointed : CommGrp.{u} ⥤ Pointed.{u} where
  obj X := ⟨X, 1⟩
  map f := ⟨f, f.hom.map_one⟩
