/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Ideal
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike
/-!

# Sheaf categories are Cartesian closed

...if the underlying presheaf category is Cartesian closed, the target category has
(chosen) finite products, and there exists a sheafification functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory Presheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (A : Type*) [Category* A]

instance [HasSheafify J A] [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] :
    MonoidalClosed (Sheaf J A) :=
  cartesianClosedOfReflective' (sheafToPresheaf _ _) {
    obj F := ⟨F.obj, (isSheaf_of_iso_iff F.2.choose_spec.some).1 F.2.choose.property⟩
    map f := ⟨f.hom⟩ } (Iso.refl _)
