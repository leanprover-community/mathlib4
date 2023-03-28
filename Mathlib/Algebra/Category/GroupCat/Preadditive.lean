/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.preadditive
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The category of additive commutative groups is preadditive.
-/


open CategoryTheory

universe u

namespace AddCommGroupCat

-- porting note: this instance was not necessary in mathlib
instance (P Q : AddCommGroupCat) : AddCommGroup (P ⟶ Q) :=
  (inferInstance : AddCommGroup (AddMonoidHom P Q))

@[simp]
lemma hom_add_apply {P Q : AddCommGroupCat} (f g : P ⟶ Q) (x : P) :
  (f + g) x = f x + g x := rfl

-- porting note: doing just `ext; simp` timeouts, what is wrong?
instance : Preadditive AddCommGroupCat where
  add_comp P Q R f f' g := by
    ext
    simp only [comp_apply, hom_add_apply, Hom.map_add]
  comp_add P Q R f g g' := by
    ext
    simp only [comp_apply, hom_add_apply]

end AddCommGroupCat
