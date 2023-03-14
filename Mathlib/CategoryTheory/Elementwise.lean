/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.elementwise
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Elementwise
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# Use the `elementwise` attribute to create applied versions of lemmas.

Usually we would use `@[elementwise]` at the point of definition,
however some early parts of the category theory library are imported by `tactic.elementwise`,
so we need to add the attribute after the fact.
-/


/-! We now add some `elementwise` attributes to lemmas that were proved earlier. -/


open CategoryTheory

-- This list is incomplete, and it would probably be useful to add more.
attribute [elementwise] iso.hom_inv_id iso.inv_hom_id is_iso.hom_inv_id is_iso.inv_hom_id

