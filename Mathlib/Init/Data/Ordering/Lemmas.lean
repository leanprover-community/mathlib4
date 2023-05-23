/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.ordering.lemmas
! leanprover-community/lean commit 4bd314f7bd5e0c9e813fc201f1279a23f13f9f1d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Data.Ordering.Basic
import Leanbin.Init.Meta.Default
import Leanbin.Init.Algebra.Classes
import Leanbin.Init.IteSimp

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option default_priority -/
set_option default_priority 100

universe u

namespace Ordering

@[simp]
theorem ite_eq_lt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.lt) = if c then a = Ordering.lt else b = Ordering.lt := by
  by_cases c <;> simp [*]
#align ordering.ite_eq_lt_distrib Ordering.ite_eq_lt_distrib

@[simp]
theorem ite_eq_eq_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.eq) = if c then a = Ordering.eq else b = Ordering.eq := by
  by_cases c <;> simp [*]
#align ordering.ite_eq_eq_distrib Ordering.ite_eq_eq_distrib

@[simp]
theorem ite_eq_gt_distrib (c : Prop) [Decidable c] (a b : Ordering) :
    ((if c then a else b) = Ordering.gt) = if c then a = Ordering.gt else b = Ordering.gt := by
  by_cases c <;> simp [*]
#align ordering.ite_eq_gt_distrib Ordering.ite_eq_gt_distrib

-- ------------------------------------------------------------------
end Ordering

section

variable {α : Type u} {lt : α → α → Prop} [DecidableRel lt]

attribute [local simp] cmpUsing

@[simp]
theorem cmpUsing_eq_lt (a b : α) : (cmpUsing lt a b = Ordering.lt) = lt a b := by simp
#align cmp_using_eq_lt cmpUsing_eq_lt

@[simp]
theorem cmpUsing_eq_gt [IsStrictOrder α lt] (a b : α) : (cmpUsing lt a b = Ordering.gt) = lt b a :=
  by
  simp; apply propext; apply Iff.intro
  · exact fun h => h.2
  · intro hba
    constructor
    · intro hab
      exact absurd (trans hab hba) (irrefl a)
    · assumption
#align cmp_using_eq_gt cmpUsing_eq_gt

@[simp]
theorem cmpUsing_eq_eq (a b : α) : (cmpUsing lt a b = Ordering.eq) = (¬lt a b ∧ ¬lt b a) := by simp
#align cmp_using_eq_eq cmpUsing_eq_eq

end

