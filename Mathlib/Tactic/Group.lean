/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module tactic.group
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Ring
import Mathbin.Tactic.DocCommands
import Mathbin.Algebra.Group.Commutator

/-!
# `group`

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using the `ring` tactic. The process needs to be repeated
since `ring` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

## Tags

group_theory
-/


-- The next four lemmas are not general purpose lemmas, they are intended for use only by
-- the `group` tactic.
@[to_additive]
theorem Tactic.Group.zpow_trick {G : Type _} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ m = a * b ^ (n + m) := by rw [mul_assoc, ← zpow_add]
#align tactic.group.zpow_trick Tactic.Group.zpow_trick
#align tactic.group.zsmul_trick Tactic.Group.zsmul_trick

@[to_additive]
theorem Tactic.Group.zpow_trick_one {G : Type _} [Group G] (a b : G) (m : ℤ) :
    a * b * b ^ m = a * b ^ (m + 1) := by rw [mul_assoc, mul_self_zpow]
#align tactic.group.zpow_trick_one Tactic.Group.zpow_trick_one
#align tactic.group.zsmul_trick_zero Tactic.Group.zsmul_trick_zero

@[to_additive]
theorem Tactic.Group.zpow_trick_one' {G : Type _} [Group G] (a b : G) (n : ℤ) :
    a * b ^ n * b = a * b ^ (n + 1) := by rw [mul_assoc, mul_zpow_self]
#align tactic.group.zpow_trick_one' Tactic.Group.zpow_trick_one'
#align tactic.group.zsmul_trick_zero' Tactic.Group.zsmul_trick_zero'

@[to_additive]
theorem Tactic.Group.zpow_trick_sub {G : Type _} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ (-m) = a * b ^ (n - m) := by rw [mul_assoc, ← zpow_add] <;> rfl
#align tactic.group.zpow_trick_sub Tactic.Group.zpow_trick_sub
#align tactic.group.zsmul_trick_sub Tactic.Group.zsmul_trick_sub

namespace Tactic

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic.SimpArgType Interactive Tactic.Group

/-- Auxiliary tactic for the `group` tactic. Calls the simplifier only. -/
unsafe def aux_group₁ (locat : Loc) : tactic Unit :=
  simp_core { failIfUnchanged := false } skip true
      [expr ``(commutatorElement_def), expr ``(mul_one), expr ``(one_mul), expr ``(one_pow),
        expr ``(one_zpow), expr ``(sub_self), expr ``(add_neg_self), expr ``(neg_add_self),
        expr ``(neg_neg), expr ``(tsub_self), expr ``(Int.ofNat_add), expr ``(Int.ofNat_mul),
        expr ``(Int.ofNat_zero), expr ``(Int.ofNat_one), expr ``(Int.ofNat_bit0),
        expr ``(Int.ofNat_bit1), expr ``(Int.mul_neg_eq_neg_mul_symm),
        expr ``(Int.neg_mul_eq_neg_mul_symm), symm_expr ``(zpow_ofNat), symm_expr ``(zpow_neg_one),
        symm_expr ``(zpow_mul), symm_expr ``(zpow_add_one), symm_expr ``(zpow_one_add),
        symm_expr ``(zpow_add), expr ``(mul_zpow_neg_one), expr ``(zpow_zero), expr ``(mul_zpow),
        symm_expr ``(mul_assoc), expr ``(zpow_trick), expr ``(zpow_trick_one),
        expr ``(zpow_trick_one'), expr ``(zpow_trick_sub), expr ``(Tactic.Ring.horner)]
      [] locat >>
    skip
#align tactic.aux_group₁ tactic.aux_group₁

/-- Auxiliary tactic for the `group` tactic. Calls `ring_nf` to normalize exponents. -/
unsafe def aux_group₂ (locat : Loc) : tactic Unit :=
  ring_nf none Tactic.Ring.NormalizeMode.raw locat
#align tactic.aux_group₂ tactic.aux_group₂

end Tactic

namespace Tactic.Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
open Tactic

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normalizes `h` which becomes `h : c = d`
  rw h,       -- the goal is now `a*d*d⁻¹ = a`
  group,      -- which then normalized and closed
end
```
-/
unsafe def group (locat : parse location) : tactic Unit := do
  when locat sorry
  aux_group₁ locat
  repeat (andthen (aux_group₂ locat) (aux_group₁ locat))
#align tactic.interactive.group tactic.interactive.group

end Tactic.Interactive

add_tactic_doc
  { Name := "group"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.group]
    tags := ["decision procedure", "simplification"] }

