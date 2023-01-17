/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.init
! leanprover-community/mathlib commit f340f229b1f461aa1c8ee11e0a172d0a3b301a4a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Mathport.Rename
import Std.Data.Rat

/-!
# Notation for the rational numbers -/

namespace Rat

@[inherit_doc] notation "ℚ" => Rat

#align rat.denom Rat.den
