/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.encodable
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Encodable.Basic
import Mathbin.Data.Nat.Gcd.Basic
import Mathbin.Data.Rat.Init

/-! # The rationals are `encodable`.

As a consequence we also get the instance `countable ℚ`.

This is kept separate from `data.rat.defs` in order to minimize imports.
-/


namespace Rat

instance : Encodable ℚ :=
  Encodable.ofEquiv (Σn : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => rfl,
      fun ⟨a, b, c, d⟩ => rfl⟩

end Rat

