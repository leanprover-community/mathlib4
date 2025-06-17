/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Ring.Int

/-! `ZMod 0` is a domain -/

/-- `ZMod 0` is a domain -/
instance : IsDomain (ZMod 0) :=
  Equiv.isDomain (RingEquiv.refl ℤ).symm
