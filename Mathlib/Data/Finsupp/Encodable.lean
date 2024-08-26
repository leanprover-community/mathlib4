/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Data.DFinsupp.Encodable
/-!
# `Encodable` and `Countable` instances for `α →₀ β`

In this file we provide instances for `Encodable (α →₀ β)` and `Countable (α →₀ β)`.
-/

instance {α β : Type*} [Encodable α] [Encodable β] [Zero β] [∀ x : β, Decidable (x ≠ 0)] :
    Encodable (α →₀ β) :=
  letI : DecidableEq α := Encodable.decidableEqOfEncodable _
  .ofEquiv _ finsuppEquivDFinsupp

instance {α β : Type*} [Countable α] [Countable β] [Zero β] : Countable (α →₀ β) := by
  classical exact .of_equiv _ finsuppEquivDFinsupp.symm
