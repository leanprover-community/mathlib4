/-
Copyright (c) 2025 Sophie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Data.DFinsupp.Defs
import Mathlib.Logic.Small.Basic

/-!
# Smallness of the `DFinsupp` type

Let `π : ι → Type v`. If `ι` and all the `π i` are `w`-small, this provides a `Small.{w}`
instance on `DFinsupp π`.

-/

universe u v w

variable {ι : Type u} {π : ι → Type v} [∀ i, Zero (π i)]

section Small

instance DFinsupp.small [Small.{w} ι] [∀ (i : ι), Small.{w} (π i)] :
    Small.{w} (DFinsupp π) := small_of_injective (f := fun x j ↦ x j) (fun f f' eq ↦ by
      ext j
      exact congr_fun eq j)

end Small
