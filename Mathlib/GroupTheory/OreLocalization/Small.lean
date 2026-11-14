/-
Copyright (c) 2026 Harald Husum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Husum
-/
module

public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Smallness of Ore localizations

We show that `X[S⁻¹]` is `w`-small if `S` and `X` are. In particular, this holds if `R` and `X`
are. The instance also applies to `Localization S` and `LocalizedModule S M`.
-/

public section

universe w

namespace OreLocalization

variable {R : Type*} [Monoid R] (S : Submonoid R) [OreSet S] (X : Type*) [MulAction R X]

@[to_additive]
instance small [Small.{w} S] [Small.{w} X] : Small.{w} X[S⁻¹] :=
  small_quotient _

end OreLocalization
