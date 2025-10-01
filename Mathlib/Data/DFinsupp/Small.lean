/-
Copyright (c) 2025 Sophie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Logic.Small.Basic

@[expose] public section

/-!
# Smallness of the `DFinsupp` type

Let `π : ι → Type v`. If `ι` and all the `π i` are `w`-small, this provides a `Small.{w}`
instance on `DFinsupp π`.

As an application, `σ →₀ R` has a `Small.{v}` instance if `σ` and `R` have one.
-/

universe u v w

variable {ι : Type u} {π : ι → Type v} [∀ i, Zero (π i)]

section Small

instance DFinsupp.small [Small.{w} ι] [∀ (i : ι), Small.{w} (π i)] :
    Small.{w} (DFinsupp π) :=
  small_of_injective (f := fun x j ↦ x j) (fun f f' eq ↦ by ext j; exact congr_fun eq j)

instance Finsupp.small {σ : Type*} {R : Type*} [Zero R]
    [Small.{u} R] [Small.{u} σ] :
    Small.{u} (σ →₀ R) := by
  classical
  exact small_map finsuppEquivDFinsupp

end Small
