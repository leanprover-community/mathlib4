/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Data.DFinsupp.Defs
public import Mathlib.Data.Fintype.Pi

/-!
# Finiteness and infiniteness of the `DFinsupp` type

## Main results

* `DFinsupp.fintype`: if the domain and codomain are finite, then `DFinsupp` is finite
* `DFinsupp.infinite_of_left`: if the domain is infinite, then `DFinsupp` is infinite
* `DFinsupp.infinite_of_exists_right`: if one fiber of the codomain is infinite,
  then `DFinsupp` is infinite
-/

@[expose] public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

section FiniteInfinite

instance DFinsupp.fintype {ι : Sort _} {π : ι → Sort _} [DecidableEq ι] [∀ i, Zero (π i)]
    [Fintype ι] [∀ i, Fintype (π i)] : Fintype (Π₀ i, π i) :=
  Fintype.ofEquiv (∀ i, π i) DFinsupp.equivFunOnFintype.symm

instance DFinsupp.infinite_of_left {ι : Sort _} {π : ι → Sort _} [∀ i, Nontrivial (π i)]
    [∀ i, Zero (π i)] [Infinite ι] : Infinite (Π₀ i, π i) := by
  letI := Classical.decEq ι; choose m hm using fun i => exists_ne (0 : π i)
  exact Infinite.of_injective _ (DFinsupp.single_left_injective hm)

/-- See `DFinsupp.infinite_of_right` for this in instance form, with the drawback that
it needs all `π i` to be infinite. -/
theorem DFinsupp.infinite_of_exists_right {ι : Sort _} {π : ι → Sort _} (i : ι) [Infinite (π i)]
    [∀ i, Zero (π i)] : Infinite (Π₀ i, π i) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective

/-- See `DFinsupp.infinite_of_exists_right` for the case that only one `π ι` is infinite. -/
instance DFinsupp.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite (π i)]
    [∀ i, Zero (π i)] [Nonempty ι] : Infinite (Π₀ i, π i) :=
  DFinsupp.infinite_of_exists_right (Classical.arbitrary ι)

end FiniteInfinite
