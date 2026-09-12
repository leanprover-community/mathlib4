/-
Copyright (c) 2026 Francisco Ramírez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Francisco Ramírez
-/

module
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Measure-preserving map from a fixed point of the pushforward

A measurable map `T` with `ν.map T = ν` (i.e. `ν` is a fixed point of the
pushforward by `T`) is `MeasurePreserving T ν ν`. This is the anonymous
constructor of `MeasurePreserving` exposed under a discoverable name, useful
in Krylov–Bogolyubov-type arguments where one obtains a fixed point of the
pushforward and needs to promote it to `MeasurePreserving`.

## Main results

* `measurePreserving_of_map_eq`: `Measurable T` + `ν.map T = ν` ⇒
  `MeasurePreserving T ν ν`.

## Tags

measure preserving, pushforward, fixed point, invariant measure
-/

@[expose] public section

open MeasureTheory

/-- A measurable map `T` with `ν.map T = ν` is `MeasurePreserving T ν ν`.
This is the constructor of `MeasurePreserving` (whose fields are
`measurable` and `map_eq`), exposed under a name discoverable in
Krylov–Bogolyubov contexts. -/
theorem measurePreserving_of_map_eq {X : Type*} [MeasurableSpace X]
    {T : X → X} (hT : Measurable T) {ν : Measure X} (hfix : ν.map T = ν) :
    MeasurePreserving T ν ν :=
  ⟨hT, hfix⟩
