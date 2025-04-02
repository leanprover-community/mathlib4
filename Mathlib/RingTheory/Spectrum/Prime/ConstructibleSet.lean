/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Order.SuccPred.WithBot
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Constructible sets in the prime spectrum

This file provides tooling for manipulating constructible sets in the prime spectrum of a ring.

## TODO

Link to constructible sets in a topological space.
-/

open Finset
open scoped Polynomial

namespace PrimeSpectrum
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

variable (R) in
/-- The data of a constructible set `s` is finitely many tuples `(f, g₁, ..., gₙ)` such that
`s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`.

To obtain `s` from its data, use `PrimeSpectrum.ConstructibleSetData.toSet`. -/
abbrev ConstructibleSetData := Finset (R × Σ n, Fin n → R)

namespace ConstructibleSetData

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | f x ∈ I} ∈ s}`. -/
def map [DecidableEq S] (f : R →+* S) (s : ConstructibleSetData R) : ConstructibleSetData S :=
  s.image fun ⟨r, n, g⟩ ↦ ⟨f r, n, f ∘ g⟩

@[simp]
lemma map_id [DecidableEq R] (s : ConstructibleSetData R) : s.map (.id _) = s := by simp [map]

lemma map_comp [DecidableEq S] [DecidableEq T] (f : S →+* T) (g : R →+* S)
    (s : ConstructibleSetData R) : s.map (f.comp g) = (s.map g).map f := by
  simp [map, image_image, Function.comp_def]

/-- Given the data of a constructible set `s`, namely finitely many tuples `(f, g₁, ..., gₙ)` such
that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) :=
  ⋃ x ∈ S, zeroLocus (Set.range x.2.2) \ zeroLocus {x.1}

@[simp]
lemma toSet_map [DecidableEq S] (f : R →+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp [← Set.range_comp]

/-- The degree bound on a constructible set for Chevalley's theorem for the inclusion `R ↪ R[X]`. -/
def degBound (S : ConstructibleSetData R[X]) : ℕ := S.sup fun e ↦ ∑ i, (e.2.2 i).degree.succ

end PrimeSpectrum.ConstructibleSetData
