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
/-- The data of a basic constructible set `s` is a tuple `(f, g₁, ..., gₙ)` -/
@[ext]
structure BasicConstructibleSetData where
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `f`. -/
  protected f : R
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `n`. -/
  protected n : ℕ
  /-- Given the data of a basic constructible set `s = V(g₁, ..., gₙ) \ V(f)`, return `g`. -/
  protected g : Fin n → R

namespace BasicConstructibleSetData

noncomputable instance : DecidableEq (BasicConstructibleSetData R) := Classical.decEq _

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | φ x ∈ I} ∈ s}`. -/
@[simps]
noncomputable def map (φ : R →+* S) (C : BasicConstructibleSetData R) :
    BasicConstructibleSetData S where
  f := φ C.f
  n := C.n
  g := φ ∘ C.g

@[simp] lemma map_id (C : BasicConstructibleSetData R) : C.map (.id _) = C := by simp [map]

@[simp] lemma map_id' : map (.id R) = id := by ext : 1; simp

lemma map_comp (φ : S →+* T) (ψ : R →+* S) (C : BasicConstructibleSetData R) :
    C.map (φ.comp ψ) = (C.map ψ).map φ := by simp [map, image_image, Function.comp_def]

lemma map_comp' (φ : S →+* T) (ψ : R →+* S) : map (φ.comp ψ) = map φ ∘ map ψ := by
  ext : 1; simp [map_comp]

/-- Given the data of a basic constructible set `s`, namely a tuple `(f, g₁, ..., gₙ)` such that
`s = V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
def toSet (C : BasicConstructibleSetData R) : Set (PrimeSpectrum R) :=
  zeroLocus (Set.range C.g) \ zeroLocus {C.f}

@[simp]
lemma toSet_map (φ : R →+* S) (C : BasicConstructibleSetData R) :
    (C.map φ).toSet = comap φ ⁻¹' C.toSet := by simp [toSet, map, ← Set.range_comp]

end BasicConstructibleSetData

variable (R) in
/-- The data of a constructible set `s` in the prime spectrum of a ring is finitely many tuples
`(f, g₁, ..., gₙ)` such that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`.

To obtain `s` from its data, use `PrimeSpectrum.ConstructibleSetData.toSet`. -/
abbrev ConstructibleSetData := Finset (BasicConstructibleSetData R)

namespace ConstructibleSetData

/-- Given the data of the constructible set `s`, build the data of the constructible set
`{I | {x | f x ∈ I} ∈ s}`. -/
noncomputable def map (φ : R →+* S) (s : ConstructibleSetData R) : ConstructibleSetData S :=
  s.image (.map φ)

@[simp]
lemma map_id (s : ConstructibleSetData R) : s.map (.id _) = s := by simp [map]

lemma map_comp (f : S →+* T) (g : R →+* S) (s : ConstructibleSetData R) :
    s.map (f.comp g) = (s.map g).map f := by
  simp [map, image_image, Function.comp_def, BasicConstructibleSetData.map_comp']

/-- Given the data of a constructible set `s`, namely finitely many tuples `(f, g₁, ..., gₙ)` such
that `s = ⋃ (f, g₁, ..., gₙ), V(g₁, ..., gₙ) \ V(f)`, return `s`. -/
def toSet (S : ConstructibleSetData R) : Set (PrimeSpectrum R) := ⋃ C ∈ S, C.toSet

@[simp]
lemma toSet_map (f : R →+* S) (s : ConstructibleSetData R) :
    (s.map f).toSet = comap f ⁻¹' s.toSet := by
  unfold toSet map
  rw [set_biUnion_finset_image]
  simp [← Set.range_comp]

/-- The degree bound on a constructible set for Chevalley's theorem for the inclusion `R ↪ R[X]`. -/
def degBound (S : ConstructibleSetData R[X]) : ℕ := S.sup fun C ↦ ∑ i, (C.g i).degree.succ

end PrimeSpectrum.ConstructibleSetData
