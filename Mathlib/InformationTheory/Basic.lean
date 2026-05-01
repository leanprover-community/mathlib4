/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Control.Random
public import Mathlib.Data.Fintype.Vector

@[expose] public section


/-!
# InformationTheory.Basic: Shared Types

Core types and definitions shared across the InformationTheory library.
This file provides the binary instruction model (`ComputerInstruction`,
`ComputerTape`, `ComputerProgram`), i.i.d. particle sources, random-walk
paths, and position helpers.

## Main definitions

* `ComputerInstruction` — a single binary choice (`Bool`).
* `ComputerTape` — a sequence of binary choices (`List Bool`).
* `ComputerProgram` — abbreviation for `ComputerTape`.
* `IIDParticleSource` — typeclass for an i.i.d. stream indexed by `ℕ`.
* `CanonicalIIDParticleSource` — an i.i.d. source emitting canonical sorted
  paths.
* `CanonicalSymmetricParticlePath` — type alias for `List Bool`.
* `RandomWalkPath` — abbreviation for `List Bool`.
* `numOnes` — count of `true` entries in a path.
* `ParticlePosition` — abbreviation for `ℤ`.
* `calcParticlePosition` — compute particle position after a walk.
* `randomWalkFromPosition` — encode a position as a random-walk path.
* `mkPseudoRandomSource` — pseudo-random i.i.d. `Bool` source from a seed.
* `mkBiasedIIDParticleSource` — biased i.i.d. `Bool` source from a seed.

## Main results

* `ComputerProgram.length_eq` — program length equals tape length.
* `ComputerProgram.append_length` — concatenation has additive length.
-/

open List

namespace InformationTheory

/-! ## ComputerInstruction / ComputerTape / ComputerProgram -/

/-- A single instruction/choice, represented by a `Bool`. -/
def ComputerInstruction := Bool

/-- A sequence of choices/instructions forming a tape. -/
def ComputerTape := List ComputerInstruction

/-- A computer program is represented as a tape of binary instructions. -/
abbrev ComputerProgram := ComputerTape

/-- Program length equals tape length. -/
@[simp] theorem ComputerProgram.length_eq (prog : ComputerProgram) :
    prog.length = (prog : ComputerTape).length := rfl

/-- Concatenating two programs yields a program with additive length. -/
@[simp] theorem ComputerProgram.append_length (p q : ComputerProgram) :
    (List.append p q).length = p.length + q.length := by
  simp

/-! ## IID Particle Sources -/

/-- An i.i.d. source producing values of type `α` indexed by `ℕ`. -/
class IIDParticleSource (α : Type) where
  /-- The stream of values. -/
  stream : ℕ → α

/-- A canonical i.i.d. source that produces symmetric, sorted paths. -/
class CanonicalIIDParticleSource extends IIDParticleSource (List Bool) where
  /-- Each stream value is the canonical sorted path. -/
  toCanonical : ∀ (n : ℕ),
    stream n = (List.replicate n true ++ List.replicate n false).mergeSort
      (fun a b => !a && b)

/-- The canonical representation of a particle path is symmetric and sorted. -/
def CanonicalSymmetricParticlePath := List Bool

/-- A random walk path is a list of boolean steps. -/
abbrev RandomWalkPath := List Bool

/-- Count the number of `true` entries in a path. -/
def numOnes (p_path : RandomWalkPath) : ℕ :=
  p_path.count true

/-- A particle position is an integer. -/
abbrev ParticlePosition := ℤ

/-- Calculate the position of a particle after walking a path from an initial position. -/
def calcParticlePosition (initial_pos : ℤ) (p_path : RandomWalkPath) : ℤ :=
  let ones := numOnes p_path
  let path_len := p_path.length
  let zeros := path_len - ones
  let mag_initial := Int.natAbs initial_pos
  let (ones', zeros') :=
    if initial_pos >= 0 then
      (ones + mag_initial, zeros)
    else
      (ones, zeros + mag_initial)
  (ones' : ℤ) - (zeros' : ℤ)

/-- Construct the random-walk encoding of a particle position. -/
def randomWalkFromPosition (pos : ParticlePosition) : RandomWalkPath :=
  let sign_bit := decide (pos >= 0)
  let magnitude := Int.natAbs pos
  List.append [sign_bit] (List.replicate magnitude true)

/-- A pseudo-random i.i.d. source seeded by a natural number. -/
instance mkPseudoRandomSource (seed : ℕ) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }

/-- A biased i.i.d. source generating `true` with probability `p / (p + q)`. -/
instance mkBiasedIIDParticleSource (seed : ℕ) (p : ℕ) (q : ℕ)
    (_h : p + q > 0) : IIDParticleSource Bool :=
{ stream := fun n =>
    let gen0 := mkStdGen seed
    let genN := (List.range n).foldl (fun g _ => (stdNext g).2) gen0
    (randBool genN).1 }

end InformationTheory
