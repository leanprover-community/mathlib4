/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.InformationTheory.Entropy.Shannon
public import Mathlib.InformationTheory.EntropyNumber.Int



/-!
# Programs and Computational Descriptions

This file defines the `Program` type — an initial state paired with a
`ComputerTape` of instructions — together with the key type aliases
used throughout the information-theory library, and the RECT / IRECT
bridge between programs and entropy.

## Main definitions

* `Program` — a state plus a `ComputerTape` of instructions.
* `ComputationalDescription` — alias for `Program`.
* `InformationContentR` / `InformationContent` /
  `CanonicalInformation` — type aliases for clarity.
* `programToEntropy` — IRECT: a program has an information content.
* `equivProgramToCanonicalInfo` — canonical equivalence
  `Program ≃ CanonicalInformation`.

## Main results

* `exists_program_of_complexity` — for any `L`, there is a program of
  complexity `L`.
* `exists_program_of_entropy` — RECT: any entropy value has a
  corresponding program.
* `program_entropy_inverse` — RECT/IRECT round-trip: complexity and
  entropy agree.

## Tags

program, computational description, RECT, IRECT, entropy
-/

@[expose] public section

open Finset Real

namespace InformationTheory

/-! ## Program -/

/-- A `Program` is defined by an initial state and a tape of
instructions that drives its evolution. -/
structure Program where
  /-- The current (initial) state of the program. -/
  current_state : ℤ
  /-- The instruction tape. -/
  tape : ComputerTape

/-- Helper to create a new program at a starting position. -/
def Program.mk' (initial_pos : Int) : Program :=
  { tape := [], current_state := initial_pos }

namespace Program

/-- The computational complexity of a `Program`, defined as the length
of its input `ComputerTape`, representing the number of i.i.d.
binary choices processed. -/
def complexity (prog : Program) : ℕ :=
  prog.tape.length

/-- Updates the tape of a `Program`, returning a new program with the
same initial state but a different instruction tape. This allows
treating a `Program` as a reusable machine and `updateTape` as the
mechanism for loading a new input tape. -/
def updateTape (prog : Program) (new_tape : ComputerTape) :
    Program :=
  { current_state := prog.current_state,
    tape := new_tape }

end Program

/-! ## Type aliases -/

/-- `InformationContentR` is the measure of uncertainty or information
in a real-valued system, quantified in bits. -/
abbrev InformationContentR := ℝ

/-- A `ComputationalDescription` is a deterministic set of
instructions that encodes the outcome of a process.
Alias for `Program`. -/
abbrev ComputationalDescription := Program

/-- The amount of information (in bits) required to distinguish one
state from an ensemble of `2^L` equiprobable states. Simply `L`. -/
abbrev InformationContent := ℕ

/-- The "information" represented by a canonical program is the pair
of numbers (outcome, runtime) that uniquely defines it. -/
abbrev CanonicalInformation := EntropyInt × ComputerTape

/-! ## Program ≃ CanonicalInformation -/

/-- The canonical equivalence `Program ≃ CanonicalInformation`.
A program *is* its initial state plus its path. -/
noncomputable def equivProgramToCanonicalInfo :
    Program ≃ CanonicalInformation :=
{
  toFun := fun prog =>
    let initialStateInfo :=
      entropyIntEquivInt.symm prog.current_state
    (initialStateInfo, prog.tape),

  invFun := fun info =>
    let initialStateVal := entropyIntEquivInt info.fst
    {
      current_state := initialStateVal,
      tape := info.snd
    },

  left_inv := by
    intro p
    simp,

  right_inv := by
    intro i
    simp
}

/-! ## RECT / IRECT -/

/-- **Simplified RECT (Information → Program):** For any given
amount of information content `L`, there exists a computer program
whose complexity is exactly `L`. -/
theorem exists_program_of_complexity (L : InformationContent) :
    ∃ (prog : Program), prog.complexity = L := by
  let gnat_L : EntropyNat := EntropyNat.ofNat L
  let tape_L : ComputerTape := gnat_L.val
  let prog_exists : Program := {
    current_state := 0,
    tape := tape_L
  }
  use prog_exists
  simp [Program.complexity, tape_L]
  exact EntropyNat.ofNat_toNat L

/-- **RECT (Rota's Entropy & Computability Theorem):**
`InformationContentR` implies a `Program`. For any amount of
information `H`, there exists a program whose complexity (tape
length) is `⌈H⌉`. -/
theorem exists_program_of_entropy (H : InformationContentR) :
    ∃ (prog : ComputationalDescription),
      prog.complexity = Nat.ceil H := by
  let L := Nat.ceil H
  use { current_state := 0, tape := List.replicate L true }
  simp [Program.complexity]
  aesop

/-- **IRECT (Inverse RECT):** A `Program` has an equivalent
`InformationContentR`. Any program of complexity `L` represents a
single choice from `2^L` equiprobable states, with information
content `L` bits. -/
noncomputable def programToEntropy
    (prog : ComputationalDescription) : InformationContentR :=
  (prog.complexity : ℝ)

/-- The inverse relationship between IRECT and RECT. -/
theorem program_entropy_inverse (L : ℕ) :
    ∃ (prog : ComputationalDescription),
      programToEntropy prog = (L : ℝ) ∧
        prog.complexity = L := by
  use { current_state := 0, tape := List.replicate L true }
  simp [programToEntropy, Program.complexity]

end InformationTheory
