/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas

/-!
  # Signed Bitvectors

  The `Bitvec` class uses a sign-less representation, meaning it has both signed and unsigned
  versions of certain operations.
  The `SignedBitvec` type is a wrapper around `Bitvec` which exposes only the signed operations,
  and introduces notation for the operations that were omitted from `Bitvec` because they would
  have been ambiguous.
-/

/-- A signed integer, represented as a `Vector` of bits -/
abbrev SignedBitvec (n : Nat) := Bitvec n

namespace SignedBitvec

  /-- less-than -/
  def lt : SignedBitvec n → SignedBitvec n → Prop :=
    Bitvec.Slt

  /-- greater-than -/
  def gt : SignedBitvec n → SignedBitvec n → Prop :=
    Bitvec.Sgt


  /-- shift right -/
  def shr : SignedBitvec n → ℕ → SignedBitvec n :=
    Bitvec.sshr



  section Notation

    instance : LT (SignedBitvec n) where
      lt := lt

    instance : HShiftRight (SignedBitvec n) ℕ ((SignedBitvec n)) where
      hShiftRight := shr

  end Notation

end SignedBitvec
