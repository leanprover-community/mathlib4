/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Similarity
public import Mathlib.Tactic.Hessenberg.CharPoly
public import Mathlib.Tactic.Hessenberg.Coeffs

/-!
# The Hessenberg recurrence on similarity certificates

The characteristic polynomial of a matrix from a `Hessenberg.Similarity` certificate, by the
recurrence on the Hessenberg form that the certificate carries.
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}

theorem charpoly_eq_ofCoeffs (cert : Hessenberg.Similarity A) :
    A.charpoly = ofCoeffs (coeffHessCharPoly n cert.H.toArray) :=
  cert.charpoly_eq.trans <| (charpoly_eq_hessCharPoly cert.H cert.H_hessenberg).trans
    (hessCharPoly_eq_ofCoeffs n _)

theorem charpoly_eq_ofCoeffs_of_eq (cert : Hessenberg.Similarity A) {Harr : Array R} {cs : List R}
    (hH : cert.H.toArray = Harr)
    (h : coeffHessCharPoly n Harr = cs) : A.charpoly = ofCoeffs cs := by
  rw [charpoly_eq_ofCoeffs cert, hH, h]

end Mathlib.Tactic.Hessenberg

end
