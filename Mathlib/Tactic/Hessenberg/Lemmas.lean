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

The characteristic polynomial of a matrix from a `Matrix.Hessenberg.Similarity` certificate, by the
recurrence on the Hessenberg form that the certificate carries.
-/

public section

open Polynomial

namespace Mathlib.Tactic.Hessenberg

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} {A : Matrix (Fin n) (Fin n) R}

theorem charpoly_eq_ofCoeffList (cert : Matrix.Hessenberg.Similarity A) :
    A.charpoly = ofCoeffList (coeffHessCharPoly n cert.H.toArray) :=
  cert.charpoly_eq.symm.trans <| (charpoly_eq_hessCharPoly cert.H cert.isUpperHessenberg).trans
    (hessCharPoly_eq_ofCoeffList n _)

theorem charpoly_eq_ofCoeffList_of_eq (cert : Matrix.Hessenberg.Similarity A) {Harr : Array R}
    {cs : List R} (hH : cert.H.toArray = Harr)
    (h : coeffHessCharPoly n Harr = cs) : A.charpoly = ofCoeffList cs := by
  rw [charpoly_eq_ofCoeffList cert, hH, h]

end Mathlib.Tactic.Hessenberg

end
