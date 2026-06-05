/-
Copyright (c) 2026 Jiabai Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiabai Wang
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

/-!
# Determinantal ideals of a generic matrix

This file defines minors of the generic matrix `Matrix.mvPolynomialX` and the ideal generated
by all minors of a fixed size.
-/

namespace Matrix

/-- Index data for a `t × t` minor of an `m × n` matrix.

The row and column choices are encoded as order embeddings, so the selected indices are listed
in strictly increasing order. -/
structure MinorIndex (m n t : ℕ) where
  /-- The chosen row indices, in increasing order. -/
  row : Fin t ↪o Fin m
  /-- The chosen column indices, in increasing order. -/
  col : Fin t ↪o Fin n

namespace MinorIndex

/-- Two minor indices are equal when they choose the same rows and columns. -/
@[ext]
theorem ext {m n t : ℕ} {I J : MinorIndex m n t}
  (hrow : ∀ a, I.row a = J.row a) (hcol : ∀ a, I.col a = J.col a) :
    I = J := by
  cases I
  cases J
  congr
  · ext a
    exact congrArg Fin.val (hrow a)
  · ext a
    exact congrArg Fin.val (hcol a)

/-- There are finitely many minor indices of any fixed shape. -/
instance instFinite {m n t : ℕ} : Finite (MinorIndex m n t) := by
  refine Finite.of_injective (fun I : MinorIndex m n t => (I.row, I.col)) ?_
  intro I J h
  cases I;cases J;cases h
  rfl

/-- The finite type structure on minor indices of any fixed shape. -/
noncomputable instance instFintype {m n t : ℕ} : Fintype (MinorIndex m n t) :=
  Fintype.ofFinite (MinorIndex m n t)

/-- The concrete minor of a matrix selected by a minor index. -/
def detSubmatrix {R : Type*} [CommRing R] {m n t : ℕ}
    (I : MinorIndex m n t) (A : Matrix (Fin m) (Fin n) R) : R :=
  det <| submatrix A I.row I.col

/-- Concrete minors are natural with respect to a ring homomorphism. -/
theorem detSubmatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {m n t : ℕ}
    (I : MinorIndex m n t) (A : Matrix (Fin m) (Fin n) R) :
    f (I.detSubmatrix A) = I.detSubmatrix (A.map f) := by
  simpa [submatrix_map] using (RingHom.map_det f (submatrix A I.row I.col))

/-- The minor of the generic `m × n` matrix selected by a minor index. -/
noncomputable def mvPolynomialMinor (R : Type*) [CommRing R] {m n t : ℕ}
    (I : MinorIndex m n t) :
    MvPolynomial (Fin m × Fin n) R :=
  I.detSubmatrix (Matrix.mvPolynomialX (Fin m) (Fin n) R)

/-- The unique `0 × 0` generic minor is `1`. -/
@[simp]
theorem mvPolynomialMinor_zero (R : Type*) [CommRing R] {m n : ℕ}
    (I : MinorIndex m n 0) :
    I.mvPolynomialMinor R = 1 := by
  rw [mvPolynomialMinor, detSubmatrix, det_isEmpty]

/-- A `1 × 1` generic minor is the corresponding variable. -/
@[simp]
theorem mvPolynomialMinor_one (R : Type*) [CommRing R] {m n : ℕ}
    (I : MinorIndex m n 1) :
    I.mvPolynomialMinor R = MvPolynomial.X (I.row 0, I.col 0) := by
  simp [mvPolynomialMinor, detSubmatrix]

/-- Evaluating a generic minor at a concrete matrix gives the corresponding concrete minor. -/
theorem eval_mvPolynomialMinor (R : Type*) [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] {m n t : ℕ}
    (A : Matrix (Fin m) (Fin n) S) (I : MinorIndex m n t) :
    MvPolynomial.aeval (fun ij : Fin m × Fin n => A ij.1 ij.2)
      (I.mvPolynomialMinor R) = I.detSubmatrix A := by
  let M : Matrix (Fin t) (Fin t) (MvPolynomial (Fin m × Fin n) R) :=
    submatrix (Matrix.mvPolynomialX (Fin m) (Fin n) R) I.row I.col
  have hdet :=
    (AlgHom.map_det (MvPolynomial.aeval fun ij : Fin m × Fin n => A ij.1 ij.2) M).symm
  have hM :
      M.map (MvPolynomial.aeval fun ij : Fin m × Fin n => A ij.1 ij.2) =
        submatrix A I.row I.col := by
    ext i j
    simp [M]
  exact Eq.mpr (congrFun (congrArg Eq (id (Eq.symm hdet))) (I.detSubmatrix A)) (congrArg det hM)

/-- Mapping coefficients sends a generic minor to the corresponding generic minor. -/
theorem map_mvPolynomialMinor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {m n t : ℕ} (I : MinorIndex m n t) :
    MvPolynomial.map f (I.mvPolynomialMinor R) = I.mvPolynomialMinor S := by
  unfold mvPolynomialMinor detSubmatrix
  have hdet :
      MvPolynomial.map f
          (det (submatrix (Matrix.mvPolynomialX (Fin m) (Fin n) R) I.row I.col)) =
        det
          ((submatrix (Matrix.mvPolynomialX (Fin m) (Fin n) R) I.row I.col).map
            (MvPolynomial.map f)) := by
    simpa using
      (RingHom.map_det (MvPolynomial.map f)
        (submatrix (Matrix.mvPolynomialX (Fin m) (Fin n) R) I.row I.col))
  have hX :
      (Matrix.mvPolynomialX (Fin m) (Fin n) R).map (MvPolynomial.map f) =
        Matrix.mvPolynomialX (Fin m) (Fin n) S := by
    ext i j
    simp
  rw [← hX]
  simpa [submatrix_map] using hdet

end MinorIndex

end Matrix

namespace MvPolynomial

/-- The finite set of all `t × t` minors of the generic `m × n` matrix. -/
noncomputable def determinantalMinorFinset
    (R : Type*) [CommRing R] (m n t : ℕ) :
    Finset (MvPolynomial (Fin m × Fin n) R) := by
  classical
  exact Finset.univ.image fun I : Matrix.MinorIndex m n t =>
    I.mvPolynomialMinor R

/-- Membership in the finite set of all generic minors. -/
theorem mem_determinantalMinorFinset
    (R : Type*) [CommRing R] {m n t : ℕ}
    {f : MvPolynomial (Fin m × Fin n) R} :
    f ∈ determinantalMinorFinset R m n t
      ↔ ∃ I : Matrix.MinorIndex m n t, I.mvPolynomialMinor R = f := by
  classical
  constructor
  · intro hf
    rcases Finset.mem_image.1 hf with ⟨I, _, hI⟩
    exact ⟨I, hI⟩
  · rintro ⟨I, hI⟩
    exact Finset.mem_image.2 ⟨I, by simp, hI⟩

/-- The ideal generated by all `t × t` minors of the generic `m × n` matrix. -/
def determinantalIdeal
    (R : Type*) [CommRing R] (m n t : ℕ) :
    Ideal (MvPolynomial (Fin m × Fin n) R) :=
  Ideal.span (determinantalMinorFinset R m n t : Set _)

/-- Every `t × t` generic minor belongs to the corresponding determinantal ideal. -/
theorem mvPolynomialMinor_mem_determinantalIdeal
    (R : Type*) [CommRing R] {m n t : ℕ}
    (I : Matrix.MinorIndex m n t) :
    I.mvPolynomialMinor R ∈ determinantalIdeal R m n t := by
  exact Ideal.subset_span ((mem_determinantalMinorFinset R).2 ⟨I, rfl⟩)

/-- A determinantal ideal is contained in `J` iff every generating minor belongs to `J`. -/
theorem determinantalIdeal_le_iff
    (R : Type*) [CommRing R] {m n t : ℕ}
    {J : Ideal (MvPolynomial (Fin m × Fin n) R)} :
    determinantalIdeal R m n t ≤ J
      ↔ ∀ I : Matrix.MinorIndex m n t, I.mvPolynomialMinor R ∈ J := by
  constructor
  · intro h I
    exact h (mvPolynomialMinor_mem_determinantalIdeal R I)
  · intro h
    rw [determinantalIdeal]
    exact Ideal.span_le.mpr fun f hf => by
      rcases (mem_determinantalMinorFinset R).1 hf with ⟨I, hI⟩
      rw [← hI]
      exact h I

/-- The determinantal ideal is the span of the finite set of generic minors. -/
theorem determinantalIdeal_eq_span_determinantalMinorFinset
    (R : Type*) [CommRing R] (m n t : ℕ) :
    determinantalIdeal R m n t =
      Ideal.span
        (determinantalMinorFinset R m n t : Set (MvPolynomial (Fin m × Fin n) R)) :=
  rfl

/-- Determinantal ideals are finitely generated. -/
theorem determinantalIdeal_fg
    (R : Type*) [CommRing R] (m n t : ℕ) :
    (determinantalIdeal R m n t).FG := by
  refine ⟨determinantalMinorFinset R m n t, ?_⟩
  exact (determinantalIdeal_eq_span_determinantalMinorFinset R m n t).symm

/-- Determinantal ideals commute with coefficient-wise base change. -/
theorem map_determinantalIdeal
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m n t : ℕ) :
    Ideal.map (MvPolynomial.map f) (determinantalIdeal R m n t) =
      determinantalIdeal S m n t := by
  rw [determinantalIdeal, determinantalIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases (mem_determinantalMinorFinset R).1 hq with ⟨I, hI⟩
    rw [← hI]
    exact (mem_determinantalMinorFinset S).2
      ⟨I, (Matrix.MinorIndex.map_mvPolynomialMinor f I).symm⟩
  · intro hp
    rcases (mem_determinantalMinorFinset S).1 hp with ⟨I, hI⟩
    refine ⟨I.mvPolynomialMinor R, (mem_determinantalMinorFinset R).2 ⟨I, rfl⟩, ?_⟩
    rw [Matrix.MinorIndex.map_mvPolynomialMinor f I, hI]

end MvPolynomial
