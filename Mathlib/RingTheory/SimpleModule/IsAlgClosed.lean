/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Wedderburn–Artin Theorem over an algebraically closed field
-/

variable (F R : Type*) [Field F] [IsAlgClosed F] [Ring R] [Algebra F R]

/-- The **Wedderburn–Artin Theorem** over algebraically closed fields: a finite-dimensional
simple algebra over an algebraically closed field is isomorphic to a matrix algebra over the field.
-/
theorem IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    [IsSimpleRing R] [FiniteDimensional F R] :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (R ≃ₐ[F] Matrix (Fin n) (Fin n) F) :=
  have := IsArtinianRing.of_finite F R
  have ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := exists_algEquiv_matrix_divisionRing_finite F R
  ⟨n, hn, ⟨e.trans <| .mapMatrix <| .symm <| .ofBijective (Algebra.ofId F D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

/-- The **Wedderburn–Artin Theorem** over algebraically closed fields: a finite-dimensional
semisimple algebra over an algebraically closed field is isomorphic to a product of matrix algebras
over the field. -/
theorem IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    [IsSemisimpleRing R] [FiniteDimensional F R] :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F) :=
  have ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing_finite F R
  ⟨n, d, hd, ⟨e.trans <| .piCongrRight fun i ↦ .mapMatrix <| .symm <| .ofBijective
    (Algebra.ofId F (D i)) IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩
