module
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Complex.Basic

/-!
Rewriting steps from Physlib's SL2C and Minkowski dual constructions and
CrouzeixConjecture's completion identity, with the project-specific data
replaced by parameters. These tests retain the original `noncomm_ring` calls.
-/

open Matrix

-- Physlib/Relativity/SL2C/Basic.lean: the image of a self-adjoint matrix.
example (M : Matrix (Fin 2) (Fin 2) ℂ)
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    M * A.1 * Mᴴ ∈ selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) := by
  noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
    conjTranspose_mul, conjTranspose_conjTranspose,
    (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]

-- Physlib/Relativity/SL2C/SelfAdjoint.lean: composition of conjugation maps.
example (M N A : Matrix (Fin 2) (Fin 2) ℂ) :
    M * N * A * (M * N)ᴴ = M * (N * A * Nᴴ) * Mᴴ := by
  noncomm_ring [Matrix.conjTranspose_mul]

-- Physlib/Relativity/MinkowskiMatrix.lean: contravariance of the dual.
example {n : Type*} [Fintype n] [DecidableEq n]
    (η Λ Λ' : Matrix n n ℝ) (hη : η * η = 1) :
    η * (Λ * Λ')ᵀ * η = (η * Λ'ᵀ * η) * (η * Λᵀ * η) := by
  simp only [transpose_mul, ← mul_assoc]
  noncomm_ring [hη]

-- CrouzeixConjecture/CompletionAlgebra.lean: inverse hypotheses in a quadratic form.
example {R₀ : Type*} [Ring R₀] (G Ginv P R : R₀)
    (hGinvG : Ginv * G = 1) (hGGinv : G * Ginv = 1) :
    4 * R - 2 * P - (G + R) * Ginv * P - P * Ginv * (G + R) +
        2 * (P * Ginv * P) =
      4 * (R - P) - (R - P) * Ginv * P - P * Ginv * (R - P) := by
  noncomm_ring [hGinvG, hGGinv]

example {R : Type*} [Ring R] (a b : R) (h : True → a * b = 0) :
    a * b + b * a = b * a := by
  noncomm_ring (config := { zeta := false }) (discharger := trivial) [h]
