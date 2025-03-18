-- import Mathlib.Algebra.Algebra.NonUnitalHom
-- import Mathlib.Algebra.Algebra.Pi
-- import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
-- import Mathlib.LinearAlgebra.StdBasis
import Mathlib

open Pi Finset

/-- Let `k` be an integral domain and `G` an arbitrary finite set.
Then any algebra morphism `φ : (G → k) →ₐ[k] k` is an evaluation map. -/
lemma eval_of_algHom {k G : Type*} [CommRing k] [IsDomain k] [DecidableEq G] [Fintype G]
    (φ : (G → k) →ₐ[k] k) : ∃ (s : G), φ = evalAlgHom _ _ s := by
  have h1 := map_one φ
  simp only [← univ_sum_single (1 : G → k), one_apply, map_sum] at h1
  obtain ⟨s, hs⟩ : ∃ (s : G), φ (single s 1) ≠ 0 := by
    by_contra
    simp_all
  have h2 : ∀ t ≠ s, φ (single t 1) = 0 := by
    intros
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero hs
    rw [← map_mul]
    convert map_zero φ
    ext u
    by_cases u = s <;> simp_all
  have h3 : φ (single s 1) = 1 := by
    rwa [Fintype.sum_eq_single s h2] at h1
  use s
  refine AlgHom.toLinearMap_injective (Basis.ext (basisFun k G) (fun t ↦ ?_))
  by_cases t = s <;> simp_all

-- #find_home eval_of_algHom
-- [Mathlib.LinearAlgebra.Matrix.ToLin, Mathlib.Algebra.Quaternion,
--  Mathlib.Algebra.Azumaya.Matrix, Mathlib.LinearAlgebra.Dimension.Free,
--  Mathlib.Algebra.Module.FinitePresentation, Mathlib.SetTheory.Cardinal.Free,
--  Mathlib.RingTheory.MvPolynomial.Basic, Mathlib.RingTheory.Polynomial.Basic]
