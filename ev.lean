import Mathlib.LinearAlgebra.LinearIndependent

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

-- variant: [CommRing K] [NoZeroSMulDivisors K V]

-- variant: definition of eigenvector
-- structure LinearMap.IsEigenvector (f : V →ₗ[K] V) (μ : K) (v : V) : Prop where
--   eq_smul : f v = μ • v

/-- Eigenvectors with distinct eigenvalues are linearly independent -/
example (f : V →ₗ[K] V) (μ ν : K) (hμν : μ ≠ ν)
    (x y : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) :
    ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  --   variant :
  --   LinearIndependent K ![x, y] := by
  -- rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congr(f $hab - ν • $hab)
  have h2 := congr(μ • $hab - f $hab)
  simp [hx, hy, ← mul_smul, mul_comm] at h1 h2
  have H1 : (μ - ν) • a • x = 0 := by
    simpa [sub_smul, mul_smul] using h1
  have H2 : (μ - ν) • b • y = 0 := by
    simpa [sub_smul, mul_smul] using h2
  simp_all [hμν, hx₀, hy₀, sub_eq_zero]

