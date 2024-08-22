import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.LinearCombination

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

-- variant: [CommRing K] [NoZeroSMulDivisors K V]

-- variant: definition of eigenvector
-- structure LinearMap.IsEigenvector (f : V →ₗ[K] V) (μ : K) (v : V) : Prop where
--   eq_smul : f v = μ • v

macro "module" : tactic =>
  `(tactic | (try simp only [← mul_smul, smul_add, add_smul, smul_sub, sub_smul, mul_add, add_mul, sub_mul, mul_sub, smul_zero]; ring_nf; abel))

/-- Eigenvectors with distinct eigenvalues are linearly independent -/
example (f : V →ₗ[K] V) (μ ν : K) (hμν : μ ≠ ν)
    (x y : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) :
    ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  --   variant :
  --   LinearIndependent K ![x, y] := by
  -- rw [LinearIndependent.pair_iff]
  intro a b hab
  have hab' := congr(f $hab) -- introduce syntax to make this `apply_fun f at hab with hab'`
  simp [hx, hy] at hab'
  have H1 : (μ - ν) • a • x = 0 := by linear_combination (norm := module) hab' - ν • hab
  have H2 : (μ - ν) • b • y = 0 := by linear_combination (norm := module) μ • hab - hab'
  simp_all [sub_eq_zero]

example (f : V →ₗ[K] V) (μ ν : K) (hμν : μ ≠ ν)
    (x y : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) :
    ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have :=
    calc (μ - ν) • a • x = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module
      _ = f (a • x + b • y) - ν • (a • x + b • y) := by simp [hx, hy]
      _ = 0 := by simp [hab]
  have :=
    calc (μ - ν) • b • y = μ • (a • x + b • y) - (a • μ • x + b • ν • y) := by module
      _ = μ • (a • x + b • y) - f (a • x + b • y) := by simp [hx, hy]
      _ = 0 := by simp [hab]
  simp_all [sub_eq_zero]

-- minimal assumptions
example
  {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
  [NoZeroSMulDivisors R M]
  (f : M →ₗ[R] M) (μ ν : R) (hμν : μ ≠ ν)
  (x y : M) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
  (hx : f x = μ • x) (hy : f y = ν • y) :
  ∀ a b : R, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have :=
  calc (μ - ν) • a • x
      = (a • μ • x + b • ν • y) -
        ν • (a • x + b • y) := by module
    _ = f (a • x + b • y) -
        ν • (a • x + b • y) := by simp [hx, hy]
    _ = 0 := by simp [hab]
  simp_all [sub_eq_zero]

/-- ### Ternary version -/

example (f : V →ₗ[K] V) (μ ν ρ : K) (hμν : μ ≠ ν) (hμρ : μ ≠ ρ) (hνρ : ν ≠ ρ)
    (x y z : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) (hz₀ : z ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) (hz : f z = ρ • z) :
    ∀ a b c : K, a • x + b • y + c • z = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c habc
  have habc' := congr(f $habc)
  have habc'' := congr(f^[2] $habc)
  simp [hx, hy, hz] at habc' habc''
  have H1 : (μ - ν) • (μ - ρ) • a • x = 0 := by
    linear_combination (norm := module) habc'' - (ν + ρ) • habc' + ν • ρ • habc
  have H2 : (μ - ν) • (ν - ρ) • b • y = 0 := by
    linear_combination (norm := module) - habc'' + (μ + ρ) • habc' - μ • ρ • habc
  have H3 : (μ - ρ) • (ν - ρ) • c • z = 0 := by
    linear_combination (norm := module) habc'' - (μ + ν) • habc' + μ • ν • habc
  simp_all [sub_eq_zero]

/-- ### Symmetry-breaking versions

... not very readable, but short!
-/

-- binary version
example (f : V →ₗ[K] V) (μ ν : K) (hμν : μ ≠ ν)
    (x y : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) :
    ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have hab' := congr(f $hab)
  simp [hx, hy] at hab'
  have H : (μ - ν) • a • x = 0 := by linear_combination (norm := module) hab' - ν • hab
  simp_all [sub_eq_zero]

example (f : V →ₗ[K] V) (μ ν : K) (hμν : μ ≠ ν)
    (x y : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) :
    ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0 := by
  intro a b hab
  have :=
  calc (μ - ν) • a • x
      = (a • μ • x + b • ν • y) - ν • (a • x + b • y) := by module
    _ = f (a • x + b • y) - ν • (a • x + b • y) := by simp [hx, hy]
    _ = 0 := by simp [hab]
  simp_all [sub_eq_zero]

-- ternary version
example (f : V →ₗ[K] V) (μ ν ρ : K) (hμν : μ ≠ ν) (hμρ : μ ≠ ρ) (hνρ : ν ≠ ρ)
    (x y z : V) (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) (hz₀ : z ≠ 0)
    (hx : f x = μ • x) (hy : f y = ν • y) (hz : f z = ρ • z) :
    ∀ a b c : K, a • x + b • y + c • z = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c habc
  have habc' := congr(f $habc)
  have habc'' := congr(f^[2] $habc)
  simp [hx, hy, hz] at habc' habc''
  have H1 : (μ - ν) • (μ - ρ) • a • x = 0 := by
    linear_combination (norm := module) habc'' - (ν + ρ) • habc' + ν • ρ • habc
  obtain rfl : a = 0 := by simp_all [sub_eq_zero]
  have H2 : (ν - ρ) • b • y = 0 := by linear_combination (norm := module) habc' - ρ • habc
  simp_all [sub_eq_zero]

section
-- spelling out a simp step
variable (f : V →ₗ[K] V)
  (μ ν : K) (x y : V) (a b : K)

example
  (hx : f x = μ • x) (hy : f y = ν • y) :
  f (a • x + b • y) =
  (a • μ • x + b • ν • y) := by
calc
    f (a • x + b • y)
    = f (a • x) + f (b • y) := by
        rw [map_add]
  _ = a • f x + b • f y := by
        rw [map_smul, map_smul]
  _ = (a • μ • x + b • ν • y) := by
        rw [hx, hy]

end
