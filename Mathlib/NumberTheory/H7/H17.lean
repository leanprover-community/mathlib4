
import Mathlib.LinearAlgebra.Matrix.PosDef
#check Matrix.posSemidef_iff_eq_transpose_mul_self

variable {n : Type} {R: Type } {A : Matrix n n R} [NonUnitalNonAssocSemiring R]
  [StarRing R] [Fintype n] [CommRing R] [PartialOrder R]


#check Matrix.PosSemidef


open Matrix MvPolynomial

/--
Theorem 1. Let A be a symmetric matrix with entries in R[x₁, . . . , xₘ].
If A is positive semidefinite for all substitutions (x₁, . . . , xₘ) ∈ Rᵐ,
then A can be expressed as a sum of squares of symmetric matrices with entries
in R(x₁, . . . , xₘ).
-/
theorem theorem1 (m n : ℕ) :
  -- Let R be the polynomial ring ℝ[x₁, ..., xₘ]
  let R := MvPolynomial (Fin m) ℝ
  -- Let K be its field of fractions, the rational functions ℝ(x₁, ..., xₘ)
  let K := FractionRing R
  -- For any n × n matrix A with polynomial entries:
  ∀ (A : Matrix (Fin n) (Fin n) ℝ),
    -- If A is symmetric,
    A.IsSymm →
    -- and if A is positive semidefinite for all real substitutions,
    (∀ (x : Fin m → ℝ), (h : A.PosSemidef) →
    -- then there exists a list of symmetric matrices S with rational function entries,
    ∃ (S : List (Matrix (Fin n) (Fin n) ℝ)), (∀ s ∈ S, s.IsSymm) ∧
      -- such that A is the sum of the squares of the matrices in S.
      (A) = (S.map (fun s ↦ s * s)).sum) := by
  -- The proof of this theorem is non-trivial and is omitted.
  sorry

variable {F : Type*} [Field F]

structure IsRealField (F : Type*) [Field F] : Type

-- We work over a generic commutative ring `R`
variable {n : ℕ} {R : Type*} [CommRing R]

/--
The **principal submatrix** of a matrix `A` for a given `Finset` of indices `s`.
It's the matrix formed by keeping the rows and columns of `A` with indices in `s`.
-/
noncomputable def principalSubmatrix (A : Matrix (Fin n) (Fin n) R) (s : Finset (Fin n)) :
    Matrix (Fin s.card) (Fin s.card) R :=
  -- This lambda function makes the type conversion explicit for Lean.
  A.submatrix (fun i => s.equivFin.symm i) (fun i => s.equivFin.symm i)

/--
The **principal minor** of `A` for a given `Finset` of indices `s`.
It is the determinant of the corresponding principal submatrix.
-/
noncomputable def principalMinor (A : Matrix (Fin n) (Fin n) R) (s : Finset (Fin n)) : R :=
  det (principalSubmatrix A s)

/--
A **computable** function that maps an index `i` from `Fin s.card` to the
`i`-th smallest index in the finset `s`.
-/
def computableFinsetMap (s : Finset (Fin n)) : Fin s.card → Fin n :=
  let sorted_s := Finset.sort (· ≤ ·) s
  fun i => sorted_s.get ⟨i.val, by
    -- We provide the value and the proof directly to construct the `Fin` type.
    rw [Finset.length_sort]
    exact i.isLt⟩

/--
The **principal submatrix** of `A` defined computably by sorting the indices in `s`.
-/
def computablePrincipalSubmatrix (A : Matrix (Fin n) (Fin n) R) (s : Finset (Fin n)) :
    Matrix (Fin s.card) (Fin s.card) R :=
  A.submatrix (computableFinsetMap s) (computableFinsetMap s)

/--
The principal minor of `A`.
-/
def computablePrincipalMinor (A : Matrix (Fin n) (Fin n) R) (s : Finset (Fin n)) : R :=
  det (computablePrincipalSubmatrix A s)

/--
The **k-th leading principal minor** of `A`.
It is the determinant of the top-left `k × k` submatrix.
The hypothesis `k ≤ n` is required.
-/
def leadingPrincipalMinor (A : Matrix (Fin n) (Fin n) R) (k : ℕ) (hk : k ≤ n) : R :=
  det (A.submatrix (Fin.castLE hk) (Fin.castLE hk))

/--
A predicate stating that `x` can be written as a sum of squares.
For example, `SumOfSq 5` is true in ℚ because 5 = 1² + 2².
-/
def SumOfSq (x : F) : Prop :=
  ∃ (l : List F), x = (l.map (fun y ↦ y * y)).sum

/--
Theorem 3. Let F be a real field and let A be a symmetric matrix with entries in F.
If the principal minors of A can be expressed as sums of squares in F, then A
is a sum of squares of symmetric matrices with entries in F.
-/
theorem theorem3 {F : Type*} [Field F] :
  -- For any n × n matrix A with entries in F:
  ∀ (A : Matrix (Fin n) (Fin n) F),
    -- If A is symmetric,
    A.IsSymm →
    -- and if all its principal minors are sums of squares in F,
    (∀ (s : Finset (Fin n)), SumOfSq (computablePrincipalMinor A s)) →
    -- then A can be expressed as a sum of squares of symmetric matrices over F.
    ∃ (S : List (Matrix (Fin n) (Fin n) F)),
      (∀ s ∈ S, s.IsSymm) ∧ A = (S.map (fun s ↦ s * s)).sum := by
  -- Proof is omitted.
  sorry
