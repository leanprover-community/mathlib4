import Mathlib.Data.Set.Intervals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.LinearAlgebra.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Polynomials
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Finset.LocallyFinite.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace

open MeasureTheory Polynomial Set Real List Complex Lagrange Finset BigOperators

noncomputable section

structure my_space :=
  (I : Set ℝ)
  (μ : Measure ℝ)
  (hIInter: ∃ (a b : ℝ), a < b ∧ I = Icc a b ∨ I = Ico a b ∨ I = Ioc a b ∨ I = Ioo a b ∨
  I = Iic a ∨ I = Iio a ∨ I = Ici a ∨ I = Ioi a ∨ I = ℝ)
  --theorem interior_Iic' {a : α} (ha : (Ioi a).Nonempty) : interior (Iic a) = Iio a
  (hμPos: μ I > 0)
  (hμAbsCont : μ.restrict I ≪ volume.restrict I)
  (hμFin : IsFiniteMeasure (μ.restrict I))

def my_integral (S: my_space)(f : ℝ → ℝ) : ℝ :=
∫ x in S.I, f x ∂S.μ

def scalar_prod (S: my_space)(p q : Polynomial ℝ) : ℝ :=
my_integral S (p*q).eval

notation "⟨" p "," q "," S "⟩"  => scalar_prod S p q

def is_orthogonal (S : my_space)(p q : Polynomial ℝ): Prop :=
⟨p, q, S⟩ = 0

def has_unit_norm (S : my_space)(p : Polynomial ℝ): Prop :=
⟨p, p, S⟩ = 1

def norm (S : my_space)(p : Polynomial ℝ): ℝ :=
⟨p, p, S⟩.sqrt

def my_basis (S : my_space) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - Polynomial.C (⟨X, 1, S⟩/⟨1, 1, S⟩)
  | n+2 => (X - Polynomial.C (⟨my_basis S n+1, X * (my_basis S n+1), S⟩/
  (norm S (my_basis S n+1))^2)) * (my_basis S n+1) +
  (- Polynomial.C (⟨my_basis S n+1, X * (my_basis S n), S⟩/
  (norm S (my_basis S n))^2)) * (my_basis S n)

def my_basis_normalized (S : my_space) : ℕ → ℝ[X] :=
λ n => (my_basis S n) * Polynomial.C (1/(norm S (my_basis S n)))


theorem degree_polynomials_basis (S : my_space) :
∀ n, Polynomial.degree (my_basis_normalized S n) = n := by
intro n
induction n with
| zero =>
rw [my_basis_normalized, my_basis]
simp only [one_div, one_mul, CharP.cast_eq_zero]
refine degree_C ?zero.ha
simp only [ne_eq, inv_eq_zero]
rw [_root_.norm]
have : ¬ ⟨1,1,S⟩ = 0 := by sorry
refine (sqrt_ne_zero ?zero.ha.h).mpr this
sorry
| succ n ih => sorry

theorem polynomial_in_span_of_orthonormal_family {n : ℕ} (S : my_space)
  (p : Polynomial ℝ) (hp_deg : Polynomial.degree p ≤ n):
  p ∈ Submodule.span ℝ ((my_basis_normalized S) '' (Set.Icc 0 n)) :=
  sorry

def is_orthonormal_family (S : my_space)(f : ℕ → ℝ[X]) : Prop :=
∀ i j, i ≠ j → ((is_orthogonal S (f i) (f j)) ∧ has_unit_norm S (f i))

theorem orthonormal_basis (S : my_space) :
is_orthonormal_family S (my_basis_normalized S) := by
sorry

def is_complex_root (p : ℝ[X]) (r : ℂ) : Prop :=
IsRoot (p.map (algebraMap ℝ ℂ)) r

def has_real_internal_roots (f : ℕ → ℝ[X])(I: Set ℝ) : Prop :=
∀ n : ℕ, ∀ r : ℂ, is_complex_root (f n) r → (r.im = 0 ∧ r.re ∈ interior I)

def has_distinct_roots (f : ℕ → ℝ[X]) : Prop :=
∀ n : ℕ, ∀ r s : ℂ, is_complex_root (f n) r ∧ is_complex_root (f n) s → r ≠ s

theorem nice_roots (S : my_space):
has_real_internal_roots (my_basis_normalized S) S.I ∧
has_distinct_roots (my_basis_normalized S) := sorry

theorem casting (b : ℂ)(I : Set ℝ)(hp: b.im=0 ∧ b.re ∈ interior I):
  ∃ (a: interior I), ↑a=b := ⟨⟨b.re, hp.2⟩, Complex.ext rfl hp.1.symm⟩

def roots_embedding (b: ℂ)(I : Set ℝ)(hp : b.im = 0 ∧ b.re ∈ interior I) : interior I :=
Classical.choose (casting b I hp)

def real_roots_of_orthogonal_polynomial (S : my_space)(n : ℕ) : Set (interior S.I):=
  {r | ∃ s : ℂ,  ∃ hq : is_complex_root (my_basis_normalized S n) s,
  (r = roots_embedding s S.I ((nice_roots S).1 n s hq))
  }

theorem finite_roots (S : my_space)(n : ℕ) :
Set.Finite (real_roots_of_orthogonal_polynomial S n) := sorry

def finite_real_roots_of_orthogonal_polynomial (S : my_space)(n : ℕ) : Finset (interior S.I):=
Set.Finite.toFinset (finite_roots S n)

def weights (S : my_space)(n: ℕ)(x: ℕ → interior S.I): ℕ → ℝ :=
λ i => my_integral S (Lagrange.basis (Finset.Icc 0 n) (Subtype.val ∘ x) i).eval

def quadrature (S : my_space)(n : ℕ)(x: ℕ → interior S.I)(f : ℝ → ℝ): ℝ :=
∑ i in (Finset.Icc 0 n), ((weights S n x) i) * f (x i)

def is_exact (S : my_space)(n : ℕ)(x: ℕ → interior S.I)(k : ℕ) :=
∀ (p : ℝ[X]), (p.degree ≤ n+k) → my_integral S p.eval = quadrature S n x p.eval

theorem exactness (S : my_space)(x: ℕ → interior S.I) :
∀ (n : ℕ), is_exact S n x 1 :=
sorry

def enumeration_function (S : my_space)(A : Finset (interior S.I))(hp : A.card>0) : ℕ → interior S.I :=
λ n => orderEmbOfFin A rfl ⟨min n (A.card-1), Nat.lt_of_le_pred hp (Nat.min_le_right n (A.card - 1))⟩

theorem non_empty (S : my_space) :
∀ n : ℕ, n>0 → (finite_real_roots_of_orthogonal_polynomial S n).card > 0 :=
sorry

theorem full_exactness (S : my_space):
∀ (n : ℕ), (hq: n > 0) → is_exact S n (enumeration_function S
(finite_real_roots_of_orthogonal_polynomial S n) (non_empty S n hq)) n :=
sorry
