/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Degree.Lemmas
import Mathlib.Data.Polynomial.Monic

#align_import data.polynomial.integral_normalization from "leanprover-community/mathlib"@"6f401acf4faec3ab9ab13a42789c4f68064a61cd"

/-!
# Theory of monic polynomials

We define `integralNormalization`, which relate arbitrary polynomials to monic ones.
-/


open BigOperators Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section IntegralNormalization

section Semiring

variable [Semiring R]

/-- If `f : R[X]` is a nonzero polynomial with root `z`, `integralNormalization f` is
a monic polynomial with root `leadingCoeff f * z`.

Moreover, `integralNormalization 0 = 0`.
-/
noncomputable def integralNormalization (f : R[X]) : R[X] :=
  ∑ i in f.support,
    monomial i (if f.degree = i then 1 else coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i))
#align polynomial.integral_normalization Polynomial.integralNormalization

@[simp]
theorem integralNormalization_zero : integralNormalization (0 : R[X]) = 0 := by
  simp [integralNormalization]
  -- 🎉 no goals
#align polynomial.integral_normalization_zero Polynomial.integralNormalization_zero

theorem integralNormalization_coeff {f : R[X]} {i : ℕ} :
    (integralNormalization f).coeff i =
      if f.degree = i then 1 else coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i) := by
  have : f.coeff i = 0 → f.degree ≠ i := fun hc hd => coeff_ne_zero_of_eq_degree hd hc
  -- ⊢ coeff (integralNormalization f) i = if degree f = ↑i then 1 else coeff f i * …
  simp (config := { contextual := true }) [integralNormalization, coeff_monomial, this,
    mem_support_iff]
#align polynomial.integral_normalization_coeff Polynomial.integralNormalization_coeff

theorem integralNormalization_support {f : R[X]} :
    (integralNormalization f).support ⊆ f.support := by
  intro
  -- ⊢ a✝ ∈ support (integralNormalization f) → a✝ ∈ support f
  simp (config := { contextual := true }) [integralNormalization, coeff_monomial, mem_support_iff]
  -- 🎉 no goals
#align polynomial.integral_normalization_support Polynomial.integralNormalization_support

theorem integralNormalization_coeff_degree {f : R[X]} {i : ℕ} (hi : f.degree = i) :
    (integralNormalization f).coeff i = 1 := by rw [integralNormalization_coeff, if_pos hi]
                                                -- 🎉 no goals
#align polynomial.integral_normalization_coeff_degree Polynomial.integralNormalization_coeff_degree

theorem integralNormalization_coeff_natDegree {f : R[X]} (hf : f ≠ 0) :
    (integralNormalization f).coeff (natDegree f) = 1 :=
  integralNormalization_coeff_degree (degree_eq_natDegree hf)
#align polynomial.integral_normalization_coeff_nat_degree Polynomial.integralNormalization_coeff_natDegree

theorem integralNormalization_coeff_ne_degree {f : R[X]} {i : ℕ} (hi : f.degree ≠ i) :
    coeff (integralNormalization f) i = coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i) := by
  rw [integralNormalization_coeff, if_neg hi]
  -- 🎉 no goals
#align polynomial.integral_normalization_coeff_ne_degree Polynomial.integralNormalization_coeff_ne_degree

theorem integralNormalization_coeff_ne_natDegree {f : R[X]} {i : ℕ} (hi : i ≠ natDegree f) :
    coeff (integralNormalization f) i = coeff f i * f.leadingCoeff ^ (f.natDegree - 1 - i) :=
  integralNormalization_coeff_ne_degree (degree_ne_of_natDegree_ne hi.symm)
#align polynomial.integral_normalization_coeff_ne_nat_degree Polynomial.integralNormalization_coeff_ne_natDegree

theorem monic_integralNormalization {f : R[X]} (hf : f ≠ 0) : Monic (integralNormalization f) :=
  monic_of_degree_le f.natDegree
    (Finset.sup_le fun i h =>
      WithBot.coe_le_coe.2 <| le_natDegree_of_mem_supp i <| integralNormalization_support h)
    (integralNormalization_coeff_natDegree hf)
#align polynomial.monic_integral_normalization Polynomial.monic_integralNormalization

end Semiring

section IsDomain

variable [Ring R] [IsDomain R]

@[simp]
theorem support_integralNormalization {f : R[X]} :
    (integralNormalization f).support = f.support := by
  by_cases hf : f = 0; · simp [hf]
  -- ⊢ support (integralNormalization f) = support f
                         -- 🎉 no goals
  ext i
  -- ⊢ i ∈ support (integralNormalization f) ↔ i ∈ support f
  refine' ⟨fun h => integralNormalization_support h, _⟩
  -- ⊢ i ∈ support f → i ∈ support (integralNormalization f)
  simp only [integralNormalization_coeff, mem_support_iff]
  -- ⊢ coeff f i ≠ 0 → (if degree f = ↑i then 1 else coeff f i * leadingCoeff f ^ ( …
  intro hfi
  -- ⊢ (if degree f = ↑i then 1 else coeff f i * leadingCoeff f ^ (natDegree f - 1  …
  split_ifs with hi <;> simp [hfi, hi, pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf)]
  -- ⊢ 1 ≠ 0
                        -- 🎉 no goals
                        -- 🎉 no goals
#align polynomial.support_integral_normalization Polynomial.support_integralNormalization

end IsDomain

section IsDomain

variable [CommRing R] [IsDomain R]

variable [CommSemiring S]

theorem integralNormalization_eval₂_eq_zero {p : R[X]} (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) :
    eval₂ f (z * f p.leadingCoeff) (integralNormalization p) = 0 :=
  calc
    eval₂ f (z * f p.leadingCoeff) (integralNormalization p) =
        p.support.attach.sum fun i =>
          f (coeff (integralNormalization p) i.1 * p.leadingCoeff ^ i.1) * z ^ i.1 := by
      rw [eval₂_eq_sum, sum_def, support_integralNormalization]
      -- ⊢ ∑ n in support p, ↑f (coeff (integralNormalization p) n) * (z * ↑f (leadingC …
      simp only [mul_comm z, mul_pow, mul_assoc, RingHom.map_pow, RingHom.map_mul]
      -- ⊢ ∑ x in support p, ↑f (coeff (integralNormalization p) x) * (↑f (leadingCoeff …
      exact Finset.sum_attach.symm
      -- 🎉 no goals
    _ =
        p.support.attach.sum fun i =>
          f (coeff p i.1 * p.leadingCoeff ^ (natDegree p - 1)) * z ^ i.1 := by
      by_cases hp : p = 0; · simp [hp]
      -- ⊢ ∑ i in Finset.attach (support p), ↑f (coeff (integralNormalization p) ↑i * l …
                             -- 🎉 no goals
      have one_le_deg : 1 ≤ natDegree p :=
        Nat.succ_le_of_lt (natDegree_pos_of_eval₂_root hp f hz inj)
      congr with i
      -- ⊢ ↑f (coeff (integralNormalization p) ↑i * leadingCoeff p ^ ↑i) * z ^ ↑i = ↑f  …
      congr 2
      -- ⊢ coeff (integralNormalization p) ↑i * leadingCoeff p ^ ↑i = coeff p ↑i * lead …
      by_cases hi : i.1 = natDegree p
      -- ⊢ coeff (integralNormalization p) ↑i * leadingCoeff p ^ ↑i = coeff p ↑i * lead …
      · rw [hi, integralNormalization_coeff_degree, one_mul, leadingCoeff, ← pow_succ,
          tsub_add_cancel_of_le one_le_deg]
        exact degree_eq_natDegree hp
        -- 🎉 no goals
      · have : i.1 ≤ p.natDegree - 1 :=
          Nat.le_pred_of_lt (lt_of_le_of_ne (le_natDegree_of_ne_zero (mem_support_iff.mp i.2)) hi)
        rw [integralNormalization_coeff_ne_natDegree hi, mul_assoc, ← pow_add,
          tsub_add_cancel_of_le this]
    _ = f p.leadingCoeff ^ (natDegree p - 1) * eval₂ f z p := by
      simp_rw [eval₂_eq_sum, sum_def, fun i => mul_comm (coeff p i), RingHom.map_mul,
               RingHom.map_pow, mul_assoc, ← Finset.mul_sum]
      congr 1
      -- ⊢ ∑ x in Finset.attach (support p), ↑f (coeff p ↑x) * z ^ ↑x = ∑ n in support  …
      exact @Finset.sum_attach _ _ p.support _ fun i => f (p.coeff i) * z ^ i
      -- 🎉 no goals
    _ = 0 := by rw [hz, mul_zero]
                -- 🎉 no goals
#align polynomial.integral_normalization_eval₂_eq_zero Polynomial.integralNormalization_eval₂_eq_zero

theorem integralNormalization_aeval_eq_zero [Algebra R S] {f : R[X]} {z : S} (hz : aeval z f = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) :
    aeval (z * algebraMap R S f.leadingCoeff) (integralNormalization f) = 0 :=
  integralNormalization_eval₂_eq_zero (algebraMap R S) hz inj
#align polynomial.integral_normalization_aeval_eq_zero Polynomial.integralNormalization_aeval_eq_zero

end IsDomain

end IntegralNormalization

end Polynomial
