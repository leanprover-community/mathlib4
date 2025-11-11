/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! # Division algorithm with respect to monomial orders

We provide a division algorithm with respect to monomial orders in polynomial rings.
Let `R` be a commutative ring, `σ` a type of indeterminates and `m : MonomialOrder σ`
a monomial ordering on `σ →₀ ℕ`.

Consider a family of polynomials `b : ι → MvPolynomial σ R` with invertible leading coefficients
(with respect to `m`) : we assume `hb : ∀ i, IsUnit (m.leadingCoeff (b i))`).

* `MonomialOrder.div hb f` furnishes
  - a finitely supported family `g : ι →₀ MvPolynomial σ R`
  - and a “remainder” `r : MvPolynomial σ R`
such that the three properties hold:
  (1) One has `f = ∑ (g i) * (b i) + r`
  (2) For every `i`, `m.degree ((g i) * (b i)` is less than or equal to that of `f`
  (3) For every `i`, every monomial in the support of `r` is strictly smaller
    than the leading term of `b i`,

The proof is done by induction, using two standard constructions

* `MonomialOrder.subLTerm f` deletes the leading term of a polynomial `f`

* `MonomialOrder.reduce hb f` subtracts from `f` the appropriate multiple of `b : MvPolynomial σ R`,
  provided `IsUnit (m.leadingCoeff b)`.

* `MonomialOrder.div_set` is the variant of `MonomialOrder.div` for a set of polynomials.

* `MonomialOrder.div_single` is the variant of `MonomialOrder.div` for a single polynomial.


## Reference : [Becker-Weispfenning1993]

-/

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

variable (m) in
/-- Delete the leading term in a multivariate polynomial (for some monomial order) -/
noncomputable def subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f - monomial (m.degree f) (m.leadingCoeff f)

theorem degree_sub_LTerm_le (f : MvPolynomial σ R) :
    m.degree (m.subLTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

theorem degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f ≠ 0) :
    m.degree (m.subLTerm f) ≺[m] m.degree f := by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f ≠ 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m), hf'] at this
  apply this
  simp [subLTerm, coeff_monomial, leadingCoeff]

variable (m) in
/-- Reduce a polynomial modulo a polynomial with unit leading term (for some monomial order) -/
noncomputable
def reduce {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.leadingCoeff f) * b

theorem degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
    (hbf : m.degree b ≤ m.degree f) (hf : m.degree f ≠ 0) :
    m.degree (m.reduce hb f) ≺[m] m.degree f := by
  have H : m.degree f =
      m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.leadingCoeff f)) +
        m.degree b := by
    classical
    rw [degree_monomial, if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_zero_iff]
      intro hf0
      apply hf
      simp [hf0]
  have H' : coeff (m.degree f) (m.reduce hb f) = 0 := by
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 2 [H]
    rw [coeff_mul_of_degree_add (m := m), leadingCoeff_monomial, mul_comm, ← mul_assoc,
      IsUnit.mul_val_inv, one_mul, ← leadingCoeff]
  rw [lt_iff_le_and_ne]
  constructor
  · classical
    apply le_trans degree_sub_le
    simp only [sup_le_iff, le_refl, true_and]
    apply le_of_le_of_eq degree_mul_le
    rw [m.toSyn.injective.eq_iff]
    exact H.symm
  · intro K
    simp only [EmbeddingLike.apply_eq_iff_eq] at K
    nth_rewrite 1 [← K] at H'
    rw [← leadingCoeff, leadingCoeff_eq_zero_iff] at H'
    rw [H', degree_zero] at K
    exact hf K.symm

/-- Division by a family of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
theorem div {ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.degree (b i * (g i)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ i, ¬ (m.degree (b i) ≤ c)) := by
  by_cases hb' : ∃ i, m.degree (b i) = 0
  · obtain ⟨i, hb0⟩ := hb'
    use Finsupp.single i ((hb i).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      nth_rewrite 2 [eq_C_of_degree_eq_zero hb0]
      rw [mul_comm, smul_eq_C_mul]
    constructor
    · intro j
      by_cases hj : j = i
      · apply le_trans degree_mul_le
        simp only [hj, hb0, Finsupp.single_eq_same, zero_add]
        apply le_of_eq
        simp only [EmbeddingLike.apply_eq_iff_eq]
        apply degree_smul (Units.isRegular _)
      · simp only [Finsupp.single_eq_of_ne hj, mul_zero, degree_zero, map_zero]
        apply bot_le
    · simp
  push_neg at hb'
  by_cases hf0 : f = 0
  · refine ⟨0, 0, by simp [hf0], ?_, by simp⟩
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
    exact bot_le
  by_cases hf : ∃ i, m.degree (b i) ≤ m.degree f
  · obtain ⟨i, hf⟩ := hf
    have deg_reduce : m.degree (m.reduce (hb i) f) ≺[m] m.degree f := by
      apply degree_reduce_lt (hb i) hf
      intro hf0'
      apply hb' i
      simpa [hf0'] using hf
    obtain ⟨g', r', H'⟩ := div hb (m.reduce (hb i) f)
    use g' +
      Finsupp.single i (monomial (m.degree f - m.degree (b i)) ((hb i).unit⁻¹ * m.leadingCoeff f))
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [reduce]
    constructor
    · rintro j
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [mul_add]
      apply le_trans degree_add_le
      simp only [sup_le_iff]
      constructor
      · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
      · classical
        rw [Finsupp.single_apply]
        split_ifs with hc
        · subst j
          grw [degree_mul_le, map_add, degree_monomial_le, ← map_add, add_tsub_cancel_of_le hf]
        · simp only [mul_zero, degree_zero, map_zero]
          exact bot_le
    · exact H'.2.2
  · push_neg at hf
    suffices ∃ (g' : ι →₀ MvPolynomial σ R), ∃ r',
        (m.subLTerm f = Finsupp.linearCombination (MvPolynomial σ R) b g' + r') ∧
        (∀ i, m.degree ((b  i) * (g' i)) ≼[m] m.degree (m.subLTerm f)) ∧
        (∀ c ∈ r'.support, ∀ i, ¬ m.degree (b i) ≤ c) by
      obtain ⟨g', r', H'⟩ := this
      use g', r' +  monomial (m.degree f) (m.leadingCoeff f)
      constructor
      · simp [← add_assoc, ← H'.1, subLTerm]
      constructor
      · exact fun b ↦ le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
      · intro c hc i
        by_cases hc' : c ∈ r'.support
        · exact H'.2.2 c hc' i
        · convert hf i
          classical
          have := MvPolynomial.support_add hc
          rw [Finset.mem_union, Classical.or_iff_not_imp_left] at this
          simpa only [Finset.mem_singleton] using support_monomial_subset (this hc')
    by_cases hf'0 : m.subLTerm f = 0
    · refine ⟨0, 0, by simp [hf'0], ?_, by simp⟩
      intro b
      simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
      exact bot_le
    · exact (div hb) (m.subLTerm f)
termination_by WellFounded.wrap
  ((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wf) (m.toSyn (m.degree f))
decreasing_by
· exact deg_reduce
· apply degree_sub_LTerm_lt
  intro hf0
  apply hf'0
  simp only [subLTerm, sub_eq_zero]
  nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
  simp

/-- Division by a *set* of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
theorem div_set {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) := by
  obtain ⟨g, r, H⟩ := m.div (b := fun (p : B) ↦ p) (fun b ↦ hB b b.prop) f
  exact ⟨g, r, H.1, H.2.1, fun c hc b hb ↦ H.2.2 c hc ⟨b, hb⟩⟩

/-- Division by a multivariate polynomial
whose leading coefficient is invertible with respect to a monomial order -/
theorem div_single {b : MvPolynomial σ R}
    (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : MvPolynomial σ R) (r : MvPolynomial σ R),
      f = g * b + r ∧
        (m.degree (b * g) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ¬ (m.degree b ≤ c)) := by
  obtain ⟨g, r, hgr, h1, h2⟩ := div_set (B := {b}) (m := m) (by simp [hb]) f
  specialize h1 ⟨b, by simp⟩
  set q := g ⟨b, by simp⟩
  simp only [Set.mem_singleton_iff, forall_eq] at h2
  simp only at h1
  refine ⟨q, r, ?_, h1, h2⟩
  rw [hgr]
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id_eq, smul_eq_mul, add_left_inj]
  rw [Finsupp.sum_eq_single ⟨b, by simp⟩ _ (by simp)]
  simp +contextual

end MonomialOrder
