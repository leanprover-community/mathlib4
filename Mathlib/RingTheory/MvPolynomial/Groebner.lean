/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Division algorithm with respect to monomial orders

We provide a division algorithm with respect to monomial orders in polynomial rings.
Let `R` be a commutative ring, `σ` a type of indeterminates and `m : MonomialOrder σ`
a monomial ordering on `σ →₀ ℕ`.

Consider a family of polynomials `b : ι → MvPolynomial σ R` with invertible leading coefficients
(with respect to `m`): we assume `hb : ∀ i, IsUnit (m.leadingCoeff (b i))`.

* `MonomialOrder.div hb f` furnishes
  - a finitely supported family `g : ι →₀ MvPolynomial σ R`
  - and a “remainder” `r : MvPolynomial σ R`
    such that the three properties hold:
    1. One has `f = ∑ (g i) * (b i) + r`
    2. For every `i`, `m.degree ((g i) * (b i)` is less than or equal to that of `f`
    3. For every `i`, every monomial in the support of `r` is strictly smaller
       than the leading term of `b i`,

The proof is done by induction, using two standard constructions

* `MonomialOrder.subLTerm f` deletes the leading term of a polynomial `f`

* `MonomialOrder.reduce hb f` subtracts from `f` the appropriate multiple of `b : MvPolynomial σ R`,
  provided `IsUnit (m.leadingCoeff b)`.

* `MonomialOrder.div_set` is the variant of `MonomialOrder.div` for a set of polynomials.

* `MonomialOrder.div_single` is the variant of `MonomialOrder.div` for a single polynomial.


## Reference : [Becker-Weispfenning1993], [MOLLER1988345]

-/

@[expose] public section

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
    rw [degree_monomial, ite_eq_right]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_zero_iff]
      intro hf0
      apply hf
      simp [hf0]
  have H' : (m.reduce hb f).coeff (m.degree f) = 0 := by
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 3 [H]
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

lemma withBotDegree_le_withBotDegree_of_toColex_support_le_toColex_support {R} [CommSemiring R]
    {f g : MvPolynomial σ R}
    (h : toColex (f.support.image m.toSyn) ≤ toColex (g.support.image m.toSyn)) :
    m.toWithBotSyn (m.withBotDegree f) ≤ m.toWithBotSyn (m.withBotDegree g) := by
  have := Finset.Colex.max_ofColex_le_max_ofColex_of_le h
  simp_rw [ofColex_toColex, Finset.max_eq_sup_coe, Finset.sup_image] at this
  -- todo: the two sub-goals should be a lemma or definition in #40010 later
  convert this <;> simp [toWithBotSyn, withBotDegree, Finset.max_eq_sup_coe]

lemma toColex_support_sub_lt_toColex_support_of_leadingTerm_eq {e : σ →₀ ℕ} {f g : MvPolynomial σ R}
    (he : e ∈ f.support) (h : m.leadingTerm g = monomial e (f.coeff e)) :
    toColex ((f - g).support.image m.toSyn) < toColex (f.support.image m.toSyn) := by
  simp_rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt, ← m.toSyn.coe_toEquiv,
    Equiv.image_eq_preimage_symm_of_finset, m.toSyn.coe_toEquiv_symm, Finset.mem_preimage]
  use m.toSyn e
  simp only [leadingTerm, leadingCoeff, monomial_eq_monomial_iff, coeff_degree_eq_zero_iff,
    mem_support_iff.mp he, and_false, or_false] at h
  rcases h with ⟨rfl, h⟩
  simp_rw [m.toSyn.symm_apply_apply, and_iff_right he, mem_support_iff, coeff_sub, h, not_ne_iff]
  refine ⟨by simp, fun b hb hfb ↦ ?_⟩
  simp only [hfb, zero_sub, ne_eq, neg_eq_zero] at hb
  apply lt_of_le_of_ne (m.toSyn.apply_symm_apply b ▸ m.le_degree <| mem_support_iff.mpr hb)
  grind [m.toSyn.symm_apply_apply]

lemma toColex_support_sub_le_toColex_support_of_leadingTerm_eq {e : σ →₀ ℕ} {f g : MvPolynomial σ R}
    (h : m.leadingTerm g = monomial e (f.coeff e)) :
    toColex ((f - g).support.image m.toSyn) ≤ toColex (f.support.image m.toSyn) := by
  by_cases he : e ∈ f.support
  · exact le_of_lt <| m.toColex_support_sub_lt_toColex_support_of_leadingTerm_eq he h
  rw [notMem_support_iff.mp he, monomial_zero, leadingTerm_eq_zero_iff] at h
  simp [h]

lemma withBotDegree_sub_le_withBotDegree {e : σ →₀ ℕ} {f g : MvPolynomial σ R}
    (h : m.leadingTerm g = monomial e (f.coeff e)) :
    m.withBotDegree (f - g) ≼'[m] m.withBotDegree f :=
  withBotDegree_le_withBotDegree_of_toColex_support_le_toColex_support <|
    toColex_support_sub_le_toColex_support_of_leadingTerm_eq h

attribute [local instance] WellFoundedLT.toWellFoundedRelation in
open Classical in
theorem weakDiv {ι : Type*} (b : ι → MvPolynomial σ R) (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.withBotDegree (b i) + m.withBotDegree (g i) ≼'[m] m.withBotDegree f) ∧
        ∀ e ∈ r.support, monomial e (r.coeff e) ∉ Ideal.span (Set.range <| m.leadingTerm ∘ b) := by
  classical
  by_cases! hb :
    ∀ e ∈ f.support, monomial e (f.coeff e) ∉ Ideal.span (Set.range (m.leadingTerm ∘ b))
  · exact ⟨0, f, by simp, by simp, hb⟩
  have hf0 : f ≠ 0 := by contrapose hb with rfl; simp
  obtain ⟨deg, hdeg_mem, hdeg_sum⟩ := hb
  simp_rw [m.monomial_mem_span_range_leadingTerm_tfae.out 1 5] at hdeg_sum
  rcases hdeg_sum with ⟨g_, hg_deg, hg_sum⟩
  have ⟨g', r', hg'sum, hg'deg, hdeg'sum⟩ := weakDiv (b := b) (f - g_.linearCombination _ b)
  use g_ + g', r'
  rw [sub_eq_iff_eq_add', ← add_assoc, ← map_add] at hg'sum
  refine ⟨hg'sum, fun i ↦ ?_, hdeg'sum⟩
  simp_rw [map_add] at ⊢ hg_deg hg'deg
  rcases le_max_iff.mp <| m.withBotDegree_add_le (g_ i) (g' i) with hle | hle
  · apply le_trans <| add_le_add (le_refl ..) hle
    apply le_trans <| hg_deg _
    exact m.le_withBotDegree hdeg_mem
  apply le_trans <| add_le_add (le_refl ..) hle
  apply le_trans <| hg'deg _
  exact m.withBotDegree_sub_le_withBotDegree hg_sum.symm
termination_by toColex <| f.support.image m.toSyn
decreasing_by exact m.toColex_support_sub_lt_toColex_support_of_leadingTerm_eq hdeg_mem hg_sum.symm

theorem weakDiv_set {B : Set (MvPolynomial σ R)} (f : MvPolynomial σ R) :
    (∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
      (∀ (b : B), m.withBotDegree b.val + m.withBotDegree (g b) ≼'[m] m.withBotDegree f) ∧
      ∀ e ∈ r.support, monomial e (r.coeff e) ∉ Ideal.span (m.leadingTerm '' B)) := by
  obtain ⟨g, r, H⟩ := m.weakDiv (b := fun (p : B) ↦ p) f
  refine ⟨g, r, H.1, H.2.1, fun e he hb ↦ H.2.2 e he <| by simpa [Set.range_comp]⟩

lemma monomial_mem_span_range_leadingTerm_iff_of_isUnit {R ι} [CommSemiring R]
    {e : σ →₀ ℕ} {c : R}
    {b : ι → MvPolynomial σ R} (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (hc : c ≠ 0) :
    monomial e c ∈ Ideal.span (Set.range (m.leadingTerm ∘ b)) ↔ ∃ i, m.degree (b i) ≤ e := by
  classical
  rw [Set.range_comp, m.span_leadingTerm_eq_span_monomial (by simpa using hb),
    ← Function.comp_def (monomial · (1 : R)) (m.degree (R := R)), Set.image_comp,
    mem_ideal_span_monomial_image]
  simp [support_monomial, hc]

/-- Division by a family of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
theorem div {ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.degree (b i * (g i)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ i, ¬ (m.degree (b i) ≤ c)) := by
  obtain ⟨g, r, hsum, hdeg, hr⟩ := m.weakDiv b f
  use g, r, hsum
  split_ands
  · intro i
    apply m.degree_le_degree_of_withBotDegree_le_withBotDegree
    exact le_trans (m.withBotDegree_mul_le ..) (hdeg i)
  intro e he
  specialize hr e he
  simpa [monomial_mem_span_range_leadingTerm_iff_of_isUnit hb (mem_support_iff.mp he)] using hr

/-!
Module doc as workaround for a parser error that prevents using `set_option`
after a `decreasing_by` block with focus dots.

See https://github.com/leanprover/lean4/issues/12573
-/

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
