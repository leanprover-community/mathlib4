/-
Copyright (c) 2025 Junyu Guo and Hao Shen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyu Guo, Hao Shen
-/
module

public import Mathlib.RingTheory.MvPolynomial.Groebner.Division
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic.DepRewrite

/-! # Remainder

The following definition is abstracted from the "remainder" as in `MonomialOrder.div_set`. And more
properties of it is covered in this file.

* `MonomialOrder.IsRemainder m f B r`: Given a multivariate polynomial `f` and a "divisors" set `B`
  of with respect to a monomial order `m`. A polynomial `r` is called a remainder of `f` on
  division by `B` if there exists a finitely supported function `g` s.t.

  1. Finite linear combination:
    `f = ∑ (g(b) * b) + r`;
  2. Degree condition:
     For each `b ∈ B`, the degree (with bot) of `g(b) * b` ≤ the degree (with bot) of `f` w.r.t.
     monomial order `m`;
  3. Remainder irreducibility:
    No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.

And there're also some equivalent variants.

* `MonomialOrder.IsRemainder.isRemainder_def'`: A variant of `MonomialOrder.IsRemainder`
  without coercion of a `Set (MvPolynomial σ R)`.

* `MonomialOrder.IsRemainder.isRemainder_def''`: A variant of `MonomialOrder.IsRemainder` where
  `g : MvPolynomial σ R →₀ MvPolynomial σ R` is replaced with a
  function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its support.

* `MonomialOrder.IsRemainder.isRemainder_def_degree`: A variant where the degree condition is
  formalized with `m.degree`, which matches the statement of `MonomialOrder.div_set`.

* `MonomialOrder.IsRemainder.isRemainder_range`: A variant of `MonomialOrder.IsRemainder` where
  divisors are given as a family of polynomials.

There exists a remainder when the polynomial ring is communitive and any divisor either has an
invertible leading coefficient or is 0.

* `MonomialOrder.IsRemainder.exists_isRemainder`.

## Naming convention

Some theorems with an argument in type `Set (MvPolynomial σ R)` and a hypothesis that leading
coefficients of all polynomials in the set are invertible have 2 variants, named as following
respectively:

* without suffix `'` or `₀`: any polynomial `b` in the set has an invertible leading coefficient
  (`IsUnit (m.leadingCoeff p)`);
* with suffix `₀`: any polynomial `b` in the set either has an invertible leading coefficient or is
  equal to 0 (`IsUnit (m.leadingCoeff p) ∨ b = 0`);
* with suffix `'`: no hypotheses on leading coefficients, while requiring `R` to be a field
  (`Field k`, where the ring is denoted as `k` instead).

## Implementation notes

The definition of remainder makes sense when `R` is a communitive ring and any polynomial in `B`
either has an invertible leading coefficient or is 0, while for simplicity we try to formalize
it without applying these restrictions as its hypotheses.

We try to adjust its formal definition s.t. it corresponds with the informal definition well when
the above condition holds, while keeps simple and still shares some common properties without these
hypotheses.

* Degree condition is formalized as
  ```lean
  m.toWithBotSyn (m.withBotDegree b.val) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
    m.toWithBotSyn (m.withBotDegree f)
  ```
  instead of `m.withBotDegree (b.val * g b) ≼'[m] m.withBotDegree f`.

  If `IsRemainder` was formalized with the latter one, some properties would require polynomials in
  `B` to have non-zero divisor leading coefficients since they need
  `m.withBotDegree (b.val * g b) = m.withBotDegree (b.val) + m.withBotDegree (g b)` with this
  formalization of `IsRemainder`. They no longer require this if `IsRemainder` is formalized with
  former one.

* Remainder irreducibility is formalized as `∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)`,
  where `¬ (m.degree b ≤ c)` is sufficient but unnecessary for the indivisibility between the
  leading term of `b` (`m.leadingTerm b`) and the term of `r` with exponents `c`
  (`monomial c (b.coeff c)`).

## Reference : [Cox2015]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

/-- Given a multivariate polynomial `f` and a "divisors" set `B` of multivariate polynomials over
`R`. A polynomial `r` is called a remainder of `f` on division by `B` with respect to a monomial
order `m`, if there exists `g : B →₀ MvPolynomial σ R` s.t.

1. Finite linear combination:
  `f = ∑ (g(b) * b) + r`;
2. Degree condition:
  For eacho `b ∈ B`, the degree (with bot) of `g(b) * b` ≤ the degree (with bot) of `f` w.r.t. `m`;
3. Remainder irreducibility:
  No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.

The definition of remainder makes sense when `R` is a communitive ring and any polynomial in `B`
either has an invertible leading coefficient or is 0. See the implementation note for the
formalization unaligned with the informal definition when not in this case.
-/
def IsRemainder {σ : Type*} (m : MonomialOrder σ) {R : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :=
  (∃ (g : B →₀ MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (b : B) ↦ b.val) g + r ∧
    ∀ (b : B),
      m.toWithBotSyn (m.withBotDegree b.val) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
        m.toWithBotSyn (m.withBotDegree f)) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

namespace IsRemainder

section CommSemiring
variable {σ : Type*} {m : MonomialOrder σ}

variable {R : Type*} [CommSemiring R]
variable (f p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)

/--
A variant of `MonomialOrder.IsRemainder` without coercion of a `Set (MvPolynomial σ R)`.
-/
theorem isRemainder_def' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B,
          m.toWithBotSyn (m.withBotDegree b) + m.toWithBotSyn (m.withBotDegree (g b)) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  apply and_congr_left'
  rw [Function.Surjective.exists (Finsupp.restrictSupportEquiv B (MvPolynomial σ R)).surjective]
  conv in Finsupp.linearCombination _ _ _ =>
    -- simp? [Finsupp.linearCombination,
    --   Finsupp.sum_subtypeDomain_index (p := (· ∈ B)) (h := fun a b ↦ b * a) x.2] says
    simp only [Finsupp.linearCombination, Finsupp.restrictSupportEquiv_apply, Finsupp.coe_lsum,
      LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, smul_eq_mul,
      Finsupp.sum_subtypeDomain_index (p := (· ∈ B)) (h := fun a b ↦ b * a) x.2]
  simp [Subtype.exists, exists_prop, -exists_and_left, and_assoc, Finsupp.linearCombination]

/--
A variant of `MonomialOrder.IsRemainder` where `g : MvPolynomial σ R →₀ MvPolynomial σ R` is
replaced with a function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its
support.
-/
theorem isRemainder_def'' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) :
    m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R) (B' : Finset (MvPolynomial σ R)),
        ↑B' ⊆ B ∧
        p = B'.sum (fun x => g x * x) + r ∧
        ∀ b' ∈ B',
          m.toWithBotSyn (m.withBotDegree (b' : MvPolynomial σ R)) +
          m.toWithBotSyn (m.withBotDegree (g b')) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  rw [isRemainder_def']
  constructor
  · intro ⟨⟨g, h₁, h₂, h₃⟩, h₄⟩
    refine ⟨?_, h₄⟩
    use g.toFun, g.support
    refine ⟨h₁, by rwa [Finsupp.linearCombination_apply, Finsupp.sum] at h₂, ?_⟩
    intro g' hg'
    exact h₃ g' (Set.mem_of_mem_of_subset hg' h₁)
  · intro ⟨⟨g, B', h₁, h₂, h₃⟩, h₄⟩
    refine ⟨?_, h₄⟩
    use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro ..)
    split_ands
    · simp_intro b' hb'
      exact Set.mem_of_mem_of_subset hb'.1 h₁
    · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
      congr 1
      simp? [Finset.filter_and, Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter,
          Finset.filter_inter] says
        simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Finset.filter_and,
          Finset.filter_mem_eq_inter, Finset.inter_self, Finset.inter_filter,
          Finsupp.onFinset_apply, id_eq, smul_eq_mul, ite_mul, zero_mul, Finset.sum_ite_mem,
          Finset.filter_inter]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : g b' = 0 <;> simp [hb']
    · intro b hb
      by_cases hbB' : b ∈ B' <;> simp [hbB', h₃]

/--
A variant of `MonomialOrder.IsRemainder_def'` where `B` is `Finset (MvPolynomial σ R)`.
-/
theorem isRemainder_finset (p : MvPolynomial σ R) (B' : Finset (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        ∀ b' ∈ B',
          m.toWithBotSyn (m.withBotDegree (b' : MvPolynomial σ R)) +
          m.toWithBotSyn (m.withBotDegree (g b')) ≤
            m.toWithBotSyn (m.withBotDegree p)) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  constructor
  · rw [isRemainder_def']
    intro ⟨⟨g, hgsup, hsum, hg⟩, hr⟩
    refine ⟨?_, hr⟩
    use g.toFun
    refine ⟨?_, hg⟩
    simp? [Finsupp.linearCombination_apply, Finsupp.sum]  at hsum says
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, id_eq, smul_eq_mul] at hsum
    rw [hsum]
    congr 1
    apply Finset.sum_subset hgsup
    simp_intro ..
  · rw [isRemainder_def'']
    intro ⟨⟨g, hsum, hg⟩, hr⟩
    refine ⟨?_, hr⟩
    use fun b' ↦ if b' ∈ B' then g b' else 0
    use B'
    split_ands
    · rfl
    · simp [hsum]
    · simp_intro .. [hg]

theorem isRemainder_iff_exists_isRemainder_finset (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p B r ↔
      (∃ (B' : Finset (MvPolynomial σ R)), ↑B' ⊆ B ∧ m.IsRemainder p B' r) ∧
        ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  simp_rw [isRemainder_def'' (B := B), isRemainder_finset]
  constructor
  · rintro ⟨⟨g, B', hB'B, hsum, hdeg⟩, hdeg'⟩
    refine ⟨⟨↑B', hB'B, ?_⟩ , hdeg'⟩
    refine ⟨⟨g, hsum, hdeg⟩, fun _ h _ hb ↦ hdeg' _ h _ (hB'B hb)⟩
  · rintro ⟨⟨B', hB'B, ⟨⟨g, hsum, hdeg⟩, -⟩⟩, hdeg'⟩
    exact ⟨⟨g, B', hB'B, hsum, hdeg⟩, hdeg'⟩

/-- `r` is a remainder of a family of polynomials, if and only if it is a remainder with properities
defined in `MonomialOrder.div` with this family of polynomials given as a map from indexes to them.

It is a variant of `MonomialOrder.IsRemainder` where divisors are given as a map from indexes to
polynomials. -/
theorem isRemainder_range {ι : Type*} (f : MvPolynomial σ R)
    (b : ι → MvPolynomial σ R) (r : MvPolynomial σ R) :
    m.IsRemainder f (Set.range b) r ↔
      (∃ g : ι →₀ MvPolynomial σ R,
        f = Finsupp.linearCombination _ b g + r ∧
        ∀ i : ι,
          m.toWithBotSyn (m.withBotDegree (b i : MvPolynomial σ R)) +
          m.toWithBotSyn (m.withBotDegree (g i)) ≤
            m.toWithBotSyn (m.withBotDegree f)) ∧
      ∀ c ∈ r.support, ∀ i : ι, b i ≠ 0 → ¬ (m.degree (b i) ≤ c) := by
  classical
  constructor
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    let idx : Set.range b ↪ ι := {
      toFun := Set.rangeSplitting b,
      inj' := Set.rangeSplitting_injective b
    }
    split_ands
    · use Finsupp.embDomain idx g
      split_ands
      · simp [h₁, idx]
      · intro i
        specialize h₂ ⟨b i, Set.mem_range_self i⟩
        wlog! h' : (Finsupp.embDomain idx g) i ≠ 0
        · simp [h']
        convert h₂
        generalize_proofs hbi
        rw [Finsupp.embDomain_apply, Ne.dite_ne_right_iff fun h ↦ by simpa [h] using h'] at h'
        rw [Finsupp.embDomain_apply, dite_cond_eq_true (by simp [h'])]
        generalize_proofs h'
        rw! (occs := [2, 3]) [← h'.choose_spec]
        simp [idx, Set.apply_rangeSplitting]
    · intro i hi b hb
      aesop
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    constructor
    · letI b'_range : Finset (Set.range b) := g.support.image (Set.rangeFactorization b)
      letI g' (x : Set.range b) : MvPolynomial σ R := (g.support.filter (b · = x)).sum g
      have mem_support (x) (hx : g' x ≠ 0) : x ∈ b'_range := by
        contrapose! hx
        simp? [b'_range, Set.rangeFactorization_eq_iff]  at hx says
          simp only [Finset.mem_image, Finsupp.mem_support_iff, ne_eq,
            Set.rangeFactorization_eq_iff, not_exists, not_and, b'_range] at hx
        apply Finset.sum_eq_zero
        simp? says simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, and_imp]
        tauto
      use Finsupp.onFinset b'_range g' mem_support
      split_ands
      · simp? [h₁, Finsupp.linearCombination_apply, Finsupp.sum] says
          simp only [h₁, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
            Finsupp.onFinset_apply]
        congr
        rw [eq_comm, Finset.sum_subset (s₂ := b'_range) (by simp) (by simp_intro ..)]
        unfold b'_range g'
        apply Finset.sum_image'
        simp? [Finset.sum_mul] says
          simp only [Finsupp.mem_support_iff, ne_eq, Set.rangeFactorization_coe, Finset.sum_mul,
            Set.rangeFactorization_eq_rangeFactorization_iff]
        intro _ _
        apply Finset.sum_congr rfl
        simp_intro ..
      · intro b1
        rw [Finsupp.onFinset]
        apply le_trans (add_le_add_right m.withBotDegree_sum_le _)
        have := (m.toWithBotSyn (m.withBotDegree b1.val) + ·)
        rw [Finset.comp_sup_eq_sup_comp_of_is_total (m.toWithBotSyn (m.withBotDegree b1.val) + ·)]
        · simp_rw [Finset.sup_le_iff, Finset.mem_filter]
          rintro _ ⟨-, h⟩
          simp [← h, h₂]
        · simp_intro _ _ _ [add_le_add]
        simp
    · aesop

/--
Remainders are preserved on insertion of the zero polynomial into the set of divisors.
-/
@[simp]
theorem isRemainder_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p (insert 0 B) r ↔ m.IsRemainder p B r := by
  unfold IsRemainder
  convert and_congr_left' ?_
  · aesop
  rw [(Finsupp.comapDomain_surjective (f := (⟨·.val, by simp⟩ : B → ↑(insert 0 B))) ?_).exists]
  on_goal 2 => simp [Function.Injective]
  congr! with g
  on_goal 2 => aesop
  rw [Finsupp.linearCombination_comapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  convert (g.support.sum_preimage ..).symm
  intro x hx hx'
  simp [or_iff_not_imp_right.mp x.prop (by simpa using hx')]

/--
Remainders are preserved with the zero polynomial removed from the set of divisors.
-/
@[simp]
theorem isRemainder_sdiff_singleton_zero_iff_isRemainder (p : MvPolynomial σ R)
  (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
  m.IsRemainder p (B \ {0}) r ↔ m.IsRemainder p B r := by
  by_cases h : 0 ∈ B
  · rw [←isRemainder_insert_zero_iff_isRemainder, show insert 0 (B \ {0}) = B by simp [h]]
  · simp [h]

variable {B} in
theorem isRemainder_zero {r : MvPolynomial σ R}
    (h : m.IsRemainder 0 B r) : r = 0 := by
  classical
  unfold IsRemainder at h
  obtain ⟨⟨g, h0sumg, hg⟩, hr⟩ := h
  rw [h0sumg, eq_comm]
  convert zero_add r
  apply Finset.sum_eq_zero (f := fun x ↦ g x * x.val)
  intro x _
  specialize hg x
  simp? at hg says
    simp only [withBotDegree_zero, toWithBotSyn_apply_bot, le_bot_iff, WithBot.add_eq_bot,
      toWithBotSyn_apply_eq_bot_iff, withBotDegree_eq_bot_iff] at hg
  rcases hg with hg | hg <;> simp [hg]

@[simp]
theorem isRemainder_zero_iff :
    m.IsRemainder 0 B r ↔ r = 0 := by
  refine ⟨isRemainder_zero, fun h ↦ ?_⟩
  exact ⟨⟨0, by simp [h]⟩, by simp [h]⟩

theorem isRemainder_iff_degree (hB : ∀ b ∈ B, m.leadingCoeff b ∈ nonZeroDivisors _) :
    m.IsRemainder f B r ↔
    (∃ (g : B →₀ MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ b.val) g + r ∧
      ∀ (b : B), m.degree (b.val * (g b)) ≼[m] m.degree f) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c) := by
  classical
  wlog! hf : f = 0
  · simp_rw [IsRemainder, ← map_add,
        ← m.withBotDegree_mul_of_left_mem_nonZeroDivisors (hB _ (Subtype.prop _)),
       withBotDegree_le_withBotDegree_iff]
    simp? [hf, -mem_support_iff] says
      simp only [hf, IsEmpty.forall_iff, and_true, Subtype.forall, ne_eq]
  simp_rw [hf, isRemainder_zero_iff]
  constructor
  · intro h
    exact ⟨⟨0, by simp [h]⟩, by simp [h]⟩
  rintro ⟨⟨g, h0sumg, hg⟩, hr⟩
  simp_rw [m.degree_zero, m.toSyn.map_zero, ← m.eq_zero_iff, AddEquiv.map_eq_zero_iff,
    mul_comm _ (g _)] at hg
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] at h0sumg
  have h_deg_r_eq_0 : m.degree r = 0 := by
    apply congrArg m.degree at h0sumg
    contrapose! h0sumg
    rw [degree_zero, ne_comm, ← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero]
    rw [← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero] at h0sumg
    rwa [degree_add_eq_right_of_lt]
    apply lt_of_le_of_lt m.degree_sum_le
    simpa [hg] using lt_of_le_of_lt Finset.sup_const_le h0sumg
  by_contra! hr0
  suffices ∀ b, g b * b = 0 by simp [this, hr0.symm] at h0sumg
  intro b
  by_contra! hgb
  obtain ⟨h_gb_ne_0, h_b_ne_0⟩ := ne_zero_and_ne_zero_of_mul hgb
  rw [m.degree_eq_zero_iff.mp h_deg_r_eq_0, support_C, ite_cond_eq_false _ _ (by simp [hr0])] at hr
  specialize hr 0 (by simp) b b.2 h_b_ne_0
  specialize hg b
  rw [m.degree_mul_of_right_mem_nonZeroDivisors h_gb_ne_0 (hB b b.2)] at hg
  rw [← hg] at hr
  simp at hr

lemma mem_ideal_of_mem_ideal {B : Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) (hr : r ∈ I) :
    p ∈ I := by
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  rw [h_eq]
  refine Ideal.add_mem _ ?_ hr
  rw [Finsupp.linearCombination_apply]
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left _ _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma term_notMem_span_leadingTerm {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)} (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  intro s hs
  rw [span_leadingTerm_eq_span_monomial hB, ← Set.image_image (monomial · 1) _ _,
    mem_ideal_span_monomial_image]
  have h1ne0: (1 : R) ≠ 0 := by
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  simp? [MvPolynomial.mem_support_iff.mp hs] says
    simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
      MvPolynomial.mem_support_iff.mp hs, imp_false, Decidable.not_not, Set.mem_image,
      exists_exists_and_eq_and, forall_eq', not_exists, not_and]
  intro b hb
  unfold MonomialOrder.IsRemainder at h
  apply h.2 s hs b hb
  by_contra hq0
  specialize hB b hb
  simp [hq0, h1ne0.symm] at hB

lemma term_notMem_span_leadingTerm₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  rw [← span_leadingTerm_sdiff_singleton_zero]
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine term_notMem_span_leadingTerm ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

lemma _root_.monomial_notMem_span_leadingTerm {r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  intro s hs
  rw [span_leadingTerm_eq_span_monomial hB,
      ← Set.image_image (monomial · 1) _ _, mem_ideal_span_monomial_image]
  simp? says
    simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff, Classical.not_imp,
      Set.mem_image, exists_exists_and_eq_and, and_imp, forall_eq', not_exists, not_and]
  split_ands
  · by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff s, h1eq0, mul_zero] at hs
    exact hs rfl
  · intro b hb
    exact h s hs b hb

lemma monomial_notMem_span_leadingTerm {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  apply _root_.monomial_notMem_span_leadingTerm hB
  intro c hc b hb
  suffices Nontrivial R from h.2 c hc b hb (m.leadingCoeff_ne_zero_iff.mp (hB _ hb).ne_zero)
  rw [nontrivial_iff_exists_ne 0]
  use 1
  by_contra h1eq0
  rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff c, h1eq0, mul_zero] at hc
  exact hc rfl

lemma monomial_notMem_span_leadingTerm₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [← span_leadingTerm_sdiff_singleton_zero]
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine monomial_notMem_span_leadingTerm ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

variable {f r B} in
lemma withBotDegree_remainder_le (h : m.IsRemainder f B r) :
    m.withBotDegree r ≼'[m] m.withBotDegree f := by
  wlog! hf : f ≠ 0
  · -- simp [hf, isRemainder_zero_iff] at h; simp [hf, h] -- "flexible" linter doesn't work here?
    simp [hf, isRemainder_zero_iff .. |>.mp <| hf ▸ h]
  wlog! hr : r ≠ 0
  · simp [hr]
  obtain ⟨g, hsum, h⟩ := h.1
  apply congrArg (m.toWithBotSyn <| m.withBotDegree ·) at hsum
  contrapose! hsum
  apply ne_of_lt
  rw [withBotDegree_add_of_right_lt]
  · exact hsum
  apply lt_of_le_of_lt withBotDegree_sum_le
  rw [Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (by simpa))]
  simp? [-mem_support_iff, -Subtype.forall] says
    simp only [Finsupp.mem_support_iff, ne_eq, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
      smul_eq_mul]
  rintro b -
  apply lt_of_le_of_lt <| m.withBotDegree_mul_le (g b) b
  simpa [add_comm] using lt_of_le_of_lt (h b) hsum

variable {p B r} in
lemma exists_withBotDegree_le_degree
    (h : m.IsRemainder p B r) (hfr : m.withBotDegree p ≠ m.withBotDegree r) :
    ∃ b ∈ B, m.withBotDegree b ≤ m.withBotDegree p := by
  classical
  rw [ne_eq, ← m.toWithBotSyn.apply_eq_iff_eq, eq_comm,
    ← ne_eq, ne_iff_lt_iff_le.mpr <| withBotDegree_remainder_le h] at hfr
  wlog! hp : p ≠ 0
  · rw [hp, isRemainder_zero_iff] at h
    simp [h, hp] at hfr
  rw [isRemainder_def''] at h
  rcases h with ⟨⟨g, B', h₁, hsum, h₃⟩, h₄⟩
  have : m.degree p ∈ p.support := m.degree_mem_support hp
  nth_rw 1 [hsum] at this
  apply Finset.mem_of_subset support_add at this
  rw [Finset.mem_union] at this
  rcases this with this | this
  on_goal 2 =>
    apply m.le_withBotDegree at this
    rw [← withBotDegree_eq_coe_degree_iff _ |>.mpr hp, ← not_lt] at this
    contradiction
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| Finset.mem_of_subset support_sum this
  use b
  refine ⟨h₁ hb.1, ?_⟩
  rcases hb with ⟨hb₁, hb₂⟩
  obtain hgbne0 : g b ≠ 0 := by
    contrapose! hb₂
    simp [hb₂]
  apply le_withBotDegree (m:=m) at hb₂
  rw [← withBotDegree_eq_coe_degree_iff _ |>.mpr hp] at hb₂
  apply le_trans' (m.withBotDegree_mul_le' ..) at hb₂
  rw [add_comm] at hb₂
  apply le_antisymm (add_comm (m.toWithBotSyn <| m.withBotDegree b) _ ▸ h₃ b hb₁) at hb₂
  simp only [← map_add, EmbeddingLike.apply_eq_iff_eq] at hb₂
  rw [← hb₂]
  exact WithBot.le_self_add (m.withBotDegree_eq_bot_iff _ |>.not.mpr hgbne0) _

variable {p B} in
lemma exists_degree_le_degree_of_zero (hp : p ≠ 0) (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, m.degree b ≤ m.degree p := by
  obtain ⟨b, hbB, hb⟩ := exists_withBotDegree_le_degree (r := 0) h (by simpa)
  use b, hbB
  wlog! hb0 : b ≠ 0
  · simp [hb0]
  simpa [(withBotDegree_eq_coe_degree_iff _).mpr _, hb0, hp] using hb

@[simp, nontriviality]
lemma of_subsingleton [Subsingleton (MvPolynomial σ R)]
    {p r : MvPolynomial σ R} {s : Set (MvPolynomial σ R)} :
    m.IsRemainder p s r := by
  simp [IsRemainder, Subsingleton.eq_zero (α := MvPolynomial σ R)]

end CommSemiring

section CommRing

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

theorem exists_isRemainder {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit <| m.leadingCoeff b) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  classical
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hB p
  use r
  rw [isRemainder_iff_degree (hB := fun _ h ↦ (hB _ h).mem_nonZeroDivisors)]
  split_ands
  · use g
    exact ⟨h.1, h.2.1⟩
  · intro c hc b hb _
    exact h.2.2 c hc b hb

/-- A variant of `div_set'` including `0` -/
theorem exists_isRemainder₀ {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, (IsUnit (m.leadingCoeff b) ∨ b = 0)) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  have hB₁ : ∀ b ∈ B \ {0}, IsUnit (m.leadingCoeff b) := by
    simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]
  obtain ⟨r, h⟩ := exists_isRemainder hB₁ p
  exists r
  rwa [← isRemainder_sdiff_singleton_zero_iff_isRemainder]

lemma mem_ideal_iff {B : Set (MvPolynomial σ R)}
    {r : MvPolynomial σ R} {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) : r ∈ I ↔ p ∈ I := by
  refine ⟨mem_ideal_of_mem_ideal hBI hpBr, ?_⟩
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  intro hp
  rw [← sub_eq_of_eq_add' h_eq]
  apply Ideal.sub_mem I hp
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma sub_mem_ideal_of_isRemainder_of_subset_ideal
    {B : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hBI : B ⊆ I) (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    r₁ - r₂ ∈ I := by
  obtain ⟨⟨f₁, h_eq₁, h_deg₁⟩, h_remain₁⟩ := hr₁
  obtain ⟨⟨f₂, h_eq₂, h_deg₂⟩, h_remain₂⟩ := hr₂
  rw [← sub_eq_of_eq_add' h_eq₁, ← sub_eq_of_eq_add' h_eq₂]
  simp? says simp only [sub_sub_sub_cancel_left]
  apply Ideal.sub_mem I
  all_goals
    apply Ideal.sum_mem
    intro g hg
    exact Ideal.mul_mem_left I _ (Set.mem_of_mem_of_subset (by simp) hBI)

lemma sub_monomial_notMem_span_leadingTerm
    {B : Set (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    ∀ s ∈ (r₁ - r₂).support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  apply _root_.monomial_notMem_span_leadingTerm hB
  intro c hc
  apply MvPolynomial.support_sub at hc
  rw [Finset.mem_union] at hc
  have {b} (hb : b ∈ B) : b ≠ 0 := by
    have : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      simp [Subsingleton.elim _ (0 : MvPolynomial σ R)] at hc
    rw [← m.leadingCoeff_ne_zero_iff]
    exact (hB b hb).ne_zero
  rcases hc with hc | hc
  · intro b hb
    exact hr₁.2 c hc b hb <| this hb
  · intro b hb
    exact hr₂.2 c hc b hb <| this hb

end CommRing

section Field

variable {k : Type*} [Field k] {σ : Type*} {m : MonomialOrder σ}

/-- A variant of `div_set'` in field -/
theorem exists_isRemainder' (B : Set (MvPolynomial σ k))
    (p : MvPolynomial σ k) :
    ∃ (r : MvPolynomial σ k), m.IsRemainder p B r := by
  apply exists_isRemainder₀
  simp [em']

lemma term_notMem_span_leadingTerm' {p r : MvPolynomial σ k}
    {B : Set (MvPolynomial σ k)} (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [←Ideal.span_sdiff_singleton_zero, ← m.image_leadingTerm_sdiff_singleton_zero]
  apply term_notMem_span_leadingTerm
  · simp
  rwa [←isRemainder_sdiff_singleton_zero_iff_isRemainder] at h

end Field

end IsRemainder

end MonomialOrder
