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

* `MonomialOrder.IsRemainder m f B r`: Given a multivariate polynomial `f` and a set `B` of
  multivariate polynomials over a commutative semiring `R`, with respect to a monomial order `m`.
  A polynomial `r` is called a remainder of `f` on division by `B` if there exists:
  (1) A finite linear combination:
    `f = ∑ (g(b) * b) + r` where `g : B →₀ R[X]` (finitely supported coefficients).
  (2) Degree condition:
    For each `b ∈ B`, the degree of `g(b) * b` is ≤ the degree of `f` under `m`.
  (3) Remainder irreducibility:
    No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.

And there're also some variant equivalent statements.

* `MonomialOrder.isRemainder_def'`: A variant of `MonomialOrder.IsRemainder` without coercion of a
  `Set (MvPolynomial σ R)`.

* `MonomialOrder.isRemainder_def''`: A variant of `MonomialOrder.IsRemainder` where
  `g : MvPolynomial σ R →₀ MvPolynomial σ R` is replaced with a
  function `g : MvPolynomial σ R → MvPolynomial σ R` without limitation on its support.

* `MonomialOrder.isRemainder_range`: A variant of `MonomialOrder.IsRemainder` where divisors are
  given as a map from indexes to polynomials.

## Naming convention

Some theorems with an argument in type `Set (MvPolynomial σ R)` have 2 variants, named as following
respectively:

* without suffix `'` or `₀`: leading coefficients of all polynomials in the set are non-zero
  divisors `· ∈ nonZeroDivisors (MvPolynomial σ R)` (or invertible `IsUnit ·`, depending on the
  theorem);
* with suffix `₀`: leading coefficients of echo polynomial in the set is non-zero divisors (or
  invertible) or 0 `· = 0`.

## Reference : [Cox2015]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

section CommSemiring
variable {σ : Type*} (m : MonomialOrder σ)

variable {R : Type*} [CommSemiring R]
variable (f p : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R)

/--
Given a multivariate polynomial `f` and a set `B` of
  multivariate polynomials over a commutative semiring `R`, with respect to a monomial order `m`.
  A polynomial `r` is called a remainder of `f` on division by `B` if there exists:
  (1) A finite linear combination:
   `f = ∑ (g(b) * b) + r` where `g : B →₀ R[X]` (finitely supported coefficients).
  (2) Degree condition:
   For each `b ∈ B`, the degree of `g(b) * b` is ≤ the degree of `f` under `m`.
  (3) Remainder irreducibility:
   No term of `r` is divisible by the leading monomial of any non-zero `b ∈ B`.
-/
def IsRemainder :=
  (∃ (g : B →₀ MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ (m.degree b ≤ c)

/--
A variant of `MonomialOrder.IsRemainder` without coercion of a `Set (MvPolynomial σ R)`.
-/
theorem isRemainder_def' (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  classical
  constructor
  · intro ⟨⟨g, h₁, h₂⟩, h₃⟩
    refine ⟨?_, h₃⟩
    use g.mapDomain Subtype.val
    split_ands
    · exact subset_trans (Finset.coe_subset.mpr Finsupp.mapDomain_support) (by simp)
    · simp [h₁]
    · intro b hb
      rw [show b = ↑(Subtype.mk b hb) by rfl, Finsupp.mapDomain_apply (by simp)]
      exact h₂ ⟨b, hb⟩
  · intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    refine ⟨?_, h₃⟩
    use {
      support := (g.support.subtype (· ∈ B)),
      toFun := (g.toFun ·),
      mem_support_toFun := by intro; simp; rfl
    }
    refine ⟨?_, by simpa⟩
    rw [h₁, eq_comm]
    congr 1
    simp? [Finsupp.linearCombination_apply, Finsupp.sum] says
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.coe_mk, smul_eq_mul, id_eq]
    apply Finset.sum_nbij (↑·)
    · simp_intro ..
    · simp_intro b _ b₁ _ h [Subtype.ext_iff]
    · simp_intro b hb
      exact Set.mem_of_subset_of_mem hg <| Finsupp.mem_support_iff.mpr hb
    · simp [DFunLike.coe]

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
          ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
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
        ∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
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

/-- `r` is a remainder of a family of polynomials, if and only if it is a remainder with properities
defined in `MonomialOrder.div` with this family of polynomials given as a map from indexes to them.

It is a variant of `MonomialOrder.IsRemainder` where divisors are given as a map from indexes to
polynomials. -/
theorem isRemainder_range {ι : Type*} (f : MvPolynomial σ R)
    (b : ι → MvPolynomial σ R) (r : MvPolynomial σ R) :
    m.IsRemainder f (Set.range b) r ↔
      (∃ g : ι →₀ MvPolynomial σ R,
        f = Finsupp.linearCombination _ b g + r ∧
        ∀ i : ι, m.degree (b i * g i) ≼[m] m.degree f) ∧
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
        simp? [Finsupp.onFinset, g', Finset.mul_sum] says
          simp only [Finsupp.onFinset, Finsupp.coe_mk, Finset.mul_sum, g']
        apply le_trans m.degree_sum_le
        simp? says
          simp only [Finset.sup_le_iff, Finset.mem_filter, Finsupp.mem_support_iff, ne_eq, and_imp]
        intro idx hidx hidx'
        simp [h₂ idx, ← hidx']
    · aesop

/--
Remainders are preserved on insertion of the zero polynomial into the set of divisors.
-/
@[simp]
theorem isRemainder_insert_zero_iff_isRemainder (p : MvPolynomial σ R)
    (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p (insert 0 B) r ↔ m.IsRemainder p B r := by
  classical
  constructor
  · by_cases hB : 0 ∈ B
    · simp [hB]
    simp_rw [isRemainder_def'']
    intro ⟨⟨g, B', hB', h₁, h₂⟩, h₃⟩
    split_ands
    · use g, (B'.erase 0)
      split_ands
      · simp [hB']
      · rw [h₁]
        congr 1
        by_cases hB'0 : 0 ∈ B'
        · nth_rw 1 [← Finset.insert_erase hB'0]
          rw [Finset.sum_insert_zero (a:=0)]
          simp
        · rw [Finset.erase_eq_self.mpr hB'0]
      · simp_intro b' hb'
        exact h₂ b' hb'.2
    · intro c hc b hbB hb
      exact h₃ c hc b (by simp [hbB]) hb
  · rw [isRemainder_def', isRemainder_def']
    intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    · use g
      split_ands
      · exact subset_trans hg (Set.subset_insert _ _)
      · exact h₁
      · intro b hb
        by_cases hb0 : b = 0
        · simp [hb0]
        · exact h₂ b ((Set.mem_insert_iff.mp hb).resolve_left hb0)
    · intro c hc b hb hbne0
      exact h₃ c hc b ((Set.mem_insert_iff.mp hb).resolve_left hbne0) hbne0

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

variable {m B} in
theorem isRemainder_zero {r : MvPolynomial σ R}
    (hB : ∀ b ∈ B, m.leadingCoeff b ∈ nonZeroDivisors _)
    (h : m.IsRemainder 0 B r) : r = 0 := by
  classical
  unfold IsRemainder at h
  obtain ⟨⟨g, h0sumg, hg⟩, hr⟩ := h
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

variable {m B} in
theorem isRemainder_zero₀ {r : MvPolynomial σ R}
    (hB : ∀ b ∈ B, m.leadingCoeff b ∈ nonZeroDivisors _ ∨ b = 0) (h : m.IsRemainder 0 B r) :
      r = 0 := by
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.isRemainder_zero ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

variable {m B} in
theorem isRemainder_zero' [NoZeroDivisors R] {r : MvPolynomial σ R} (h : m.IsRemainder 0 B r) :
    r = 0 := by
  refine isRemainder_zero₀ ?_ h
  intro b _
  rw [or_iff_not_imp_right]
  exact (mem_nonZeroDivisors_of_ne_zero <| m.leadingCoeff_ne_zero_iff.mpr ·)

variable {m} in
theorem isRemainder_finset₁ (p : MvPolynomial σ R) {B' : Finset (MvPolynomial σ R)}
    (hB' : ∀ b' ∈ B', m.leadingCoeff b' ∈ nonZeroDivisors _)
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero hB' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

variable {m} in
theorem isRemainder_finset₁₀ (p : MvPolynomial σ R) {B' : Finset (MvPolynomial σ R)}
    (hB' : ∀ b' ∈ B', m.leadingCoeff b' ∈ nonZeroDivisors _ ∨ b' = 0)
    (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero₀ hB' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

variable {m} in
theorem isRemainder_finset₁' [NoZeroDivisors R] (p : MvPolynomial σ R)
    (B' : Finset (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    m.IsRemainder p B' r ↔
      (∃ (g : MvPolynomial σ R → MvPolynomial σ R),
        p = B'.sum (fun x => g x * x) + r ∧
        (∀ b' ∈ B', m.degree ((b' : MvPolynomial σ R) * (g b')) ≼[m] m.degree p) ∧
        (p = 0 → g = 0)
      ) ∧
      ∀ c ∈ r.support, ∀ b ∈ B', b ≠ 0 → ¬ (m.degree b ≤ c) := by
  constructor
  · by_cases hp0 : p = 0
    · rw [hp0]
      intro h
      apply m.isRemainder_zero' at h
      simp [h]
    rw [isRemainder_finset]
    rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    exact ⟨⟨g, h₁, h₂, by simp [hp0]⟩, h₃⟩
  · rintro ⟨⟨g, h₁, h₂, -⟩, h₃⟩
    rw [isRemainder_finset]
    exact ⟨⟨g, h₁, h₂⟩, h₃⟩

theorem isRemainder_def'₁ [NoZeroDivisors R] (p : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : m.IsRemainder p B r ↔
      (∃ (g : MvPolynomial σ R →₀ MvPolynomial σ R),
        ↑g.support ⊆ B ∧
        p = Finsupp.linearCombination _ id g + r ∧
        ∀ b ∈ B, m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree p ∧
        (p = 0 → g = 0)) ∧
      ∀ c ∈ r.support, ∀ g' ∈ B, g' ≠ 0 → ¬ (m.degree g' ≤ c) := by
  by_cases! h : p ≠ 0
  · simp [isRemainder_def', h]
  rw [h]
  constructor
  · intro h'
    refine ⟨⟨0, ?_, ?_⟩, ?_⟩ <;> simp [isRemainder_zero' h']
  · intro h'
    rw [isRemainder_def']
    aesop

variable {m} in
lemma mem_ideal_of_isRemainder_of_mem_ideal {B : Set (MvPolynomial σ R)} {r : MvPolynomial σ R}
    {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) (hr : r ∈ I) :
    p ∈ I := by
  obtain ⟨⟨f, h_eq, h_deg⟩, h_remain⟩ := hpBr
  rw [h_eq]
  refine Ideal.add_mem _ ?_ hr
  rw [Finsupp.linearCombination_apply]
  apply Ideal.sum_mem
  exact fun _ _ ↦ Ideal.mul_mem_left _ _ (Set.mem_of_mem_of_subset (by simp) hBI)

variable {m} in
lemma term_notMem_span_leadingTerm_of_isRemainder {p r : MvPolynomial σ R}
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

variable {m} in
lemma term_notMem_span_leadingTerm_of_isRemainder₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  rw [← span_leadingTerm_sdiff_singleton_zero]
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.term_notMem_span_leadingTerm_of_isRemainder ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

variable {m} in
lemma monomial_notMem_span_leadingTerm {r : MvPolynomial σ R}
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

variable {m} in
lemma monomial_notMem_span_leadingTerm_of_isRemainder {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  apply monomial_notMem_span_leadingTerm hB
  intro c hc b hb
  suffices Nontrivial R from h.2 c hc b hb (m.leadingCoeff_ne_zero_iff.mp (hB _ hb).ne_zero)
  rw [nontrivial_iff_exists_ne 0]
  use 1
  by_contra h1eq0
  rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff c, h1eq0, mul_zero] at hc
  exact hc rfl

variable {m} in
lemma monomial_notMem_span_leadingTerm_of_isRemainder₀ {p r : MvPolynomial σ R}
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [← span_leadingTerm_sdiff_singleton_zero]
  rw [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  refine m.monomial_notMem_span_leadingTerm_of_isRemainder ?_ h
  simp_intro .. [or_iff_not_imp_right.mp (hB _ _)]

variable {m} in
lemma exists_degree_le_degree_of_isRemainder_zero
    (p : MvPolynomial σ R) (hp : p ≠ 0) (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, m.leadingCoeff b ∈ nonZeroDivisors _)
    (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, m.degree b ≤ m.degree p := by
  classical
  rw [isRemainder_def''] at h
  rcases h with ⟨⟨g, B', h₁, hsum, h₃⟩, h₄⟩
  simp? at hsum says simp only [add_zero] at hsum
  have : m.degree p ∈ p.support := m.degree_mem_support hp
  rw [hsum] at this
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| hsum.symm ▸ Finset.mem_of_subset support_sum this
  use b
  refine ⟨h₁ hb.1, ?_⟩
  rcases hb with ⟨hb₁, hb₂⟩
  obtain hgbne0 : g b ≠ 0 := by
    contrapose! hb₂
    simp [hb₂]
  apply le_degree (m:=m) at hb₂
  apply le_antisymm (mul_comm b _ ▸ h₃ b hb₁) at hb₂
  simp? at hb₂ says simp only [EmbeddingLike.apply_eq_iff_eq] at hb₂
  rw [degree_mul_of_right_mem_nonZeroDivisors hgbne0] at hb₂
  · exact le_of_add_le_right (le_of_eq hb₂)
  exact hB b (Set.mem_of_mem_of_subset hb₁ h₁)

variable {m} in
lemma exists_degree_le_degree_of_isRemainder_zero₀
    (p : MvPolynomial σ R) (hp : p ≠ 0) (B : Set (MvPolynomial σ R))
    (hB : ∀ b ∈ B, m.leadingCoeff b ∈ nonZeroDivisors _ ∨ b = 0)
    (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p := by
  rw [← isRemainder_sdiff_singleton_zero_iff_isRemainder] at h
  convert m.exists_degree_le_degree_of_isRemainder_zero p hp (B \ {0}) ?_ h using 2
  · simp [and_assoc]
  · simp_intro a b [or_iff_not_imp_right.mp (hB _ _)]

end CommSemiring

section CommRing

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

/-- A variant of `MonomialOrder.div_set` using `MonomialOrder.IsRemainder`. -/
theorem exists_isRemainder {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit <| m.leadingCoeff b) (p : MvPolynomial σ R) :
    ∃ (r : MvPolynomial σ R), m.IsRemainder p B r := by
  obtain ⟨g, r, h⟩ := MonomialOrder.div_set hB p
  use r
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
  obtain ⟨r, h⟩ := m.exists_isRemainder hB₁ p
  exists r
  rwa [← m.isRemainder_sdiff_singleton_zero_iff_isRemainder]

lemma mem_ideal_iff_of_isRemainder {B : Set (MvPolynomial σ R)}
    {r : MvPolynomial σ R} {I : Ideal (MvPolynomial σ R)} {p : MvPolynomial σ R}
    (hBI : B ⊆ I) (hpBr : m.IsRemainder p B r) : r ∈ I ↔ p ∈ I := by
  refine ⟨m.mem_ideal_of_isRemainder_of_mem_ideal hBI hpBr, ?_⟩
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

lemma sub_monomial_notMem_span_leadingTerm_of_isRemainder
    {B : Set (MvPolynomial σ R)} {p r₁ r₂ : MvPolynomial σ R}
    (hB : ∀ p ∈ B, IsUnit (m.leadingCoeff p))
    (hr₁ : m.IsRemainder p B r₁) (hr₂ : m.IsRemainder p B r₂) :
    ∀ s ∈ (r₁ - r₂).support, monomial s 1 ∉ Ideal.span (m.leadingTerm '' B) := by
  classical
  apply m.monomial_notMem_span_leadingTerm hB
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

lemma term_notMem_span_leadingTerm_of_isRemainder' {p r : MvPolynomial σ k}
    {B : Set (MvPolynomial σ k)} (h : m.IsRemainder p B r) :
    ∀ s ∈ r.support, monomial s (r.coeff s) ∉ Ideal.span (m.leadingTerm '' B) := by
  rw [←Ideal.span_sdiff_singleton_zero, ← m.image_leadingTerm_sdiff_singleton_zero]
  apply term_notMem_span_leadingTerm_of_isRemainder
  · simp
  rwa [←isRemainder_sdiff_singleton_zero_iff_isRemainder] at h

lemma exists_degree_le_degree_of_isRemainder_zero' (p : MvPolynomial σ k) (hp : p ≠ 0)
    (B : Set (MvPolynomial σ k)) (h : m.IsRemainder p B 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree p :=
  m.exists_degree_le_degree_of_isRemainder_zero₀ p hp B (by simp [em']) h

end Field

end MonomialOrder
