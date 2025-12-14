/-
Copyright (c) 2025 Junyu Guo and Hao Shen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyu Guo, Hao Shen
-/
module

public import Mathlib.RingTheory.MvPolynomial.Groebner.Division
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
## Remainder

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
    split_ands
    · use g.mapDomain Subtype.val
      split_ands
      · exact subset_trans (Finset.coe_subset.mpr Finsupp.mapDomain_support) (by simp)
      · simp [h₁]
      · intro b hb
        rw [show b = ↑(Subtype.mk b hb) by rfl, Finsupp.mapDomain_apply (by simp)]
        exact h₂ ⟨b, hb⟩
    · exact h₃
  · intro ⟨⟨g, hg, h₁, h₂⟩, h₃⟩
    split_ands
    · use {
        support := (g.support.subtype (· ∈ B)),
        toFun := (g.toFun ·),
        mem_support_toFun := by intro; simp; rfl
      }
      split_ands
      · rw [h₁, eq_comm]
        congr 1
        simp [Finsupp.linearCombination_apply, Finsupp.sum]
        apply Finset.sum_nbij (↑·)
        · simp_intro ..
        · simp_intro b _ b₁ _ h [Subtype.ext_iff]
        · simp_intro b hb
          exact Set.mem_of_subset_of_mem hg <| Finsupp.mem_support_iff.mpr hb
        · simp [DFunLike.coe]
      · simpa
    · exact h₃

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
    split_ands
    · use Finsupp.onFinset B' (fun b' => if b' ∈ B' then g b' else 0) (by simp_intro ..)
      split_ands
      · simp_intro b' hb'
        exact Set.mem_of_mem_of_subset hb'.1 h₁
      · rw [Finsupp.linearCombination_apply, Finsupp.sum, h₂, Finsupp.support_onFinset]
        congr 1
        simp [Finset.filter_and, Finset.filter_mem_eq_inter,
          Finset.inter_self, Finset.inter_filter, Finset.filter_inter]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b' _
        by_cases hb' : g b' = 0 <;> simp [hb']
      · intro b hb
        by_cases hbB' : b ∈ B'
        · simp [hbB', h₃]
        · simp [hbB']
    · exact h₄

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
    split_ands
    · use g.toFun
      split_ands
      · simp [Finsupp.linearCombination_apply, Finsupp.sum] at hsum
        rw [hsum]
        congr 1
        apply Finset.sum_subset hgsup
        simp_intro ..
      · exact hg
    · exact hr
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
    let idx : (↑(Set.range b)) ↪ ι := {
      toFun := Set.rangeSplitting b,
      inj' := Set.rangeSplitting_injective b
    }
    split_ands
    · use Finsupp.embDomain idx g
      split_ands
      · ext
        simp [h₁, Finsupp.linearCombination_apply, Finsupp.sum]
        congr
        simp [idx, Set.apply_rangeSplitting]
      · intro i
        specialize h₂ ⟨b i, Set.mem_range_self i⟩
        simp at h₂
        by_cases h' : (Finsupp.embDomain idx g) i = 0
        · simp [h']
        simp at h'
        convert h₂
        generalize_proofs hbi
        convert_to g.embDomain idx (hbi.choose) = _
        · simp [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain, Finsupp.single_apply] at ⊢ h'
          congr
          ext
          congr
          obtain ⟨a, ha, ha'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
          simp [idx] at ha'
          convert_to i = Set.rangeSplitting b ⟨b i, hbi⟩
          simp [← ha'.1, Set.apply_rangeSplitting]
        · exact Finsupp.embDomain_apply_self idx g ⟨b i, hbi⟩
    · intro i hi b hb
      aesop
  · rintro ⟨⟨g, h₁, h₂⟩, h₃⟩
    refine ⟨?_, ?_⟩
    · let b_support : Finset (Set.range b) :=
        (g.support.biUnion fun i ↦
          {⟨b i, Set.mem_range_self i⟩})
      let b' : ι → Set.range b := fun i ↦ ⟨b i, Set.mem_range_self i⟩
      let g' : Set.range b → MvPolynomial σ R := fun x ↦
         Finset.sum (g.support.filter fun i ↦ b' i = x) fun i ↦ g i
      have mem_support : ∀ x, g' x ≠ 0 → x ∈ b_support := by
        intro x hx
        obtain ⟨i, hi, hb'x⟩ : ∃ i ∈ g.support, b' i = x := by
          contrapose! hx
          simp [g']
          rw [Finset.sum_filter]
          suffices (g.support.filter (fun i => b' i = x)) = ∅ by
            rw [← Finset.sum_filter, this, Finset.sum_empty]
          ext i
          simp at hx
          simp
          exact hx i
        simp [b_support, Finset.mem_biUnion]
        use i
        constructor
        · exact Finsupp.mem_support_iff.mp hi
        · exact hb'x.symm
      use Finsupp.onFinset b_support g' mem_support
      split_ands
      · simp [h₁, Finsupp.linearCombination_apply, Finsupp.sum]
        congr
        calc
          ∑ x ∈ g.support, g x * b x
            = ∑ x ∈ g.support, g x * (b' x : MvPolynomial σ R) := by rfl
          _ = ∑ y ∈ Finset.image b' g.support,
              (∑ x ∈ g.support.filter (b' · = y), g x) * (y : MvPolynomial σ R) := by
            rw [Finset.sum_image']
            intro y hy
            rw [Finset.sum_filter]
            ext x
            congr
            calc
              (∑ a ∈ g.support, if b' a = b' y then g a else 0) * ↑(b' y) =
                  (∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j) * ↑(b' y) := by
                congr 1
                simp [Finset.sum_filter]
              _ = ∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j * ↑(b' y) :=
                Finset.sum_mul {j ∈ g.support | b' j = b' y} ⇑g ↑(b' y)
              _ = ∑ j ∈ g.support.filter (fun j ↦ b' j = b' y), g j * ↑(b' j) := by
                apply Finset.sum_congr rfl
                intro j hj
                congr 2
                exact (Finset.mem_filter.mp hj).2.symm
          _ = ∑ y ∈ Finset.image b' g.support, g' y * (y : MvPolynomial σ R) := by rfl
          _ = ∑ y ∈ b_support, g' y * (y : MvPolynomial σ R) := by
            congr
            ext y
            simp [b_support, Eq.comm (a:=y), b']
          _ = ∑ x ∈ (Finsupp.onFinset b_support g' mem_support).support, g' x * ↑x := by
            rw [Finsupp.support_onFinset, Finset.sum_filter]
            congr
            ext x
            by_cases hx : g' x = 0 <;> simp [hx]
      · intro b1
        simp [Finsupp.onFinset, g']
        rw [Finset.mul_sum]
        have sum_eq : (∑ i ∈ g.support.filter (fun i => b' i = b1), ↑b1 * g i) =
            (∑ i ∈ g.support.filter (fun i => b' i = b1), b i * g i) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          rw [Finset.mem_filter] at hi
          congr
          exact Subtype.ext_iff.mp hi.2.symm
        rw [sum_eq]
        have degree_le : ∀ i ∈ g.support.filter (fun i => b' i = b1),
            m.degree (b i * g i) ≼[m] m.degree f := by
          intro i hi
          rw [Finset.mem_filter] at hi
          exact h₂ i
        trans (g.support.filter fun i ↦ b' i = b1).sup fun i ↦ m.toSyn (m.degree (b i * g i))
        · exact m.degree_sum_le
        · exact Finset.sup_le (fun i hi ↦ degree_le i hi)
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
  unfold IsRemainder at h
  obtain ⟨⟨g, h0sumg, hg⟩, hr⟩ := h
  conv at hg =>
    intro b
    simp
    rw [← m.eq_zero_iff, AddEquiv.map_eq_zero_iff, mul_comm]
  simp [Finsupp.linearCombination_apply, Finsupp.sum] at h0sumg
  have rdeg0 : m.degree r = 0 := by
    apply congrArg m.degree at h0sumg
    contrapose! h0sumg
    simp [-ne_eq]
    rw [ne_comm, ← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero, add_comm]
    rw [← AddEquiv.map_ne_zero_iff m.toSyn, ← m.toSyn_lt_iff_ne_zero] at h0sumg
    rwa [degree_add_of_lt]
    apply lt_of_le_of_lt m.degree_sum_le
    simp [hg]
    exact lt_of_le_of_lt Finset.sup_const_le h0sumg
  contrapose! hr
  use 0
  split_ands
  · rw [m.degree_eq_zero_iff.mp rdeg0]; simp [hr]
  contrapose! h0sumg
  simp at h0sumg
  suffices ∀ b : B, g b * ↑b = 0 by simp [this, hr.symm]
  intro b
  suffices ¬b.1 = 0 → g b = 0 by by_cases h : g b = 0 <;> aesop
  intro hb
  specialize hg b
  specialize h0sumg b b.2 hb
  contrapose! hg
  rw [m.degree_mul_of_right_mem_nonZeroDivisors hg <| hB ↑b (by simp)]
  simp [h0sumg]

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
theorem isRemainder_finset₀₁ (p : MvPolynomial σ R) {B' : Finset (MvPolynomial σ R)}
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
theorem isRemainder_finset'₁ [NoZeroDivisors R] (p : MvPolynomial σ R)
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
  by_cases h : p ≠ 0
  · simp [isRemainder_def', h]
  push_neg at h
  rw [h]
  constructor
  · intro h'
    simp [isRemainder_zero' h']
    use 0
    simp
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
  simp [MvPolynomial.mem_support_iff.mp hs]
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
  simp
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
  have : Nontrivial R := by
    rw [nontrivial_iff_exists_ne 0]
    use 1
    by_contra h1eq0
    rw [MvPolynomial.mem_support_iff, ← mul_one <| r.coeff c, h1eq0, mul_zero] at hc
    exact hc rfl
  refine h.2 c hc b hb (m.leadingCoeff_ne_zero_iff.mp (hB _ hb).ne_zero)

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
  simp at hsum
  have : m.degree p ∈ p.support := m.degree_mem_support hp
  rw [hsum] at this
  obtain ⟨b, hb⟩ := Finset.mem_biUnion.mp <| hsum.symm ▸ Finset.mem_of_subset support_sum this
  use b
  constructor
  · exact h₁ hb.1
  · rcases hb with ⟨hb₁, hb₂⟩
    have := h₃ b hb₁
    obtain hgbne0 : g b ≠ 0 := by
      contrapose! hb₂
      simp [hb₂]
    apply le_degree (m:=m) at hb₂
    rw [mul_comm b] at this
    apply le_antisymm this at hb₂
    simp at hb₂
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
  · simp
    rw [and_assoc]
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
  simp
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
