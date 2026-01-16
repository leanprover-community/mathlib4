/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Division
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Finsupp.Weight

/-!
# Division of `MvPolynomial` by monomials

## Main definitions

* `MvPolynomial.divMonomial x s`: divides `x` by the monomial `MvPolynomial.monomial 1 s`
* `MvPolynomial.modMonomial x s`: the remainder upon dividing `x` by the monomial
  `MvPolynomial.monomial 1 s`.

## Main results

* `MvPolynomial.divMonomial_add_modMonomial`, `MvPolynomial.modMonomial_add_divMonomial`:
  `divMonomial` and `modMonomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Where possible, the results in this file should be first proved in the generality of
`AddMonoidAlgebra`, and then the versions specialized to `MvPolynomial` proved in terms of these.

-/

@[expose] public section


variable {σ R : Type*} [CommSemiring R]

namespace MvPolynomial

section CopiedDeclarations

/-! Please ensure the declarations in this section are direct translations of `AddMonoidAlgebra`
results. -/


/-- Divide by `monomial 1 s`, discarding terms not divisible by this. -/
noncomputable def divMonomial (p : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  AddMonoidAlgebra.divOf p s

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

@[simp]
theorem coeff_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) (s' : σ →₀ ℕ) :
    coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x :=
  rfl

@[simp]
theorem support_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    (x /ᵐᵒⁿᵒᵐⁱᵃˡ s).support = x.support.preimage _ (add_right_injective s).injOn :=
  rfl

@[simp]
theorem zero_divMonomial (s : σ →₀ ℕ) : (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.zero_divOf _

theorem divMonomial_zero (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x :=
  x.divOf_zero

theorem add_divMonomial (x y : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (x + y) /ᵐᵒⁿᵒᵐⁱᵃˡ s = x /ᵐᵒⁿᵒᵐⁱᵃˡ s + y /ᵐᵒⁿᵒᵐⁱᵃˡ s :=
  map_add (N := _ →₀ _) _ _ _

theorem divMonomial_add (a b : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x /ᵐᵒⁿᵒᵐⁱᵃˡ (a + b) = x /ᵐᵒⁿᵒᵐⁱᵃˡ a /ᵐᵒⁿᵒᵐⁱᵃˡ b :=
  x.divOf_add _ _

@[simp]
theorem divMonomial_monomial_mul (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.of'_mul_divOf _

@[simp]
theorem divMonomial_mul_monomial (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.mul_of'_divOf _

@[simp]
theorem divMonomial_monomial (a : σ →₀ ℕ) : monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R) :=
  AddMonoidAlgebra.of'_divOf _

/-- The remainder upon division by `monomial 1 s`. -/
noncomputable def modMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  x.modOf s

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]
theorem coeff_modMonomial_of_not_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : ¬s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x :=
  x.modOf_apply_of_not_exists_add s s'
    (by
      rintro ⟨d, rfl⟩
      exact h le_self_add)

@[simp]
theorem coeff_modMonomial_of_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0 :=
  x.modOf_apply_of_exists_add _ _ <| exists_add_of_le h

@[simp]
theorem monomial_mul_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.of'_mul_modOf _

@[simp]
theorem mul_monomial_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.mul_of'_modOf _

@[simp]
theorem monomial_modMonomial (s : σ →₀ ℕ) : monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.of'_modOf _

theorem divMonomial_add_modMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐⁱᵃˡ s = x :=
  AddMonoidAlgebra.divOf_add_modOf x s

theorem modMonomial_add_divMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = x :=
  AddMonoidAlgebra.modOf_add_divOf x s

theorem monomial_one_dvd_iff_modMonomial_eq_zero {i : σ →₀ ℕ} {x : MvPolynomial σ R} :
    monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0 :=
  AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

end CopiedDeclarations

section XLemmas

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]
theorem X_mul_divMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_monomial_mul _ _

@[simp]
theorem X_divMonomial (i : σ) : (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1 :=
  divMonomial_monomial (Finsupp.single i 1)

@[simp]
theorem mul_X_divMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_mul_monomial _ _

@[simp]
theorem X_mul_modMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_mul_modMonomial _ _

@[simp]
theorem mul_X_modMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  mul_monomial_modMonomial _ _

@[simp]
theorem modMonomial_X (i : σ) : (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_modMonomial _

theorem divMonomial_add_modMonomial_single (x : MvPolynomial σ R) (i : σ) :
    X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_add_modMonomial _ _

theorem modMonomial_add_divMonomial_single (x : MvPolynomial σ R) (i : σ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 + X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) = x :=
  modMonomial_add_divMonomial _ _

theorem X_dvd_iff_modMonomial_eq_zero {i : σ} {x : MvPolynomial σ R} :
    X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_one_dvd_iff_modMonomial_eq_zero

end XLemmas

/-! ### Some results about dvd (`∣`) on `monomial` and `X` -/


theorem monomial_dvd_monomial {r s : R} {i j : σ →₀ ℕ} :
    monomial i r ∣ monomial j s ↔ (s = 0 ∨ i ≤ j) ∧ r ∣ s := by
  constructor
  · rintro ⟨x, hx⟩
    rw [MvPolynomial.ext_iff] at hx
    have hj := hx j
    have hi := hx i
    classical
    simp_rw [coeff_monomial, if_pos] at hj hi
    simp_rw [coeff_monomial_mul'] at hi hj
    split_ifs at hj with hi
    · exact ⟨Or.inr hi, _, hj⟩
    · exact ⟨Or.inl hj, hj.symm ▸ dvd_zero _⟩
  · rintro ⟨h | hij, d, rfl⟩
    · simp_rw [h, monomial_zero, dvd_zero]
    · refine ⟨monomial (j - i) d, ?_⟩
      rw [monomial_mul, add_tsub_cancel_of_le hij]

@[simp]
theorem monomial_one_dvd_monomial_one [Nontrivial R] {i j : σ →₀ ℕ} :
    monomial i (1 : R) ∣ monomial j 1 ↔ i ≤ j := by
  rw [monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true]

@[simp]
theorem X_dvd_X [Nontrivial R] {i j : σ} :
    (X i : MvPolynomial σ R) ∣ (X j : MvPolynomial σ R) ↔ i = j := by
  refine monomial_one_dvd_monomial_one.trans ?_
  simp_rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Finsupp.single_apply_ne_zero,
    ne_eq, reduceCtorEq, not_false_eq_true, and_true]

@[simp]
theorem X_dvd_monomial {i : σ} {j : σ →₀ ℕ} {r : R} :
    (X i : MvPolynomial σ R) ∣ monomial j r ↔ r = 0 ∨ j i ≠ 0 := by
  refine monomial_dvd_monomial.trans ?_
  simp_rw [one_dvd, and_true, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

theorem eq_divMonomial_single [IsLeftCancelAdd R]
    {i : σ} {p q r : MvPolynomial σ R} (h : p = X i * q + r)
    (hr : ∀ n ∈ r.support, n i = 0) :
    q = p.divMonomial (Finsupp.single i 1) := by
  ext n
  rw [coeff_divMonomial, h, coeff_add, coeff_X_mul, left_eq_add, ← notMem_support_iff]
  intro hn
  simpa using hr _ hn

instance [IsLeftCancelAdd R] :
    IsCancelAdd (MvPolynomial σ R) := by
  suffices IsLeftCancelAdd (MvPolynomial σ R) from
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _
  refine { add_left_cancel := fun f g h H ↦ ?_ }
  ext d
  simpa using congr_arg (coeff d) H

theorem eq_modMonomial_single [IsLeftCancelAdd R]
    {σ : Type*} {i : σ} {p q r : MvPolynomial σ R}
    (h : p = X i * q + r) (hr : ∀ n ∈ r.support, n i = 0) :
    r = p.modMonomial (Finsupp.single i 1) := by
  have h' := id h
  rwa [← p.divMonomial_add_modMonomial_single i,
    eq_divMonomial_single h hr, add_right_inj, eq_comm] at h'

section CommRing

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

theorem eq_modMonomial_single_iff (h : X i ∣ p - r) :
    r = p.modMonomial (Finsupp.single i 1) ↔
      ∀ n ∈ r.support, n i = 0 := by
  refine ⟨fun h n ↦ ?_, fun hr ↦ ?_⟩
  · contrapose!
    intro hn
    rw [h, notMem_support_iff]
    apply coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply eq_modMonomial_single (q := q) _ hr
    rwa [← sub_eq_iff_eq_add]

theorem X_dvd_mul_iff [IsCancelMulZero R] :
    X i ∣ p * q ↔ X i ∣ p ∨ X i ∣ q := by
  nontriviality R
  have _ : NoZeroDivisors (MvPolynomial σ R) :=
    IsLeftCancelMulZero.to_noZeroDivisors (MvPolynomial σ R)
  constructor
  · intro h
    suffices (p.modMonomial (Finsupp.single i 1)) * (q.modMonomial (Finsupp.single i 1)) =
          (p * q).modMonomial (Finsupp.single i 1) by
      simp only [X_dvd_iff_modMonomial_eq_zero] at h ⊢
      rwa [h, mul_eq_zero] at this
    have hp := p.modMonomial_add_divMonomial_single i
    have hq := q.modMonomial_add_divMonomial_single i
    rw [eq_modMonomial_single_iff]
    · intro n
      contrapose
      intro hn
      classical
      rw [notMem_support_iff, coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_antidiagonal] at hx
      simp only [← hx, Finsupp.coe_add, Pi.add_apply, Nat.add_eq_zero_iff, not_and_or] at hn
      rcases hn with hn | hn
      · rw [coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
      · rw [mul_comm, coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
    · nth_rewrite 1 [← hp]
      nth_rewrite 1 [← hq]
      simp only [add_mul, mul_add, add_assoc, add_sub_cancel_left]
      simp only [← mul_assoc, mul_comm _ (X i)]
      simp only [mul_assoc, ← mul_add (X i)]
      apply dvd_mul_right
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h q
    · exact dvd_mul_of_dvd_right h p

theorem X_prime [IsCancelMulZero R] [Nontrivial R] : Prime (X i : MvPolynomial σ R) := by
  refine ⟨X_ne_zero i, ?_, fun p q ↦ X_dvd_mul_iff.mp⟩
  intro h
  rw [isUnit_iff_exists] at h
  rcases h with ⟨u, hu, -⟩
  apply_fun constantCoeff at hu
  simp at hu

theorem dvd_X_mul_iff [IsCancelMulZero R] :
    p ∣ X i * q ↔ p ∣ q ∨ (X i ∣ p ∧ p.divMonomial (Finsupp.single i 1) ∣ q) := by
  constructor
  · rintro ⟨r, hp⟩
    have : X i ∣ p ∨ X i ∣ r := by simp [← X_dvd_mul_iff, ← hp]
    apply this.symm.imp
    · rintro ⟨r, rfl⟩
      obtain rfl : q = p * r := by rw [← X_mul_cancel_left_iff (i := i), hp, mul_left_comm]
      exact dvd_mul_right p r
    · intro hip
      refine ⟨hip, ?_⟩
      rw [X_dvd_iff_modMonomial_eq_zero] at hip
      rw [← p.modMonomial_add_divMonomial_single i, hip,
        zero_add, mul_assoc, X_mul_cancel_left_iff] at hp
      use r
  · rintro (hp | ⟨hi, hq⟩)
    · exact dvd_mul_of_dvd_right hp (X i)
    · suffices p = X i * p.divMonomial (Finsupp.single i 1) by
        rw [this]
        exact mul_dvd_mul_left (X i) hq
      conv_lhs => rw [← p.modMonomial_add_divMonomial (Finsupp.single i 1)]
      simpa only [← C_mul_X_eq_monomial, C_1, one_mul, add_eq_right,
        ← X_dvd_iff_modMonomial_eq_zero]

theorem dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n : σ →₀ ℕ} :
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices ∀ (d) (n : σ →₀ ℕ) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r from this n.degree n rfl p q
  classical
  intro d
  induction d with
  | zero =>
    intro n hn p
    rw [Finsupp.degree_eq_zero_iff] at hn
    simp only [hn, monomial_zero', C_1, one_mul, nonpos_iff_eq_zero, exists_and_left,
      exists_eq_left, exists_eq_right', implies_true]
  | succ d hd =>
    intro n hn p q
    refine ⟨fun hp ↦ ?_, fun ⟨m, r, hmn, hrq, hp⟩ ↦ ?_⟩
    · obtain ⟨i, hi⟩ : n.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro hn'
        simp [hn'] at hn
      let n' := n - Finsupp.single i 1
      have hn' : n' + Finsupp.single i 1 = n := by
        apply Finsupp.sub_add_single_one_cancel
        rwa [← Finsupp.mem_support_iff]
      have hnn' : n' ≤ n := by simp [← hn']
      have hd' : n'.degree = d := by
        rw [← add_left_inj, ← hn, ← hn']
        simp
      rw [← hn', monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, dvd_X_mul_iff] at hp
      rcases hp with hp | hp
      · obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' p q).mp hp
        exact ⟨m, r, le_trans hm hnn', hr, hp⟩
      · obtain ⟨p', rfl⟩ := hp.1
        obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' _ _).mp hp.2
        use m + Finsupp.single i 1, r, ?_, hr
        · simp [monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, ← hp]
        · simpa [← hn'] using hm
    · rw [hp, ← add_tsub_cancel_of_le hmn, ← mul_one 1, ← monomial_mul, mul_one, mul_assoc]
      apply mul_dvd_mul dvd_rfl
      apply dvd_mul_of_dvd_right hrq

end CommRing

end MvPolynomial
