/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.Destutter
import Mathlib.Data.Sign.Basic

/-!

# Descartes' Rule of Signs

We define the "sign changes" in the coefficients of a polynomial, and prove Descartes'
Rule of Signs: a real polynomial has at most as many positive roots as there are sign
changes. A sign change is when there is a positive coefficient followed by a negative
coefficient, or vice versa, with any number of zero coefficients in between.

## Main Definitions

- `Polynomial.signVariations`: The number of sign changes in a polynomial's coefficients,
  where `0` coefficients are ignored.

## Main theorem

- `Polynomial.roots_countP_pos_le_signVariations`. States that
  `P.roots.countP (0 < ·) ≤ P.signVariations`, so that positive roots are counted with multiplicity.
  It's currently proved for any `CommRing` with `IsStrictOrderedRing`. There is likely some correct
  statement in terms of a (noncommutative) `Ring`, but `Polynomial.roots` is only defined for
  commutative rings.

## Reference

[Wikipedia: Descartes' Rule of Signs](https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs)
-/

namespace Polynomial

section Semiring
variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

/-- Counts the number of times that the coefficients in a polynomial change sign, with
the convention that 0 can count as either sign. -/
def signVariations : ℕ :=
  letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· ≠ 0)
  (nonzero_signs.destutter (· ≠ ·)).length - 1

variable (R) in
@[simp]
theorem signVariations_zero : signVariations (0 : R[X]) = 0 := by
  simp [signVariations]

/-- Sign variations of a monomial are always zero. -/
@[simp]
theorem signVariations_monomial (d : ℕ) (c : R) : signVariations (monomial d c) = 0 := by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, signVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

/-- If the first two signs are the same, then sign_variations is unchanged by eraseLead -/
theorem signVariations_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff) :
    signVariations P.eraseLead = signVariations P := by
  by_cases hpz : P = 0
  · simp_all
  · have h₂ : nextCoeff P ≠ 0 := by intro; simp_all
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    simp [signVariations, List.destutter, leadingCoeff_eraseLead_eq_nextCoeff h₂, hl, h, h₂,
      coeffList_eraseLead hpz]

/-- If we drop the leading coefficient, the sign changes drop by 0 or 1 depending on whether
the first two nonzero coeffients match. -/
theorem signVariations_eq_eraseLead_add_ite {P : Polynomial R} (h : P ≠ 0) :
    signVariations P = signVariations P.eraseLead + if SignType.sign P.leadingCoeff
      = -SignType.sign P.eraseLead.leadingCoeff then 1 else 0 := by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) ≠ 0 := by simp_all
  rw [signVariations, signVariations, coeffList_eraseLead hpz]
  rw [List.map_cons, List.map_append, List.map_replicate]
  rcases h_eL : P.eraseLead.coeffList with _ | ⟨c, cs⟩
  · simp [coeffList_eq_nil.mp h_eL, h]
  simp only [List.filter_append, List.filter_replicate, List.map_cons, List.filter, ne_eq, hsl]
  have h₁ : SignType.sign c ≠ 0 := by
    by_contra h₂
    suffices eraseLead P = 0 by grind [coeffList_zero]
    by_contra h
    have := coeffList_eq_cons_leadingCoeff h
    grind [leadingCoeff_eq_zero, sign_eq_zero_iff]
  simp only [decide_not, sign_zero, List.destutter, Bool.false_eq_true, reduceIte, h₁,
    decide_false, Bool.not_false, List.nil_append, List.destutter', decide_true, Bool.not_true]
  obtain rfl : c = leadingCoeff P.eraseLead := by
    have h_eL : eraseLead P ≠ 0 := by simp [← coeffList_eq_nil, h_eL]
    obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff h_eL
    grind
  by_cases h₄ : SignType.sign P.leadingCoeff = SignType.sign P.eraseLead.leadingCoeff
  · grind [SignType.neg_eq_self_iff]
  rw [if_pos h₄, if_pos ?_]
  · grind [Nat.sub_add_cancel, List.length_pos_of_ne_nil, List.destutter'_ne_nil ]
  cases _ : SignType.sign P.leadingCoeff
  <;> cases _ : SignType.sign P.eraseLead.leadingCoeff
  <;> grind [= SignType.neg_eq_neg_one, SignType.zero_eq_zero, SignType.pos_eq_one,
      SignType.neg_eq_neg_one, neg_neg]

/-- We can only lose, not gain, sign changes if we drop the leading coefficient. -/
theorem signVariations_eraseLead_le : signVariations P.eraseLead ≤ signVariations P := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

/-- We can only lose at most one sign changes if we drop the leading coefficient. -/
theorem signVariations_le_eraseLead_succ : signVariations P ≤ signVariations P.eraseLead + 1 := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [signVariations_eq_eraseLead_add_ite]

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] (P : Polynomial R) {x : R}

/-- The number of sign changes does not change if we negate. -/
@[simp]
theorem signVariations_neg : signVariations (-P) = signVariations P := by
  rw [signVariations, signVariations, coeffList_neg]
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x:R) => -x) = (fun x => -x) ∘ SignType.sign := by
    grind [Left.sign_neg]
  have h_neg_destutter (l : List SignType) :
      (l.destutter (¬· = ·)).map (- ·) = (l.map (- ·)).destutter (¬· = ·)  := by
    grind [List.map_destutter, neg_inj]
  rw [hsc, List.comp_map, ← h_neg_destutter, List.length_map]
  congr 5
  funext
  simp [SignType.sign]

end OrderedRing

section StrictOrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

/-- The number of sign changes does not change if we multiply by any nonzero scalar. -/
@[simp]
theorem signVariations_C_mul (P : Polynomial R) (hx : η ≠ 0) :
    signVariations (C η * P) = signVariations P := by
  wlog hx2 : 0 < η
  · simpa [lt_of_le_of_ne (le_of_not_gt hx2), hx] using this (η := -η) (P := -P)
  rw [signVariations, signVariations]
  rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2)), ← List.comp_map]
  congr 5
  funext
  simp [hx2, sign_mul]

/-- If P's coefficients start with signs `[+, -, ...]`, then multiplying by a binomial `X - η`
  commutes with `eraseLead` in the number of sign changes. This is because the product of
  `P` and `X - η` has the pattern `[+, -, ...]` as well, so then `P.eraseLead` starts with
  `[-,...]`, and multiplying by `X - η` gives `[-, ...]` too. -/
lemma signVariations_eraseLead_mul_X_sub_C (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
    (hc : P.nextCoeff < 0) :
    ((X - C η) * P).eraseLead.signVariations = ((X - C η) * P.eraseLead).signVariations := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one.mpr (natDegree_pos_of_nextCoeff_ne_zero hc.ne)
  have hndxP : natDegree ((X - C η) * P) = P.natDegree + 1 := by
    have hPn0 : P ≠ 0 :=
      leadingCoeff_ne_zero.mp hP₀.ne'
    rw [natDegree_mul (X_sub_C_ne_zero η) hPn0, natDegree_X_sub_C, add_comm]
  have hndxeP : natDegree ((X - C η) * P.eraseLead) = P.natDegree := by
    have hePn0 : P.eraseLead ≠ 0 :=
      mt nextCoeff_eq_zero_of_eraseLead_eq_zero hc.ne
    rw [natDegree_mul (X_sub_C_ne_zero η) hePn0, natDegree_X_sub_C, add_comm]
    exact natDegree_eraseLead_add_one hc.ne
  have hQ : ((X - C η) * P).nextCoeff = coeff P d - η * coeff P (d + 1) := by
    grind [nextCoeff_of_natDegree_pos, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ, sub_neg]
    trans 0
    · grind [nextCoeff_of_natDegree_pos]
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP, natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [signVariations, signVariations, this]
    have : 0 < natDegree ((X - C η) * P.eraseLead) := by omega
    grind [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff,
      LT.lt.ne, sign_neg, coeffList_eraseLead, ne_zero_of_natDegree_gt,
      nextCoeff_eq_zero_of_eraseLead_eq_zero]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0, ← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP, hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne, ← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ, mul_sub, sub_mul, sub_mul, X_mul_monomial, C_mul_monomial, monomial_sub]
  rw [leadingCoeff, nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos), hd, Nat.add_sub_cancel]
  abel

/-- This lemma is really a specialization of `succ_signVariations_le_sub_mul` to monomials. -/
lemma succ_signVariations_X_sub_C_mul_monomial {d c} (hc : c ≠ 0) (hη : 0 < η) :
    (monomial d c).signVariations + 1 ≤ ((X - C η) * monomial d c).signVariations := by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c using 1
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) ≠ 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c ≠ SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', signVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)

private lemma exists_cons_of_leadingCoeff_pos (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff ≠ 0) :
    ∃ c₀ cs, ((X - C η) * P).coeffList = P.leadingCoeff :: c₀ :: cs ∧
      ((X - C η) * P.eraseLead).coeffList = P.nextCoeff :: cs := by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅ : (X - C η) ≠ 0 := X_sub_C_ne_zero η
  have h₆ : P.eraseLead ≠ 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  apply leadingCoeff_eraseLead_eq_nextCoeff at h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅ h₆)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have h₇ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅ h₃, natDegree_X_sub_C, add_comm]
    have h₈ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        h₅, h₆, h₂, h₄, add_comm 1]
    have : P.eraseLead.natDegree + 2 = ((X - C η) * P.eraseLead).coeffList.length := by
      simp [h₅, h₆, natDegree_mul, add_comm 1]
    have : P.natDegree + 2 = ((X - C η) * P).coeffList.length := by simp [X_sub_C_ne_zero, h₃, h₇]
    have := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    by_cases h₉ : ((X - C η) * P).nextCoeff = 0
    · suffices ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      rw [nextCoeff_of_natDegree_pos (h₇ ▸ P.natDegree.succ_pos), h₇] at h₉
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, C_mul_monomial, eq_of_sub_eq_zero,
        coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        rw [← self_sub_monomial_natDegree_leadingCoeff]
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      rw [nextCoeff_of_natDegree_pos (h₇ ▸ P.natDegree.succ_pos), h₇] at h₉
      grind [coeff_X_sub_C_mul, map_sub, C_mul_monomial, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]

/-- If a polynomial starts with two positive coefficients, then the sign changes in the product
`(X - η) * P` is the same as `(X - η) * P.eraseLead`. This lemma lets us do induction on the
degree of P when P starts with matching coefficient signs. Of course this is also true when the
first two coefficients of P are *negative*, but we just prove the case where they're positive
since it's cleaner and sufficient for the later use. -/
lemma signVariations_X_sub_C_mul_eraseLead_le (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff) :
    signVariations ((X - C η) * P.eraseLead) ≤ signVariations ((X - C η) * P) := by
  obtain ⟨c₀, cs, ⟨hcs, hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h h₂.ne'
  simp +decide only [hcs, hecs, h, h₂, signVariations, List.destutter, List.map_cons, sign_pos,
    List.filter_cons_of_pos, tsub_le_iff_right,
    Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  rw [List.filter_cons]
  split; swap --does c₀ = 0? If so, the trailing nonzero coefficient lists are identical.
  · rfl
  rw [List.destutter'_cons]
  split; swap --does SignType.sign c₀ = 1? If so, the destutter doesn't care about it.
  · rfl
  rcases hcs : (cs.map SignType.sign).filter fun x ↦ decide (x ≠ 0) with _ | ⟨r, rs⟩
  · simp
  · rw [← List.destutter_cons', ← List.destutter_cons']
    grind [List.destutter_cons_cons]

/-- Multiplying a polynomial by a linear term `X - η` adds at least one sign change. This is the
basis for the induction in `roots_countP_pos_le_signVariations`. -/
theorem succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P ≠ 0) :
    signVariations P + 1 ≤ signVariations ((X - C η) * P) := by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P
  rename_i d ih

  -- can assume it starts positive, otherwise negate P
  wlog h_lC : 0 < leadingCoeff P generalizing P with H
  · simpa using @H (-P) (by simpa) (by simpa) (by grind [leadingCoeff_eq_zero, leadingCoeff_neg])

  --Adding a new root doesn't make the product zero, and increases degree by exactly one.
  have h_mul : (X - C η) * P ≠ 0 := mul_ne_zero (X_sub_C_ne_zero η) hP
  have h_deg_mul : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hP, natDegree_X_sub_C, add_comm]

  rcases d with _ | d
  · --P is zero degree, therefore a constant.
    have hcQ : 0 < coeff P 0 := by grind [leadingCoeff]
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      grind [coeff_X_sub_C_mul, mul_zero, coeff_eq_zero_of_natDegree_lt]
    dsimp [signVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hP, withBotSucc_degree_eq_natDegree_add_one h_mul]
    simp [h_deg_mul, hxcQ, hη, hcQ, hd, List.range_succ]

  -- P is positive degree. Set up some temporary variables for signs for the nextCoeffs.
  generalize hs_nC : SignType.sign P.nextCoeff = s_nC
  generalize hs_nC_mul : SignType.sign ((X - C η) * P).nextCoeff = s_nC_mul

  --We're really doing induction on `P.eraseLead` in a sense
  have h_ih : P.eraseLead.natDegree < d + 1 := by grind [eraseLead_natDegree_le]

  have h_mul_lC : SignType.sign ((X - C η) * P).leadingCoeff = 1 := by simp [h_lC]
  have h_ηP : 0 < η * coeff P (d + 1) := by grind [leadingCoeff, mul_pos]

  rcases s_nC.trichotomy with rfl | rfl | rfl; rotate_left
  · -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    obtain rfl : s_nC_mul = -1 := by
      have : coeff P d = 0 := by simpa [nextCoeff, hd] using hs_nC
      simp [*, ← hs_nC_mul, nextCoeff, coeff_X_sub_C_mul]

    /- We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
      hypothesis on eraseLead P. but that isn't actually true: we could have P a monomial
      and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
      true as written for P ≠ 0.) So we need to do a case-split and handle this separately. -/
    by_cases eraseLead P = 0
    · grind [succ_signVariations_X_sub_C_mul_monomial,
        eraseLead_add_monomial_natDegree_leadingCoeff, zero_add]
    · /- Dropping the lead of the product exactly drops the first two of the eraseLead. This
        decreases the sign variations of the eraseLead by at least one, and of the product by at
       most one, so we can induct. -/
      have : signVariations ((X - C η) * P).eraseLead + 1 =
          signVariations ((X - C η) * P) := by
        simp [-leadingCoeff_mul, ← sign_ne_zero,
          signVariations_eq_eraseLead_add_ite h_mul, leadingCoeff_eraseLead_eq_nextCoeff,
          hs_nC_mul, h_mul_lC]
      have : ((X - C η) * P.eraseLead).signVariations ≤
          ((X - C η) * P).eraseLead.signVariations := by
        have := signVariations_eraseLead_le (eraseLead ((X - C η) * P))
        rwa [← eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne']
        grind [sign_eq_zero_iff]
      grind [signVariations_le_eraseLead_succ]

  all_goals (
    have h₁ : nextCoeff P ≠ 0 := by simp [← sign_ne_zero, hs_nC]
    specialize ih _ h_ih (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl
    have : P.signVariations = P.eraseLead.signVariations + ?_ := by
      simp [signVariations_eq_eraseLead_add_ite hP, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        hs_nC, h_lC]
      exact rfl
  )
  · /- P starts with [+,+,...]. (X-C)*P starts with [+,?,...]. After dropping the lead of P, this
      becomes [+,...] and [+,...]. So the sign variations on P are unchanged when we induct, while
      (X-C)*P can only lose at most one sign change. -/
    grind [sign_eq_one_iff, signVariations_X_sub_C_mul_eraseLead_le]
  · /- P starts with [+,-,...], so (X-C)*P starts with [+,-,...]. After dropping the lead of P, this
    becomes [-,...] and [-,...]. Dropping the first one of each decreases (X-C)*P by one and P by
    one, so we can induct. -/
    trans ((X - C η) * P).eraseLead.signVariations + 1
    · grind [signVariations_eraseLead_mul_X_sub_C, sign_eq_neg_one_iff]
    · suffices SignType.sign ((X - C η) * P).nextCoeff = -1 by
        simp +decide [signVariations_eq_eraseLead_add_ite h_mul, h_lC,
          leadingCoeff_eraseLead_eq_nextCoeff, ← sign_eq_zero_iff, this]
      grind [← sign_eq_neg_one_iff, coeff_X_sub_C_mul, nextCoeff]

end StrictOrderedRing
section CommStrictOrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (P : Polynomial R)

/-- **Descartes' Rule of Signs**: the number of positive roots is at most the number of sign
variations. -/
theorem roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) ≤ signVariations P := by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P --Induct on number of roots.
  · exact zero_le _
  rename_i ih
  have hp : P ≠ 0 := by grind [roots_zero, Multiset.countP_zero]
  -- we can take a positive root, η, because the number of roots is positive
  obtain ⟨η, η_root, η_pos⟩ : ∃ x, x ∈ P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  -- (X - η) divides P(X), so write P(X) = (X - η) * Q(X)
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  -- P has at least num_roots sign variations
  grw [ih Q, succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]

end CommStrictOrderedRing
end Polynomial
