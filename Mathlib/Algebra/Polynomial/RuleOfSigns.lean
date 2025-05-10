/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Algebra.Polynomial.CoeffList
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.List.Destutter
import Mathlib.Data.Sign

/-!

# Descartes' Rule of Signs

We define the "sign changes" in the coefficients of a polynomial, and prove Descartes'
Rule of Signs: a real polynomial has at most as many positive roots as there are sign
changes. A sign change is when there is a positive coefficient followed by a negative
coefficient, or vice versa, with any number of zero coefficients in between.

## Main Definitions

- `Polynomial.SignVariations`: The number of sign changes in a

## Main theorem

- `Polynomial.roots_countP_pos_le_SignVariations`. States that
`P.roots.countP (0 < ·) ≤ P.SignVariations`, so that positive roots are counted with multiplicity.
It's currently roved for any `CommRing` with `IsStrictOrderedRing`. There is likely some correct
statement in terms of a (noncommutative) `Ring`, but `Polynomial.roots` is only defined for
commutative rings.

## Reference

https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs
-/

namespace Polynomial

section Semiring
variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

/-- Counts the number of times that the coefficients in a polynomial change sign, with
the convention that 0 can count as either sign. -/
noncomputable def SignVariations : ℕ :=
    let coeff_signs := (coeffList P).map SignType.sign;
    let nonzero_signs := coeff_signs.filter (· ≠ 0);
    (nonzero_signs.destutter (· ≠ ·)).length - 1

variable (R) in
@[simp]
theorem signvar_zero : SignVariations (0 : R[X]) = 0 :=
  by simp [SignVariations]

/-- Sign variations of a monomial are always zero. -/
@[simp]
theorem signvar_monomial (d : ℕ) (c : R) : SignVariations (monomial d c) = 0 := by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, SignVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

/-- If the first two signs are the same, then sign_variations is unchanged by eraseLead -/
theorem signvar_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff) :
  SignVariations P = SignVariations P.eraseLead := by
  by_cases hpz : (P = 0)
  · simp_all
  · have h₂ : nextCoeff P ≠ 0 := (by simp_all [·])
    obtain ⟨_, hl⟩ := coeffList_eq_cons_leadingCoeff (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂)
    dsimp [SignVariations]
    rw [coeffList_eraseLead hpz, hl, leadingCoeff_eraseLead_eq_nextCoeff h₂]
    simp_all [h, List.destutter]

/-- If we drop the leading coefficient, the sign changes drop by 0 or 1 depending on whether
the first two nonzero coeffients match. -/
theorem signvar_eq_eraseLead_add_ite {P : Polynomial R} (h : P ≠ 0) :
    SignVariations P = SignVariations P.eraseLead + if SignType.sign P.leadingCoeff
      = -SignType.sign P.eraseLead.leadingCoeff then 1 else 0 := by
  by_cases hpz : P = 0
  · simp_all
  have hsl : SignType.sign (leadingCoeff P) ≠ 0 := by simp_all
  obtain hc := coeffList_eraseLead hpz
  dsimp [SignVariations]
  rw [hc, List.map_cons, List.map_append, List.map_replicate, List.filter, decide_eq_true hsl]
  simp only [SignVariations, decide_not, lt_self_iff_false, sign_zero, List.filter_append,
    List.filter_replicate, decide_true, Bool.not_true, ite_false, List.nil_append]
  cases hcep : P.eraseLead.coeffList
  case neg.nil =>
    simp [coeffList_eq_nil.mp hcep, h]
  case neg.cons c cs =>
    rw [List.map_cons, List.filter]
    have hc2 : SignType.sign c ≠ 0 := by
      by_contra hc2
      suffices eraseLead P = 0 by
        simp [this] at hcep
      by_contra h
      obtain ⟨l, hl⟩ := coeffList_eq_cons_leadingCoeff h
      rw [hcep, List.cons.injEq] at hl
      rcases hl with ⟨ha, _⟩
      rw [sign_eq_zero_iff.mp hc2, eq_comm, leadingCoeff_eq_zero] at ha
      exact h ha
    simp only [List.destutter, Bool.false_eq_true, ↓reduceIte, hc2, decide_false, Bool.not_false,
        List.nil_append, List.destutter']
    have hel : eraseLead P ≠ 0 := by
      simp [← coeffList_eq_nil, hcep]
    have hc4 : c = leadingCoeff P.eraseLead := by
      obtain ⟨ls,hls⟩ := coeffList_eq_cons_leadingCoeff hel
      cases hcep ▸ hls
      rfl
    by_cases hc3 : SignType.sign (leadingCoeff P) = SignType.sign c
    · cases hc6 : SignType.sign c
      · exact (hc2 hc6).elim
      all_goals
      cases hl2 : SignType.sign (leadingCoeff P)
      · exact (hsl hl2).elim
      all_goals simp_all
    · have hc5 : SignType.sign (leadingCoeff P) = -SignType.sign c := by
        cases hc6 : SignType.sign c
        · exact (hc2 hc6).elim
        all_goals
        cases hl2 : SignType.sign (leadingCoeff P)
        · exact (hsl hl2).elim
        all_goals first
        | rfl
        | simp_all
      rw [if_pos hc3, ← hc4, if_pos hc5,
        Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
      simp only [List.length_cons, add_tsub_cancel_right]

/-- We can only lose, not gain, sign changes if we drop the leading coefficient. -/
theorem signvar_eraseLead_le : SignVariations P.eraseLead ≤ SignVariations P := by
  by_cases hpz : P = 0
  · simp [hpz]
  have := signvar_eq_eraseLead_add_ite hpz
  by_cases SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff
  · simp_all
  · simp_all

/-- We can only lose at most one sign changes if we drop the leading coefficient. -/
theorem signvar_le_eraseLead_succ : SignVariations P ≤ SignVariations P.eraseLead + 1 := by
  by_cases hpz : P = 0
  · simp [hpz]
  have h := signvar_eq_eraseLead_add_ite hpz
  by_cases SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff
  · simp_all
  · simp_all

end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] (P : Polynomial R) {x : R}

/-- The number of sign changes does not change if we negate. -/
@[simp]
theorem signvar_neg : SignVariations (-P) = SignVariations P := by
  dsimp [SignVariations]
  rw [coeffList_neg]
  congr 1
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x:R) => -x) = (fun x => -x) ∘ SignType.sign := by
    funext n
    simp [Left.sign_neg]
  rw [hsc, List.comp_map]
  have h_neg_destutter (l : List SignType) : (List.destutter (¬· = ·) l).map (- ·) =
      List.destutter (¬· = ·) (l.map (- ·)) := by
    apply List.map_destutter
    simp only [neg_inj, implies_true]
  rw [← h_neg_destutter, List.length_map]
  congr
  funext x
  simp [SignType.sign, apply_ite (@Neg.neg SignType _), apply_ite (· = (0 : SignType))]

end OrderedRing

section StrictOrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

/-- The number of sign changes does not change if we multiply by any nonzero scalar. -/
@[simp]
theorem signvar_C_mul (P : Polynomial R) (hx : η ≠ 0) :
    SignVariations (C η * P) = SignVariations P := by
  wlog hx2 : 0 < η
  · have hnegneg : (C (-η) * (-P)) = (C η * P) := by
      simp
    rw [← signvar_neg P, ← hnegneg]
    exact this (-P) (neg_ne_zero.mpr hx) <| Left.neg_pos_iff.mpr
      <| lt_of_le_of_ne (not_lt.mp hx2) hx
  · dsimp [SignVariations]
    congr 3
    rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2)), ← List.comp_map]
    congr 2
    funext
    simp [hx2, sign_mul]

/-- If P's coefficients start with signs `[+, -, ...]`, then multiplying by a binomial `X - η`
  commutes with `eraseLead` in the number of sign changes. This is because the product of
  `P` and `X - η` has the pattern `[+, -, ...]` as well, so then `P.eraseLead` starts with
  `[-,...]`, and multiplying by `X - η` gives `[-, ...]` too. -/
lemma signvar_ereaseLead_mul_XC_eq_XC_mul_eraseLead (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
    (hc : P.nextCoeff < 0) :
    ((X - C η) * P).eraseLead.SignVariations = ((X - C η) * P.eraseLead).SignVariations := by
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
    rw [nextCoeff_of_natDegree_pos (hndxP ▸ P.natDegree.succ_pos)]
    rw [hndxP, hd, Nat.add_sub_cancel, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ, sub_neg]
    trans 0
    · rwa [nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos), hd, Nat.add_sub_cancel] at hc
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP, natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [SignVariations, SignVariations, this]
    rw [coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero hQ₁.ne)]
    have hndeP0 : 0 < natDegree ((X - C η) * P.eraseLead) :=
      Nat.lt_of_sub_eq_succ (hd ▸ hndxeP)
    rw [coeffList_eraseLead (ne_zero_of_natDegree_gt hndeP0)]
    rw [List.map_cons, List.map_cons, leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
    rw [sign_neg hQ₁, sign_neg ?_, this, hndxeP, hndexP0]
    rwa [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff hc.ne]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP, hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne, ← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ, mul_sub, sub_mul, sub_mul, X_mul_monomial, C_mul_monomial, monomial_sub]
  rw [leadingCoeff, nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos), hd, Nat.add_sub_cancel]
  abel

/-- This lemma is really a specialization of `succ_sign_lin_mul` to monomials. -/
lemma succ_sign_lin_mul_monomial {d c} (hc : c ≠ 0) (hη : 0 < η) :
    (monomial d c).SignVariations + 1 ≤ ((X - C η) * monomial d c).SignVariations := by
  have h₁ : nextCoeff ((X - C η) * monomial d c) = -(η * c) := by
    convert coeff_mul_monomial (X - C η) d 0 c using 1
    · simp [hc, nextCoeff, natDegree_mul (X_sub_C_ne_zero η)]
    · simp
  have h₂ : eraseLead ((X - C η) * monomial d c) ≠ 0 := by
    apply mt nextCoeff_eq_zero_of_eraseLead_eq_zero
    simp [h₁, hc, hη.ne']
  have h₃ : SignType.sign c ≠ SignType.sign (-(η * c)) := by
    simp [hη, hc, Left.sign_neg, sign_mul]
  simpa [h₁, h₂, h₃, hc, hη.ne', SignVariations, List.destutter_cons_cons,
    ← leadingCoeff_cons_eraseLead, coeffList_eraseLead, leadingCoeff_eraseLead_eq_nextCoeff]
  using List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)

private lemma exists_cons_of_leadingCoeff_pos (η) (h₁ : 0 < leadingCoeff P) (h₂ : P.nextCoeff ≠ 0) :
    ∃ c₀ cs, ((X - C η) * P).coeffList = P.leadingCoeff :: c₀ :: cs ∧
      ((X - C η) * P.eraseLead).coeffList = P.nextCoeff :: cs := by
  have h₃ := leadingCoeff_ne_zero.mp h₁.ne'
  have h₄ := natDegree_eraseLead_add_one h₂
  have h₅₁ : (X - C η) ≠ 0 := X_sub_C_ne_zero η
  have h₅₂ : P.eraseLead ≠ 0 := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₂
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nextCoeff_ne_zero h₂)
  replace h₂ := leadingCoeff_eraseLead_eq_nextCoeff h₂
  have h_cons := coeffList_eraseLead (mul_ne_zero h₅₁ h₅₂)
  generalize ((X - C η) * P.eraseLead).natDegree -
    ((X - C η) * P.eraseLead).eraseLead.degree.succ = n at h_cons ⊢
  use nextCoeff ((X - C η) * P), .replicate n 0 ++ coeffList ((X - C η) * P.eraseLead).eraseLead
  constructor
  · have hM := leadingCoeff_monic_mul (q := P) (monic_X_sub_C η)
    have h₆ : natDegree ((X - C η) * P) = P.natDegree + 1 := by
      rw [natDegree_mul h₅₁ h₃, natDegree_X_sub_C, add_comm]
    have h₇ : ((X - C η) * P.eraseLead).eraseLead =
        (X - C η) * P.eraseLead - monomial P.natDegree P.nextCoeff := by
      simp [← self_sub_monomial_natDegree_leadingCoeff (_ * _), natDegree_mul,
        hM, h₅₁, h₅₂, h₂, h₄, add_comm 1]
    have _ := calc P.eraseLead.natDegree + 2
      _ = ((X - C η) * P.eraseLead).coeffList.length := by
        simp [h₅₁, h₅₂, natDegree_mul, add_comm 1]
      _ = n + ((X - C η) * P.eraseLead).eraseLead.coeffList.length + 1 := by
        simp [h_cons]
    by_cases h₈ : ((X - C η) * P).nextCoeff = 0
    · suffices h : ((X - C η) * P).eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have hn1 := coeffList_eraseLead (mul_ne_zero (X_sub_C_ne_zero η) h₃)
        generalize ((X - C η) * P).natDegree -
          ((X - C η) * P).eraseLead.degree.succ = m at hn1 ⊢
        have hn0n1 : m = n + 1 := by
          have hl := calc P.natDegree + 2
            _ = (coeffList ((X - C η) * P)).length := by simp [X_sub_C_ne_zero, h₃, h₆]
            _ = m + ((X - C η) * P.eraseLead).eraseLead.coeffList.length + 1 := by simp [h, hn1]
          linarith
        simp [hn1, h, h₈, hn0n1, List.replicate_succ]
      rw [← self_sub_monomial_natDegree_leadingCoeff, h₆, hM, h₇]
      rw [← self_sub_monomial_natDegree_leadingCoeff, mul_sub]
      suffices h : C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        simp [h, X_mul_monomial, sub_mul]
        abel
      rw [nextCoeff_of_natDegree_pos (h₆ ▸ P.natDegree.succ_pos), h₆,
        Nat.add_sub_cancel, hd, coeff_X_sub_C_mul] at h₈
      rw [leadingCoeff, nextCoeff_of_natDegree_pos (h₄ ▸ P.eraseLead.natDegree.succ_pos),
        hd, C_mul_monomial, ← eq_of_sub_eq_zero h₈, Nat.add_sub_cancel]
    · suffices h : ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have hn0 := leadingCoeff_cons_eraseLead h₈
        have hn1 := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₈)
        generalize ((X - C η) * P).eraseLead.natDegree -
          ((X - C η) * P).eraseLead.eraseLead.degree.succ = m at hn1 ⊢
        have hn0n2 : m = n := by
          have hl := calc P.natDegree + 2
            _ = (coeffList ((X - C η) * P)).length := by simp [X_sub_C_ne_zero, h₃, h₆]
            _ = m + ((X - C η) * P).eraseLead.eraseLead.coeffList.length + 2 := by simp [← hn0, hn1]
          rw [h] at hl
          linarith
        simp [← hn0, hn1, h, hn0n2, leadingCoeff_eraseLead_eq_nextCoeff h₈]
      rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_eraseLead_eq_nextCoeff h₈]
      rw [show natDegree (eraseLead ((X - C η) * P)) = P.natDegree from
        Nat.add_right_cancel (natDegree_eraseLead_add_one h₈ ▸ h₆)]
      rw [← self_sub_monomial_natDegree_leadingCoeff, h₆, hM, h₇]
      rw [← self_sub_monomial_natDegree_leadingCoeff, mul_sub]
      suffices h : monomial P.natDegree ((X - C η) * P).nextCoeff =
        monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        rw [h, sub_mul _ _ (monomial _ _), X_mul_monomial]
        abel
      rw [nextCoeff_of_natDegree_pos (h₆ ▸ P.natDegree.succ_pos), h₆, Nat.add_sub_cancel]
      rw [leadingCoeff, nextCoeff_of_natDegree_pos (h₄ ▸ P.eraseLead.natDegree.succ_pos)]
      simp [hd, coeff_X_sub_C_mul]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]

/-- If a polynomial starts with two positive coefficients, then the sign changes in the product
`(X - η) * P` is the same as `(X - η) * P.eraseLead`. This lemma lets us do induction on the
degree of P when P starts with matching coefficient signs. Of course this is also true when the
first two coefficients of P are *negative*, but we just prove the case where they're positive
since it's cleaner and sufficient for the later use. -/
lemma signvar_mul_eraseLead_le_of_nextCoeff (h₁ : 0 < leadingCoeff P) (h₂ : 0 < P.nextCoeff) :
    SignVariations ((X - C η) * P.eraseLead) ≤ SignVariations ((X - C η) * P) := by
  obtain ⟨c₀,cs,⟨hcs,hecs⟩⟩ := exists_cons_of_leadingCoeff_pos η h₁ h₂.ne'
  dsimp [SignVariations]
  simp only [hcs, hecs, List.destutter, decide_not, List.map_cons, h₁, sign_pos, one_ne_zero,
    decide_false, Bool.not_false, List.filter_cons_of_pos, h₂, tsub_le_iff_right]
  rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _))]
  dsimp [List.filter]
  split --split on whether c₀ = 0 or not.
  swap
  · rfl --if c₀ = 0, the trailing nonzero coefficient lists are identical.
  dsimp [List.destutter']
  split --split on whether SignType.sign c₀ = 1 or not.
  swap
  · rfl --if sign c₀ = 1, the destutter doesn't care about it.
  rw [← List.destutter_cons' , ← List.destutter_cons']
  rcases hr : List.filter (fun x => !decide (x = 0)) (List.map (⇑SignType.sign) cs)
    with _ | ⟨r, rs⟩
  · simp
  · have hc₀ : SignType.sign c₀ = -1 := by
      cases _ : SignType.sign c₀ <;> simp_all
    rw [List.destutter_cons_cons, List.destutter_cons_cons, hc₀]
    split
    next h₃ =>
      have h₄ : ¬(-1 ≠ r) := by
        cases r <;> simp_all [List.filter_eq_cons_iff]
      simp only [List.length_cons, if_neg h₄]
      exact Nat.succ_le_succ <| (List.length_destutter'_congr _ (by tauto)).le
    next h₃ =>
      suffices h₄ : r = 1 by
        rw [h₄]
        exact Nat.le_trans (Nat.le_succ _) (Nat.le_succ _)
      cases r
      · have h : SignType.zero ∈ SignType.zero :: rs := List.mem_cons.mpr (.inl rfl)
        rw [← hr] at h
        simpa using List.of_mem_filter h
      · tauto
      · rfl

/-- Multiplying a polynomial by a linear term `X - η` adds at least one sign change. This is the
basis for the induction in `roots_countP_pos_le_SignVariations`. -/
theorem succ_sign_lin_mul (hη : 0 < η) (hq : P ≠ 0) :
    SignVariations P + 1 ≤ SignVariations ((X - C η) * P) := by
  -- do induction on the degree
  generalize hd : P.natDegree = d
  induction' d using Nat.strong_induction_on with d ih generalizing P
  -- rw [eq_comm] at hd
  -- can assume it starts positive, otherwise negate P
  wlog hqpos : 0 < leadingCoeff P generalizing P with H
  · have h : leadingCoeff P < 0 :=
      lt_of_le_of_ne (le_of_not_lt hqpos) (mt leadingCoeff_eq_zero.mp hq)
    simpa using H (P := -P) (by simpa) (by simpa) (by simpa)
  --the new polynomial isn't zero
  have hm : (X - C η) * P ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero η) hq
  --LHS is one degree higher than RHS
  have hdQ : natDegree ((X - C η) * P) = natDegree P + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero η) hq, natDegree_X_sub_C, add_comm]
  rcases d with _ | d
  · --zero degree
    have hcQ : 0 < coeff P 0 := by
      rwa [leadingCoeff, hd] at hqpos
    have hxcQ : coeff ((X - C η) * P) 1 = coeff P 0 := by
      have h : coeff P 1 = 0 :=
        coeff_eq_zero_of_natDegree_lt (hd ▸ zero_lt_one)
      rw [coeff_X_sub_C_mul, sub_eq_self, h, mul_zero]
    dsimp [SignVariations, coeffList]
    rw [withBotSucc_degree_eq_natDegree_add_one hq, withBotSucc_degree_eq_natDegree_add_one hm]
    simp [hdQ, hcQ, hxcQ, hη, hcQ, hd, List.range_succ]

  --positive degree
  set sq0 := SignType.sign P.leadingCoeff with hsq0
  set sq1 := SignType.sign P.nextCoeff with hsq1
  set sηq0 := SignType.sign ((X - C η) * P).leadingCoeff with hsηq0
  set sηq1 := SignType.sign ((X - C η) * P).nextCoeff with hsηq1

  have h_sq0_pos : sq0 = 1 :=
    hsq0 ▸ sign_pos hqpos
  have h_sq0_sηq0 : sq0 = sηq0 := by
    simp [hsq0, hsηq0]
  have hnDeQ : P.eraseLead.natDegree < d + 1 :=
    have := eraseLead_natDegree_le P
    by omega
  have h₂ : 0 < η * coeff P (d + 1) := mul_pos hη <| by
    rw [leadingCoeff, h_sq0_pos, hd] at hsq0
    exact sign_eq_one_iff.mp hsq0.symm

  cases hcsq1 : sq1
  · --sq1 is zero
    -- P starts with [+,0,...] so (X-C)*P starts with [+,-,...].
    have hcsηq1 : sηq1 = -1 := by
      have : coeff P d = 0 := by
        rw [(Nat.sub_eq_of_eq_add hd).symm, hd, ← sign_eq_zero_iff, eq_comm]
        simpa [nextCoeff, hcsq1, hd] using hsq1
      apply sign_eq_neg_one_iff.mpr
      rw [nextCoeff, natDegree_mul (X_sub_C_ne_zero η) hq, natDegree_X_sub_C]
      simp only [add_eq_zero, one_ne_zero, false_and, add_tsub_cancel_left, ite_false]
      rwa [hd, coeff_X_sub_C_mul, sub_neg, this]

    have h_e3LQ : SignVariations ((X - C η) * P).eraseLead + 1 =
        SignVariations ((X - C η) * P) := by
      rw [signvar_eq_eraseLead_add_ite hm, leadingCoeff_eraseLead_eq_nextCoeff ?_,
        ← hsηq1, ← hsηq0, hcsηq1, ← h_sq0_sηq0, h_sq0_pos]
      · simp
      · simp [← sign_ne_zero, ← hsηq1, hcsηq1]

    --We would like to just `have : eraseLead P ≠ 0`, so that we can use the inductive
    --hypothesis on eraseLead P. but that isn't actually true: we could have P = C * X^n,
    --and then eraseLead P = 0, and then the inductive hypothesis doesn't hold. (It's only
    --true as written for P ≠ 0.) So we need to do a case-split and handle this separately.
    by_cases h_eQ_nz : eraseLead P = 0
    · --this is the edge case where eraseLead P = 0. Therefore, P is a monomial.
      rw [← eraseLead_add_monomial_natDegree_leadingCoeff P, h_eQ_nz, zero_add]
      exact succ_sign_lin_mul_monomial hqpos.ne' hη
    · --Dropping the lead of Q exactly drops the first two of LQ. This decreases the sign
      --variations of LQ by at least one, and Q by at most one, so we can induct.
      have h_elMul : eraseLead (eraseLead ((X - C η) * P)) = (X - C η) * (eraseLead P) :=
        eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero hη.ne' <|
          sign_eq_zero_iff.mp (SignType.zero_eq_zero ▸ hcsq1 ▸ hsq1)
      have h_e2LQ := signvar_eraseLead_le (eraseLead ((X - C η) * P))
      rw [h_elMul] at h_e2LQ
      linarith [signvar_le_eraseLead_succ P, ih _ hnDeQ h_eQ_nz rfl]
  all_goals (
    have h₁ : nextCoeff P ≠ 0 := by
      simp [← sign_ne_zero, ← hsq1, hcsq1]

    specialize ih _ hnDeQ (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₁) rfl

    have h_eQ : P.SignVariations = P.eraseLead.SignVariations + ?_ := by
      simp [signvar_eq_eraseLead_add_ite hq, leadingCoeff_eraseLead_eq_nextCoeff h₁,
        ← hsq0, ← hsq1, h_sq0_pos, hcsq1]
      exact rfl
  )
  · --sq1 is negative
    -- P starts with [+,-,...], so (X-C)*P starts with [+,-,...].
    -- After dropping the lead of P, this becomes [-,...] and [-,...].
    -- Dropping the first one of each decreases (X-C)*P by one and P by one, so we can induct.
    have hηq1 : sηq1 = -1 := by
      have hc : coeff P d < 0 := by
        rw [(Nat.sub_eq_of_eq_add hd).symm, hd, ← sign_eq_neg_one_iff, eq_comm]
        simpa [nextCoeff, hcsq1, hd] using hsq1
      apply sign_eq_neg_one_iff.mpr
      simpa [nextCoeff, natDegree_mul, X_sub_C_ne_zero, hq, hd, coeff_X_sub_C_mul] using hc.trans h₂

    have h₂ : ((X - C η) * P).eraseLead.leadingCoeff = ((X - C η) * P).nextCoeff := by
      refine leadingCoeff_eraseLead_eq_nextCoeff (fun h ↦ ?_)
      simp [h, hsηq1] at hηq1

    have hLQ : ((X - C η) * P).SignVariations = ((X - C η) * P).eraseLead.SignVariations + 1 := by
      rw [signvar_eq_eraseLead_add_ite hm, ← hsηq0, ← h_sq0_sηq0, h₂]
      simp [← hsηq1, hηq1, h_sq0_pos]

    have hLQ2 : ((X - C η) * P).eraseLead.SignVariations =
        ((X - C η) * P.eraseLead).SignVariations := by
      apply signvar_ereaseLead_mul_XC_eq_XC_mul_eraseLead hη hqpos
      exact sign_eq_neg_one_iff.mp (SignType.neg_eq_neg_one ▸ hcsq1 ▸ hsq1)

    linarith

  · --sq1 is positive
    -- P starts with [+,+,...]. (X-C)*P starts with [+,?,...].
    -- After dropping the lead of P, this becomes [+,...] and [+,...].
    -- So the sign variations on P are unchanged when we induct, while (X-C)*P can only lose at
    -- most one sign change.
    have hLQ : ((X - C η) * P.eraseLead).SignVariations ≤ ((X - C η) * P).SignVariations := by
      apply signvar_mul_eraseLead_le_of_nextCoeff hqpos
      simp [← hsq1, hcsq1, ← sign_eq_one_iff]

    linarith

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (P : Polynomial R)

/-- **Descartes' Rule of Signs**: the number of positive roots is at most the number of sign
variations. -/
theorem roots_countP_pos_le_SignVariations : P.roots.countP (0 < ·) ≤ SignVariations P := by
    generalize h : P.roots.countP (0 < ·) = num_pos_roots
    induction' num_pos_roots with num_roots_m1 ih generalizing P
    · exact zero_le _
    · --otherwise induct on number of roots.
      have hp : P ≠ 0 := by
        rintro rfl
        simp at h
      -- we can take a positive root, η, because the number of roots is positive
      obtain ⟨η, η_root, η_pos⟩ : ∃ x, x ∈ P.roots ∧ (fun x ↦ 0 < x) x := by
        simp only [← Multiset.countP_pos, h, Nat.zero_lt_succ]
      -- (X - η) divies P(X), so write P(X) = (X - η) * Q(X)
      obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
      -- Q is nonzero
      have hq_nz : Q ≠ 0 := by
        rintro rfl
        simp at hp
      -- Q has one less positive root than P
      have q_roots_m1 : num_roots_m1 = Q.roots.countP (0 < ·) := by
        simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos,
          ← Nat.succ.injEq, ← Multiset.cons_zero, Multiset.countP_cons, Nat.one_add]
      -- P has at least num_roots sign variations
      calc
      _ ≤ SignVariations Q + 1 :=
        Nat.add_le_add_right (ih Q q_roots_m1.symm) 1
      _ ≤ _ :=
        succ_sign_lin_mul η_pos hq_nz

end StrictOrderedRing
end Polynomial
