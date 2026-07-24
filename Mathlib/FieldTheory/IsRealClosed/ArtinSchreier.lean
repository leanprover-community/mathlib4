/-
Copyright (c) 2026 Kiran S. Kedlaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kiran S. Kedlaya
-/
module

public import Mathlib.FieldTheory.ArtinSchreierExtension
public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!

# Artin-Schreier theorem

This file proves the Artin-Schreier theorem `isAlgClosed_or_isRealClosed`:
a field admitting a finite extension which is algebraically closed is either algebraically
closed or real closed.

-/

universe u

section Lemmas

open IntermediateField Module Nat Polynomial

variable {F : Type u} {K : Type u} [Field F] [Field K] [Algebra F K] [Hac : IsAlgClosed K]

-- All of these lemmas are easy corollaries of the main theorem.

/- If a field admits an algebraically closed extension of degree dividing a prime `p`, any
   polynomial either has a root or has all irreducible divisors of degree `p` and degree
   divisible by `p`. -/
lemma divisor_by_finrank {p : ℕ} (f : F[X]) (hr : finrank F K ∣ p) (hp : p.Prime) :
    (∃ x, f.IsRoot x) ∨ (∀ d, Irreducible d → d ∣ f → d.natDegree = p) := by
  rw [or_iff_not_imp_right]
  push Not
  rintro ⟨d, h1, h2, h3⟩
  have h := h1.natDegree_dvd_finrank (Hac.splits _)
  have h := ((dvd_prime hp).mp (h.trans hr)).resolve_right h3
  have ⟨x, hx⟩ := exists_root_of_natDegree_eq_one h
  exact ⟨x, hx.dvd h2⟩

lemma divisor_by_finrank' {p : ℕ} (f : F[X]) (hr : finrank F K ∣ p) (hp : p.Prime) :
    (∃ x, f.IsRoot x) ∨ p ∣ f.natDegree :=
  (divisor_by_finrank f hr hp).imp_right (fun h ↦ dvd_natDegree_of_monic_of_irreducible
    f (fun d _ h1 h2 ↦ (h d h1 h2).symm.dvd))

/- A field admitting a finite extension which is algebraically closed is perfect. -/
lemma finite_alg_closure_perfect [hf : FiniteDimensional F K] : PerfectField F := by
  open CharP FaithfulSMul IsPurelyInseparable PerfectRing in
  let E := separableClosure F K
  let p := ringExpChar E
  have : PerfectField E := by
    let n := exponent E K
    rcases expChar_is_prime_or_one E p with h | h
    · have : PerfectRing E p := by
        refine ofSurjective E p (fun b ↦ ?_)
        obtain ⟨x, hx⟩ := Hac.exists_pow_nat_eq ((algebraMap E K) b) (expChar_pow_pos E p (n + 1))
        rw [pow_succ', ←pow_mul_pow_sub p (elemExponent_le_exponent E x)] at hx
        use elemReduct E x ^ p ^ (n - elemExponent E x)
        apply (algebraMap_injective E K).eq_iff.mp
        rw [←hx, frobenius_def, ←pow_mul, map_pow, algebraMap_elemReduct_eq' E p]
        ring
      exact toPerfectField E p
    · have := ringExpChar.of_eq h
      have := charZero_of_expChar_one' E
      exact PerfectField.ofCharZero
  exact perfectField_of_isSeparable_of_perfectField_top F E

/- If a field admits an extension of prime degree `p` which is algebraically closed, then
   its characteristic cannot equal `p`. -/
lemma finite_alg_closure_prime {p : ℕ} (hp : p.Prime) (hr : finrank F K = p) : ¬CharP F p := by
  let t := p - 1
  subst hr
  have hf := FiniteDimensional.of_finrank_pos hp.pos
  have := finite_alg_closure_perfect (hf := hf)
  have : IsAlgClosure F K := ⟨Hac, inferInstance⟩
  have h : IsGalois F K := inferInstance
  by_contra
  obtain ⟨a, x, ha⟩ := ((isCyclic_charP_tfae hp rfl).out 0 4).mp h
  have h := irreducible_artinSchreierPoly_tower hp rfl a x ha
  have h := (degree_eq_iff_natDegree_eq_of_pos one_pos).mp (Hac.degree_eq_one_of_irreducible K h)
  rw [(artinSchreierPoly_isMonicOfDegree _ hp.one_lt).1] at h
  simp_all [Nat.not_prime_one]

/- If `a` and `b` belong to a field which admits an algebraically closed quadratic extension,
   then one of `a^2 + b` or `-b` is a square. -/
lemma quadratic_alg_closure (h : finrank F K ∣ 2) (a b : F) :
    IsSquare (a*a + b) ∨ IsSquare (-b) := by
  let g := monomial 4 1 + monomial 2 (-2*a) + monomial 0 (a^2 + b)
  have h1 : g.IsMonicOfDegree 4 := by
    subst g
    exact ⟨by compute_degree!, by monicity⟩
  rcases divisor_by_finrank g h prime_two with ⟨x, hx⟩ | h
  · right
    use x^2 - a
    simp only [IsRoot.def, g, eval_add, eval_monomial] at hx
    grind only
  · obtain ⟨f, h3, h4, ⟨e, he⟩⟩ := exists_monic_irreducible_factor g
      (not_isUnit_of_natDegree_pos g (by simp [h1.1]))
    subst g
    have hf : f.IsMonicOfDegree 2 := ⟨h f h4 ⟨e, he⟩, h3⟩
    let f₀ := f.coeff 0; let f₁ := f.coeff 1; let e₀ := e.coeff 0; let e₁ := e.coeff 1
    have : f₀*e₀ = a^2 + b ∧ f₀*e₁ + f₁*e₀ = 0 ∧ f₀ + f₁*e₁ + e₀ = -2*a ∧ f₁ + e₁ = 0 := by
      have h2 : ∀ {t : F[X]}, t.IsMonicOfDegree 2 → t.coeff 2 = 1 ∧ t.coeff 3 = 0 := by
        intro _ ⟨h1, h2⟩
        rw [←h1]
        exact ⟨h2, coeff_eq_zero_of_natDegree_lt (by grind)⟩
      have hm := fun n ↦ (coeff_mul f e n).symm
      simp only [←he, coeff_add, coeff_monomial] at hm
      open And in have hm' := intro (hm 0) (intro (hm 1) (intro (hm 2) (hm 3)))
      simp [Finset.antidiagonal, h2 hf, h2 (hf.of_mul_left (by rw [←he]; exact h1))] at hm'
      ring_nf at hm' ⊢
      exact hm'
    by_cases f₁ = 0
    · right
      use f₀ + a
      grind only
    · left
      use f₀
      grind only

/- A field containing a square root of `-1` and admitting a finite extension which is algebraically
   closed is itself algebraically closed. -/
lemma finite_alg_closure_i [hf : FiniteDimensional F K] (hm : IsSquare (-1 : F)) :
    IsAlgClosed F := by
  open IsGalois Subgroup in
  have := finite_alg_closure_perfect (hf := hf)
  have : IsAlgClosure F K := ⟨Hac, inferInstance⟩
  have h : finrank F K = 1 := by
    by_contra h
    have ⟨p, hp, hd⟩ := exists_prime_and_dvd h
    have := fact_iff.mpr hp
    have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (hd.trans (card_aut_eq_finrank _ _).symm.dvd)
    have hr := (finrank_fixedField_eq_card (zpowers g)).trans ((card_zpowers g).trans hg)
    have hG := isCyclic_of_prime_card ((card_aut_eq_finrank _ K).trans hr)
    have h := ((isCyclic_tfae (fixedField (zpowers g)) K ?_).out 0 1).mp
    · rw [hr] at h
      have ⟨a, h2, _⟩ := h ⟨inferInstance, hG⟩
      have h3 := (X_pow_sub_C_irreducible_iff_of_prime hp).mp h2
      by_cases h1 : p = 2
      · subst h1
        absurd (isSquare_iff_exists_sq a).mp.mt (by aesop)
        refine (quadratic_alg_closure hr.dvd 0 a).elim (by simp) (fun h ↦ ?_)
        have := (hm.map (algebraMap F _)).mul h
        aesop
      · have h := (X_pow_sub_C_irreducible_iff_of_prime_pow hp h1 (n := 2) (by simp)).mpr h3
        have h := h.natDegree_dvd_finrank (Hac.splits _)
        simp [hr, not_pos_pow_dvd hp.one_lt] at h
    rw [hr]
    rcases divisor_by_finrank' _ hr.dvd hp with ⟨z, hz⟩ | hz
    · have := neZero_iff.mpr ((CharP.charP_iff_prime_eq_zero hp).mpr.mt
        (finite_alg_closure_prime hp hr))
      exact ⟨z, (mem_primitiveRoots hp.pos).mpr (isRoot_cyclotomic_iff.mp hz)⟩
    · absurd hz
      simp [natDegree_cyclotomic, totient_prime hp, hp.one_lt]
  have h := equivOfEq (bot_eq_top_iff_finrank_eq_one.mpr h)
  exact Hac.of_ringEquiv _ _ (((botEquiv _ _).symm.trans h).trans topEquiv).symm

/- A field in which `-1` is not a square, but adjoining its square root gives an algebraic
   closure, is real closed. -/
omit Hac in
lemma RealClosed_from_quadratic (h1 : ¬IsSquare (-1 : F)) (h2 : ∃ i : K, i ^ 2 = -1 ∧
    IsAlgClosed F⟮i⟯) : IsRealClosed F := by
  open adjoin IsIntegral minpoly in
  obtain ⟨i, h2a, _⟩ := h2
  have h := natDegree_le_of_dvd (dvd F i (by aesop)) (X_pow_add_C_ne_zero two_pos (1 : F))
  rw [natDegree_X_pow_add_C] at h
  have hi : IsIntegral F i := by apply of_pow two_pos; rw [h2a]; exact isIntegral_one.neg
  have hr : finrank F F⟮i⟯ ∣ 2 := (dvd_prime prime_two).mpr (by grind [finrank hi, natDegree_pos])
  have hssq : ∀ x : F, IsSumSq x → IsSquare x := by
    apply IsSumSq.rec'
    · simp
    · rintro a b ⟨y, rfl⟩ - h
      by_cases h0 : b = 0
      · simp_all
      · contrapose h1
        rw [←neg_div_self h0]
        exact ((quadratic_alg_closure hr y b).resolve_left h1).div h
  have := isSemireal_iff_not_isSumSq_neg_one.mpr ((hssq _).mt h1)
  constructor
  · have := quadratic_alg_closure hr 0
    simp_all
  · intro f _
    exact (divisor_by_finrank' f hr prime_two).resolve_right (by grind)

end Lemmas

/- The Artin-Schreier theorem: a field admitting a finite extension which is algebraically closed
   is either algebraically closed or real closed. -/
public theorem isAlgClosed_or_isRealClosed (F : Type u) (K : Type u) [Field F] [Field K]
    [Algebra F K] [IsAlgClosed K] [FiniteDimensional F K] : IsAlgClosed F ∨ IsRealClosed F := by
  open IntermediateField in
  by_cases hF : IsSquare (-1 : F)
  · left
    exact finite_alg_closure_i hF (K := K)
  · right
    have ⟨i, hi⟩ := ‹IsAlgClosed K›.exists_pow_nat_eq (-1) two_pos
    refine RealClosed_from_quadratic hF ⟨i, ⟨hi, finite_alg_closure_i ?_ (K := K)⟩⟩
    apply (isSquare_iff_exists_sq _).mpr
    symm at hi
    aesop
