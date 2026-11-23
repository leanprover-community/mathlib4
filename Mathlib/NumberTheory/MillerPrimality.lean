/-
Copyright (c) 2026 Zhuoyuan Hao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhuoyuan Hao
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Miller's strong probable-prime test

For an odd composite modulus, all bases that pass the test lie in one proper subgroup of the
units. A nonprincipal Dirichlet character trivial on that subgroup turns a bound on character
witnesses into a bound on the bases needed to detect compositeness.
-/

public section

namespace Nat

/-- For `n - 1 = 2 ^ s * d` with `d` odd, the strong probable-prime test to base `a`
asks whether `a ^ d = 1` or `a ^ (2 ^ r * d) = -1` for some `r < s`, modulo `n`. -/
@[expose] def IsStrongProbablePrime (n a : ℕ) : Prop :=
  (a : ZMod n) ^ (ordCompl[2] (n - 1)) = 1 ∨
    ∃ r < (n - 1).factorization 2, (a : ZMod n) ^ (2 ^ r * ordCompl[2] (n - 1)) = -1

private lemma eq_one_or_exists_pow_eq_neg_one {K : Type*} [Field K] {z : K} {s : ℕ}
    (h : z ^ (2 ^ s) = 1) : z = 1 ∨ ∃ r < s, z ^ (2 ^ r) = -1 := by
  induction s with
  | zero => exact Or.inl (by simpa using h)
  | succ s ih =>
    rw [pow_succ, pow_mul] at h
    rcases sq_eq_one_iff.mp h with h | h
    · exact (ih h).imp_right fun ⟨r, hr, hz⟩ ↦ ⟨r, Nat.lt_succ_of_lt hr, hz⟩
    · exact Or.inr ⟨s, Nat.lt_succ_self s, h⟩

/-- A prime passes the strong probable-prime test to every positive base below it. -/
theorem IsStrongProbablePrime.of_prime {p a : ℕ} (hp : p.Prime) (ha : 0 < a) (hap : a < p) :
    IsStrongProbablePrime p a := by
  let : Fact p.Prime := ⟨hp⟩
  have hne : (a : ZMod p) ≠ 0 := fun hz ↦
    (not_dvd_of_pos_of_lt ha hap) ((ZMod.natCast_eq_zero_iff a p).mp hz)
  have h : ((a : ZMod p) ^ (ordCompl[2] (p - 1))) ^ (ordProj[2] (p - 1)) = 1 := by
    rw [← pow_mul, Nat.mul_comm, ordProj_mul_ordCompl_eq_self]
    exact ZMod.pow_card_sub_one_eq_one hne
  exact (eq_one_or_exists_pow_eq_neg_one h).imp_right fun ⟨r, hr, hz⟩ ↦
    ⟨r, hr, by rwa [Nat.mul_comm, pow_mul]⟩

private lemma pow_eq_one_of_pow_eq_neg_one {R : Type*} [CommRing R] {z : R} {r t d : ℕ}
    (hrt : r < t) (h : z ^ (2 ^ r * d) = -1) : z ^ (2 ^ t * d) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hrt
  rw [pow_add, pow_succ, show 2 ^ r * 2 * 2 ^ k * d = (2 ^ r * d * 2) * 2 ^ k by ring,
    pow_mul, pow_mul, h]
  simp

/-- A base that passes Miller's test satisfies the Fermat congruence. -/
theorem IsStrongProbablePrime.pow_sub_one_eq_one {n a : ℕ} (h : IsStrongProbablePrime n a) :
    (a : ZMod n) ^ (n - 1) = 1 := by
  conv_lhs => rhs; rw [← ordProj_mul_ordCompl_eq_self (n - 1) 2]
  rcases h with h | ⟨r, hr, h⟩
  · rw [Nat.mul_comm, pow_mul, h, one_pow]
  · exact pow_eq_one_of_pow_eq_neg_one hr h

/-- For `2 < n`, a base that passes Miller's test is a unit modulo `n`. -/
theorem IsStrongProbablePrime.isUnit {n a : ℕ} (h : IsStrongProbablePrime n a) (hn : 2 < n) :
    IsUnit (a : ZMod n) :=
  IsUnit.of_pow_eq_one h.pow_sub_one_eq_one (by omega)

/-- The units whose `e`th power is one of the two signs. -/
private def signSubgroup (n e : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {u | u ^ e = 1 ∨ u ^ e = -1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change x ^ e = 1 ∨ x ^ e = -1 at hx
    change y ^ e = 1 ∨ y ^ e = -1 at hy
    change (x * y) ^ e = 1 ∨ (x * y) ^ e = -1
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [mul_pow, hx, hy]
  inv_mem' := by
    intro x hx
    change x ^ e = 1 ∨ x ^ e = -1 at hx
    change (x⁻¹) ^ e = 1 ∨ (x⁻¹) ^ e = -1
    rcases hx with hx | hx <;> simp [inv_pow, hx]

/-- CRT splices the first component of a negative witness with 1 in the
second component. Its power has mixed signs and leaves the diagonal. -/
private lemma signSubgroup_ne_top {p q e : ℕ} (hp : 2 < p) (hq : 2 < q)
    (hc : p.Coprime q) (w : (ZMod (p * q))ˣ) (hw : w ^ e = -1) :
    signSubgroup (p * q) e ≠ ⊤ := by
  let E := ZMod.chineseRemainder hc
  let y : ZMod p × ZMod q := ((E (w : ZMod (p * q))).1, 1)
  have hunit : IsUnit y := Prod.isUnit_iff.mpr
    ⟨(w.isUnit.map E.toMonoidHom).map (MonoidHom.fst _ _), isUnit_one⟩
  let v := (hunit.map E.symm.toMonoidHom).unit
  have hv : E (v : ZMod (p * q)) = y := by
    change E (E.symm y) = y
    exact E.apply_symm_apply _
  have hfirst : (E (w : ZMod (p * q))).1 ^ e = -1 := by
    simpa using congrArg (fun u : (ZMod (p * q))ˣ ↦ (E u).1) hw
  intro hall
  have hvH : v ∈ signSubgroup (p * q) e := hall ▸ Subgroup.mem_top v
  rcases hvH with h | h
  · have bad : (-1 : ZMod p) = 1 := by
      simpa [hv, y, hfirst] using congrArg (fun u : (ZMod (p * q))ˣ ↦ (E u).1) h
    rcases ZMod.neg_one_eq_one_iff.mp bad with h | h <;> omega
  · have bad : (1 : ZMod q) = -1 := by
      simpa [hv, y] using congrArg (fun u : (ZMod (p * q))ˣ ↦ (E u).2) h
    rcases ZMod.neg_one_eq_one_iff.mp bad.symm with h | h <;> omega

private lemma exists_coprime_factors {n : ℕ} (h : n.IsCarmichael) (hodd : Odd n) :
    ∃ p q, n = p * q ∧ 2 < p ∧ 2 < q ∧ p.Coprime q := by
  have hn := h.two_lt
  obtain ⟨q, hq⟩ := n.minFac_dvd
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have hpLt := (Nat.not_prime_iff_minFac_lt (by omega)).mp h.not_prime
  have hpodd := hodd.of_dvd_nat n.minFac_dvd
  have hqodd := hodd.of_dvd_nat (show q ∣ n by rw [hq]; exact dvd_mul_left _ _)
  have hq1 : q ≠ 1 := by intro h1; simp [h1] at hq; omega
  have hp2 := hp.two_le
  obtain ⟨x, hx⟩ := hpodd
  obtain ⟨y, hy⟩ := hqodd
  exact ⟨n.minFac, q, hq, by omega, by omega, Nat.coprime_of_squarefree_mul (hq ▸ h.squarefree)⟩

/-- For an odd composite modulus greater than two, all units passing Miller's test belong
to a single proper subgroup. -/
theorem exists_proper_subgroup_isStrongProbablePrime {n : ℕ} (hn : 2 < n) (hodd : Odd n)
    (hc : ¬ n.Prime) : ∃ H : Subgroup (ZMod n)ˣ, H < ⊤ ∧
      ∀ (a : ℕ) (u : (ZMod n)ˣ), (u : ZMod n) = (a : ZMod n) →
        IsStrongProbablePrime n a → u ∈ H := by
  classical
  let F := (powMonoidHom (α := (ZMod n)ˣ) (n - 1)).ker
  by_cases hF : F = ⊤
  · have hC : n.IsCarmichael := by
      refine ⟨hn, hc, fun b hb ↦ ?_⟩
      have hb0 : b ≠ 0 := by rintro rfl; simp at hb; omega
      apply (Nat.probablePrime_iff_zmod_one n hb0).mpr
      have H : ZMod.unitOfCoprime b hb ∈ F := by rw [hF]; trivial
      change (ZMod.unitOfCoprime b hb) ^ (n - 1) = 1 at H
      simpa [ZMod.coe_unitOfCoprime] using
        congrArg (fun z : (ZMod n)ˣ ↦ (z : ZMod n)) H
    obtain ⟨p, q, hpq, hp, hq, hco⟩ := exists_coprime_factors hC hodd
    subst n
    let N := p * q
    let s := (N - 1).factorization 2
    let d := ordCompl[2] (N - 1)
    -- Choose the last squaring stage at which any unit can reach minus one.
    let P := fun t : ℕ ↦ ∃ w : (ZMod N)ˣ, w ^ (2 ^ t * d) = -1
    have hd : Odd d := Nat.not_even_iff_odd.mp
      fun h ↦ Nat.not_dvd_ordCompl Nat.prime_two (show N - 1 ≠ 0 by dsimp [N]; omega) h.two_dvd
    have h0 : P 0 := ⟨-1, by simp [hd.neg_one_pow]⟩
    let t := Nat.findGreatest P s
    obtain ⟨w, hw⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le s) h0
    refine ⟨signSubgroup N (2 ^ t * d), (signSubgroup_ne_top hp hq hco w hw).lt_top, ?_⟩
    intro a u hu ha
    change u ^ (2 ^ t * d) = 1 ∨ u ^ (2 ^ t * d) = -1
    rcases ha with h | ⟨r, hr, h⟩
    · left
      apply Units.ext
      change (u : ZMod N) ^ (2 ^ t * d) = 1
      rw [hu, Nat.mul_comm (2 ^ t) d, pow_mul]
      change (a : ZMod N) ^ d = 1 at h
      rw [h, one_pow]
    · have huR : u ^ (2 ^ r * d) = -1 := by
        apply Units.ext
        change (u : ZMod N) ^ (2 ^ r * d) = -1
        rwa [hu]
      have hle : r ≤ t := Nat.le_findGreatest (P := P) (le_of_lt hr) ⟨u, huR⟩
      rcases lt_or_eq_of_le hle with hlt | he
      · left
        apply Units.ext
        change (u : ZMod N) ^ (2 ^ t * d) = 1
        rw [hu]; exact pow_eq_one_of_pow_eq_neg_one hlt h
      · right; rwa [← he]
  · refine ⟨F, Ne.lt_top hF, ?_⟩
    intro a u hu ha
    change u ^ (n - 1) = 1
    apply Units.ext
    change (u : ZMod n) ^ (n - 1) = 1
    rw [hu]; exact ha.pow_sub_one_eq_one

private theorem character_of_proper_subgroup {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ) (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ n, χ ≠ 1 ∧ ∀ u ∈ H, χ u = 1 := by
  classical
  let e := MulChar.subgroupOrderIsoSubgroupMulChar (ZMod n) ℂ
  have hne : (e H).ofDual ≠ ⊥ := by
    intro hb
    apply hH
    apply e.injective
    rw [e.map_top]
    exact hb
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨x.val, fun h ↦ hx (Subtype.ext h),
    MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp x.property⟩

/-- If every nonprincipal character modulo `n` has a witness at most `B` among the positive
bases below `n`, Miller's test on those bases detects primality. -/
theorem prime_iff_forall_isStrongProbablePrime_of_dirichletCharacter_witness {n B : ℕ}
    (hn : 2 < n) (hodd : Odd n) (hw : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
      ∃ a : ℕ, 1 ≤ a ∧ a < n ∧ a ≤ B ∧ χ (a : ZMod n) ≠ 1) :
    n.Prime ↔ ∀ a, 1 ≤ a → a < n → a ≤ B → IsStrongProbablePrime n a := by
  refine ⟨fun hp a ha han _ ↦ IsStrongProbablePrime.of_prime hp ha han, fun tests ↦ ?_⟩
  by_contra hc
  let : NeZero n := ⟨by omega⟩
  obtain ⟨H, hH, hmem⟩ := exists_proper_subgroup_isStrongProbablePrime hn hodd hc
  obtain ⟨χ, hχ, htriv⟩ := character_of_proper_subgroup H hH.ne
  obtain ⟨a, ha, han, hB, hw⟩ := hw χ hχ
  have hpass := tests a ha han hB
  obtain ⟨u, hu⟩ := hpass.isUnit hn
  exact hw (hu ▸ htriv u (hmem a u hu hpass))

end Nat
