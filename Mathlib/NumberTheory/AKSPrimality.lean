/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Interval.Set.Nat
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
/-!
# Existence of a polynomially bounded runtime primality testing algorithm

In 2002 Agrawal, Kayal and Saxena have proven the existence of a polynomially bounded
primality testing algorithm.

The goal of this file is to show the existence of a simultaneously general, polynomial-time,
deterministic and unconditionally correct primality test.

- The primality test is general as it works for any number given, unlike specialized tests
  that work for only a subset of numbers (e.g Mersenne numbers or Fermat numbers).
- The algorithm runtime complexity is polynomially bounded by the number of digits.
- The runtime is deterministic, as opposed probabilistic tests such as Miller-Rabin.
  If the algorithm returns prime, the number is prime.
  If the algorithm returns composite, the number is composite.
- The algorithm is unconditionally correct as it does not depend on any unproven hypotheses.

## References

<https://en.wikipedia.org/wiki/AKS_primality_test>
The proof reference is <https://www3.nd.edu/~andyp/notes/AKS.pdf>.
The paper by the original authors is
<https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf>.

## Main Theorems

- `is_prime_pow_of_quotient_of_ideal_span_of_primitive_root_generator_polynomial` this is the AKS
  Primality test. If `(X + a) ^ n = X ^ n + a` modulo `(ZMod n)[X] / X ^ r - 1` and some other
  minor conditions hold, then `n` is a prime power. The coefficients `a` are polynomially bounded
  in the digit size of `n`.

## Tags

prime number, polynomial prime number test, AKS, Agrawal-Kayal-Saxena
-/

open Polynomial Finset Nat

namespace AKS

section Introspective

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The introspective relation, named by the original authors, only used for the construction of the
final theorem, and thus made private. -/
def introspective (f : K[X]) (n : ℕ) (r : ℕ) [NeZero r] : Prop :=
  ∀ μ ∈ (primitiveRoots r K), f.eval (μ ^ n) = f.eval μ ^ n

variable {r : ℕ} [NeZero r]

theorem introspective_eq {μ : K} {f : K[X]} {n : ℕ} (h : IsPrimitiveRoot μ r)
    (hi : introspective f n r) : f.eval (μ ^ n) = f.eval μ ^ n := by
  haveI : r ≠ 0 := NeZero.out
  exact hi μ ((mem_primitiveRoots (by lia)).mpr h)

theorem introspective_one {f : K[X]} : introspective f 1 r := by
  grind [introspective]

theorem introspective_p {p a : ℕ} [Fact p.Prime] [ExpChar K p] :
    introspective (X - C (a : K)) p r := by
  intro μ hμ
  simp only [eval_sub, eval_X, eval_C]
  change (frobenius K p) μ - _ = (frobenius K p) (μ - a)
  simp

theorem introspective_n_div_p {p a n : ℕ} [Fact p.Prime] [ExpChar K p]
    (h : introspective (X - C (a : K)) n r) (hd : p ∣ n) (hc : p.Coprime r) :
    introspective (X - C (a : K)) (n / p) r := by
  simp only [map_natCast, introspective] at ⊢ h
  intro μ hμ
  have h2 : p * (n / p) = n := Nat.mul_div_cancel' hd
  simp only [eval_sub, eval_X, eval_natCast] at h ⊢
  let π := IsPrimitiveRoot.primitiveRootsPowEquivOfCoprime (R := K) hc
  replace h := h (π.symm ⟨μ, hμ⟩) (by grind)
  have _ : π (π.symm ⟨μ, hμ⟩) = μ := by simp
  revert h
  refine (Eq.congr ?_ ?_).mp
  · nth_rw 1 [sub_left_inj, ← h2, pow_mul]
    congr
  · nth_rw 1 [← h2, pow_mul]
    congr
    change (frobenius K p) _ = _
    simp only [map_sub]
    congr
    simp

/-- The product of two polynomials is introspective. -/
theorem introspective_mul_poly {n : ℕ} {f g : K[X]} (hf : introspective f n r)
    (hg : introspective g n r) : introspective (f * g) n r := by
  intro μ hm
  simp only [eval_mul, hf μ hm, hg μ hm]
  ring

/-- The product of coprime exponents is introspective. -/
theorem introspective_mul_of_coprime {d e : ℕ} {f : K[X]} (hf : introspective f e r)
    (hg : introspective f d r) (h : e.Coprime r) : introspective f (e * d) r := by
  intro μ hm
  have mu : μ ^ e ∈ primitiveRoots r K := by
    have hl : 0 < r := pos_of_neZero r
    simp only [mem_primitiveRoots hl] at ⊢ hm
    exact IsPrimitiveRoot.pow_of_coprime hm e h
  rw [pow_mul, hg (μ ^ e) mu, hf μ hm]
  ring

/-- Necessary condition for the auxilliary proof. -/
theorem introspective_of_multiset {p n b : ℕ} [Fact p.Prime] [ExpChar K p] (d e : ℕ)
    (s : Multiset (Fin b)) (hs : ∀ x : Fin b, introspective (ofMultiset {(x.val : K)}) n r)
    (hcprm : n.Coprime r) (hdiv : p ∣ n) :
    (introspective (ofMultiset (s.map fun x ↦ (x.val : K))) (p ^ d * (n / p) ^ e) r) := by
  simp only [ofMultiset_apply]
  have hcprm2 := Coprime.coprime_mul_right (Eq.symm (Nat.mul_div_cancel' hdiv) ▸ hcprm)
  induction s using Multiset.induction_on with
  | empty => simp [introspective]
  | cons x l h1 =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine introspective_mul_poly ?_ h1
    clear h1
    refine introspective_mul_of_coprime ?_ ?_ ?_
    · induction d with
      | zero => simp [introspective_one]
      | succ i hi =>
        simp only [map_natCast, pow_succ, mul_comm]
        exact introspective_mul_of_coprime introspective_p hi hcprm2
    · induction e with
      | zero => simp [introspective_one]
      | succ i hi =>
        simp only [pow_succ, mul_comm]
        refine introspective_mul_of_coprime ?_ hi ?_
        · have hsx := hs x
          simp only [ofMultiset_apply, Multiset.map_singleton, Multiset.prod_singleton] at hsx
          exact introspective_n_div_p hsx hdiv hcprm2
        · exact Coprime.coprime_div_left hcprm hdiv
    · exact Coprime.pow_left d hcprm2

end Introspective

section Rest

variable {K : Type*} [CommRing K] [IsDomain K]

/-- Helper structure to bundle hypotheses. -/
structure Conditions (r p n a q : ℕ) (μ : K) [Fact p.Prime] [ExpChar K p]
    [CharP K p] [NeZero r] where
  n_coprime_r : n.Coprime r
  n_ge_3 : 3 ≤ n
  a_def : a = ⌊(√(φ r) * (Real.logb 2 n))⌋₊
  nlogb_lt_od : (Real.logb 2 n) ^ 2 < orderOf (n : ZMod r)
  icc_coprime: ∀ y ∈ Icc 1 a, n.Coprime y
  icc_introspective: ∀ y : Icc 0 a, introspective ((X : K[X]) - C (y : K)) n r
  is_primitive_root : IsPrimitiveRoot μ r
  p_prime : p.Prime
  q_prime : q.Prime
  p_dvd_n : p ∣ n
  q_dvd_n : q ∣ n
  p_ne_q : p ≠ q

variable {p n a q : ℕ} {μ : K} [Fact p.Prime] [CharP K p] [ExpChar K p]

variable {r : ℕ} [NeZero r]

/-- Function used in the AKS proof. -/
def f (_ : Conditions r p n a q μ) : ℕ × ℕ → ℕ := fun x : ℕ × ℕ ↦ p ^ x.1 * (n / p) ^ x.2

/-- Set used in the AKS proof. -/
def se1 (h : Conditions r p n a q μ) := f h '' Set.univ

/-- Set used in the AKS proof. -/
def se2 (h : Conditions r p n a q μ) := (Nat.cast (R := ZMod r)) '' se1 h

/-- Set used in the AKS proof, subset of `se1` -/
def se3 (h : Conditions r p n a q μ) :=
  f h '' Set.Icc 0 ⌊√(se2 h).ncard⌋₊ ×ˢ Set.Icc 0 ⌊√(se2 h).ncard⌋₊

theorem se3_subset_se1 (h : Conditions r p n a q μ) : se3 h ⊆ se1 h := by
  grind [se3, se1]

/-- Function used in the AKS proof. -/
noncomputable def sp1 (_ : Conditions r p n a q μ) :=
  fun s : Multiset (Fin (a + 1)) ↦ ofMultiset (s.map (fun x ↦ (x.val : K)))

/-- Set used in the AKS proof. -/
def sp2 (h : Conditions r p n a q μ) := (sp1 h '' Set.univ).image (eval μ ·)

theorem se2_ncard_ne_zero (h : Conditions r p n a q μ) : (se2 h).ncard ≠ 0 := by
  have h1 : 1 ∈ se2 h := by
    unfold se2 se1 f
    simp only [Set.image_univ, Set.mem_image, Set.mem_range, Prod.exists,
      exists_exists_exists_and_eq, cast_mul, cast_pow]
    use 0, 0
    simp
  exact Set.ncard_ne_zero_of_mem h1

/-- All relevant exponents and polynomials are introspective. -/
theorem forall_in_se1_in_image_sp1_introspective (h : Conditions r p n a q μ) :
    ∀ e ∈ se1 h, ∀ f ∈ sp1 h '' Set.univ, introspective f e r := by
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  intro e he f hf
  simp only [Set.image_univ, Set.mem_range] at hf
  obtain ⟨s , hs⟩ := hf
  rw [← hs]
  simp only [se1, Set.image_univ, Set.mem_range, Prod.exists] at he
  obtain ⟨i, j, heq⟩ := he
  rw [← heq]
  refine introspective_of_multiset (p := p) (K := K) (r := r) i j s ?_ n_coprime_r p_dvd_n
  intro ⟨m, hm⟩
  replace heq := icc_introspective ⟨m, (by grind)⟩
  simp only [map_natCast, ofMultiset_apply, Multiset.map_singleton,
    Multiset.prod_singleton] at heq ⊢
  exact heq

theorem se2_subset_units (h : Conditions r p n a q μ) :
    se2 h ⊆ (fun x : (ZMod r)ˣ ↦ x.val) '' Set.univ := by
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  intro x hx
  simp only [Set.image_univ, Set.mem_range]
  have hu : IsUnit x := by
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime x.val r]
    unfold se2 se1 f at hx
    simp only [Set.image_univ, Set.mem_image, Set.mem_range, Prod.exists,
      exists_exists_exists_and_eq, cast_mul, cast_pow] at hx
    obtain ⟨a, b, hx⟩ := hx
    norm_cast at hx
    rw [← hx, ZMod.val_natCast, ZMod.coprime_mod_iff_coprime]
    refine Coprime.mul_left ?_ ?_
    · exact Coprime.pow_left _ (Coprime.of_dvd_left p_dvd_n n_coprime_r)
    · exact Coprime.pow_left _ (Coprime.of_dvd_left (div_dvd_of_dvd p_dvd_n) n_coprime_r)
  exact ⟨hu.unit, rfl⟩

theorem injective_f (h : Conditions r p n a q μ) : (f h).Injective := by
  unfold f
  intro ⟨d₁, d₂⟩ ⟨e₁, e₂⟩ heq
  by_contra! hcon
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  have hn : 0 < n := by lia
  have hpn0 := Nat.Prime.ne_zero p_prime
  have _ : n / p ≠ 0 := by grind [Nat.div_ne_zero_iff, Nat.le_of_dvd hn p_dvd_n]
  have hne0_1 : p ^ d₁ ≠ 0 := by grind [pow_ne_zero]
  have hne0_2 : (n / p) ^ d₂ ≠ 0 := by grind [pow_ne_zero]
  have hne0_3 : p ^ e₁ ≠ 0 := by grind [pow_ne_zero]
  have hne0_4 : (n / p) ^ e₂ ≠ 0 := by grind [pow_ne_zero]
  have nd : ¬ q ∣ p := fun x ↦ p_ne_q.symm <| (prime_dvd_prime_iff_eq q_prime p_prime).mp x
  have _ : p.factorization p ≠ 0 := by grind [Prime.factorization_self]
  have _ : (n / p).factorization q ≠ 0 := by
    simp only [ne_eq, factorization_eq_zero_iff, Nat.div_eq_zero_iff, not_or, Decidable.not_not,
      not_lt]
    refine ⟨q_prime, ⟨?_ ,⟨Nat.Prime.ne_zero p_prime, le_of_dvd hn p_dvd_n⟩⟩⟩
    apply dvd_div_of_mul_dvd
    exact Prime.dvd_mul_of_dvd_ne p_ne_q p_prime q_prime p_dvd_n q_dvd_n
  have hf := congrArg factorization heq
  rw [factorization_mul hne0_1 hne0_2, factorization_mul hne0_3 hne0_4] at hf
  by_cases hc : d₂ = e₂ ∧ d₁ ≠ e₁
  · rw [hc.1, add_left_inj] at hf
    replace hp := DFunLike.congr_fun hf p
    simp only [factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_eq_mul_right_iff] at hp
    grind
  · simp only [ne_eq, not_and, Decidable.not_not] at hc
    have hc2 : d₂ ≠ e₂ := by grind
    replace hf := DFunLike.congr_fun hf q
    have hpf : p.factorization q = 0 := by grind [factorization_eq_zero_iff]
    have _ : (n / p).factorization q = 0 := by
      simp only [factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Pi.add_apply,
        Pi.mul_apply, Pi.natCast_apply, cast_id, hpf, mul_zero, zero_add, mul_eq_mul_right_iff, hc2,
        false_or] at hf
      exact hf
    grind

theorem injective_sp1 (h : Conditions r p n a q μ) : (sp1 h).Injective := by
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  have _ := Nat.Prime.ne_zero p_prime
  intro x y heq
  have hi := ofMultiset_injective (R := K) heq
  contrapose! hi
  suffices (fun x : Fin (a + 1) ↦ (x.val : K)).Injective by grind [Multiset.map_injective]
  intro x2 y2 hxy
  have hm (z : Fin (a + 1)) : z.val ∈ Set.Iio p := by
    obtain ⟨z, hz⟩ := z
    simp only [Set.mem_Iio]
    by_contra! hcon
    exact @not_coprime_of_dvd_of_dvd p n p (Prime.one_lt p_prime)
      ((ModEq.dvd_iff rfl p_dvd_n).mp p_dvd_n) (dvd_refl p) (icc_coprime p (by grind))
  grind [(CharP.natCast_injOn_Iio K p) (hm x2) (hm y2)]

theorem se2_lt_se3 (h : Conditions r p n a q μ) : (se2 h).ncard < (se3 h).ncard := by
  unfold se3
  rw [Set.ncard_image_of_injective _ (injective_f h), Set.ncard_prod, ← sq,
    Set.ncard_Icc_nat, Nat.sub_zero]
  rify
  have hs : (se2 h).ncard = √(se2 h).ncard ^ 2 := by grind [Real.sq_sqrt, cast_nonneg']
  rw [hs, sq_lt_sq]
  simp only [cast_nonneg', Real.sq_sqrt, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact Real.real_sqrt_lt_nat_sqrt_succ

theorem le_pow_floor_sqrt_se2 {h : Conditions r p n a q μ} {x : ℕ} (hx : x ∈ (se3 h)) :
    x ≤ n ^ ⌊√(se2 h).ncard⌋₊ := by
  unfold se3 f at hx
  simp only [Set.Icc_prod_Icc, Set.mem_image, Set.mem_Icc,
    Prod.exists, Prod.mk_le_mk, _root_.zero_le, and_self, true_and] at hx
  obtain ⟨a, b, ⟨ha, hb⟩, heq⟩ := hx
  rw [← heq]
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  have hn : 0 < n := by lia
  have hppos := (Nat.ne_zero_iff_zero_lt.mp (Nat.Prime.ne_zero p_prime))
  have hnppos : 0 < (n / p)  := by grind [Nat.div_ne_zero_iff, Nat.le_of_dvd hn p_dvd_n]
  calc
    _ ≤ p ^ ⌊√↑(se2 h).ncard⌋₊ * (n / p) ^ ⌊√↑(se2 h).ncard⌋₊ :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hppos ha) (Nat.pow_le_pow_right hnppos hb)
    _ = _ := by rw [← mul_pow, mul_div_eq_iff_dvd.mpr p_dvd_n]

theorem natDegree_eq (h : Conditions r p n a q μ) (s : Multiset (Fin (a + 1))) :
    (sp1 h s).natDegree ≤ s.card := by
  unfold sp1
  simp only [ofMultiset_apply, Multiset.map_map, Function.comp_apply]
  calc
    _ ≤ _ := natDegree_multiset_prod_le _
    _ ≤ _ := by simp [-map_natCast]

/-- Here we use the assumption that `p` is not a prime power. -/
theorem aux_le (h : Conditions r p n a q μ) :
    (sp2 h).ncard ≤ (n : ℝ) ^ (√(se2 h).ncard) ∧ (sp2 h).Finite := by
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  have hm : ∀ a ∈ se3 h, ↑a ∈ se2 h := by
    unfold se3 se2 se1
    intro b _
    have _ : b ∈ f h '' Set.univ := by
      revert b
      exact Set.image_mono (by grind)
    grind
  obtain ⟨x, hx, y, hy, ⟨hne, heq⟩⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to (se2_lt_se3 h) hm
  have hn0 : (X : K[X]) ^ x - X ^ y ≠ 0 := by
    rw [← coeffs_nonempty_iff]
    have _ : ((X : K[X]) ^ x - X ^ y).coeff x ≠ 0 := by
      suffices _ : ((X : K[X]) ^ x - X ^ y).coeff x = 1 by
        grind [(NeZero.of_not_dvd K (n := 1) (Nat.Prime.not_dvd_one p_prime)).out]
      simpa
    grind [coeff_mem_coeffs]
  have hf := finite_setOf_isRoot hn0
  have hss : (sp2 h) ⊆ {z | ((X : K[X]) ^ x - X ^ y).IsRoot z} := by
    simp only [Set.image_univ, IsRoot.def, Set.image_subset_iff, Set.preimage_setOf_eq, sp2]
    intro o ho
    simp only [eval_sub, eval_pow, eval_X, Set.mem_setOf_eq, sub_eq_zero]
    have ho : o ∈ sp1 h '' Set.univ := by grind
    have hi1 := forall_in_se1_in_image_sp1_introspective h x (by grind [se3_subset_se1]) o ho
    have hi2 := forall_in_se1_in_image_sp1_introspective h y (by grind [se3_subset_se1]) o ho
    rw [← introspective_eq is_primitive_root hi1, ← introspective_eq is_primitive_root hi2]
    suffices μ ^ x = μ ^ y by rw [this]
    replace heq : x ≡ y [MOD r] := by rw [← ZMod.natCast_eq_natCast_iff x y r, heq]
    exact pow_eq_pow_of_modEq heq is_primitive_root.pow_eq_one
  refine ⟨?_, Set.Finite.subset hf hss⟩
  suffices (sp2 h).ncard ≤ n ^ ⌊√(se2 h).ncard⌋₊ by
    rify at this
    apply le_trans this
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (x := n) (by norm_cast; grind)
    exact floor_le (Real.sqrt_nonneg ↑(se2 h).ncard)
  have hrs : (sp2 h).ncard  ≤ (((X : K[X]) ^ x - X ^ y).rootSet K).ncard := by
    suffices {z | ((X : K[X]) ^ x - X ^ y).IsRoot z} = (((X : K[X]) ^ x - X ^ y).rootSet K) by
      rw [← this]
      rw [← Set.finite_coe_iff] at hf
      exact Set.ncard_le_ncard hss
    ext z
    simp [mem_rootSet, hn0]
  calc
    _ ≤ _ := hrs
    _ ≤ _ := ncard_rootSet_le ((X : K[X]) ^ x - X ^ y) K
    _ ≤ _ := natDegree_sub_le (X ^ x) (X ^ y)
    _ ≤ max x y := by
      repeat rw [← monomial_one_right_eq_X_pow]
      rw [natDegree_monomial_eq x (one_ne_zero' K), natDegree_monomial_eq y (one_ne_zero' K)]
    _ ≤ _ := max_le (le_pow_floor_sqrt_se2 hx) (le_pow_floor_sqrt_se2 hy)

theorem se2_choose_le_sp2 (h : Conditions r p n a q μ) :
    ((se2 h).ncard + a).choose ((se2 h).ncard - 1) ≤ (sp2 h).ncard := by
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  have hsinj : Set.InjOn (eval μ ·) (sp1 h '' {x | x.card ≤ (se2 h).ncard - 1}) := by
    intro f hf g hg heq
    by_contra! hcon
    simp only [Set.mem_image, Set.mem_setOf_eq] at hf hg heq
    obtain ⟨hf, hf1, hf2⟩ := hf
    obtain ⟨hg, hg1, hg2⟩ := hg
    have hk : max f.natDegree g.natDegree ≤ (se2 h).ncard - 1 := by
      grind [natDegree_eq h hf, natDegree_eq h hg]
    refine and_not_self (a := (f - g).roots.card ≤ (se2 h).ncard - 1) ⟨?_, ?_⟩
    · calc
        _ ≤ _ := card_roots' (f - g)
        _ ≤ _ := natDegree_sub_le f g
        _ ≤ _ := hk
    · simp only [not_le, lt_iff_add_one_le, sub_one_add_one (se2_ncard_ne_zero h)]
      have fs : (se2 h).Finite := by
        have ss : Set.univ.Finite (α := (ZMod r)) := by
          rw [Set.univ_finite_iff_nonempty_fintype]
          exact ⟨inferInstance⟩
        grind [Set.Finite.subset]
      let emb := Function.Embedding.mk (fun a : ZMod r ↦ μ ^ a.val) (by
        intro b c hbc
        simp only at hbc
        apply ZMod.val_injective
        refine IsPrimitiveRoot.pow_inj is_primitive_root (by grind) (by grind) hbc)
      let ss := fs.toFinset.map emb
      have hd : ∀ s ∈ ss, eval s (f - g) = 0 := by
        intro s hs
        simp only [emb, mem_map, Set.Finite.mem_toFinset, Function.Embedding.coeFn_mk, ss] at hs
        rw [eval_sub, sub_eq_iff_eq_add, zero_add]
        obtain ⟨m, hm, hs⟩ := hs
        simp only [se2, Set.mem_image] at hm
        obtain ⟨e, ⟨he1, he2⟩⟩ := hm
        have ht : μ ^ (e : (ZMod r)).val = μ ^ e := by
          refine pow_eq_pow_of_modEq ?_ is_primitive_root.pow_eq_one
          simp [ModEq]
        have hif := (forall_in_se1_in_image_sp1_introspective h) e he1 (sp1 h hf) (by grind)
        have hig := (forall_in_se1_in_image_sp1_introspective h) e he1 (sp1 h hg) (by grind)
        rw [← hs, ← hf2, ← hg2, ← he2, ht, introspective_eq is_primitive_root hif,
          introspective_eq is_primitive_root hig]
        grind
      have hs : (f - g).natDegree ≤ #ss := by
        simp only [ss, Finset.card_map, ← Set.ncard_eq_toFinset_card]
        grind [natDegree_sub_le]
      have hn := roots_eq_of_natDegree_le_card_of_ne_zero hd hs (by grind)
      simp [hn, ss, ← Set.ncard_eq_toFinset_card]
  rw [sp2]
  refine le_trans (b := ((eval μ ·) '' (sp1 h '' {x | x.card ≤ (se2 h).ncard - 1}
    )).ncard) ?_ (Set.ncard_le_ncard (by grind) (aux_le h).2)
  rw [hsinj.ncard_image , Set.ncard_image_of_injective _ (injective_sp1 h)]
  apply le_of_eq
  have hsiccf := Set.finite_Icc 0 ((se2 h).ncard - 1)
  have key1 : ∀ i ∈ Set.Icc 0 ((se2 h).ncard - 1),
      ((fun y ↦ {x : Multiset (Fin (a + 1)) | x.card = y}) i).Finite := by
    intro z _
    exact Finite.of_equiv (Sym (Fin (a + 1)) z) (Equiv.cast rfl)
  have key2 : (Set.Icc 0 ((se2 h).ncard - 1)).PairwiseDisjoint
      fun y ↦ {x : Multiset (Fin (a + 1)) | x.card = y} := by
    intro x hx y hy hne
    grind
  have key := Set.Finite.ncard_biUnion
      (s := fun y ↦ {x : Multiset (Fin (a+1)) | x.card = y}) hsiccf key1 key2
  symm
  revert key
  refine (Eq.congr ?_ ?_).mp
  · congr
    ext z
    simp
  · nth_rw 3 [← Nat.sub_one_add_one (se2_ncard_ne_zero h)]
    rw [add_assoc, add_comm 1 a, add_comm _ (a + 1), ← choose_symm_add]
    rw [add_comm (a + 1) _, ← sum_range_multichoose]
    have dd := finsum_mem_eq_finite_toFinset_sum (s := Set.Icc 0 ((se2 h).ncard - 1))
        (fun i ↦ {x : Multiset (Fin (a + 1)) | x.card = i}.ncard) hsiccf
    simp only [dd, range_succ_eq_Icc_zero, Set.toFinite_toFinset, Set.toFinset_Icc]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [mem_Icc, _root_.zero_le, true_and] at hz
    rw [← Sym.card_sym_fin_eq_multichoose, Fintype.card, ← Set.ncard_coe_finset]
    apply Set.ncard_congr'
    exact Equiv.mk (fun x ↦ ⟨Sym.mk x.1 x.2, by simp⟩) (fun x ↦ ⟨x , by simp⟩)
      (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem pow_2_le_choose {x : ℕ} (h : 2 ≤ x) : 2 ^ (x + 1) < (2 * x + 1).choose x := by
  have _ : Nat.choose 5 2 = 10 := rfl
  induction x, h using Nat.le_induction (m := 2)
  · grind
  · grind [choose_le_succ, choose_le_middle]

theorem not_aux_le (h : Conditions r p n a q μ) :
    (n : ℝ) ^ (√(se2 h).ncard) < (sp2 h).ncard := by
  obtain ⟨n_coprime_r, n_ge_3, a_def, nlogb_lt_od, icc_coprime, icc_introspective,
    is_primitive_root, p_prime, q_prime, p_dvd_n, q_dvd_n, p_ne_q⟩ := id h
  have _ : NeZero n := .mk (by lia)
  have h1 := Real.rpow_logb (b := 2) (x := n) (by grind) (by grind) (by norm_cast; grind)
  rw [← h1, ← Real.rpow_mul (by grind)]
  set e := (se2 h).ncard
  have henz : e ≠ 0 := se2_ncard_ne_zero h
  replace h1 := lt_floor_add_one (Real.logb 2 n * √e)
  replace h1 := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by grind)).mpr h1
  have h3 : (Real.logb 2 n) ^ 2 < e := by
    apply lt_of_lt_of_le nlogb_lt_od
    norm_cast
    have injon := (pow_injOn_Iio_orderOf (x := (n : (ZMod r)))).ncard_image
    simp only [Set.ncard_Iio_nat] at injon
    rw [← injon]
    unfold e
    refine Set.ncard_le_ncard ?_ (Set.toFinite (se2 h))
    intro y ⟨z, _, hz⟩
    simp only at hz
    rw [← hz]
    unfold se2 se1 f
    simp only [Set.image_univ, Set.mem_image, Set.mem_range, Prod.exists,
      exists_exists_exists_and_eq, cast_mul, cast_pow]
    use z, z
    norm_cast
    have he : p ^ z * (n / p) ^ z = n ^ z := by
      nth_rw 2 [← Nat.mul_div_cancel' p_dvd_n]
      ring
    rw [he]
  apply lt_trans h1
  norm_cast
  have logb_pos : 0 < Real.logb 2 n := Real.logb_pos (by grind) (by norm_num; grind)
  replace h1 : 2 ≤ ⌊Real.logb 2 n * √e⌋₊ := by
    apply le_floor
    suffices 2 ≤ (Real.logb 2 n) ^ 2 by
      grind [(le_trans this), sq, mul_le_mul_iff_of_pos_left logb_pos, Real.le_sqrt' logb_pos]
    suffices 3 / 2 ≤ Real.logb 2 n by
      calc
        (2 : ℝ) ≤ (3 / 2) ^ 2 := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) this 2
    apply (div_le_iff₀ (by norm_num)).mpr
    rw [mul_comm, ← Real.logb_rpow_eq_mul_logb_of_pos (by norm_cast; grind)]
    calc
      _ = Real.logb 2 (2 ^ (3 : ℝ)) := (Real.logb_rpow (by norm_num) (by norm_num)).symm
      _ ≤ Real.logb 2 (n ^ (2 : ℝ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
        norm_cast
        grind [Nat.pow_le_pow_left n_ge_3 2]
  apply lt_of_lt_of_le (pow_2_le_choose h1)
  refine le_trans ?_ (se2_choose_le_sp2 h)
  replace logb_pos : 0 ≤ Real.logb 2 n := by grind
  have _ : ⌊Real.logb 2 n * √e⌋₊ ≤ e - 1 := by
    suffices ⌊Real.logb 2 n * √e⌋₊ < e by grind
    have hl : 0 ≤ Real.logb 2 n * √e := by positivity
    apply (floor_lt hl).mpr
    have henonneg : 0 ≤ (e : ℝ) := by exact cast_nonneg' e
    nth_rw 2 [← Real.sq_sqrt henonneg]
    replace hepos : 0 < (e : ℝ) := by
      norm_cast
      grind
    replace hepos2 : 0 < √e := by grind [Real.lt_sqrt_of_sq_lt]
    rw [sq]
    exact mul_lt_mul_of_pos_right ((Real.lt_sqrt logb_pos).mpr h3) hepos2
  have h2 : e ≤ φ r := by
    rw [← ZMod.card_units_eq_totient r, Fintype.card, ← Set.ncard_coe_finset]
    have _ : @Set.univ (ZMod r)ˣ = SetLike.coe (Finset.univ (α := (ZMod r)ˣ)) := by grind
    calc
      _ ≤ _ := Set.ncard_le_ncard (se2_subset_units h)
      _ ≤ _ := Set.ncard_image_le
      _ ≤ _ := by grind
  calc
    _ = (⌊Real.logb 2 n * √e⌋₊ + (⌊Real.logb 2 n * √e⌋₊ + 1)).choose ⌊Real.logb 2 n * √e⌋₊ := by
      grind
    _ = _ := choose_symm_add
    _ ≤ (e + ⌊Real.logb 2 n * √e⌋₊).choose (⌊Real.logb 2 n * √e⌋₊ + 1) := by
      apply choose_le_choose
      grind
    _ = (e + ⌊Real.logb 2 n * √e⌋₊).choose (e - 1) := by
      apply choose_symm_of_eq_add
      grind
    _ ≤ _ := by
      apply choose_le_choose
      suffices ⌊Real.logb 2 ↑n * √↑e⌋₊ ≤ a by grind
      rw [a_def, mul_comm]
      apply floor_le_floor
      refine mul_le_mul_of_nonneg_right ?_ logb_pos
      apply Real.sqrt_le_sqrt
      exact_mod_cast h2

theorem aux (h : Conditions r p n a q μ) : False := by
  grind [aux_le h, not_aux_le h]

end Rest

end AKS

@[expose] public section

/-- The **AKS primality test**. If `(X + a) ^ n = X ^ n + a` modulo `(ZMod n)[X] / X ^ r - 1`
  and some other minor conditions hold, then `n` is a prime power. -/
theorem is_prime_pow_of_quotient_of_ideal_span_of_primitive_root_generator_polynomial
    {n r a : ℕ} (hc : n.Coprime r) (hn : 3 ≤ n)
    (ha : a = ⌊√(φ r) * (Real.logb 2 n)⌋₊) (hc2 : ∀ y ∈ Icc 1 a, n.Coprime y)
    (hod : Real.logb 2 n ^ 2 < orderOf (n : ZMod r)) (heq : ∀ y ∈ Icc 1 a,
    (Ideal.Quotient.mk (Ideal.span {(X : (ZMod n)[X]) ^ r - 1}))
      ((X : (ZMod n)[X]) ^ n - (C (y : (ZMod n)))) =
    (Ideal.Quotient.mk (Ideal.span {(X : (ZMod n)[X]) ^ r - 1}))
      (((X : (ZMod n)[X]) - (C (y : ZMod n))) ^ n)) : IsPrimePow n := by
  by_contra hcon
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (not_isPrimePow_iff_nontrivial_of_two_le (show 2 ≤ n by lia)).mp hcon
  clear hcon
  simp only [SetLike.mem_coe] at hp hq
  obtain ⟨pp , hp, -⟩ := mem_primeFactors.mp hp
  obtain ⟨pq , hq, -⟩ := mem_primeFactors.mp hq
  haveI : Fact p.Prime := .mk pp
  set K := AlgebraicClosure (ZMod p)
  have _ : NeZero (r : K) := by
    apply NeZero.of_not_dvd K
    exact (Nat.Prime.coprime_iff_not_dvd (n := r) pp).mp (Coprime.coprime_dvd_left hp hc)
  have _ : NeZero r := NeZero.of_neZero_natCast K
  have henough : HasEnoughRootsOfUnity K r := inferInstance
  obtain ⟨ν , hν⟩ := henough.1
  refine AKS.aux (AKS.Conditions.mk hc hn ha hod hc2 ?_ hν pp pq hp hq hpq)
  intro ⟨y, hyy⟩
  unfold AKS.introspective
  intro μ hμ
  by_cases hcas: y = 0
  · simp [hcas]
  · have yy : y ∈ Icc 1 a := by grind
    replace heq := heq y yy
    let f := by
      refine Ideal.Quotient.lift
        (Ideal.span {(X : (ZMod n)[X]) ^ r - 1}) (eval₂RingHom (ZMod.castHom hp K) μ) ?_
      intro s hs
      rw [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_left] at hs
      obtain ⟨c , hc⟩ := hs
      rw [hc, map_mul]
      apply mul_eq_zero_of_right
      simp only [coe_eval₂RingHom, eval₂_sub, eval₂_X_pow, eval₂_one]
      rw [IsPrimitiveRoot.pow_eq_one]
      · simp
      · exact (mem_primitiveRoots (by grind)).mp hμ
    have g : μ = f ⟦X⟧ := by
      change μ = (eval₂RingHom (ZMod.castHom hp K)) μ X
      simp
    have hoh : eval (μ ^ n) ((X : K[X]) - C (y : K)) = μ ^ n - y := by
      rw [eval_sub, eval_X, eval_C]
    have hoh2 : eval μ ((X : K[X]) - C (y : K)) ^ n = (μ - y) ^ n := by
      rw [eval_sub, eval_X, eval_C]
    have yy : (⟨y, hyy⟩ : Icc 0 a) = y := by grind
    rw [yy, hoh, hoh2]
    replace hoh : f ⟦ X ^ n - y.cast ⟧ = μ ^ n - y.cast := by
      change (eval₂RingHom (ZMod.castHom hp K)) μ (X ^ n - y.cast ) = _
      simp
    rw [← hoh]
    replace hoh : f ⟦(X - y.cast) ^ n⟧ = (μ - y.cast) ^ n := by
      change (eval₂RingHom (ZMod.castHom hp K)) μ ((X - y.cast) ^ n) = _
      simp [eval₂_pow]
    rw [← hoh]
    apply congr_arg
    exact heq

end
