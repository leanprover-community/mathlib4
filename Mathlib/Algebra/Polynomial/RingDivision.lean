/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Coprime.Basic

/-!
# Theory of univariate polynomials

We prove basic results about univariate polynomials.

-/

assert_not_exists Ideal.map

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

theorem natDegree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S}
    (hz : aeval z p = 0) (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.natDegree :=
  natDegree_pos_of_eval₂_root hp (algebraMap R S) hz inj

theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_aeval_root hp hz inj)

end

theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div p hq],
            (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic

theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (modByMonicHom q) ↔ q ∣ p :=
  LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

section

variable [Ring S]

theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} (hq : q.Monic) {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
    --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  rw [modByMonic_eq_sub_mul_div p hq, map_sub, map_mul, hx, zero_mul,
    sub_zero]

end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), natTrailingDegree_mul hp hq]
    apply WithTop.coe_add

end NoZeroDivisors


section CommRing

variable [CommRing R]

theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0, sub_zero]
  convert (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

/-- See `Polynomial.rootMultiplicity_eq_natTrailingDegree'` for the special case of `t = 0`. -/
theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).natTrailingDegree :=
  rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

section nonZeroDivisors

open scoped nonZeroDivisors

theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ (h.coeff_natDegree ▸ one_mem R⁰)

theorem mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff ∈ R⁰) : p ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ h

theorem mem_nonZeroDivisors_of_trailingCoeff {p : R[X]} (h : p.trailingCoeff ∈ R⁰) : p ∈ R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ h

end nonZeroDivisors

theorem natDegree_pos_of_monic_of_aeval_eq_zero [Nontrivial R] [Semiring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : p.Monic) {x : S} (hx : aeval x p = 0) :
    0 < p.natDegree :=
  natDegree_pos_of_aeval_root (Monic.ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap R S)).mp (FaithfulSMul.algebraMap_injective R S))

theorem rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : ℕ} (h : p ≠ 0) :
    (p * (X - C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n := by
  have h2 := monic_X_sub_C a |>.pow n |>.mul_left_ne_zero h
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h a
  · rw [le_rootMultiplicity_iff h2, pow_add]
    exact mul_dvd_mul_right (pow_rootMultiplicity_dvd p a) _

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (X - C x) = 1 :=
  pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1

theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

theorem rootMultiplicity_mul' {p q : R[X]} {x : R}
    (hpq : (p /ₘ (X - C x) ^ p.rootMultiplicity x).eval x *
      (q /ₘ (X - C x) ^ q.rootMultiplicity x).eval x ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]

theorem Monic.neg_one_pow_natDegree_mul_comp_neg_X {p : R[X]} (hp : p.Monic) :
    ((-1) ^ p.natDegree * p.comp (-X)).Monic := by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

variable [IsDomain R] {p q : R[X]}

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [hu.symm]

theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩

theorem prime_X : Prime (X : R[X]) := by
  convert prime_X_sub_C (0 : R)
  simp

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).irreducible

theorem irreducible_X : Irreducible (X : R[X]) :=
  Prime.irreducible prime_X

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).irreducible

lemma aeval_ne_zero_of_isCoprime {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
    {p q : R[X]} (h : IsCoprime p q) (s : S) : aeval s p ≠ 0 ∨ aeval s q ≠ 0 := by
  by_contra! hpq
  rcases h with ⟨_, _, h⟩
  apply_fun aeval s at h
  simp only [map_add, map_mul, map_one, hpq.left, hpq.right, mul_zero, add_zero, zero_ne_one] at h

theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

open scoped Function in -- required for scoped `on` notation
theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit

theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  classical
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q), if_neg hpq, rootMultiplicity_eq_multiplicity p,
    if_neg hp, rootMultiplicity_eq_multiplicity q, if_neg hq,
    multiplicity_mul (prime_X_sub_C x) (finiteMultiplicity_X_sub_C _ hpq)]

open Multiset in
theorem exists_multiset_roots [DecidableEq R] :
    ∀ {p : R[X]} (_ : p ≠ 0), ∃ s : Multiset R,
      (Multiset.card s : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p, hp =>
    haveI := Classical.propDecidable (∃ x, IsRoot p x)
    if h : ∃ x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx, h, mul_zero] at hp; exact hp rfl
      have wf : degree (p /ₘ (X - C x)) < degree p :=
        degree_divByMonic_lt _ (monic_X_sub_C x) hp ((degree_X_sub_C x).symm ▸ by decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots _ (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p := by
        rw [degree_X_sub_C, degree_eq_natDegree hp]
        rw [degree_eq_natDegree hp] at hpd
        exact WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 hpd)
      have hdiv0 : p /ₘ (X - C x) ≠ 0 :=
        mt (divByMonic_eq_zero_iff (monic_X_sub_C x)).1 <| not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = Multiset.card t + 1 := by
            congr
            exact mod_cast Multiset.card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_divByMonic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_comm]
            exact add_le_add (le_refl (1 : WithBot ℕ)) htd,
        by
          intro a
          conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hx]
          rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
            rootMultiplicity_X_sub_C, ← htr a]
          split_ifs with ha
          · rw [ha, count_cons_self, add_comm]
          · rw [count_cons_of_ne ha, zero_add]⟩
    else
      ⟨0, (degree_eq_natDegree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _), by
        intro a
        rw [count_zero, rootMultiplicity_eq_zero (not_exists.mp h a)]⟩
termination_by p => natDegree p
decreasing_by {
  apply (Nat.cast_lt (α := WithBot ℕ)).mp
  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0] at wf
  assumption}

end CommRing

end Polynomial
