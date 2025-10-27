/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Regular.SMul

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`Monic.mul`, `Monic.map`, `Monic.pow`.
-/


noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section Semiring

variable [Semiring R] {p q r : R[X]}

theorem monic_zero_iff_subsingleton : Monic (0 : R[X]) ↔ Subsingleton R :=
  subsingleton_iff_zero_eq_one

theorem not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ (0 : R) ≠ 1 :=
  (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).not

theorem monic_zero_iff_subsingleton' :
    Monic (0 : R[X]) ↔ (∀ f g : R[X], f = g) ∧ ∀ a b : R, a = b :=
  Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp [eq_iff_true_of_subsingleton], fun h => subsingleton_iff.mpr h.2⟩

theorem Monic.as_sum (hp : p.Monic) :
    p = X ^ p.natDegree + ∑ i ∈ range p.natDegree, C (p.coeff i) * X ^ i := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.natDegree) = 1 by rw [this, one_mul]
  exact congr_arg C hp

@[deprecated (since := "2025-08-14")] alias ne_zero_of_ne_zero_of_monic :=
  Monic.ne_zero_of_polynomial_ne

theorem Monic.map [Semiring S] (f : R →+* S) (hp : Monic p) : Monic (p.map f) :=
  subsingleton_or_nontrivial S |>.elim (fun h ↦ h.allEq _ _) fun _ ↦
    f.map_one ▸ hp ▸ leadingCoeff_map_eq_of_isUnit_leadingCoeff _ <| hp ▸ isUnit_one

theorem monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) :
    Monic (C b * p) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

theorem monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) :
    Monic (p * C b) := by
  unfold Monic
  nontriviality
  rw [leadingCoeff_mul' _] <;> simp [leadingCoeff_C b, hp]

theorem monic_X_pow_add {n : ℕ} (H : degree p < n) : Monic (X ^ n + p) :=
  monic_of_degree_le n
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H, add_zero])

variable (a) in
theorem monic_X_pow_add_C {n : ℕ} (h : n ≠ 0) : (X ^ n + C a).Monic :=
  monic_X_pow_add <| (lt_of_le_of_lt degree_C_le
    (by simp only [Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq, h, not_false_eq_true]))

theorem monic_X_add_C (x : R) : Monic (X + C x) :=
  pow_one (X : R[X]) ▸ monic_X_pow_add_C x one_ne_zero

theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
  letI := Classical.decEq R
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else by
    have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
      simp [Monic.def.1 hp, Monic.def.1 hq, Ne.symm h0]
    rw [Monic.def, leadingCoeff_mul' this, Monic.def.1 hp, Monic.def.1 hq, one_mul]

theorem Monic.pow (hp : Monic p) : ∀ n : ℕ, Monic (p ^ n)
  | 0 => monic_one
  | n + 1 => by
    rw [pow_succ]
    exact (Monic.pow hp n).mul hp

theorem Monic.add_of_left (hp : Monic p) (hpq : degree q < degree p) : Monic (p + q) := by
  rwa [Monic, add_comm, leadingCoeff_add_of_degree_lt hpq]

theorem Monic.add_of_right (hq : Monic q) (hpq : degree p < degree q) : Monic (p + q) := by
  rwa [Monic, leadingCoeff_add_of_degree_lt hpq]

theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic := by
  contrapose! hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]

theorem Monic.of_mul_monic_right (hq : q.Monic) (hpq : (p * q).Monic) : p.Monic := by
  contrapose! hpq
  rw [Monic.def] at hpq ⊢
  rwa [leadingCoeff_mul_monic hq]

namespace Monic

lemma comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  nontriviality R
  have : (p.comp q).natDegree = p.natDegree * q.natDegree :=
    natDegree_comp_eq_of_mul_ne_zero <| by simp [hp.leadingCoeff, hq.leadingCoeff]
  rw [Monic.def, Polynomial.leadingCoeff, this, coeff_comp_degree_mul_degree h, hp.leadingCoeff,
    hq.leadingCoeff, one_pow, mul_one]

lemma comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + C r)).Monic := by
  nontriviality R
  refine hp.comp (monic_X_add_C _) fun ha ↦ ?_
  rw [natDegree_X_add_C] at ha
  exact one_ne_zero ha

@[deprecated (since := "2025-10-26")] alias natDegree_eq_zero_iff_eq_one := natDegree_eq_zero

@[simp]
theorem degree_le_zero_iff_eq_one (hp : p.Monic) : p.degree ≤ 0 ↔ p = 1 := by
  rw [← hp.natDegree_eq_zero, natDegree_eq_zero_iff_degree_le_zero]

theorem natDegree_mul (hp : p.Monic) (hq : q.Monic) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  nontriviality R
  apply natDegree_mul'
  simp [hp.leadingCoeff, hq.leadingCoeff]

theorem degree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degree := by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul', hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leadingCoeff, one_mul, leadingCoeff_ne_zero]

nonrec theorem natDegree_mul' (hp : p.Monic) (hq : q ≠ 0) :
    (p * q).natDegree = p.natDegree + q.natDegree := by
  rw [natDegree_mul']
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

theorem natDegree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p).natDegree := by
  by_cases h : q = 0
  · simp [h]
  rw [hp.natDegree_mul' h, Polynomial.natDegree_mul', add_comm]
  simpa [hp.leadingCoeff, leadingCoeff_ne_zero]

theorem _root_.Polynomial.not_isUnit_X_add_C [Nontrivial R] (a : R) : ¬ IsUnit (X + C a) := by
  rintro ⟨⟨_, g, hfg, hgf⟩, rfl⟩
  have h := (monic_X_add_C a).natDegree_mul' (right_ne_zero_of_mul_eq_one hfg)
  rw [hfg, natDegree_one, natDegree_X_add_C] at h
  grind

theorem not_dvd_of_natDegree_lt (hp : Monic p) (h0 : q ≠ 0) (hl : natDegree q < natDegree p) :
    ¬p ∣ q := by
  rintro ⟨r, rfl⟩
  rw [hp.natDegree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_ge (Nat.le_add_right _ _)

theorem not_dvd_of_degree_lt (hp : Monic p) (h0 : q ≠ 0) (hl : degree q < degree p) : ¬p ∣ q :=
  Monic.not_dvd_of_natDegree_lt hp h0 <| natDegree_lt_natDegree h0 hl

theorem nextCoeff_mul (hp : Monic p) (hq : Monic q) :
    nextCoeff (p * q) = nextCoeff p + nextCoeff q := by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;> simp [hp.leadingCoeff, hq.leadingCoeff, mul_coeff_one, add_comm]

theorem nextCoeff_pow (hp : p.Monic) (n : ℕ) : (p ^ n).nextCoeff = n • p.nextCoeff := by
  induction n with
  | zero => rw [pow_zero, zero_smul, ← map_one (f := C), nextCoeff_C_eq_zero]
  | succ n ih => rw [pow_succ, (hp.pow n).nextCoeff_mul hp, ih, succ_nsmul]

theorem eq_one_of_map_eq_one {S : Type*} [Semiring S] [Nontrivial S] (f : R →+* S) (hp : p.Monic)
    (map_eq : p.map f = 1) : p = 1 := by
  nontriviality R
  have hdeg : p.degree = 0 := by
    rw [← degree_map_eq_of_leadingCoeff_ne_zero f _, map_eq, degree_one]
    · rw [hp.leadingCoeff, f.map_one]
      exact one_ne_zero
  have hndeg : p.natDegree = 0 :=
    WithBot.coe_eq_coe.mp ((degree_eq_natDegree hp.ne_zero).symm.trans hdeg)
  convert eq_C_of_degree_eq_zero hdeg
  rw [← hndeg, ← Polynomial.leadingCoeff, hp.leadingCoeff, C.map_one]

theorem natDegree_pow (hp : p.Monic) (n : ℕ) : (p ^ n).natDegree = n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n hn => rw [pow_succ, (hp.pow n).natDegree_mul hp, hn, Nat.succ_mul, add_comm]

end Monic

@[simp]
theorem natDegree_pow_X_add_C [Nontrivial R] (n : ℕ) (r : R) : ((X + C r) ^ n).natDegree = n := by
  rw [(monic_X_add_C r).natDegree_pow, natDegree_X_add_C, mul_one]

theorem Monic.eq_one_of_isUnit (hm : Monic p) (hpu : IsUnit p) : p = 1 := by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.natDegree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h, natDegree_one, eq_comm, add_eq_zero] at this
  exact hm.natDegree_eq_zero.mp this.1

theorem Monic.isUnit_iff (hm : p.Monic) : IsUnit p ↔ p = 1 :=
  ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩

theorem eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q) : p = q := by
  obtain ⟨u, rfl⟩ := hpq
  rw [(hp.of_mul_monic_left hq).eq_one_of_isUnit u.isUnit, mul_one]

end Semiring

section CommSemiring

variable [CommSemiring R] {p : R[X]}

theorem monic_multiset_prod_of_monic (t : Multiset ι) (f : ι → R[X]) (ht : ∀ i ∈ t, Monic (f i)) :
    Monic (t.map f).prod := by
  revert ht
  refine t.induction_on ?_ ?_; · simp
  intro a t ih ht
  rw [Multiset.map_cons, Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))

theorem monic_prod_of_monic (s : Finset ι) (f : ι → R[X]) (hs : ∀ i ∈ s, Monic (f i)) :
    Monic (∏ i ∈ s, f i) :=
  monic_multiset_prod_of_monic s.1 f hs

theorem monic_finprod_of_monic (α : Type*) (f : α → R[X])
    (hf : ∀ i ∈ Function.mulSupport f, Monic (f i)) :
    Monic (finprod f) := by
  classical
  rw [finprod_def]
  split_ifs
  · exact monic_prod_of_monic _ _ fun a ha => hf a ((Set.Finite.mem_toFinset _).mp ha)
  · exact monic_one

theorem Monic.nextCoeff_multiset_prod (t : Multiset ι) (f : ι → R[X]) (h : ∀ i ∈ t, Monic (f i)) :
    nextCoeff (t.map f).prod = (t.map fun i => nextCoeff (f i)).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_
  · simp only [Multiset.notMem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [nextCoeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      Monic.nextCoeff_mul, ih]
    exacts [fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]

theorem Monic.nextCoeff_prod (s : Finset ι) (f : ι → R[X]) (h : ∀ i ∈ s, Monic (f i)) :
    nextCoeff (∏ i ∈ s, f i) = ∑ i ∈ s, nextCoeff (f i) :=
  Monic.nextCoeff_multiset_prod s.1 f h

variable [NoZeroDivisors R] {p q : R[X]}

lemma irreducible_of_monic (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 := by
  refine
    ⟨fun h f g hf hg hp => (h.2 hp.symm).imp hf.eq_one_of_isUnit hg.eq_one_of_isUnit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_isUnit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) ?_ ?_ ?_).symm.imp
          (isUnit_of_mul_eq_one f _)
          (isUnit_of_mul_eq_one g _)⟩⟩
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, mul_comm, ← hfg, ← Monic]
  · rwa [Monic, leadingCoeff_mul, leadingCoeff_C, ← leadingCoeff_mul, ← hfg, ← Monic]
  · rw [mul_mul_mul_comm, ← C_mul, ← leadingCoeff_mul, ← hfg, hp.leadingCoeff, C_1, mul_one,
      mul_comm, ← hfg]


lemma Monic.irreducible_iff_natDegree (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1, and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero, hb.natDegree_eq_zero]

lemma Monic.irreducible_iff_natDegree' (hp : p.Monic) : Irreducible p ↔ p ≠ 1 ∧
    ∀ f g : R[X], f.Monic → g.Monic → f * g = p → g.natDegree ∉ Ioc 0 (p.natDegree / 2) := by
  simp_rw [hp.irreducible_iff_natDegree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.natDegree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.natDegree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.natDegree g.natDegree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, by gcongr⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, by gcongr⟩

/-- Alternate phrasing of `Polynomial.Monic.irreducible_iff_natDegree'` where we only have to check
one divisor at a time. -/
lemma Monic.irreducible_iff_lt_natDegree_lt {p : R[X]} (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  rw [hp.irreducible_iff_natDegree', and_iff_right hp1]
  constructor
  · rintro h g hg hdg ⟨f, rfl⟩
    exact h f g (hg.of_mul_monic_left hp) hg (mul_comm f g) hdg
  · rintro h f g - hg rfl hdg
    exact h g hg hdg (dvd_mul_left g f)

lemma Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ := by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree', and_iff_right, hnd]
  · push_neg
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [zero_lt_two, Nat.div_self, Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [ha.natDegree_mul hb, hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using ha.nextCoeff_mul hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · simp
  · rintro rfl
    simp [natDegree_one] at hnd

end CommSemiring

section Semiring

variable [Semiring R]

@[simp]
theorem Monic.natDegree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).natDegree = P.natDegree := by
  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)
  rw [coeff_map, Monic.coeff_natDegree hmo, RingHom.map_one]
  exact one_ne_zero

@[simp]
theorem Monic.degree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).degree = P.degree := by
  simp_all

section Injective

open Function

variable [Semiring S] {f : R →+* S}

@[deprecated (since := "2025-10-26")]
alias leadingCoeff_map' := leadingCoeff_map_of_injective
@[deprecated (since := "2025-10-26")]
alias leadingCoeff_of_injective := leadingCoeff_map_of_injective

theorem monic_of_injective (hf : Injective f) {p : R[X]} (hp : (p.map f).Monic) : p.Monic := by
  apply hf
  rw [← leadingCoeff_map_of_injective hf, hp.leadingCoeff, f.map_one]

theorem _root_.Function.Injective.monic_map_iff (hf : Injective f) {p : R[X]} :
    p.Monic ↔ (p.map f).Monic :=
  ⟨Monic.map _, Polynomial.monic_of_injective hf⟩

end Injective

end Semiring

section Ring

variable [Ring R] {p : R[X]}

theorem monic_X_sub_C (x : R) : Monic (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p < n) : Monic (X ^ n - p) := by
  simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) < n by rwa [← degree_neg p] at H)

/-- `X ^ n - a` is monic. -/
theorem monic_X_pow_sub_C {R : Type u} [Ring R] (a : R) {n : ℕ} (h : n ≠ 0) :
    (X ^ n - C a).Monic := by
  simpa only [map_neg, ← sub_eq_add_neg] using monic_X_pow_add_C (-a) h

theorem not_isUnit_X_pow_sub_one (R : Type*) [Ring R] [Nontrivial R] (n : ℕ) :
    ¬IsUnit (X ^ n - 1 : R[X]) := by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp at h
  apply hn
  rw [← @natDegree_one R, ← (monic_X_pow_sub_C _ hn).eq_one_of_isUnit h, natDegree_X_pow_sub_C]

lemma Monic.comp_X_sub_C {p : R[X]} (hp : p.Monic) (r : R) : (p.comp (X - C r)).Monic := by
  simpa using hp.comp_X_add_C (-r)

theorem Monic.sub_of_left {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p) :
    Monic (p - q) := by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]

theorem Monic.sub_of_right {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q) :
    Monic (p - q) := by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [natDegree_neg, coeff_neg, show q.coeff q.natDegree = -1 from hq, neg_neg]
  rw [sub_eq_add_neg]
  apply Monic.add_of_right this
  rwa [degree_neg]

end Ring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

@[simp]
theorem not_monic_zero : ¬Monic (0 : R[X]) :=
  not_monic_zero_iff.mp zero_ne_one

end NonzeroSemiring

section NotZeroDivisor

-- TODO: using gh-8537, rephrase lemmas that involve commutation around `*` using the op-ring
variable [Semiring R] {p : R[X]}

theorem Monic.mul_left_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : q * p ≠ 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne, ← degree_eq_bot, hp.degree_mul, WithBot.add_eq_bot, not_or, degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

theorem Monic.mul_right_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : p * q ≠ 0 := by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne, ← degree_eq_bot, hp.degree_mul_comm, hp.degree_mul, WithBot.add_eq_bot, not_or,
    degree_eq_bot]
  refine ⟨hq, ?_⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_le] at h
  refine (lt_trans ?_ h).ne'
  simp

theorem Monic.mul_natDegree_lt_iff (h : Monic p) {q : R[X]} :
    (p * q).natDegree < p.natDegree ↔ p ≠ 1 ∧ q = 0 := by
  by_cases hq : q = 0
  · suffices 0 < p.natDegree ↔ p.natDegree ≠ 0 by simpa [hq, ← h.natDegree_eq_zero]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.natDegree_mul', hq]

theorem Monic.mul_right_eq_zero_iff (h : Monic p) {q : R[X]} : p * q = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_right_ne_zero, hq]

theorem Monic.mul_left_eq_zero_iff (h : Monic p) {q : R[X]} : q * p = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_left_ne_zero, hq]

theorem Monic.isRegular {R : Type*} [Ring R] {p : R[X]} (hp : Monic p) : IsRegular p := by
  constructor
  · intro q r h
    dsimp only at h
    rw [← sub_eq_zero, ← hp.mul_right_eq_zero_iff, mul_sub, h, sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero, ← hp.mul_left_eq_zero_iff, sub_mul, h, sub_self]

theorem degree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).degree = p.degree := by
  refine le_antisymm ?_ ?_
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine h ?_
    simpa using hm m le_rfl

theorem natDegree_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree hp, ← degree_eq_natDegree,
    degree_smul_of_smul_regular p h]
  contrapose! hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp

theorem leadingCoeff_smul_of_smul_regular {S : Type*} [SMulZeroClass S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, coeff_smul,
    natDegree_smul_of_smul_regular p h]

theorem monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) :
    Monic (h.unit⁻¹ • p) := by
  rw [Monic.def, leadingCoeff_smul_of_smul_regular _ (isSMulRegular_of_group _), Units.smul_def]
  simp

theorem isUnit_leadingCoeff_mul_right_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    p * q = 0 ↔ q = 0 := by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q := by
      ext
      simp only [Units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← mul_assoc]
    rwa [this, Monic.mul_right_eq_zero_iff] at hp
    exact monic_of_isUnit_leadingCoeff_inv_smul _
  · rintro rfl
    simp

theorem isUnit_leadingCoeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    q * p = 0 ↔ q = 0 := by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [zero_mul] at hp
    rwa [mul_assoc, Monic.mul_left_eq_zero_iff] at hp
    refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    simp
  · rintro rfl
    rw [zero_mul]

end NotZeroDivisor

end Polynomial
