/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Ideal.Over

/-!
# Frobenius Elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists unique a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≃ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

This file proves the existence of Frobenius elements in a more general setting.

## Main statements

Let `G` be a finite group acting on a commutative ring `B`, and let `A = B^G` be the ring of
invariants.

* `exists_smul_of_comap_eq`: `G` acts transitively on primes of `B` above the same prime of `A`.


-/

open scoped Pointwise

section ForMathlib

-- PRed
lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction' n with n hn
  · rw [pow_zero, one_smul]
  · rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)

-- PRed
instance {G : Type*} [Monoid G] {α : Type*} [Preorder α]
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] :
    CovariantClass G αᵒᵈ HSMul.hSMul LE.le :=
  ⟨fun g _ _ h ↦ smul_mono_right (α := α) g h⟩

-- PRed
lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a := by
  induction' n with n hn
  · rw [pow_zero, one_smul]
  · rw [pow_succ', mul_smul]
    exact (smul_mono_right g hn).trans h

-- PRed
lemma smul_eq_of_le_smul
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) : g • a = a := by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul, ← pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm key h

-- PRed
lemma smul_eq_of_smul_le
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) : g • a = a := by
  have key := smul_mono_right g (pow_smul_le h (Nat.card G - 1))
  rw [smul_smul, ← _root_.pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm h key

end ForMathlib

section integrallemma

open Polynomial

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

theorem IsAlgebraic.def_of_mem_nonZeroDivisors
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ (q : Polynomial R), q.coeff 0 ≠ 0 ∧ aeval s q = 0 := by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq, map_mul, aeval_X_pow] at hp
  exact ⟨q, hq, (nonZeroDivisors S).pow_mem hs (rootMultiplicity 0 p) (aeval s q) hp⟩

theorem IsAlgebraic.exists_nonzero_dvd
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ r : R, r ≠ 0 ∧ s ∣ (algebraMap R S) r := by
  obtain ⟨q, hq0, hq⟩ := hRs.def_of_mem_nonZeroDivisors hs
  have key := map_dvd (Polynomial.aeval s) (Polynomial.X_dvd_sub_C (p := q))
  rw [map_sub, hq, zero_sub, dvd_neg, Polynomial.aeval_X, Polynomial.aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

theorem lem0 (A B K L : Type*) [CommRing A] [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra A B] [h : Algebra.IsAlgebraic A B] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (x : L) :
    ∃ (b : B) (a : A), a ≠ 0 ∧ x = algebraMap B L b / algebraMap A L a := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  obtain ⟨a, ha, b, h⟩ := (h.isAlgebraic y).exists_nonzero_dvd hy
  refine ⟨x * b, a, ha, ?_⟩
  rw [IsScalarTower.algebraMap_apply A B L, h, map_mul, map_mul, mul_div_mul_right]
  rw [Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
  contrapose! ha
  rw [ha, mul_zero] at h
  replace ha := congrArg (algebraMap B L) h
  rwa [map_zero, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L,
    NoZeroSMulDivisors.algebraMap_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff] at ha

end integrallemma

section charpoly

open Polynomial

namespace MulSemiringAction

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]

noncomputable def charpoly (b : B) : B[X] :=
  ∏ g : G, (X - C (g • b))

theorem charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b)) := rfl

theorem charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b) := by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

theorem charpoly_monic (b : B) : (charpoly G b).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)

theorem charpoly_eval (b : B) : (charpoly G b).eval b = 0 := by
  rw [charpoly_eq, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul, eval_sub, eval_C, eval_X, sub_self]

variable {G}

theorem charpoly_smul (b : B) (g : G) : g • (charpoly G b) = charpoly G b := by
  rw [charpoly_eq_prod_smul, Finset.smul_prod_perm]

private theorem charpoly_coeff_smul (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, charpoly_smul]

variable {A : Type*} [CommRing A] [Algebra A B]

theorem exists_map_eq_charpoly
    (hinv : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b) (b : B) :
    ∃ M : A[X], M.Monic ∧ M.map (algebraMap A B) = charpoly G b := by
  let f : ℕ → A := fun k ↦ (hinv ((charpoly G b).coeff k) (charpoly_coeff_smul b k)).choose
  have hf : ∀ k, algebraMap A B (f k) = (charpoly G b).coeff k :=
    fun k ↦ (hinv ((charpoly G b).coeff k) (charpoly_coeff_smul b k)).choose_spec
  use X ^ (charpoly G b).natDegree + ∑ k ∈ Finset.range (charpoly G b).natDegree, C (f k) * X ^ k
  constructor
  · apply Polynomial.monic_X_pow_add
    rw [← Fin.sum_univ_eq_sum_range]
    apply Polynomial.degree_sum_fin_lt
  · simp_rw [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, hf]
    exact (charpoly_monic G b).as_sum.symm

theorem isIntegral_quot_quot
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b) :
    Algebra.IsIntegral A B where
  isIntegral b := by
    obtain ⟨f, hf1, hf2⟩ := exists_map_eq_charpoly hFull' b
    refine ⟨f, hf1, ?_⟩
    rw [← eval_map, hf2, charpoly_eval]

end MulSemiringAction

end charpoly

section transitivity

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- If `G` is finite, then `G` acts transitively on primes of `B` above the same prime of `A`. -/
theorem exists_smul_of_comap_eq [Finite G]
    (hAB : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, b = algebraMap A B a)
    (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime]
    (hPQ : P.under A = Q.under A) :
    ∃ g : G, Q = g • P := by
  cases nonempty_fintype G
  have : ∀ (P Q : Ideal B) [P.IsPrime] [Q.IsPrime], P.under A = Q.under A →
      ∃ g ∈ (⊤ : Finset G), Q ≤ g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ ↦ hP.smul _)]
    intro b hb
    suffices h : ∃ g ∈ Finset.univ, g • b ∈ P by
      obtain ⟨g, -, hg⟩ := h
      apply Set.mem_biUnion (Finset.mem_univ g⁻¹) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
    obtain ⟨a, ha⟩ := hAB (∏ g : G, g • b) (Finset.smul_prod_perm b)
    rw [← hP.prod_mem_iff, ha, ← P.mem_comap, ← P.under_def A,
      hPQ, Q.mem_comap, ← ha, hQ.prod_mem_iff]
    exact ⟨1, Finset.mem_univ 1, (one_smul G b).symm ▸ hb⟩
  obtain ⟨g, -, hg⟩ := this P Q hPQ
  have h := hP.smul g -- should this be an instance?
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((P.under_smul A g).trans hPQ).symm
  exact ⟨g, le_antisymm hg (smul_eq_of_le_smul (hg.trans hg') ▸ hg')⟩

end transitivity

section stabilizerAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]

def stabilizerAction : MulAction.stabilizer G Q →* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) where
  toFun g :=
  { __ := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv G B g) g.2.symm
    commutes' := fun q ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      simp [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] }
  map_one' := AlgEquiv.ext (fun q ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp)
  map_mul' g h := AlgEquiv.ext (fun q ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [mul_smul])

end stabilizerAction

section CRT

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  (Q : Ideal B) [Q.IsPrime]

-- technical CRT lemma
theorem lem1 [DecidableEq (Ideal B)] :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ (a ∉ Q) ∧
    (∀ g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a else 0)) := by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := ((Finset.univ : Finset G).filter (fun g ↦ g • Q ≠ Q)).inf (fun g ↦ g • Q)
  have h1 : ¬ P ≤ Q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_iff_exists.mp h1
  replace hbP : ∀ g : G, g • Q ≠ Q → b ∈ g • Q :=
    fun g hg ↦ (Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩) : P ≤ g • Q) hbP
  let f := MulSemiringAction.charpoly G b
  obtain ⟨q, hq, hq0⟩ :=
    (f.map (algebraMap B (B ⧸ Q))).exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      (Polynomial.map_monic_ne_zero (MulSemiringAction.charpoly_monic G b)) 0
  rw [map_zero, sub_zero] at hq hq0
  let j := (f.map (algebraMap B (B ⧸ Q))).rootMultiplicity 0
  let k := q.natDegree
  let r := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j))
  have hr : r.map (algebraMap B (B ⧸ Q)) = q := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range_succ_iff]
    split_ifs with hn
    · rw [← Polynomial.coeff_map, hq, Polynomial.coeff_X_pow_mul]
    · rw [map_zero, eq_comm, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_le hn)]
  have hf : f.eval b = 0 := MulSemiringAction.charpoly_eval G b
  have hr : r.eval b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hbQ ⊢
    replace hf := congrArg (algebraMap B (B ⧸ Q)) hf
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map] at hf ⊢
    rwa [map_zero, hq, ← hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (pow_ne_zero _ hbQ)] at hf
  let a := f.coeff j
  have ha : ∀ g : G, g • a = a := MulSemiringAction.charpoly_coeff_smul b j
  have hr' : ∀ g : G, g • Q ≠ Q → a - r.eval b ∈ g • Q := by
    intro g hg
    have hr : r = ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j)) := rfl
    rw [← Ideal.neg_mem_iff, neg_sub, hr, Finset.sum_range_succ', Polynomial.eval_add,
        Polynomial.eval_monomial, zero_add, pow_zero, mul_one, add_sub_cancel_right]
    simp only [ ← Polynomial.monomial_mul_X]
    rw [← Finset.sum_mul, Polynomial.eval_mul_X]
    exact Ideal.mul_mem_left (g • Q) _ (hbP g hg)
  refine ⟨a, a - r.eval b, ha, ?_, fun h ↦ ?_⟩
  · rwa [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, ← Polynomial.coeff_map,
      ← zero_add j, hq, Polynomial.coeff_X_pow_mul, ← Polynomial.X_dvd_iff]
  · rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.smul_mem_pointwise_smul_iff (a := h⁻¹), smul_sub, inv_smul_smul]
    simp only [← eq_inv_smul_iff (g := h), eq_comm (a := Q)]
    split_ifs with hh
    · rwa [ha, sub_sub_cancel_left, hh, Q.neg_mem_iff]
    · rw [smul_zero, sub_zero]
      exact hr' h⁻¹ hh

theorem lem2 [DecidableEq (Ideal B)] (b₀ : B)
    (hx : ∀ g : G, g • Q = Q → algebraMap B (B ⧸ Q) (g • b₀) = algebraMap B (B ⧸ Q) b₀) :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ (a ∉ Q) ∧
    (∀ g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a * b₀ else 0)) := by
  obtain ⟨a, b, ha1, ha2, hb⟩ := lem1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g ↦ ?_⟩
  rw [smul_mul', map_mul, hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]

end CRT

section polylemma

open Polynomial

theorem lem3 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [NoZeroDivisors S]
    {a : S} {i j : ℕ} {p : Polynomial R} (h : p.map (algebraMap R S) = (X - C a) ^ i * X ^ j)
    (f : S ≃ₐ[R] S) (hi : i ≠ 0) :
    f a = a := by
  by_cases ha : a = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval a) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom, map_map, f.toAlgHom.comp_algebraMap, h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hi, zero_mul,
    zero_eq_mul, or_iff_left (pow_ne_zero j ha), pow_eq_zero_iff hi, sub_eq_zero] at hf
  exact hf.symm

end polylemma

section part_b

section redo_part_b

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime]
  [Q.LiesOver P]
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [NoZeroSMulDivisors (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

open IsScalarTower Polynomial in
theorem lem4 (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b)
    (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, stabilizerAction G P Q g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  classical
  cases nonempty_fintype G
  revert hx
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  intro hx
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := lem2 G Q b₀ (fun g hg ↦ hx ⟨g, hg⟩)
  obtain ⟨M, _, key⟩ := MulSemiringAction.exists_map_eq_charpoly hAB b
  replace key := congrArg (map (algebraMap B (B ⧸ Q))) key
  rw [map_map, ← algebraMap_eq, algebraMap_eq A (A ⧸ P) (B ⧸ Q),
      ← map_map, MulSemiringAction.charpoly, Polynomial.map_prod] at key
  have key₀ : ∀ g : G, (X - C (g • b)).map (algebraMap B (B ⧸ Q)) =
      if g • Q = Q then X - C (algebraMap B (B ⧸ Q) (a * b₀)) else X := by
    intro g
    rw [Polynomial.map_sub, map_X, map_C, hb]
    split_ifs
    · rfl
    · rw [map_zero, map_zero, sub_zero]
  simp only [key₀, Finset.prod_ite, Finset.prod_const] at key
  replace key := congrArg (map (algebraMap (B ⧸ Q) L)) key
  rw [map_map, ← algebraMap_eq, algebraMap_eq (A ⧸ P) K L,
      ← map_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key
  replace key := lem3 key f (Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr
    ⟨Finset.mem_univ 1, one_smul G Q⟩))
  simp only [map_mul] at key
  obtain ⟨a, rfl⟩ := hAB a ha1
  rwa [← algebraMap_apply A B (B ⧸ Q), algebraMap_apply A (A ⧸ P) (B ⧸ Q),
      ← algebraMap_apply, algebraMap_apply (A ⧸ P) K L, f.commutes, mul_right_inj'] at key
  rwa [← algebraMap_apply, algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      ← algebraMap_apply A (A ⧸ P) (B ⧸ Q), algebraMap_apply A B (B ⧸ Q),
      Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]

end redo_part_b

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

noncomputable def fullHom : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) :=
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (stabilizerAction G P Q)

theorem fullHom_surjective1
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b)
    (f : L ≃ₐ[K] L) (x : L) (hx : ∀ g : MulAction.stabilizer G Q, fullHom G P Q K L g x = x) :
    f x = x := by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := MulSemiringAction.isIntegral_quot_quot hAB
  have := Ideal.Quotient.algebra_isIntegral_of_liesOver Q P
  obtain ⟨b, a, ha, rfl⟩ := lem0 (A ⧸ P) (B ⧸ Q) K L x
  simp only [map_div₀, IsScalarTower.algebraMap_apply (A ⧸ P) K L, AlgEquiv.commutes] at hx ⊢
  replace ha : algebraMap (A ⧸ P) L a ≠ 0 := by
    rwa [Ne, IsScalarTower.algebraMap_apply (A ⧸ P) K L,
      NoZeroSMulDivisors.algebraMap_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
  simp only [← IsScalarTower.algebraMap_apply (A ⧸ P) K L, div_left_inj' ha] at hx ⊢
  refine lem4 G P Q K L hAB f b (fun g ↦ IsFractionRing.injective (B ⧸ Q) L ?_)
  exact (IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L
    (stabilizerAction G P Q g) b).symm.trans (hx g)

theorem fullHom_surjective
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b) :
    Function.Surjective (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L)) := by
  let action : MulSemiringAction (MulAction.stabilizer G Q) L :=
    MulSemiringAction.compHom _
      (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L))
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x ↦ fullHom_surjective1 G P Q K L hAB f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

end part_b
