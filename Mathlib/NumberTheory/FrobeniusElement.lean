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

-- PRed
namespace MulSemiringAction

open Polynomial

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]

/-- Characteristic polynomial of a group action on a ring. -/
noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))

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

end MulSemiringAction

-- PRed
namespace Algebra

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

class IsInvariant : Prop where
  isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b

variable {A B G}

theorem isInvariant_def :
    IsInvariant A B G ↔ ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

end Algebra

-- PRed
namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Fintype G] [MulSemiringAction G B] [IsInvariant A B G]

theorem exists_map_eq_charpoly (b : B) :
    ∃ M : A[X], M.Monic ∧ M.map (algebraMap A B) = charpoly G b := by
  have hinv k : ∃ a : A, algebraMap A B a = (charpoly G b).coeff k :=
    isInvariant ((charpoly G b).coeff k) (charpoly_coeff_smul b k)
  let f : ℕ → A := fun k ↦ (hinv k).choose
  have hf : ∀ k, algebraMap A B (f k) = (charpoly G b).coeff k := fun k ↦ (hinv k).choose_spec
  use X ^ (charpoly G b).natDegree + ∑ k ∈ Finset.range (charpoly G b).natDegree, C (f k) * X ^ k
  constructor
  · apply Polynomial.monic_X_pow_add
    rw [← Fin.sum_univ_eq_sum_range]
    apply Polynomial.degree_sum_fin_lt
  · simp_rw [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, hf]
    exact (charpoly_monic G b).as_sum.symm

include G in
theorem isIntegral : Algebra.IsIntegral A B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨f, hf1, hf2⟩ := exists_map_eq_charpoly A B G b
  refine ⟨f, hf1, ?_⟩
  rw [← eval_map, hf2, charpoly_eval]

end Algebra.IsInvariant

namespace Algebra.IsInvariant

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [IsInvariant A B G]

/-- If `G` is finite, then `G` acts transitively on primes of `B` above the same prime of `A`. -/
theorem exists_smul_of_comap_eq
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
    obtain ⟨a, ha⟩ := isInvariant (A := A) (∏ g : G, g • b) (Finset.smul_prod_perm b)
    rw [← hP.prod_mem_iff, ← ha, ← P.mem_comap, ← P.under_def A,
      hPQ, Q.mem_comap, ha, hQ.prod_mem_iff]
    exact ⟨1, Finset.mem_univ 1, (one_smul G b).symm ▸ hb⟩
  obtain ⟨g, -, hg⟩ := this P Q hPQ
  have h := hP.smul g -- should this be an instance?
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((P.under_smul A g).trans hPQ).symm
  exact ⟨g, le_antisymm hg (smul_eq_of_le_smul (hg.trans hg') ▸ hg')⟩

end Algebra.IsInvariant

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
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [NoZeroSMulDivisors (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

open IsScalarTower Polynomial in
theorem lem4 [Algebra.IsInvariant A B G]
    (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, Ideal.Quotient.stabilizerHom Q P G g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  classical
  cases nonempty_fintype G
  revert hx
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  intro hx
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := lem2 G Q b₀ (fun g hg ↦ hx ⟨g, hg⟩)
  obtain ⟨M, _, key⟩ := Algebra.IsInvariant.exists_map_eq_charpoly A B G b
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
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) a ha1
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
  MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (Ideal.Quotient.stabilizerHom Q P G)

theorem fullHom_surjective1
    [Algebra.IsInvariant A B G]
    (f : L ≃ₐ[K] L) (x : L) (hx : ∀ g : MulAction.stabilizer G Q, fullHom G P Q K L g x = x) :
    f x = x := by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  replace ha : algebraMap (A ⧸ P) L a ≠ 0 := by
    rwa [Ne, IsScalarTower.algebraMap_apply (A ⧸ P) K L,
      NoZeroSMulDivisors.algebraMap_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
  replace hy : algebraMap (B ⧸ Q) L y ≠ 0 :=
    mt (NoZeroSMulDivisors.algebraMap_eq_zero_iff (B ⧸ Q) L).mp (nonZeroDivisors.ne_zero hy)
  replace h : algebraMap (B ⧸ Q) L x / algebraMap (B ⧸ Q) L y =
      algebraMap (B ⧸ Q) L b / algebraMap (A ⧸ P) L a := by
    rw [mul_comm, Algebra.smul_def, mul_comm] at h
    rw [div_eq_div_iff hy ha, ← map_mul, ← h, map_mul, ← IsScalarTower.algebraMap_apply]
  simp only [h, map_div₀, IsScalarTower.algebraMap_apply (A ⧸ P) K L, AlgEquiv.commutes] at hx ⊢
  simp only [← IsScalarTower.algebraMap_apply, div_left_inj' ha] at hx ⊢
  exact lem4 G P Q K L f b (fun g ↦ IsFractionRing.injective (B ⧸ Q) L
    ((IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L
      (Ideal.Quotient.stabilizerHom Q P G g) b).symm.trans (hx g)))

theorem fullHom_surjective
    [Algebra.IsInvariant A B G] :
    Function.Surjective (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L)) := by
  let action : MulSemiringAction (MulAction.stabilizer G Q) L :=
    MulSemiringAction.compHom _
      (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L))
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x ↦ fullHom_surjective1 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

end part_b
