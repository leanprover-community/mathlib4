/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.RingTheory.Invariant.Defs
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

The main application is in algebraic number theory, where `G := Gal(L/K)` is the Galois group
of some finite Galois extension of number fields, and `A := 𝓞K` and `B := 𝓞L` are their ring of
integers. This main result in this file implies the existence of Frobenius elements in this setting.
See `Mathlib/RingTheory/Frobenius.lean`.

## Main statements

Let `G` be a finite group acting on a commutative ring `B` satisfying `Algebra.IsInvariant A B G`.

* `Algebra.IsInvariant.isIntegral`: `B/A` is an integral extension.
* `Algebra.IsInvariant.exists_smul_of_under_eq`: `G` acts transitivity on the prime ideals of `B`
  lying above a given prime ideal of `A`.

If `Q` is a prime ideal of `B` lying over a prime ideal `P` of `A`, then

* `IsFractionRing.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`.
* `Ideal.Quotient.stabilizerHom_surjective`:
  The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`.
* `Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under`:
  If `k` is a domain containing `B/Q`, then any `A/P`-algebra automorphism of `k` restricts to
  an automorphism of `B/Q`.
-/

open scoped Pointwise

section Galois

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

/-- In the AKLB setup, the Galois group of `L/K` acts on `B`. -/
noncomputable def IsIntegralClosure.MulSemiringAction [Algebra.IsAlgebraic K L] :
    MulSemiringAction (L ≃ₐ[K] L) B :=
  MulSemiringAction.compHom B (galRestrict A K L B).toMonoidHom

/-- In the AKLB setup, every fixed point of `B` lies in the image of `A`. -/
theorem Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B (L ≃ₐ[K] L) := by
  replace h := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb ↦ ?_⟩
  replace hb : algebraMap B L b ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  rw [h, IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective B L), ← hk,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    (FaithfulSMul.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

/-- A variant of `Algebra.isInvariant_of_isGalois`, replacing `Gal(L/K)` by `Aut(B/A)`. -/
theorem Algebra.isInvariant_of_isGalois' [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsInvariant A B (B ≃ₐ[A] B) :=
  ⟨fun b h ↦ (isInvariant_of_isGalois A K L B).1 b (fun g ↦ h (galRestrict A K L B g))⟩

end Galois

section Quotient

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subring B H) where
  smul := Quotient.lift (fun g x ↦ ⟨g • x, fun h ↦ by
    simpa [mul_smul] using congr(g • $(x.2 ⟨_, ‹H.Normal›.conj_mem' _ h.2 g⟩))⟩) (by
    rintro _ a ⟨⟨⟨b⟩, hb⟩, rfl⟩
    ext c
    simpa [mul_smul] using congr(a • $(c.2 ⟨b, hb⟩)))
  one_smul b := Subtype.ext (one_smul G b.1)
  mul_smul := Quotient.ind₂ fun _ _ _ ↦ Subtype.ext (mul_smul _ _ _)
  smul_zero := Quotient.ind fun _ ↦ Subtype.ext (smul_zero _)
  smul_add := Quotient.ind fun _ _ _ ↦ Subtype.ext (smul_add _ _ _)
  smul_one := Quotient.ind fun _ ↦ Subtype.ext (smul_one _)
  smul_mul := Quotient.ind fun _ _ _ ↦ Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance (H : Subgroup G) [H.Normal] :
    MulSemiringAction (G ⧸ H) (FixedPoints.subalgebra A B H) :=
  inferInstanceAs (MulSemiringAction (G ⧸ H) (FixedPoints.subring B H))

instance (H : Subgroup G) [H.Normal] :
    SMulCommClass (G ⧸ H) A (FixedPoints.subalgebra A B H)  where
  smul_comm := Quotient.ind fun g r h ↦ Subtype.ext (smul_comm g r h.1)

instance (H : Subgroup G) [H.Normal] [Algebra.IsInvariant A B G] :
    Algebra.IsInvariant A (FixedPoints.subalgebra A B H) (G ⧸ H) where
  isInvariant x hx := by
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) x.1
      (fun g ↦ congr_arg Subtype.val (hx g))
    exact ⟨y, Subtype.ext hy⟩

end Quotient

section transitivity

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

namespace MulSemiringAction

open Polynomial

variable {B} [Fintype G]

/-- Characteristic polynomial of a finite group action on a ring. -/
noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))

theorem charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b)) := rfl

theorem charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b) := by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

theorem monic_charpoly (b : B) : (charpoly G b).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)

theorem eval_charpoly (b : B) : (charpoly G b).eval b = 0 := by
  rw [charpoly_eq, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul, eval_sub, eval_C, eval_X, sub_self]

variable {G}

theorem smul_charpoly (b : B) (g : G) : g • (charpoly G b) = charpoly G b := by
  rw [charpoly_eq_prod_smul, Finset.smul_prod_perm]

theorem smul_coeff_charpoly (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, smul_charpoly]

end MulSemiringAction

namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable [IsInvariant A B G]

theorem charpoly_mem_lifts [Fintype G] (b : B) :
    charpoly G b ∈ Polynomial.lifts (algebraMap A B) :=
  (charpoly G b).lifts_iff_coeff_lifts.mpr fun n ↦ isInvariant _ (smul_coeff_charpoly b n)

theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (monic_charpoly G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, eval_charpoly]⟩

/-- `G` acts transitively on the prime ideals of `B` above a given prime ideal of `A`. -/
theorem exists_smul_of_under_eq [Finite G] [SMulCommClass G A B]
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
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((P.under_smul A g).trans hPQ).symm
  exact ⟨g, le_antisymm hg (smul_eq_of_le_smul (hg.trans hg') ▸ hg')⟩

theorem orbit_eq_primesOver [Finite G] [SMulCommClass G A B] (P : Ideal A) (Q : Ideal B)
    [hP : Q.LiesOver P] [hQ : Q.IsPrime] : MulAction.orbit G Q = P.primesOver B := by
  refine Set.ext fun R ↦ ⟨fun ⟨g, hg⟩ ↦ hg ▸ ⟨hQ.smul g, hP.smul g⟩, fun h ↦ ?_⟩
  have : R.IsPrime := h.1
  obtain ⟨g, hg⟩ := exists_smul_of_under_eq A B G Q R (hP.over.symm.trans h.2.over)
  exact ⟨g, hg.symm⟩

end Algebra.IsInvariant

end transitivity

section surjectivity

open FaithfulSMul IsScalarTower Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [Algebra (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]
  [Algebra.IsInvariant A B G]

/-- A technical lemma for `fixed_of_fixed1`. -/
private theorem fixed_of_fixed1_aux1 [DecidableEq (Ideal B)] :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ a ∉ Q ∧
    ∀ g : G, algebraMap B (B ⧸ Q) (g • b) = algebraMap B (B ⧸ Q) (if g • Q = Q then a else 0) := by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := Finset.inf {g : G | g • Q ≠ Q} (fun g ↦ g • Q)
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
      (Polynomial.map_monic_ne_zero (MulSemiringAction.monic_charpoly G b)) 0
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
    · rw [map_zero, eq_comm, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
  have hf : f.eval b = 0 := MulSemiringAction.eval_charpoly G b
  have hr : r.eval b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hbQ ⊢
    replace hf := congrArg (algebraMap B (B ⧸ Q)) hf
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map] at hf ⊢
    rwa [map_zero, hq, ← hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (pow_ne_zero _ hbQ)] at hf
  let a := f.coeff j
  have ha : ∀ g : G, g • a = a := MulSemiringAction.smul_coeff_charpoly b j
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

/-- A technical lemma for `fixed_of_fixed1`. -/
private theorem fixed_of_fixed1_aux2 [DecidableEq (Ideal B)] (b₀ : B)
    (hx : ∀ g : G, g • Q = Q → algebraMap B (B ⧸ Q) (g • b₀) = algebraMap B (B ⧸ Q) b₀) :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ a ∉ Q ∧
    (∀ g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a * b₀ else 0)) := by
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g ↦ ?_⟩
  rw [smul_mul', map_mul, hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]

/-- A technical lemma for `fixed_of_fixed1`. -/
private theorem fixed_of_fixed1_aux3 [NoZeroDivisors B] {b : B} {i j : ℕ} {p : Polynomial A}
    (h : p.map (algebraMap A B) = (X - C b) ^ i * X ^ j) (f : B ≃ₐ[A] B) (hi : i ≠ 0) :
    f b = b := by
  by_cases ha : b = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval b) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom, map_map, f.toAlgHom.comp_algebraMap, h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hi, zero_mul,
    zero_eq_mul, or_iff_left (pow_ne_zero j ha), pow_eq_zero_iff hi, sub_eq_zero] at hf
  exact hf.symm

/-- This theorem will be made redundant by `IsFractionRing.stabilizerHom_surjective`. -/
private theorem fixed_of_fixed1 [NoZeroSMulDivisors (B ⧸ Q) L] (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, Ideal.Quotient.stabilizerHom Q P G g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  classical
  cases nonempty_fintype G
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := fixed_of_fixed1_aux2 G Q b₀ (fun g hg ↦ hx ⟨g, hg⟩)
  obtain ⟨M, key⟩ := (mem_lifts _).mp (Algebra.IsInvariant.charpoly_mem_lifts A B G b)
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
  replace key := fixed_of_fixed1_aux3 key f (Finset.card_ne_zero_of_mem
    (Finset.mem_filter.mpr ⟨Finset.mem_univ 1, one_smul G Q⟩))
  simp only [map_mul] at key
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) a ha1
  rwa [← algebraMap_apply A B (B ⧸ Q), algebraMap_apply A (A ⧸ P) (B ⧸ Q),
      ← algebraMap_apply, algebraMap_apply (A ⧸ P) K L, f.commutes, mul_right_inj'] at key
  rwa [← algebraMap_apply, algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      ← algebraMap_apply A (A ⧸ P) (B ⧸ Q), algebraMap_apply A B (B ⧸ Q),
      Ne, algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

variable [IsFractionRing (A ⧸ P) K] [IsFractionRing (B ⧸ Q) L]

/-- If `Q` lies over `P`, then the stabilizer of `Q` acts on `Frac(B/Q)/Frac(A/P)`. -/
noncomputable def IsFractionRing.stabilizerHom : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) :=
  MonoidHom.comp (IsFractionRing.fieldEquivOfAlgEquivHom K L) (Ideal.Quotient.stabilizerHom Q P G)

/-- This theorem will be made redundant by `IsFractionRing.stabilizerHom_surjective`. -/
private theorem fixed_of_fixed2 (f : L ≃ₐ[K] L) (x : L)
    (hx : ∀ g : MulAction.stabilizer G Q, IsFractionRing.stabilizerHom G P Q K L g x = x) :
    f x = x := by
  obtain ⟨_⟩ := nonempty_fintype G
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  have : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  replace ha : algebraMap (A ⧸ P) L a ≠ 0 := by
    rwa [Ne, algebraMap_apply (A ⧸ P) K L, algebraMap_eq_zero_iff, algebraMap_eq_zero_iff]
  replace hy : algebraMap (B ⧸ Q) L y ≠ 0 :=
    mt (algebraMap_eq_zero_iff (B ⧸ Q) L).mp (nonZeroDivisors.ne_zero hy)
  replace h : algebraMap (B ⧸ Q) L x / algebraMap (B ⧸ Q) L y =
      algebraMap (B ⧸ Q) L b / algebraMap (A ⧸ P) L a := by
    rw [mul_comm, Algebra.smul_def, mul_comm] at h
    rw [div_eq_div_iff hy ha, ← map_mul, ← h, map_mul, ← algebraMap_apply]
  simp only [h, map_div₀, algebraMap_apply (A ⧸ P) K L, AlgEquiv.commutes] at hx ⊢
  simp only [← algebraMap_apply, div_left_inj' ha] at hx ⊢
  exact fixed_of_fixed1 G P Q K L f b (fun g ↦ IsFractionRing.injective (B ⧸ Q) L
    ((IsFractionRing.fieldEquivOfAlgEquiv_algebraMap K L L
      (Ideal.Quotient.stabilizerHom Q P G g) b).symm.trans (hx g)))

/-- The stabilizer subgroup of `Q` surjects onto `Aut(Frac(B/Q)/Frac(A/P))`. -/
theorem IsFractionRing.stabilizerHom_surjective :
    Function.Surjective (stabilizerHom G P Q K L) := by
  let _ := MulSemiringAction.compHom L (stabilizerHom G P Q K L)
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x ↦ fixed_of_fixed2 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

/-- The stabilizer subgroup of `Q` surjects onto `Aut((B/Q)/(A/P))`. -/
theorem Ideal.Quotient.stabilizerHom_surjective :
    Function.Surjective (Ideal.Quotient.stabilizerHom Q P G) := by
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
  let _ := FractionRing.liftAlgebra (A ⧸ P) (FractionRing (B ⧸ Q))
  have key := IsFractionRing.stabilizerHom_surjective G P Q
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q))
  rw [IsFractionRing.stabilizerHom, MonoidHom.coe_comp] at key
  exact key.of_comp_left (IsFractionRing.fieldEquivOfAlgEquivHom_injective (A ⧸ P) (B ⧸ Q)
    (FractionRing (A ⧸ P)) (FractionRing (B ⧸ Q)))

end surjectivity

section normal

variable {A B k : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Finite G] [Group G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.LiesOver P]
  [CommRing k] [Algebra (A ⧸ P) k] [Algebra (B ⧸ Q) k] [IsScalarTower (A ⧸ P) (B ⧸ Q) k]
  [IsDomain k] [FaithfulSMul (B ⧸ Q) k]

include G in
/--
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.

This is basically the fact that `L/K` normal implies `κ(Q)/κ(P)` normal in the Galois setting.
-/
lemma Ideal.Quotient.exists_algHom_fixedPoint_quotient_under
    (σ : k →ₐ[A ⧸ P] k) :
    ∃ τ : (B ⧸ Q) →ₐ[A ⧸ P] B ⧸ Q, ∀ x : B ⧸ Q,
      algebraMap _ _ (τ x) = σ (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) →ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  suffices (σ.comp f).range ≤ f.range by
    let e := (AlgEquiv.ofInjective f hf)
    exact ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion this)).comp (σ.comp f).rangeRestrict,
      fun x ↦ congr_arg Subtype.val (e.apply_symm_apply ⟨_, _⟩)⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  cases nonempty_fintype G
  algebraize [(algebraMap (A ⧸ P) k).comp (algebraMap A (A ⧸ P)),
    (algebraMap (B ⧸ Q) k).comp (algebraMap B (B ⧸ Q))]
  haveI : IsScalarTower A (B ⧸ Q) k := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (mk P x))
  haveI : IsScalarTower A B k := .of_algebraMap_eq fun x ↦
    (IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) k (mk P x))
  obtain ⟨P, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G x
  have : Polynomial.aeval x P = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map,
      ← Polynomial.coe_mapRingHom (R := A), hp, MulSemiringAction.eval_charpoly]
  have : Polynomial.aeval (σ (algebraMap (B ⧸ Q) k (mk _ x))) P = 0 := by
    refine (DFunLike.congr_fun (Polynomial.aeval_algHom ((σ.restrictScalars A).comp
      (IsScalarTower.toAlgHom A (B ⧸ Q) k)) _) P).trans ?_
    rw [AlgHom.comp_apply, ← algebraMap_eq, Polynomial.aeval_algebraMap_apply, this,
      map_zero, map_zero]
  rw [← Polynomial.aeval_map_algebraMap B, ← Polynomial.coe_mapRingHom, hp] at this
  obtain ⟨τ, hτ⟩ : ∃ τ : G, σ (algebraMap _ _ x) = algebraMap _ _ (τ • x) := by
    simpa [MulSemiringAction.charpoly, sub_eq_zero, Finset.prod_eq_zero_iff] using this
  exact ⟨Ideal.Quotient.mk _ (τ • x), hτ.symm⟩

include G in
/--
For any domain `k` containing `B ⧸ Q`,
any endomorphism of `k` can be restricted to an endomorphism of `B ⧸ Q`.
-/
lemma Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under
    (σ : k ≃ₐ[A ⧸ P] k) :
    ∃ τ : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q, ∀ x : B ⧸ Q,
      algebraMap _ _ (τ x) = σ (algebraMap (B ⧸ Q) k x) := by
  let f : (B ⧸ Q) →ₐ[A ⧸ P] k := IsScalarTower.toAlgHom _ _ _
  have hf : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨τ₁, h₁⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.toAlgHom
  obtain ⟨τ₂, h₂⟩ := Ideal.Quotient.exists_algHom_fixedPoint_quotient_under G P Q σ.symm.toAlgHom
  refine ⟨{ __ := τ₁, invFun := τ₂, left_inv := ?_, right_inv := ?_ }, h₁⟩
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, e⟩ := Ideal.Quotient.mk_surjective (τ₁ (Ideal.Quotient.mk Q x))
    apply hf
    dsimp [f] at h₁ h₂ ⊢
    refine .trans ?_ (σ.symm_apply_apply _)
    rw [← h₁, ← e, h₂]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, e⟩ := Ideal.Quotient.mk_surjective (τ₂ (Ideal.Quotient.mk Q x))
    apply hf
    dsimp [f] at h₁ h₂ ⊢
    refine .trans ?_ (σ.apply_symm_apply _)
    rw [← h₂, ← e, h₁]

end normal
