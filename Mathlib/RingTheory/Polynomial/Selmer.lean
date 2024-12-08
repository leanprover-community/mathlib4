/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/

section Inertia

open scoped Pointwise

-- PRed
namespace Algebra

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- An action of a group `G` on an extension of rings `B/A` is invariant if every fixed point of
`B` lies in the image of `A`. The converse statement that every point in the image of `A` is fixed
by `G` is `smul_algebraMap` (assuming `SMulCommClass A B G`). -/
@[mk_iff] class IsInvariant : Prop where
  isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b

end Algebra

section Galois

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]

include A in
noncomputable def IsIntegralClosure.MulSemiringAction [FiniteDimensional K L] :
    MulSemiringAction (L ≃ₐ[K] L) B := by
  let f : (L ≃ₐ[K] L) →* (B ≃ₐ[A] B) := galRestrict A K L B
  exact MulSemiringAction.compHom B f

instance IsIntegralClosure.SMulCommClass [FiniteDimensional K L] :
    let _ := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass (L ≃ₐ[K] L) A B := by
  intro
  exact ⟨fun f ↦ map_smul (galRestrict A K L B f)⟩

instance Algebra.isInvariant_of_isGalois [FiniteDimensional K L] [h : IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Algebra.IsInvariant A B (L ≃ₐ[K] L) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine ⟨fun b hb ↦ ?_⟩
  replace hb : algebraMap B L b ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rintro ⟨g, -⟩
    exact (algebraMap_galRestrict_apply A g b).symm.trans (congrArg (algebraMap B L) (hb g))
  have key := ((IsGalois.tfae (F := K) (E := L)).out 0 1).mp h
  rw [key, IntermediateField.mem_bot] at hb
  obtain ⟨k, hk⟩ := hb
  have hb : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  rw [← isIntegral_algebraMap_iff (NoZeroSMulDivisors.algebraMap_injective B L), ← hk,
    isIntegral_algebraMap_iff (NoZeroSMulDivisors.algebraMap_injective K L)] at hb
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L,
    (NoZeroSMulDivisors.algebraMap_injective B L).eq_iff] at hk
  exact ⟨a, hk⟩

end Galois

section transitivity

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

-- PRed
namespace MulSemiringAction

open Polynomial

variable {B} [Fintype G]

/-- Characteristic polynomial of a finite group action on a ring. -/
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

theorem charpoly_coeff_smul (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, charpoly_smul]

end MulSemiringAction

namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable [IsInvariant A B G]

-- PRed
theorem charpoly_mem_lifts [Fintype G] (b : B) :
    charpoly G b ∈ Polynomial.lifts (algebraMap A B) :=
  (charpoly G b).lifts_iff_coeff_lifts.mpr fun n ↦ isInvariant _ (charpoly_coeff_smul b n)

-- PRed
include G in
theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (charpoly_monic G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, charpoly_eval]⟩

/-- `G` acts transitively on primes of `B` above the same prime of `A`. -/
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

end Algebra.IsInvariant

end transitivity

section surjectivity

open IsScalarTower NoZeroSMulDivisors Polynomial

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
  revert hx
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  intro hx
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
  have : P.IsPrime := Ideal.over_def Q P ▸ Ideal.IsPrime.under A Q
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

theorem IsFractionRing.stabilizerHom_surjective :
    Function.Surjective (stabilizerHom G P Q K L) := by
  let _ := MulSemiringAction.compHom L (stabilizerHom G P Q K L)
  intro f
  obtain ⟨g, hg⟩ := FixedPoints.toAlgAut_surjective (MulAction.stabilizer G Q) L
    (AlgEquiv.ofRingEquiv (f := f) (fun x ↦ fixed_of_fixed2 G P Q K L f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

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

section inertia

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L]
  [FiniteDimensional K L] [IsGalois K L]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

noncomputable def inertiaSubgroup :=
  let _ := IsIntegralClosure.MulSemiringAction A K L B
  (Ideal.Quotient.stabilizerHom Q P (L ≃ₐ[K] L)).ker.map
    (MulAction.stabilizer (L ≃ₐ[K] L) Q).subtype

end inertia

end Inertia

namespace Polynomial

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [this, pow_zero, pow_one, eq_self_iff_true, or_true, true_or]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, self_eq_add_left] at h1)
  · exact one_ne_zero (by rwa [key, self_eq_add_right] at h1)
  · exact z_ne_zero (pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ, Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).isPrimitive

open Equiv Pointwise

open IntermediateField

attribute [local instance] Gal.splits_ℚ_ℂ

instance {α β : Type*} [Monoid α] [Subsingleton β] [MulAction α β] :
    MulAction.IsPretransitive α β :=
  ⟨fun _ _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩

open NumberField

variable {K : Type*} [Field K] [NumberField K]

noncomputable def inertiaSubgroup  (q : Ideal (𝓞 K)) : Subgroup (K ≃ₐ[ℚ] K) :=
  _root_.inertiaSubgroup ℤ ℚ K (𝓞 K) (q.under ℤ) q

variable (K) [IsGalois ℚ K]

theorem keythm : ⨆ (q : Ideal (𝓞 K)) (hq : q.IsMaximal), inertiaSubgroup q = ⊤ := by
  -- key idea: fixed field of this subgroup has no ramified primes
  let G := K ≃ₐ[ℚ] K
  let H := ⨆ (q : Ideal (𝓞 K)) (hq : q.IsMaximal), inertiaSubgroup q
  let F := fixedField H
  change H = ⊤
  suffices h : F = ⊥ by
    rw [← fixingSubgroup_fixedField H]
    change fixingSubgroup F = ⊤
    rw [h]
    -- easy lemma for mathlib
    ext
    simp [IntermediateField.fixingSubgroup, _root_.fixingSubgroup, fixingSubmonoid, mem_bot]
  have key : ∀ (q : Ideal (𝓞 F)) (hq : q.IsMaximal), inertiaSubgroup q = ⊥ := by
    sorry
  suffices h : ¬ 1 < Module.finrank ℚ F by
    rw [← IntermediateField.finrank_eq_one_iff]
    rw [not_lt] at h
    refine le_antisymm h ?_
    rw [Nat.succ_le_iff]
    refine @Module.finrank_pos ℚ F _ _ _ _ _ ?_ _
    exact Module.Free.noZeroSMulDivisors ℚ ↥F
  intro h
  -- maybe better to use discriminant ideal here?
  replace h := NumberField.abs_discr_gt_two h
  sorry

theorem X_pow_sub_X_sub_one_gal :
    Function.Bijective (Gal.galActionHom (X ^ n - X - 1 : ℚ[X]) ℂ) := by
  let f : ℚ[X] := X ^ n - X - 1
  change Function.Bijective (Gal.galActionHom f ℂ)
  have : MulAction.IsPretransitive f.Gal (f.rootSet ℂ) := by
    rcases eq_or_ne n 1 with rfl | hn
    · have : IsEmpty (rootSet f ℂ) := by simp [f]
      infer_instance
    exact Gal.galAction_isPretransitive _ _ (X_pow_sub_X_sub_one_irreducible_rat hn)
  let K := f.SplittingField
  have : NumberField K := by constructor
  have : IsGalois ℚ K := by constructor
  let R := 𝓞 K
  let S0 : Set f.Gal := ⋃ (q : Ideal R) (hq : q.IsMaximal),
    (↑(inertiaSubgroup q : Set (f.SplittingField ≃ₐ[ℚ] f.SplittingField)))
  let S : Set f.Gal := S0 \ {1}
  have hS0 : Subgroup.closure S0 = ⊤ := by
    simp only [S0, Subgroup.closure_iUnion, Subgroup.closure_eq]
    exact keythm K
  have hS1 : Subgroup.closure S = ⊤ := by
    have h : Subgroup.closure (S0 ∩ {1}) = ⊥ := by
      rw [eq_bot_iff, ← Subgroup.closure_singleton_one]
      exact Subgroup.closure_mono Set.inter_subset_right
    rw [← hS0, ← Set.diff_union_inter S0 {1}, Subgroup.closure_union, h, sup_bot_eq]
  have hS2 : ∀ σ ∈ S, Perm.IsSwap (MulAction.toPermHom f.Gal (f.rootSet ℂ) σ) := by
    rintro σ ⟨hσ, hσ1 : σ ≠ 1⟩
    rw [Set.mem_iUnion] at hσ
    obtain ⟨q, hσ⟩ := hσ
    rw [Set.mem_iUnion] at hσ
    obtain ⟨hq, hσ⟩ := hσ
    rw [SetLike.mem_coe] at hσ
    let F := R ⧸ q
    let π : R →+* F := Ideal.Quotient.mk q
    have : Field F := Ideal.Quotient.field q
    -- finite field, might not need to consider the characteristic
    -- reduce to action on roots in R
    sorry
  exact ⟨Gal.galActionHom_injective f ℂ, surjective_of_isSwap_of_isPretransitive S hS2 hS1⟩

  -- have : ∀ p : Nat.Primes, ∀ q : factors (map (algebraMap ℤ R) p)
  -- roots lie in the ring of integers OK
  -- if q is a prime idea of OK, then there is a ring homomorphism to the finite field OK/q
  -- the whole Galois group acts on OK
  -- the decomposition group acts on OK/q
  -- the inertia group acts trivially on OK/q
  --
  -- there are n roots in OK
  -- there are n or n-1 roots in OK/q (possible double root)
  -- Let σ(x) = x (mod p) for all x in OK
  -- If there are n roots in OK/q, then σ must act trivially on the roots in OK
  -- If x and y collapse (mod p), then maybe σ swaps x and y, but no more
  -- Now run through p's and σ's

  -- the key is proving closure/generating
  -- we need to know that if a subgroup contains every σ(x) = x (mod p) for every p, then it's ⊤
  -- we need to know that if a subfield is fixed by ..., then it's ⊥
  -- key facts from algebraic number theory: p divides discriminant implies ramified
  -- ramified means there exists σ(x) = x (mod p)

end Polynomial
