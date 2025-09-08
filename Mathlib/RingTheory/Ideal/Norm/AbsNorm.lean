/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.Algebra.CharP.Quotient
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Basis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-!

# Ideal norms

This file defines the absolute ideal norm `Ideal.absNorm (I : Ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

* `Submodule.cardQuot (S : Submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
  This maps `⊥` to `0` and `⊤` to `1`.
* `Ideal.absNorm (I : Ideal R)`: the absolute ideal norm, defined as
  the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.

## Main results

* `map_mul Ideal.absNorm`: multiplicativity of the ideal norm is bundled in
  the definition of `Ideal.absNorm`
* `Ideal.natAbs_det_basis_change`: the ideal norm is given by the determinant
  of the basis change matrix
* `Ideal.absNorm_span_singleton`: the ideal norm of a principal ideal is the
  norm of its generator
-/

open Module
open scoped nonZeroDivisors

section abs_norm

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

section

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `Ideal.absNorm`.
-/
noncomputable def cardQuot (S : Submodule R M) : ℕ :=
  AddSubgroup.index S.toAddSubgroup

theorem cardQuot_apply (S : Submodule R M) : cardQuot S = Nat.card (M ⧸ S) := by
  rfl

variable (R M)

@[simp]
theorem cardQuot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0 :=
  AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite

@[simp]
theorem cardQuot_top : cardQuot (⊤ : Submodule R M) = 1 :=
  AddSubgroup.index_top

variable {R M}

@[simp]
theorem cardQuot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤ :=
  AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])

end

end Submodule

section RingOfIntegers

variable {S : Type*} [CommRing S]

open Submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
theorem cardQuot_mul_of_coprime
    {I J : Ideal S} (coprime : IsCoprime I J) : cardQuot (I * J) = cardQuot I * cardQuot J := by
  rw [cardQuot_apply, cardQuot_apply, cardQuot_apply,
    Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv,
    Nat.card_prod]

/-- If the `d` from `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.mul_add_mem_pow_succ_inj (P : Ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
    (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1)) (h : d - d' ∈ P) :
    a * d + e - (a * d' + e') ∈ P ^ (i + 1) := by
  have : a * d - a * d' ∈ P ^ (i + 1) := by
    simp only [← mul_sub]
    exact Ideal.mul_mem_mul a_mem h
  convert Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
  ring

section PPrime

variable {P : Ideal S} [P_prime : P.IsPrime]

/-- If `a ∈ P^i \ P^(i+1)` and `c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`Ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] (hP : P ≠ ⊥)
    {i : ℕ} (a c : S) (a_mem : a ∈ P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
    ∃ d : S, ∃ e ∈ P ^ (i + 1), a * d + e = c := by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1) by
    rw [eq_b] at c_mem
    simp only [mul_comm a]
    exact Ideal.mem_span_singleton_sup.mp c_mem
  refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
    (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a_mem))
      (Ideal.pow_succ_lt_pow hP i).le)).symm
  contrapose! a_notMem with this
  rw [this]
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩

theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P : Ideal S} [P_prime : P.IsPrime]
    (hP : P ≠ ⊥) {i : ℕ} {a b : S} (a_notMem : a ∉ P ^ (i + 1)) (ab_mem : a * b ∈ P ^ (i + 1)) :
    b ∈ P := by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem

/-- The choice of `d` in `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] (hP : P ≠ ⊥)
    {i : ℕ} (a d d' e e' : S)
    (a_notMem : a ∉ P ^ (i + 1)) (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
    (h : a * d + e - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P := by
  have h' : a * (d - d') ∈ P ^ (i + 1) := by
    convert Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
theorem cardQuot_pow_of_prime [IsDedekindDomain S] (hP : P ≠ ⊥) {i : ℕ} :
    cardQuot (P ^ i) = cardQuot P ^ i := by
  induction' i with i ih
  · simp
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkQ (P ^ i) ≃ S ⧸ P by
    rw [pow_succ' (cardQuot P), ← ih, cardQuot_apply (P ^ i.succ), ←
      card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le, cardQuot_apply (P ^ i),
      cardQuot_apply P, Nat.card_congr hquot]
  choose a a_mem a_notMem using SetLike.exists_of_lt this
  choose f g hg hf using fun c (hc : c ∈ P ^ i) =>
    Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_notMem hc
  choose k hk_mem hk_eq using fun c' (hc' : c' ∈ map (mkQ (P ^ i.succ)) (P ^ i)) =>
    Submodule.mem_map.mp hc'
  refine Equiv.ofBijective (fun c' => Quotient.mk'' (f (k c' c'.prop) (hk_mem c' c'.prop))) ⟨?_, ?_⟩
  · rintro ⟨c₁', hc₁'⟩ ⟨c₂', hc₂'⟩ h
    rw [Subtype.mk_eq_mk, ← hk_eq _ hc₁', ← hk_eq _ hc₂', mkQ_apply, mkQ_apply,
      Submodule.Quotient.eq, ← hf _ (hk_mem _ hc₁'), ← hf _ (hk_mem _ hc₂')]
    refine Ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) ?_
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.mk''_eq_mk,
      Submodule.Quotient.eq] using h
  · intro d'
    refine Quotient.inductionOn' d' fun d => ?_
    have hd' := (mem_map (f := mkQ (P ^ i.succ))).mpr ⟨a * d, Ideal.mul_mem_right d _ a_mem, rfl⟩
    refine ⟨⟨_, hd'⟩, ?_⟩
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq]
    refine
      Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_notMem (hg _ (hk_mem _ hd')) (zero_mem _) ?_
    rw [hf, add_zero]
    exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')

end PPrime

/-- Multiplicativity of the ideal norm in number rings. -/
theorem cardQuot_mul [IsDedekindDomain S] [Module.Free ℤ S] (I J : Ideal S) :
    cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis ℤ S
  haveI : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i hI =>
        have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
        cardQuot_pow_of_prime hI.ne_zero)
      fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
        (Ideal.isUnit_iff.mp
          (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))

/-- The absolute norm of the ideal `I : Ideal R` is the cardinality of the quotient `R ⧸ I`. -/
noncomputable def Ideal.absNorm [Nontrivial S] [IsDedekindDomain S] [Module.Free ℤ S] :
    Ideal S →*₀ ℕ where
  toFun := Submodule.cardQuot
  map_mul' I J := by rw [cardQuot_mul]
  map_one' := by rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by
    have : Infinite S := Module.Free.infinite ℤ S
    rw [Ideal.zero_eq_bot, cardQuot_bot]

namespace Ideal

variable [Nontrivial S] [IsDedekindDomain S] [Module.Free ℤ S]

theorem absNorm_apply (I : Ideal S) : absNorm I = cardQuot I := rfl

@[simp]
theorem absNorm_bot : absNorm (⊥ : Ideal S) = 0 := by rw [← Ideal.zero_eq_bot, map_zero]

@[simp]
theorem absNorm_top : absNorm (⊤ : Ideal S) = 1 := by rw [← Ideal.one_eq_top, map_one]

@[simp]
theorem absNorm_eq_one_iff {I : Ideal S} : absNorm I = 1 ↔ I = ⊤ := by
  rw [absNorm_apply, cardQuot_eq_one_iff]

theorem absNorm_ne_zero_iff (I : Ideal S) : Ideal.absNorm I ≠ 0 ↔ Finite (S ⧸ I) :=
  ⟨fun h => Nat.finite_of_card_ne_zero h, fun h =>
    (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩

theorem absNorm_dvd_absNorm_of_le {I J : Ideal S} (h : J ≤ I) : Ideal.absNorm I ∣ Ideal.absNorm J :=
  map_dvd absNorm (dvd_iff_le.mpr h)

theorem irreducible_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    Irreducible I :=
  irreducible_iff.mpr
    ⟨fun h =>
      hI.not_isUnit (by simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using h),
      by
      rintro a b rfl
      simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using
        hI.isUnit_or_isUnit (map_mul absNorm a b)⟩

theorem isPrime_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    I.IsPrime :=
  isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))

theorem prime_of_irreducible_absNorm_span {a : S} (ha : a ≠ 0)
    (hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set S)))) : Prime a :=
  (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)

theorem absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) ∈ I := by
  rw [absNorm_apply, cardQuot, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    Quotient.index_eq_zero]

theorem span_singleton_absNorm_le (I : Ideal S) : Ideal.span {(Ideal.absNorm I : S)} ≤ I := by
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.absNorm_mem I]

theorem span_singleton_absNorm {I : Ideal S} (hI : (Ideal.absNorm I).Prime) :
    Ideal.span (singleton (Ideal.absNorm I : ℤ)) = I.comap (algebraMap ℤ S) := by
  have : Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I : ℤ))) := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ← Nat.prime_iff_prime_int]
  apply (this.isMaximal _).eq_of_le
  · exact ((isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).mpr hI)).comap (algebraMap ℤ S)).ne_top
  · rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
    exact absNorm_mem I
  · rw [Ne, span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hI.ne_zero

variable [Module.Finite ℤ S]

/-- Let `e : S ≃ I` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the norm of `I` is given by taking the determinant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result. -/
theorem natAbs_det_equiv (I : Ideal S) {E : Type*} [EquivLike E S I] [AddEquivClass E S I] (e : E) :
    Int.natAbs
        (LinearMap.det
          ((Submodule.subtype I).restrictScalars ℤ ∘ₗ AddMonoidHom.toIntLinearMap (e : S →+ I))) =
      Ideal.absNorm I := by
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥
  · subst hI
    have : (1 : S) ≠ 0 := one_ne_zero
    have : (1 : S) = 0 := EquivLike.injective e (Subsingleton.elim _ _)
    contradiction
  exact Submodule.natAbs_det_equiv (I.restrictScalars ℤ) e

/-- Let `b` be a basis for `S` over `ℤ` and `bI` a basis for `I` over `ℤ` of the same dimension.
Then an alternative way to compute the norm of `I` is given by taking the determinant of `bI`
over `b`. -/
theorem natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ S)
    (I : Ideal S) (bI : Basis ι ℤ I) : (b.det ((↑) ∘ bI)).natAbs = Ideal.absNorm I :=
  Submodule.natAbs_det_basis_change b (I.restrictScalars ℤ) bI

@[simp]
theorem absNorm_span_singleton (r : S) :
    absNorm (span ({r} : Set S)) = (Algebra.norm ℤ r).natAbs := by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · simp only [hr, Ideal.span_zero, Ideal.absNorm_bot,
      LinearMap.det_zero'', Set.singleton_zero, map_zero, Int.natAbs_zero]
  letI := Ideal.finiteQuotientOfFreeOfNeBot (span {r}) (mt span_singleton_eq_bot.mp hr)
  let b := Module.Free.chooseBasis ℤ S
  rw [← natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]
  congr
  refine b.ext fun i => ?_
  simp

theorem absNorm_dvd_norm_of_mem {I : Ideal S} {x : S} (h : x ∈ I) :
    ↑(Ideal.absNorm I) ∣ Algebra.norm ℤ x := by
  rw [← Int.dvd_natAbs, ← absNorm_span_singleton x, Int.natCast_dvd_natCast]
  exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)

@[simp]
theorem absNorm_span_insert (r : S) (s : Set S) :
    absNorm (span (insert r s)) ∣ gcd (absNorm (span s)) (Algebra.norm ℤ r).natAbs :=
  (dvd_gcd_iff _ _ _).mpr
    ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
      _root_.trans
        (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
        (by rw [absNorm_span_singleton])⟩

theorem absNorm_eq_zero_iff {I : Ideal S} : Ideal.absNorm I = 0 ↔ I = ⊥ := by
  constructor
  · intro hI
    rw [← le_bot_iff]
    intros x hx
    rw [mem_bot, ← Algebra.norm_eq_zero_iff (R := ℤ), ← Int.natAbs_eq_zero,
      ← Ideal.absNorm_span_singleton, ← zero_dvd_iff, ← hI]
    apply Ideal.absNorm_dvd_absNorm_of_le
    rwa [Ideal.span_singleton_le_iff_mem]
  · rintro rfl
    exact absNorm_bot

theorem absNorm_ne_zero_iff_mem_nonZeroDivisors {I : Ideal S} :
    absNorm I ≠ 0 ↔ I ∈ (Ideal S)⁰ := by
  simp_rw [ne_eq, Ideal.absNorm_eq_zero_iff, mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot]

theorem absNorm_pos_iff_mem_nonZeroDivisors {I : Ideal S} :
    0 < absNorm I ↔ I ∈ (Ideal S)⁰ := by
  rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors, Nat.pos_iff_ne_zero]

theorem absNorm_ne_zero_of_nonZeroDivisors (I : (Ideal S)⁰) : absNorm (I : Ideal S) ≠ 0 :=
  absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

theorem absNorm_pos_of_nonZeroDivisors (I : (Ideal S)⁰) : 0 < absNorm (I : Ideal S) :=
  absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

theorem finite_setOf_absNorm_eq [CharZero S] (n : ℕ) :
    {I : Ideal S | Ideal.absNorm I = n}.Finite := by
  obtain hn | hn := Nat.eq_zero_or_pos n
  · simp only [hn, absNorm_eq_zero_iff, Set.setOf_eq_eq_singleton, Set.finite_singleton]
  · let f := fun I : Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
    refine Set.Finite.of_finite_image (f := f) ?_ ?_
    · suffices Finite (S ⧸ @Ideal.span S _ {↑n}) by
        let g := ((↑) : Ideal (S ⧸ @Ideal.span S _ {↑n}) → Set (S ⧸ @Ideal.span S _ {↑n}))
        refine Set.Finite.of_finite_image (f := g) ?_ SetLike.coe_injective.injOn
        exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      rw [← absNorm_ne_zero_iff, absNorm_span_singleton]
      simpa only [Ne, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff, Nat.cast_eq_zero] using
        ne_of_gt hn
    · intro I hI J hJ h
      rw [← comap_map_mk (span_singleton_absNorm_le I), ← hI.symm, ←
        comap_map_mk (span_singleton_absNorm_le J), ← hJ.symm]
      congr

theorem finite_setOf_absNorm_le [CharZero S] (n : ℕ) :
    {I : Ideal S | Ideal.absNorm I ≤ n}.Finite := by
  rw [show {I : Ideal S | Ideal.absNorm I ≤ n} =
    (⋃ i ∈ Set.Icc 0 n, {I : Ideal S | Ideal.absNorm I = i}) by ext; simp]
  refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOf_absNorm_eq i)

theorem finite_setOf_absNorm_le₀ [CharZero S] (n : ℕ) :
    {I : (Ideal S)⁰ | Ideal.absNorm (I : Ideal S) ≤ n}.Finite := by
  have : Finite {I : Ideal S // I ∈ (Ideal S)⁰ ∧ absNorm I ≤ n} :=
    (finite_setOf_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I ↦ absNorm I ≤ n)).symm

theorem card_norm_le_eq_card_norm_le_add_one (n : ℕ) [CharZero S] :
    Nat.card {I : Ideal S // absNorm I ≤ n} =
      Nat.card {I : (Ideal S)⁰ // absNorm (I : Ideal S) ≤ n} + 1 := by
  classical
  have : Finite {I : Ideal S // I ∈ (Ideal S)⁰ ∧ absNorm I ≤ n} :=
    (finite_setOf_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  have : Finite {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I ≤ n} :=
    (finite_setOf_absNorm_le n).subset fun _ ⟨_, h⟩ ↦ h
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ I ∈ (Ideal S)⁰)
    (fun I ↦ absNorm I ≤ n))]
  let e : {I : Ideal S // absNorm I ≤ n} ≃ {I : Ideal S // I ∈ (Ideal S)⁰ ∧ absNorm I ≤ n} ⊕
      {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I ≤ n} := by
    refine (Equiv.subtypeEquivRight ?_).trans (subtypeOrEquiv _ _ ?_)
    · intro _
      simp_rw [← or_and_right, em, true_and]
    · exact Pi.disjoint_iff.mpr fun I ↦ Prop.disjoint_iff.mpr (by tauto)
  simp_rw [Nat.card_congr e, Nat.card_sum, add_right_inj]
  conv_lhs =>
    enter [1, 1, I]
    rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors, ne_eq, not_not, and_iff_left_iff_imp.mpr
      (fun h ↦ by rw [h]; exact Nat.zero_le n), absNorm_eq_zero_iff]
  rw [Nat.card_unique]

theorem norm_dvd_iff {x : S} (hx : Prime (Algebra.norm ℤ x)) {y : ℤ} :
    Algebra.norm ℤ x ∣ y ↔ x ∣ y := by
  rw [← Ideal.mem_span_singleton (y := x), ← eq_intCast (algebraMap ℤ S), ← Ideal.mem_comap,
    ← Ideal.span_singleton_absNorm, Ideal.mem_span_singleton, Ideal.absNorm_span_singleton,
    Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

end Ideal

end RingOfIntegers

section Int

open Ideal

@[simp]
theorem Int.ideal_span_absNorm_eq_self (J : Ideal ℤ) :
    span {(absNorm J : ℤ)} = J := by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp

end Int

end abs_norm
