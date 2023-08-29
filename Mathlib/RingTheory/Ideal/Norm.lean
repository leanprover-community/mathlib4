/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Int.AbsoluteValue
import Mathlib.Data.Int.Associated
import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.LocalProperties
import Mathlib.RingTheory.Localization.NormTrace

#align_import ring_theory.ideal.norm from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!

# Ideal norms

This file defines the absolute ideal norm `Ideal.absNorm (I : Ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite),
and the relative ideal norm `Ideal.spanNorm R (I : Ideal S) : Ideal S` as the ideal spanned by
the norms of elements in `I`.

## Main definitions

 * `Submodule.cardQuot (S : Submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.
 * `Ideal.absNorm (I : Ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.
 * `Ideal.spanNorm R (I : Ideal S)`: the ideal spanned by the norms of elements in `I`.
    This is used to define `Ideal.relNorm`.
 * `Ideal.relNorm R (I : Ideal S)`: the relative ideal norm as a bundled monoid-with-zero morphism,
   defined as the ideal spanned by the norms of elements in `I`.

## Main results

 * `map_mul Ideal.absNorm`: multiplicativity of the ideal norm is bundled in
   the definition of `Ideal.absNorm`
 * `Ideal.natAbs_det_basis_change`: the ideal norm is given by the determinant
   of the basis change matrix
 * `Ideal.absNorm_span_singleton`: the ideal norm of a principal ideal is the
   norm of its generator
 * `map_mul Ideal.relNorm`: multiplicativity of the relative ideal norm
-/


open scoped BigOperators

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
#align submodule.card_quot Submodule.cardQuot

@[simp]
theorem cardQuot_apply (S : Submodule R M) [h : Fintype (M ⧸ S)] :
    cardQuot S = Fintype.card (M ⧸ S) := by
  -- Porting note: original proof was AddSubgroup.index_eq_card _
  suffices Fintype (M ⧸ S.toAddSubgroup) by convert AddSubgroup.index_eq_card S.toAddSubgroup
  -- ⊢ Fintype (M ⧸ toAddSubgroup S)
  convert h
  -- 🎉 no goals
#align submodule.card_quot_apply Submodule.cardQuot_apply

variable (R M)

@[simp]
theorem cardQuot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0 :=
  AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite
#align submodule.card_quot_bot Submodule.cardQuot_bot

-- @[simp] -- Porting note: simp can prove this
theorem cardQuot_top : cardQuot (⊤ : Submodule R M) = 1 :=
  AddSubgroup.index_top
#align submodule.card_quot_top Submodule.cardQuot_top

variable {R M}

@[simp]
theorem cardQuot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤ :=
  AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])
                                     -- 🎉 no goals
#align submodule.card_quot_eq_one_iff Submodule.cardQuot_eq_one_iff

end

end Submodule

section RingOfIntegers

variable {S : Type*} [CommRing S] [IsDomain S]

open Submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
theorem cardQuot_mul_of_coprime [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]
    {I J : Ideal S} (coprime : I ⊔ J = ⊤) : cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis ℤ S
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  cases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex ℤ S)
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  · haveI : Subsingleton S := Function.Surjective.subsingleton b.repr.toEquiv.symm.surjective
    -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
    nontriviality S
    -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
    exfalso
    -- ⊢ False
    exact not_nontrivial_iff_subsingleton.mpr ‹Subsingleton S› ‹Nontrivial S›
    -- 🎉 no goals
  haveI : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  by_cases hI : I = ⊥
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  · rw [hI, Submodule.bot_mul, cardQuot_bot, zero_mul]
    -- 🎉 no goals
  by_cases hJ : J = ⊥
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  · rw [hJ, Submodule.mul_bot, cardQuot_bot, mul_zero]
    -- 🎉 no goals
  have hIJ : I * J ≠ ⊥ := mt Ideal.mul_eq_bot.mp (not_or_of_not hI hJ)
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  letI := Classical.decEq (Module.Free.ChooseBasisIndex ℤ S)
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  letI := I.fintypeQuotientOfFreeOfNeBot hI
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  letI := J.fintypeQuotientOfFreeOfNeBot hJ
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  letI := (I * J).fintypeQuotientOfFreeOfNeBot hIJ
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  rw [cardQuot_apply, cardQuot_apply, cardQuot_apply,
    Fintype.card_eq.mpr ⟨(Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv⟩,
    Fintype.card_prod]
#align card_quot_mul_of_coprime cardQuot_mul_of_coprime

/-- If the `d` from `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.mul_add_mem_pow_succ_inj (P : Ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
    (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1)) (h : d - d' ∈ P) :
    a * d + e - (a * d' + e') ∈ P ^ (i + 1) := by
  have : a * d - a * d' ∈ P ^ (i + 1) := by
    convert Ideal.mul_mem_mul a_mem h using 1 <;> simp [mul_sub, pow_succ, mul_comm]
  convert Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
  -- ⊢ a * d + e - (a * d' + e') = a * d - a * d' + (e - e')
  ring
  -- 🎉 no goals
#align ideal.mul_add_mem_pow_succ_inj Ideal.mul_add_mem_pow_succ_inj

section PPrime

variable {P : Ideal S} [P_prime : P.IsPrime] (hP : P ≠ ⊥)

/-- If `a ∈ P^i \ P^(i+1)` and `c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`Ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] {i : ℕ} (a c : S) (a_mem : a ∈ P ^ i)
    (a_not_mem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
    ∃ d : S, ∃ e ∈ P ^ (i + 1), a * d + e = c := by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1)
  -- ⊢ ∃ d e, e ∈ P ^ (i + 1) ∧ a * d + e = c
  · rw [eq_b] at c_mem
    -- ⊢ ∃ d e, e ∈ P ^ (i + 1) ∧ a * d + e = c
    simp only [mul_comm a]
    -- ⊢ ∃ d e, e ∈ P ^ (i + 1) ∧ d * a + e = c
    exact Ideal.mem_span_singleton_sup.mp c_mem
    -- 🎉 no goals
  refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
    (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a_mem))
      (Ideal.pow_succ_lt_pow hP i).le)).symm
  contrapose! a_not_mem with this
  -- ⊢ a ∈ P ^ (i + 1)
  rw [this]
  -- ⊢ a ∈ span {a} ⊔ P ^ (i + 1)
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
  -- 🎉 no goals
#align ideal.exists_mul_add_mem_pow_succ Ideal.exists_mul_add_mem_pow_succ

theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P : Ideal S} [P_prime : P.IsPrime]
    (hP : P ≠ ⊥) {i : ℕ} {a b : S} (a_not_mem : a ∉ P ^ (i + 1)) (ab_mem : a * b ∈ P ^ (i + 1)) :
    b ∈ P := by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_not_mem ab_mem ⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_not_mem
  -- 🎉 no goals
#align ideal.mem_prime_of_mul_mem_pow Ideal.mem_prime_of_mul_mem_pow

/-- The choice of `d` in `Ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] {i : ℕ} (a d d' e e' : S)
    (a_not_mem : a ∉ P ^ (i + 1)) (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
    (h : a * d + e - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P := by
  have h' : a * (d - d') ∈ P ^ (i + 1) := by
    convert Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_not_mem h'
  -- 🎉 no goals
#align ideal.mul_add_mem_pow_succ_unique Ideal.mul_add_mem_pow_succ_unique

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
theorem cardQuot_pow_of_prime [IsDedekindDomain S] [Module.Finite ℤ S] [Module.Free ℤ S] {i : ℕ} :
    cardQuot (P ^ i) = cardQuot P ^ i := by
  let _ := Module.Free.chooseBasis ℤ S
  -- ⊢ cardQuot (P ^ i) = cardQuot P ^ i
  classical
  induction' i with i ih
  · simp
  letI := Ideal.fintypeQuotientOfFreeOfNeBot (P ^ i.succ) (pow_ne_zero _ hP)
  letI := Ideal.fintypeQuotientOfFreeOfNeBot (P ^ i) (pow_ne_zero _ hP)
  letI := Ideal.fintypeQuotientOfFreeOfNeBot P hP
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkQ (P ^ i) ≃ S ⧸ P
  · rw [pow_succ (cardQuot P), ← ih, cardQuot_apply (P ^ i.succ), ←
      card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le, cardQuot_apply (P ^ i),
      cardQuot_apply P]
    congr 1
    rw [Fintype.card_eq]
    exact ⟨hquot⟩
  choose a a_mem a_not_mem using SetLike.exists_of_lt this
  choose f g hg hf using fun c (hc : c ∈ P ^ i) =>
    Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_not_mem hc
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
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq,
      Subtype.coe_mk]
    refine
      Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_not_mem (hg _ (hk_mem _ hd')) (zero_mem _) ?_
    rw [hf, add_zero]
    exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')
#align card_quot_pow_of_prime cardQuot_pow_of_prime

end PPrime

/-- Multiplicativity of the ideal norm in number rings. -/
theorem cardQuot_mul [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S] (I J : Ideal S) :
    cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis ℤ S
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  cases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex ℤ S)
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  · haveI : Subsingleton S := Function.Surjective.subsingleton b.repr.toEquiv.symm.surjective
    -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
    nontriviality S
    -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
    exfalso
    -- ⊢ False
    exact not_nontrivial_iff_subsingleton.mpr ‹Subsingleton S› ‹Nontrivial S›
    -- 🎉 no goals
  haveI : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i hI =>
        have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
        cardQuot_pow_of_prime hI.ne_zero)
      fun {I J} hIJ => cardQuot_mul_of_coprime
        (Ideal.isUnit_iff.mp
          (hIJ _ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))
#align card_quot_mul cardQuot_mul

/-- The absolute norm of the ideal `I : Ideal R` is the cardinality of the quotient `R ⧸ I`. -/
noncomputable def Ideal.absNorm [Infinite S] [IsDedekindDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] : Ideal S →*₀ ℕ where
  toFun := Submodule.cardQuot
  map_mul' I J := by dsimp only; rw [cardQuot_mul]
                     -- ⊢ cardQuot (I * J) = cardQuot I * cardQuot J
                 -- ⊢ cardQuot 1 = 1
                  -- 🎉 no goals
                             -- 🎉 no goals
                                 -- 🎉 no goals
  map_one' := by dsimp only; rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by rw [Ideal.zero_eq_bot, cardQuot_bot]
#align ideal.abs_norm Ideal.absNorm

namespace Ideal

variable [Infinite S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]

theorem absNorm_apply (I : Ideal S) : absNorm I = cardQuot I := rfl
#align ideal.abs_norm_apply Ideal.absNorm_apply

@[simp]
theorem absNorm_bot : absNorm (⊥ : Ideal S) = 0 := by rw [← Ideal.zero_eq_bot, _root_.map_zero]
                                                      -- 🎉 no goals
#align ideal.abs_norm_bot Ideal.absNorm_bot

@[simp]
theorem absNorm_top : absNorm (⊤ : Ideal S) = 1 := by rw [← Ideal.one_eq_top, _root_.map_one]
                                                      -- 🎉 no goals
#align ideal.abs_norm_top Ideal.absNorm_top

@[simp]
theorem absNorm_eq_one_iff {I : Ideal S} : absNorm I = 1 ↔ I = ⊤ := by
  rw [absNorm_apply, cardQuot_eq_one_iff]
  -- 🎉 no goals
#align ideal.abs_norm_eq_one_iff Ideal.absNorm_eq_one_iff

theorem absNorm_ne_zero_iff (I : Ideal S) : Ideal.absNorm I ≠ 0 ↔ Finite (S ⧸ I) :=
  ⟨fun h => Nat.finite_of_card_ne_zero h, fun h =>
    (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).finiteIndex⟩
#align ideal.abs_norm_ne_zero_iff Ideal.absNorm_ne_zero_iff

/-- Let `e : S ≃ I` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the norm of `I` is given by taking the determinant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result. -/
theorem natAbs_det_equiv (I : Ideal S) {E : Type*} [AddEquivClass E S I] (e : E) :
    Int.natAbs
        (LinearMap.det
          ((Submodule.subtype I).restrictScalars ℤ ∘ₗ AddMonoidHom.toIntLinearMap (e : S →+ I))) =
      Ideal.absNorm I := by
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  · subst hI
    -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype ⊥)) (AddMo …
    have : (1 : S) ≠ 0 := one_ne_zero
    -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype ⊥)) (AddMo …
    have : (1 : S) = 0 := EquivLike.injective e (Subsingleton.elim _ _)
    -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype ⊥)) (AddMo …
    contradiction
    -- 🎉 no goals
  let ι := Module.Free.ChooseBasisIndex ℤ S
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let b := Module.Free.chooseBasis ℤ S
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  cases isEmpty_or_nonempty ι
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  · nontriviality S
    -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
    exact (not_nontrivial_iff_subsingleton.mpr
      (Function.Surjective.subsingleton b.repr.toEquiv.symm.surjective) (by infer_instance)).elim
  -- Thus `(S ⧸ I)` is isomorphic to a product of `ZMod`s, so it is a fintype.
  letI := Ideal.fintypeQuotientOfFreeOfNeBot I hI
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  -- Use the Smith normal form to choose a nice basis for `I`.
  letI := Classical.decEq ι
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let a := I.smithCoeffs b hI
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let b' := I.ringBasis b hI
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let ab := I.selfBasis b hI
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  have ab_eq := I.selfBasis_def b hI
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let e' : S ≃ₗ[ℤ] I := b'.equiv ab (Equiv.refl _)
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let f : S →ₗ[ℤ] S := (I.subtype.restrictScalars ℤ).comp (e' : S →ₗ[ℤ] I)
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  let f_apply : ∀ x, f x = b'.equiv ab (Equiv.refl _) x := fun x => rfl
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype I)) (AddMo …
  suffices (LinearMap.det f).natAbs = Ideal.absNorm I by
    calc
      _ = (LinearMap.det ((Submodule.subtype I).restrictScalars ℤ ∘ₗ
            (AddEquiv.toIntLinearEquiv e : S ≃ₗ[ℤ] I))).natAbs := rfl
      _ = (LinearMap.det ((Submodule.subtype I).restrictScalars ℤ ∘ₗ _)).natAbs :=
            Int.natAbs_eq_iff_associated.mpr (LinearMap.associated_det_comp_equiv _ _ _)
      _ = absNorm I := this
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i; rw [f_apply, b'.equiv_apply, Equiv.refl_apply, ab_eq]
  -- `det f` is equal to `∏ i, a i`,
  letI := Classical.decEq ι
  -- ⊢ Int.natAbs (↑LinearMap.det f) = ↑absNorm I
  calc
    Int.natAbs (LinearMap.det f) = Int.natAbs (LinearMap.toMatrix b' b' f).det := by
      rw [LinearMap.det_toMatrix]
    _ = Int.natAbs (Matrix.diagonal a).det := ?_
    _ = Int.natAbs (∏ i, a i) := by rw [Matrix.det_diagonal]
    _ = ∏ i, Int.natAbs (a i) := (map_prod Int.natAbsHom a Finset.univ)
    _ = Fintype.card (S ⧸ I) := ?_
    _ = absNorm I := (Submodule.cardQuot_apply _).symm
  -- since `LinearMap.toMatrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  · congr 2; ext i j
    -- ⊢ ↑(LinearMap.toMatrix b' b') f = Matrix.diagonal a
             -- ⊢ ↑(LinearMap.toMatrix b' b') f i j = Matrix.diagonal a i j
    rw [LinearMap.toMatrix_apply, ha, LinearEquiv.map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    -- ⊢ ↑(Finsupp.single j (a j)) i = Matrix.diagonal a i j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
      -- 🎉 no goals
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne (Ne.symm h)]
      -- 🎉 no goals
  -- Now we map everything through the linear equiv `S ≃ₗ (ι → ℤ)`,
  -- which maps `(S ⧸ I)` to `Π i, ZMod (a i).nat_abs`.
  haveI : ∀ i, NeZero (a i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr (Ideal.smithCoeffs_ne_zero b I hI i)⟩
  simp_rw [Fintype.card_eq.mpr ⟨(Ideal.quotientEquivPiZMod I b hI).toEquiv⟩, Fintype.card_pi,
    ZMod.card]
#align ideal.nat_abs_det_equiv Ideal.natAbs_det_equiv

/-- Let `b` be a basis for `S` over `ℤ` and `bI` a basis for `I` over `ℤ` of the same dimension.
Then an alternative way to compute the norm of `I` is given by taking the determinant of `bI`
over `b`. -/
theorem natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ S)
    (I : Ideal S) (bI : Basis ι ℤ I) : (b.det ((↑) ∘ bI)).natAbs = Ideal.absNorm I := by
  let e := b.equiv bI (Equiv.refl _)
  -- ⊢ Int.natAbs (↑(Basis.det b) (Subtype.val ∘ ↑bI)) = ↑absNorm I
  calc
    (b.det ((Submodule.subtype I).restrictScalars ℤ ∘ bI)).natAbs =
        (LinearMap.det ((Submodule.subtype I).restrictScalars ℤ ∘ₗ (e : S →ₗ[ℤ] I))).natAbs :=
      by rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv I e
#align ideal.nat_abs_det_basis_change Ideal.natAbs_det_basis_change

@[simp]
theorem absNorm_span_singleton (r : S) :
    absNorm (span ({r} : Set S)) = (Algebra.norm ℤ r).natAbs := by
  rw [Algebra.norm_apply]
  -- ⊢ ↑absNorm (span {r}) = Int.natAbs (↑LinearMap.det (↑(Algebra.lmul ℤ S) r))
  by_cases hr : r = 0
  -- ⊢ ↑absNorm (span {r}) = Int.natAbs (↑LinearMap.det (↑(Algebra.lmul ℤ S) r))
  · simp only [hr, Ideal.span_zero, Algebra.coe_lmul_eq_mul, eq_self_iff_true, Ideal.absNorm_bot,
      LinearMap.det_zero'', Set.singleton_zero, _root_.map_zero, Int.natAbs_zero]
  letI := Ideal.fintypeQuotientOfFreeOfNeBot (span {r}) (mt span_singleton_eq_bot.mp hr)
  -- ⊢ ↑absNorm (span {r}) = Int.natAbs (↑LinearMap.det (↑(Algebra.lmul ℤ S) r))
  let b := Module.Free.chooseBasis ℤ S
  -- ⊢ ↑absNorm (span {r}) = Int.natAbs (↑LinearMap.det (↑(Algebra.lmul ℤ S) r))
  rw [← natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]
  -- ⊢ Int.natAbs (↑LinearMap.det (LinearMap.comp (↑ℤ (Submodule.subtype (span {r}) …
  congr
  -- ⊢ LinearMap.comp (↑ℤ (Submodule.subtype (span {r}))) (AddMonoidHom.toIntLinear …
  refine b.ext fun i => ?_
  -- ⊢ ↑(LinearMap.comp (↑ℤ (Submodule.subtype (span {r}))) (AddMonoidHom.toIntLine …
  simp
  -- 🎉 no goals
#align ideal.abs_norm_span_singleton Ideal.absNorm_span_singleton

theorem absNorm_dvd_absNorm_of_le {I J : Ideal S} (h : J ≤ I) : Ideal.absNorm I ∣ Ideal.absNorm J :=
  map_dvd absNorm (dvd_iff_le.mpr h)
#align ideal.abs_norm_dvd_abs_norm_of_le Ideal.absNorm_dvd_absNorm_of_le

theorem absNorm_dvd_norm_of_mem {I : Ideal S} {x : S} (h : x ∈ I) :
    ↑(Ideal.absNorm I) ∣ Algebra.norm ℤ x := by
  rw [← Int.dvd_natAbs, ← absNorm_span_singleton x, Int.coe_nat_dvd]
  -- ⊢ ↑absNorm I ∣ ↑absNorm (span {x})
  exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)
  -- 🎉 no goals
#align ideal.abs_norm_dvd_norm_of_mem Ideal.absNorm_dvd_norm_of_mem

@[simp]
theorem absNorm_span_insert (r : S) (s : Set S) :
    absNorm (span (insert r s)) ∣ gcd (absNorm (span s)) (Algebra.norm ℤ r).natAbs :=
  (dvd_gcd_iff _ _ _).mpr
    ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
      _root_.trans
        (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
        (by rw [absNorm_span_singleton])⟩
            -- 🎉 no goals
#align ideal.abs_norm_span_insert Ideal.absNorm_span_insert

theorem irreducible_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    Irreducible I :=
  irreducible_iff.mpr
    ⟨fun h =>
      hI.not_unit (by simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using h),
                      -- 🎉 no goals
      by
      rintro a b rfl
      -- ⊢ IsUnit a ∨ IsUnit b
      simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using
        hI.isUnit_or_isUnit (_root_.map_mul absNorm a b)⟩
#align ideal.irreducible_of_irreducible_abs_norm Ideal.irreducible_of_irreducible_absNorm

theorem isPrime_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    I.IsPrime :=
  isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))
#align ideal.is_prime_of_irreducible_abs_norm Ideal.isPrime_of_irreducible_absNorm

theorem prime_of_irreducible_absNorm_span {a : S} (ha : a ≠ 0)
    (hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set S)))) : Prime a :=
  (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)
#align ideal.prime_of_irreducible_abs_norm_span Ideal.prime_of_irreducible_absNorm_span

theorem absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) ∈ I := by
  rw [absNorm_apply, cardQuot, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    Quotient.index_eq_zero]
#align ideal.abs_norm_mem Ideal.absNorm_mem

theorem span_singleton_absNorm_le (I : Ideal S) : Ideal.span {(Ideal.absNorm I : S)} ≤ I := by
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.absNorm_mem I]
  -- 🎉 no goals
#align ideal.span_singleton_abs_norm_le Ideal.span_singleton_absNorm_le

theorem finite_setOf_absNorm_eq [CharZero S] {n : ℕ} (hn : 0 < n) :
    {I : Ideal S | Ideal.absNorm I = n}.Finite := by
  let f := fun I : Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
  -- ⊢ Set.Finite {I | ↑absNorm I = n}
  refine @Set.Finite.of_finite_image _ _ _ f ?_ ?_
  -- ⊢ Set.Finite (f '' {I | ↑absNorm I = n})
  · suffices Finite (S ⧸ @Ideal.span S _ {↑n}) by
      let g := ((↑) : Ideal (S ⧸ @Ideal.span S _ {↑n}) → Set (S ⧸ @Ideal.span S _ {↑n}))
      refine @Set.Finite.of_finite_image _ _ _ g ?_ (SetLike.coe_injective.injOn _)
      exact Set.Finite.subset (@Set.finite_univ _ (@Set.finite' _ this)) (Set.subset_univ _)
    rw [← absNorm_ne_zero_iff, absNorm_span_singleton]
    -- ⊢ Int.natAbs (↑(Algebra.norm ℤ) ↑n) ≠ 0
    simpa only [Ne.def, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff, Nat.cast_eq_zero] using
      ne_of_gt hn
  · intro I hI J hJ h
    -- ⊢ I = J
    rw [← comap_map_mk (span_singleton_absNorm_le I), ← hI.symm, ←
      comap_map_mk (span_singleton_absNorm_le J), ← hJ.symm]
    congr
    -- 🎉 no goals
#align ideal.finite_set_of_abs_norm_eq Ideal.finite_setOf_absNorm_eq

end Ideal

end RingOfIntegers

end abs_norm

section SpanNorm

namespace Ideal

open Submodule

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- `Ideal.spanNorm R (I : Ideal S)` is the ideal generated by mapping `Algebra.norm R` over `I`.

See also `Ideal.relNorm`.
-/
def spanNorm (I : Ideal S) : Ideal R :=
  Ideal.span (Algebra.norm R '' (I : Set S))
#align ideal.span_norm Ideal.spanNorm

@[simp]
theorem spanNorm_bot [Nontrivial S] [Module.Free R S] [Module.Finite R S] :
    spanNorm R (⊥ : Ideal S) = ⊥ := span_eq_bot.mpr fun x hx => by simpa using hx
                                                                   -- 🎉 no goals
#align ideal.span_norm_bot Ideal.spanNorm_bot

variable {R}

@[simp]
theorem spanNorm_eq_bot_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S]
    {I : Ideal S} : spanNorm R I = ⊥ ↔ I = ⊥ := by
  simp only [spanNorm, Ideal.span_eq_bot, Set.mem_image, SetLike.mem_coe, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂,
    Algebra.norm_eq_zero_iff_of_basis (Module.Free.chooseBasis R S), @eq_bot_iff _ _ _ I,
    SetLike.le_def]
  rfl
  -- 🎉 no goals
#align ideal.span_norm_eq_bot_iff Ideal.spanNorm_eq_bot_iff

variable (R)

theorem norm_mem_spanNorm {I : Ideal S} (x : S) (hx : x ∈ I) : Algebra.norm R x ∈ I.spanNorm R :=
  subset_span (Set.mem_image_of_mem _ hx)
#align ideal.norm_mem_span_norm Ideal.norm_mem_spanNorm

@[simp]
theorem spanNorm_singleton {r : S} : spanNorm R (span ({r} : Set S)) = span {Algebra.norm R r} :=
  le_antisymm
    (span_le.mpr fun x hx =>
      mem_span_singleton.mpr
        (by
          obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
          -- ⊢ ↑(Algebra.norm R) r ∣ ↑(Algebra.norm R) x
          exact map_dvd _ (mem_span_singleton.mp hx')))
          -- 🎉 no goals
    ((span_singleton_le_iff_mem _).mpr (norm_mem_spanNorm _ _ (mem_span_singleton_self _)))
#align ideal.span_norm_singleton Ideal.spanNorm_singleton

@[simp]
theorem spanNorm_top : spanNorm R (⊤ : Ideal S) = ⊤ := by
  -- Porting note: was
  -- simp [← Ideal.span_singleton_one]
  rw [← Ideal.span_singleton_one, spanNorm_singleton]
  -- ⊢ span {↑(Algebra.norm R) 1} = ⊤
  simp
  -- 🎉 no goals
#align ideal.span_norm_top Ideal.spanNorm_top

theorem map_spanNorm (I : Ideal S) {T : Type*} [CommRing T] (f : R →+* T) :
    map f (spanNorm R I) = span (f ∘ Algebra.norm R '' (I : Set S)) := by
  rw [spanNorm, map_span, Set.image_image]
  -- ⊢ span ((fun x => ↑f (↑(Algebra.norm R) x)) '' ↑I) = span (↑f ∘ ↑(Algebra.norm …
  -- Porting note: `Function.comp` reducibility
  rfl
  -- 🎉 no goals
#align ideal.map_span_norm Ideal.map_spanNorm

@[mono]
theorem spanNorm_mono {I J : Ideal S} (h : I ≤ J) : spanNorm R I ≤ spanNorm R J :=
  Ideal.span_mono (Set.monotone_image h)
#align ideal.span_norm_mono Ideal.spanNorm_mono

theorem spanNorm_localization (I : Ideal S) [Module.Finite R S] [Module.Free R S] (M : Submonoid R)
    {Rₘ : Type*} (Sₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
    [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ] :
    spanNorm Rₘ (I.map (algebraMap S Sₘ)) = (spanNorm R I).map (algebraMap R Rₘ) := by
  cases h : subsingleton_or_nontrivial R
  -- ⊢ spanNorm Rₘ (map (algebraMap S Sₘ) I) = map (algebraMap R Rₘ) (spanNorm R I)
  · haveI := IsLocalization.unique R Rₘ M
    -- ⊢ spanNorm Rₘ (map (algebraMap S Sₘ) I) = map (algebraMap R Rₘ) (spanNorm R I)
    simp
    -- 🎉 no goals
  let b := Module.Free.chooseBasis R S
  -- ⊢ spanNorm Rₘ (map (algebraMap S Sₘ) I) = map (algebraMap R Rₘ) (spanNorm R I)
  rw [map_spanNorm]
  -- ⊢ spanNorm Rₘ (map (algebraMap S Sₘ) I) = span (↑(algebraMap R Rₘ) ∘ ↑(Algebra …
  refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  -- ⊢ ↑(map (algebraMap S Sₘ) I) ⊆ ↑(Algebra.norm Rₘ) ⁻¹' ↑(Submodule.span Rₘ (↑(a …
  · rintro a' ha'
    -- ⊢ a' ∈ ↑(Algebra.norm Rₘ) ⁻¹' ↑(Submodule.span Rₘ (↑(algebraMap R Rₘ) ∘ ↑(Alge …
    simp only [Set.mem_preimage, submodule_span_eq, ← map_spanNorm, SetLike.mem_coe,
      IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
      IsLocalization.mem_map_algebraMap_iff M Rₘ, Prod.exists] at ha' ⊢
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha'
    -- ⊢ ∃ a b, ↑(Algebra.norm Rₘ) a' * ↑(algebraMap R Rₘ) ↑b = ↑(algebraMap R Rₘ) ↑a
    refine ⟨⟨Algebra.norm R a, norm_mem_spanNorm _ _ ha⟩,
      ⟨s ^ Fintype.card (Module.Free.ChooseBasisIndex R S), pow_mem hs _⟩, ?_⟩
    simp only [Submodule.coe_mk, Subtype.coe_mk, map_pow] at has ⊢
    -- ⊢ ↑(Algebra.norm Rₘ) a' * ↑(algebraMap R Rₘ) s ^ Fintype.card (Module.Free.Cho …
    apply_fun Algebra.norm Rₘ at has
    -- ⊢ ↑(Algebra.norm Rₘ) a' * ↑(algebraMap R Rₘ) s ^ Fintype.card (Module.Free.Cho …
    rwa [_root_.map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R Rₘ,
      Algebra.norm_algebraMap_of_basis (b.localizationLocalization Rₘ M Sₘ),
      Algebra.norm_localization R M a] at has
  · intro a ha
    -- ⊢ a ∈ ↑(algebraMap R Rₘ) ∘ ↑(Algebra.norm R) ⁻¹' ↑(Submodule.span Rₘ (↑(Algebr …
    rw [Set.mem_preimage, Function.comp_apply, ← Algebra.norm_localization (Sₘ := Sₘ) R M a]
    -- ⊢ ↑(Algebra.norm Rₘ) (↑(algebraMap S Sₘ) a) ∈ ↑(Submodule.span Rₘ (↑(Algebra.n …
    exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))
    -- 🎉 no goals
#align ideal.span_norm_localization Ideal.spanNorm_localization

theorem spanNorm_mul_spanNorm_le (I J : Ideal S) :
    spanNorm R I * spanNorm R J ≤ spanNorm R (I * J) := by
  rw [spanNorm, spanNorm, spanNorm, Ideal.span_mul_span', ← Set.image_mul]
  -- ⊢ span (↑(Algebra.norm R) '' (↑I * ↑J)) ≤ span (↑(Algebra.norm R) '' ↑(I * J))
  refine Ideal.span_mono (Set.monotone_image ?_)
  -- ⊢ ↑I * ↑J ≤ ↑(I * J)
  rintro _ ⟨x, y, hxI, hyJ, rfl⟩
  -- ⊢ (fun x x_1 => x * x_1) x y ∈ ↑(I * J)
  exact Ideal.mul_mem_mul hxI hyJ
  -- 🎉 no goals
#align ideal.span_norm_mul_span_norm_le Ideal.spanNorm_mul_spanNorm_le

/-- This condition `eq_bot_or_top` is equivalent to being a field.
However, `Ideal.spanNorm_mul_of_field` is harder to apply since we'd need to upgrade a `CommRing R`
instance to a `Field R` instance. -/
theorem spanNorm_mul_of_bot_or_top [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S]
    (eq_bot_or_top : ∀ I : Ideal R, I = ⊥ ∨ I = ⊤) (I J : Ideal S) :
    spanNorm R (I * J) = spanNorm R I * spanNorm R J := by
  refine le_antisymm ?_ (spanNorm_mul_spanNorm_le R _ _)
  -- ⊢ spanNorm R (I * J) ≤ spanNorm R I * spanNorm R J
  cases' eq_bot_or_top (spanNorm R I) with hI hI
  -- ⊢ spanNorm R (I * J) ≤ spanNorm R I * spanNorm R J
  · rw [hI, spanNorm_eq_bot_iff.mp hI, bot_mul, spanNorm_bot]
    -- ⊢ ⊥ ≤ ⊥ * spanNorm R J
    exact bot_le
    -- 🎉 no goals
  rw [hI, Ideal.top_mul]
  -- ⊢ spanNorm R (I * J) ≤ spanNorm R J
  cases' eq_bot_or_top (spanNorm R J) with hJ hJ
  -- ⊢ spanNorm R (I * J) ≤ spanNorm R J
  · rw [hJ, spanNorm_eq_bot_iff.mp hJ, mul_bot, spanNorm_bot]
    -- 🎉 no goals
  rw [hJ]
  -- ⊢ spanNorm R (I * J) ≤ ⊤
  exact le_top
  -- 🎉 no goals
#align ideal.span_norm_mul_of_bot_or_top Ideal.spanNorm_mul_of_bot_or_top

@[simp]
theorem spanNorm_mul_of_field {K : Type*} [Field K] [Algebra K S] [IsDomain S] [Module.Finite K S]
    (I J : Ideal S) : spanNorm K (I * J) = spanNorm K I * spanNorm K J :=
  spanNorm_mul_of_bot_or_top K eq_bot_or_top I J
#align ideal.span_norm_mul_of_field Ideal.spanNorm_mul_of_field

variable [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]

variable [Module.Finite R S] [Module.Free R S]

/-- Multiplicativity of `Ideal.spanNorm`. simp-normal form is `map_mul (Ideal.relNorm R)`. -/
theorem spanNorm_mul (I J : Ideal S) : spanNorm R (I * J) = spanNorm R I * spanNorm R J := by
  nontriviality R
  -- ⊢ spanNorm R (I * J) = spanNorm R I * spanNorm R J
  cases subsingleton_or_nontrivial S
  -- ⊢ spanNorm R (I * J) = spanNorm R I * spanNorm R J
  · have : ∀ I : Ideal S, I = ⊤ := fun I => Subsingleton.elim I ⊤
    -- ⊢ spanNorm R (I * J) = spanNorm R I * spanNorm R J
    simp [this I, this J, this (I * J)]
    -- 🎉 no goals
  refine eq_of_localization_maximal ?_
  -- ⊢ ∀ (P : Ideal R) (x : IsMaximal P), map (algebraMap R (Localization.AtPrime P …
  intro P hP
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  by_cases hP0 : P = ⊥
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  · subst hP0
    -- ⊢ map (algebraMap R (Localization.AtPrime ⊥)) (spanNorm R (I * J)) = map (alge …
    rw [spanNorm_mul_of_bot_or_top]
    -- ⊢ ∀ (I : Ideal R), I = ⊥ ∨ I = ⊤
    intro I
    -- ⊢ I = ⊥ ∨ I = ⊤
    refine or_iff_not_imp_right.mpr fun hI => ?_
    -- ⊢ I = ⊥
    exact (hP.eq_of_le hI bot_le).symm
    -- 🎉 no goals
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  letI : Algebra (Localization.AtPrime P) (Localization P') := localizationAlgebra P.primeCompl S
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization P') :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.map_eq (T := P') (Q := Localization P') P.primeCompl.le_comap_map x).symm)
  have h : P' ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (NoZeroSMulDivisors.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain (Localization P') := IsLocalization.isDomain_localization h
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  haveI : IsDedekindDomain (Localization P') := IsLocalization.isDedekindDomain S h _
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  letI := Classical.decEq (Ideal (Localization P'))
  -- ⊢ map (algebraMap R (Localization.AtPrime P)) (spanNorm R (I * J)) = map (alge …
  haveI : IsPrincipalIdealRing (Localization P') :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P hP0
  rw [Ideal.map_mul, ← spanNorm_localization R I P.primeCompl (Localization P'),
    ← spanNorm_localization R J P.primeCompl (Localization P'),
    ← spanNorm_localization R (I * J) P.primeCompl (Localization P'), Ideal.map_mul,
    ← (I.map _).span_singleton_generator, ← (J.map _).span_singleton_generator,
    span_singleton_mul_span_singleton, spanNorm_singleton, spanNorm_singleton,
    spanNorm_singleton, span_singleton_mul_span_singleton, _root_.map_mul]
#align ideal.span_norm_mul Ideal.spanNorm_mul

/-- The relative norm `Ideal.relNorm R (I : Ideal S)`, where `R` and `S` are Dedekind domains,
and `S` is an extension of `R` that is finite and free as a module. -/
def relNorm : Ideal S →*₀ Ideal R where
  toFun := spanNorm R
  map_zero' := spanNorm_bot R
  map_one' := by dsimp only; rw [one_eq_top, spanNorm_top R, one_eq_top]
                 -- ⊢ spanNorm R 1 = 1
                             -- 🎉 no goals
  map_mul' := spanNorm_mul R
#align ideal.rel_norm Ideal.relNorm

theorem relNorm_apply (I : Ideal S) : relNorm R I = span (Algebra.norm R '' (I : Set S) : Set R) :=
  rfl
#align ideal.rel_norm_apply Ideal.relNorm_apply

@[simp]
theorem spanNorm_eq (I : Ideal S) : spanNorm R I = relNorm R I := rfl
#align ideal.span_norm_eq Ideal.spanNorm_eq

@[simp]
theorem relNorm_bot : relNorm R (⊥ : Ideal S) = ⊥ := by
  simpa only [zero_eq_bot] using _root_.map_zero (relNorm R : Ideal S →*₀ _)
  -- 🎉 no goals
#align ideal.rel_norm_bot Ideal.relNorm_bot

@[simp]
theorem relNorm_top : relNorm R (⊤ : Ideal S) = ⊤ := by
  simpa only [one_eq_top] using map_one (relNorm R : Ideal S →*₀ _)
  -- 🎉 no goals
#align ideal.rel_norm_top Ideal.relNorm_top

variable {R}

@[simp]
theorem relNorm_eq_bot_iff {I : Ideal S} : relNorm R I = ⊥ ↔ I = ⊥ :=
  spanNorm_eq_bot_iff
#align ideal.rel_norm_eq_bot_iff Ideal.relNorm_eq_bot_iff

variable (R)

theorem norm_mem_relNorm (I : Ideal S) {x : S} (hx : x ∈ I) : Algebra.norm R x ∈ relNorm R I :=
  norm_mem_spanNorm R x hx
#align ideal.norm_mem_rel_norm Ideal.norm_mem_relNorm

@[simp]
theorem relNorm_singleton (r : S) : relNorm R (span ({r} : Set S)) = span {Algebra.norm R r} :=
  spanNorm_singleton R
#align ideal.rel_norm_singleton Ideal.relNorm_singleton

theorem map_relNorm (I : Ideal S) {T : Type*} [CommRing T] (f : R →+* T) :
    map f (relNorm R I) = span (f ∘ Algebra.norm R '' (I : Set S)) :=
  map_spanNorm R I f
#align ideal.map_rel_norm Ideal.map_relNorm

@[mono]
theorem relNorm_mono {I J : Ideal S} (h : I ≤ J) : relNorm R I ≤ relNorm R J :=
  spanNorm_mono R h
#align ideal.rel_norm_mono Ideal.relNorm_mono

end Ideal

end SpanNorm
