/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Isomorphisms between `adicCompletion ℚ` and `ℚ_[p]`

Let `R` have field of fractions `ℚ`. If `v : HeightOneSpectrum R`, then `v.adicCompletion ℚ` is
the uniform space completion of `ℚ` with respect to the `v`-adic valuation.
On the other hand, `ℚ_[p]` is the `p`-adic numbers, defined as the completion of `ℚ` with respect
to the `p`-adic norm using the completion of Cauchy sequences. This file constructs continuous
`ℚ`-algebra` isomorphisms between the two, as well as continuous `ℤ`-algebra isomorphisms for their
respective rings of integers.

Isomorphisms are provided in both directions, allowing traversal of the following diagram:
```
HeightOneSpectrum R <----------->  Nat.Primes
          |                               |
          |                               |
          v                               v
v.adicCompletionIntegers ℚ  <------->   ℤ_[p]
          |                               |
          |                               |
          v                               v
v.adicCompletion ℚ  <--------------->   ℚ_[p]
```

## Main definitions
- `Rat.HeightOneSpectrum.primesEquiv` : the equivalence between height-one prime ideals of
  `R` and prime numbers in `ℕ`.
- `Rat.HeightOneSpectrum.padicEquiv v` : the continuous `ℚ`-algebra isomorphism
  `v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`.
- `Padic.adicCompletionEquiv p` : the continuous `ℚ`-algebra isomorphism
  `ℚ_[p] ≃A[ℚ] (primesEquiv.symm p).adicCompletion ℚ`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v` : the continuous `ℤ`-algebra
  isomorphism `v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[natGenerator v]`.
- `PadicInt.adicCompletionIntegersEquiv p` : the continuous `ℤ`-algebra isomorphism
  `ℤ_[p] ≃A[ℤ] (primesEquiv.symm p).adicCompletionIntegers ℚ`.

TODO : Abstract the isomorphisms in this file using a universal predicate on adic completions,
along the lines of `IsComplete` + uniformity arises from a valuation + the valuations are
equivalent. It is best to do this after `Valued` has been refactored, or at least after
`adicCompletion` has `IsValuativeTopology` instance.
-/

@[expose] public section

open IsDedekindDomain UniformSpace.Completion NumberField PadicInt

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable (R : Type*) [CommRing R] [Algebra R ℚ]

theorem Rat.int_algebraMap_injective : Function.Injective (algebraMap ℤ R) :=
  .of_comp (IsScalarTower.algebraMap_eq ℤ R ℚ ▸ RingHom.injective_int (algebraMap ℤ ℚ))

variable [IsFractionRing R ℚ] [IsIntegralClosure R ℤ ℚ]

theorem Rat.int_algebraMap_surjective : Function.Surjective (algebraMap ℤ R) := by
  intro x
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 <|
    IsIntegral.algebraMap (B := ℚ) (IsIntegralClosure.isIntegral ℤ ℚ x)
  exact ⟨y, IsFractionRing.injective R ℚ <| by simp only [← IsScalarTower.algebraMap_apply, hy]⟩

/-- If `R : CommRing` has field of fractions `ℚ` then it is isomorphic to `ℤ`. -/
noncomputable def Rat.intEquiv : R ≃+* ℤ :=
  RingEquiv.ofBijective _ ⟨int_algebraMap_injective R, int_algebraMap_surjective R⟩ |>.symm

namespace Rat.HeightOneSpectrum

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsFractionRing R ℚ] [IsIntegralClosure R ℤ ℚ]

/-- If `v : HeightOneSpectrum R` then `natGenerator v` is the generator in `ℕ` of the corresponding
ideal in `ℤ`. -/
noncomputable def natGenerator (v : HeightOneSpectrum R) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map <| intEquiv R) |>.natAbs

theorem span_natGenerator (v : HeightOneSpectrum R) :
    Ideal.span {(natGenerator v : ℤ)} = v.asIdeal.map (intEquiv R) := by
  simp [natGenerator]

theorem natGenerator_dvd_iff (v : HeightOneSpectrum R) {n : ℕ} :
    natGenerator v ∣ n ↔ ↑n ∈ v.asIdeal.map (intEquiv R) := by
  rw [← span_natGenerator, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

theorem prime_natGenerator (v : HeightOneSpectrum R) : Nat.Prime (natGenerator v) :=
  Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective (intEquiv R).injective).not.2 v.ne_bot)

variable [IsDedekindDomain R]

/-- The equivalence between height-one prime ideals of `R` and primes in `ℕ`. -/
noncomputable def primesEquiv : HeightOneSpectrum R ≃ Nat.Primes where
  toFun v := ⟨natGenerator v, prime_natGenerator v⟩
  invFun p :=
    have h : Prime ((Ideal.span {(p.1 : ℤ)}).map (intEquiv R).symm) :=
      map_prime_of_equiv _ (by simp [← Nat.prime_iff_prime_int, p.2]) (by simp [p.2.ne_zero])
    .ofPrime h
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    rw [← v.asIdeal.comap_map_of_bijective _ (intEquiv R).bijective, ← span_natGenerator]
  right_inv p := by
    simp only [Ideal.map_symm, natGenerator, HeightOneSpectrum.ofPrime_asIdeal]
    congr
    simp [Ideal.map_comap_of_surjective _ (intEquiv R).surjective,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self _)]

theorem valuation_equiv_padicValuation (v : HeightOneSpectrum R) :
    (v.valuation ℚ).IsEquiv (padicValuation (primesEquiv v)) := by
  simp [primesEquiv, Valuation.isEquiv_iff_val_le_one, valuation_le_one_iff_den,
    padicValuation_le_one_iff, natGenerator_dvd_iff,
    map_natCast (intEquiv R) _ ▸ Ideal.apply_mem_of_equiv_iff]

open Valuation

/-- The uniform space isomorphism `ℚ ≃ᵤ ℚ`, where the LHS has the uniformity from
`HeightOneSpectrum.valuation ℚ v` and the RHS has uniformity from
`Rat.padicValuation (natGenerator v)`, for a height-one prime ideal
`v : HeightOneSpectrum R`. -/
noncomputable def withValEquiv (v : HeightOneSpectrum R) :
    WithVal (v.valuation ℚ) ≃ᵤ WithVal (padicValuation (primesEquiv v)) :=
  (valuation_equiv_padicValuation v).uniformEquiv
    (exists_div_eq_of_surjective (v.valuation_surjective ℚ))
    (exists_div_eq_of_surjective (surjective_padicValuation (primesEquiv v)))

/-- The continuous `ℚ`-algebra isomorphism between `v.adicCompletion ℚ` and `ℚ_[primesEquiv v]`. -/
noncomputable def adicCompletion.padicEquiv (v : HeightOneSpectrum R) :
    v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v] where
  __ := (mapRingEquiv _ (withValEquiv v).continuous
      (withValEquiv v).symm.continuous).trans Padic.withValRingEquiv
  __ := ((mapEquiv (withValEquiv v)).trans Padic.withValUniformEquiv).toHomeomorph
  commutes' := by simp

/-- The continuous `ℤ`-algebra isomorphism between `v.adicCompletionIntegers ℚ` and
`ℤ_[primesEquiv v]`. -/
noncomputable def adicCompletionIntegers.padicIntEquiv (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[primesEquiv v] where
  __ := let e := (mapRingEquiv _ (withValEquiv v).continuous
          (withValEquiv v).symm.continuous).restrict _ _ fun _ ↦ by
            simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
              (v.valuation_surjective ℚ) (surjective_padicValuation _)
        e.trans withValIntegersRingEquiv
  __ := let e := (mapEquiv (withValEquiv v)).subtype fun _ ↦ by
          simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
            (v.valuation_surjective ℚ) (surjective_padicValuation _)
        (e.trans withValIntegersUniformEquiv).toHomeomorph
  commutes' := by simp

/-- The diagram
```
v.adicCompletionIntegers ℚ  ----->  ℤ_[primesEquiv v]
      |                               |
      |                               |
      v                               v
v.adicCompletion ℚ  ------------->  ℚ_[primesEquiv v]
```
commutes. -/
theorem adicCompletionIntegers.coe_padicIntEquiv_apply (v : HeightOneSpectrum R)
    (x : v.adicCompletionIntegers ℚ) : padicIntEquiv v x = adicCompletion.padicEquiv v x := rfl

/-- The diagram
```
v.adicCompletionIntegers ℚ  <-----  ℤ_[primesEquiv v]
      |                               |
      |                               |
      v                               v
v.adicCompletion ℚ  <-------------  ℚ_[primesEquiv v]
```
commutes. -/
theorem adicCompletionIntegers.coe_padicIntEquiv_symm_apply (v : HeightOneSpectrum R)
    (x : ℤ_[primesEquiv v]) : (adicCompletionIntegers.padicIntEquiv v).symm x =
      (adicCompletion.padicEquiv v).symm x := rfl

theorem adicCompletion.padicEquiv_bijOn (v : HeightOneSpectrum R) :
    Set.BijOn (padicEquiv v) (v.adicCompletionIntegers ℚ) (subring (primesEquiv v)) := by
  refine ⟨fun x hx ↦ ?_, (padicEquiv v).injective.injOn, fun y hy ↦ ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntEquiv_apply, hx]⟩

end Rat.HeightOneSpectrum

open Rat.HeightOneSpectrum

namespace Padic

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
  [IsIntegralClosure R ℤ ℚ]

/-- The continuous `ℚ`-algebra isomorphism between `ℚ_[p]` and
`(primesEquiv.symm p).adicCompletion ℚ`. -/
noncomputable def adicCompletionEquiv (p : Nat.Primes) :
    ℚ_[p] ≃A[ℚ] ((primesEquiv (R := R)).symm p).adicCompletion ℚ := by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletion.padicEquiv (primesEquiv.symm p)).symm

end Padic

namespace PadicInt

open Padic

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
  [IsIntegralClosure R ℤ ℚ]

/-- The continuous `ℤ`-algebra isomorphism between `ℤ_[p]` and
`(primesEquiv.symm p).adicCompletionIntegers ℚ`. -/
noncomputable def adicCompletionIntegersEquiv (p : Nat.Primes) :
    ℤ_[p] ≃A[ℤ] ((primesEquiv (R := R)).symm p).adicCompletionIntegers ℚ := by
  apply (ContinuousAlgEquiv.cast (primesEquiv.apply_symm_apply p).symm).trans
    (adicCompletionIntegers.padicIntEquiv (primesEquiv.symm p)).symm

/-- The diagram
```
ℤ_[p]  -------->  (primesEquiv.symm p).adicCompletionIntegers ℚ
   |                          |
   |                          |
   v                          v
ℚ_[p]  -------->  (primesEquiv.symm p).adicCompletion ℚ
```
commutes. -/
theorem coe_adicCompletionIntegersEquiv_apply (p : Nat.Primes) (x : ℤ_[p]) :
    (adicCompletionIntegersEquiv R p x) = adicCompletionEquiv R p x := by
  simp only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.trans_apply,
    adicCompletionIntegers.coe_padicIntEquiv_symm_apply,
    adicCompletionEquiv, ContinuousAlgEquiv.trans_apply, ContinuousAlgEquiv.cast_apply,
    EmbeddingLike.apply_eq_iff_eq, Equiv.cast_apply, eq_cast_iff_heq]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

/-- The diagram
```
ℤ_[p]  <--------  (primesEquiv.symm p).adicCompletionIntegers ℚ
   |                          |
   |                          |
   v                          v
ℚ_[p]  <--------  (primesEquiv.symm p).adicCompletion ℚ
```
commutes. -/
theorem coe_adicCompletionIntegersEquiv_symm_apply (p : Nat.Primes)
    (x : (primesEquiv.symm p).adicCompletionIntegers ℚ) :
    (adicCompletionIntegersEquiv R p).symm x = (adicCompletionEquiv R p).symm x := by
  simp only [adicCompletionIntegersEquiv, ContinuousAlgEquiv.symm_trans_apply,
    ContinuousAlgEquiv.symm_symm, adicCompletionEquiv, Equiv.cast_apply, eq_cast_iff_heq,
    ← adicCompletionIntegers.coe_padicIntEquiv_apply, ContinuousAlgEquiv.cast_symm_apply]
  rw [← Subtype.heq_iff_coe_heq (by rw [primesEquiv.apply_symm_apply])
    (by rw [primesEquiv.apply_symm_apply])]
  exact cast_heq _ _

end PadicInt
