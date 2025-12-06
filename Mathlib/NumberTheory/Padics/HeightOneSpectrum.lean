/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Int.Basic

/-!
# Isomorphisms between `adicCompletion ℚ` and `ℚ_[p]`

If `v : HeightOneSpectrum ℚ`, then `v.adicCompletion ℚ` is the uniform space completion of `ℚ`
with respect to the `v`-adic valuation, which definition generalises to Dedekind domains and
their field of fractions. On the other hand, `ℚ_[p]` is the `p`-adic numbers, defined as the
completion of `ℚ` with respect to the `p`-adic norm using the completion of Cauchy sequences.
This file constructs uniform and `ℚ`-algebra` isomorphisms between the two, as well as for their
respective rings of integers.

Isomorphisms are provided in both directions, allowing traversal of the following diagram:
```
v.adicCompletion ℚ  <------------->  ℚ_[p]
      ↑                               ↑
      |                               |
      |                               |
v.adicCompletionIntegers ℚ  <----->  ℤ_[p]
      ↑                               ↑
      |                               |
      |                               |
HeightOneSpectrum (𝓞 ℚ) <-------> Nat.Primes
```

## Main definitions
- `Rat.HeightOneSpectrum.primesEquiv` : the equivalence between height-one prime ideals of
  `𝓞 ℚ` and prime numbers in `ℕ`.
- `Rat.HeightOneSpectrum.padicUniformEquiv v` : `v.adicCompletion ℚ ≃ᵤ ℚ_[primesEquiv v]`.
- `Padic.adicCompletionUniformEquiv p` : `ℚ_[p] ≃ᵤ (primesEquiv.symm ⟨p, _⟩).adicCompletion ℚ`.
- `Rat.HeightOneSpectrum.padicAlgEquiv v` : `v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[primesEquiv v]`.
- `Padic.adicCompletionAlgEquiv p` : `ℚ_[p] ≃ₐ[ℚ] (primesEquiv.symm ⟨p, _⟩).adicCompletion ℚ`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntUniformEquiv v` :
  `v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v]`.
- `PadicInt.adicCompletionIntegersUniformEquiv p` :
  `ℤ_[p] ≃ᵤ (primesEquiv.symm ⟨p, _⟩).adicCompletionIntegers ℚ`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntRingEquiv v` :
  `v.adicCompletionIntegers ℚ ≃+* ℤ_[natGenerator v]`.
- `PadicInt.adicCompletionIntegersRingEqui p` :
  `ℤ_[p] ≃ₐ[ℤ] (primesEquiv.symm ⟨p, _⟩).adicCompletionIntegers ℚ`.
-/

@[expose] public section

open IsDedekindDomain UniformSpace.Completion NumberField PadicInt

namespace Rat.HeightOneSpectrum

/-- The generator in `ℕ` of a height-one prime ideal in `𝓞 ℚ`. -/
noncomputable def natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map ringOfIntegersEquiv) |>.natAbs

theorem span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.span {(natGenerator v : ℤ)} = v.asIdeal.map ringOfIntegersEquiv := by
  simp [natGenerator]

theorem natGenerator_dvd_iff (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} :
    natGenerator v ∣ n ↔ ↑n ∈ v.asIdeal.map ringOfIntegersEquiv := by
  rw [← span_natGenerator, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

theorem prime_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : Nat.Prime (natGenerator v) :=
  Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective ringOfIntegersEquiv.injective).not.2 v.ne_bot)

local instance (p : Nat.Primes) : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by simp [p.2.ne_zero])).2 <| Nat.prime_iff_prime_int.1 p.2

@[simps]
noncomputable def primesEquiv : HeightOneSpectrum (𝓞 ℚ) ≃ Nat.Primes where
  toFun v := ⟨natGenerator v, prime_natGenerator v⟩
  invFun p :=
    have h : Prime ((Ideal.span {(p.1 : ℤ)}).map ringOfIntegersEquiv.symm) :=
      map_prime_of_equiv _ (by simp [← Nat.prime_iff_prime_int, p.2]) (by simp [p.2.ne_zero])
    .ofPrime h
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    rw [← v.asIdeal.comap_map_of_bijective _ ringOfIntegersEquiv.bijective, ← span_natGenerator]
  right_inv p := by
    simp only [Ideal.map_symm, natGenerator, HeightOneSpectrum.ofPrime_asIdeal]
    congr
    simp [Ideal.map_comap_of_surjective _ ringOfIntegersEquiv.surjective,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self _)]

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem valuation_equiv_padicValuation (v : HeightOneSpectrum (𝓞 ℚ)) :
    (v.valuation ℚ).IsEquiv (padicValuation (primesEquiv v)) := by
  simp [Valuation.isEquiv_iff_val_le_one, padicValuation_le_one_iff, valuation_le_one_iff_den,
    natGenerator_dvd_iff, ← Ideal.apply_mem_of_equiv_iff (f := ringOfIntegersEquiv)]

open Valuation

/-- The uniform space isomorphism `ℚ ≃ᵤ ℚ`, where the LHS has the uniformity from
`HeightOneSpectrum.valuation ℚ v` and the RHS has uniformity from
`Rat.padicValuation (natGenerator v)`, for a height-one prime ideal
`v : HeightOneSpectrum (𝓞 ℚ)`. -/
noncomputable def valuationEquivPadicValuation (v : HeightOneSpectrum (𝓞 ℚ)) :
    WithVal (v.valuation ℚ) ≃ᵤ WithVal (padicValuation (primesEquiv v)) :=
  (valuation_equiv_padicValuation v).uniformEquiv
    (fun γ ↦ by obtain ⟨r, hr⟩ := v.valuation_surjective ℚ γ; exact ⟨r, 1, by aesop⟩)
    (fun γ ↦ by
      obtain ⟨r, hr⟩ := surjective_padicValuation (primesEquiv v) γ;
      exact ⟨r, 1, by aesop⟩)

/-- The uniform space isomorphism `v.adicCompletion ℚ ≃ᵤ ℚ_[natGenerator v]`. -/
noncomputable def adicCompletion.padicUniformEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃ᵤ ℚ_[primesEquiv v] :=
  (mapEquiv (valuationEquivPadicValuation v)).trans Padic.withValUniformEquiv

/-- `adicCompletion.padicUniformEquiv` as a `ℚ`-algebra isomorphism. -/
noncomputable def adicCompletion.padicAlgEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[primesEquiv v] where
  __ := (mapRingEquiv _ (valuationEquivPadicValuation v).continuous
      (valuationEquivPadicValuation v).symm.continuous).trans Padic.withValRingEquiv
  commutes' q := by simp

/-- The uniform space isomorphism `v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v]`. -/
noncomputable def adicCompletionIntegers.padicIntUniformEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[primesEquiv v] :=
  let e : v.adicCompletionIntegers ℚ ≃ᵤ
      (Valued.v.valuationSubring : ValuationSubring (padicValuation _).Completion) :=
    (mapEquiv (valuationEquivPadicValuation v)).subtype fun _ ↦ by
      simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (v.valuation_surjective ℚ) (surjective_padicValuation _)
  e.trans withValIntegersUniformEquiv

theorem adicCompletionIntegers.coe_padicIntUniformEquiv_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (x : v.adicCompletionIntegers ℚ) :
    padicIntUniformEquiv v x = adicCompletion.padicAlgEquiv v x := rfl

theorem adicCompletionIntegers.coe_padicIntUniformEquiv_symm_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (x : ℤ_[primesEquiv v]) :
    (adicCompletionIntegers.padicIntUniformEquiv v).symm x =
      (adicCompletion.padicUniformEquiv v).symm x := rfl

/-- `adicCompletionIntegers.padicIntUniformEquiv` as a ring isomorphism. -/
noncomputable def adicCompletionIntegers.padicIntAlgEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletionIntegers ℚ ≃ₐ[ℤ] ℤ_[primesEquiv v] where
  __ := let e : v.adicCompletionIntegers ℚ ≃+*
          (Valued.v.valuationSubring : ValuationSubring (padicValuation _).Completion) :=
        (mapRingEquiv _ (valuationEquivPadicValuation v).continuous
          (valuationEquivPadicValuation v).symm.continuous).restrict _ _ fun _ ↦ by
          simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
            (v.valuation_surjective ℚ) (surjective_padicValuation _)
      e.trans withValIntegersRingEquiv
  commutes' z := by simp

theorem adicCompletionIntegers.coe_padicIntAlgEquiv_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (x : v.adicCompletionIntegers ℚ) :
    padicIntAlgEquiv v x = adicCompletion.padicAlgEquiv v x := rfl

theorem adicCompletionIntegers.coe_padicIntAlgEquiv_symm_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (x : ℤ_[primesEquiv v]) :
    (adicCompletionIntegers.padicIntAlgEquiv v).symm x =
      (adicCompletion.padicAlgEquiv v).symm x := rfl

theorem adicCompletion.padicAlgEquiv_bijOn (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set.BijOn (padicAlgEquiv v) (v.adicCompletionIntegers ℚ) (subring (primesEquiv v)) := by
  refine ⟨fun x hx ↦ ?_, (padicAlgEquiv v).injective.injOn, fun y hy ↦ ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntAlgEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntAlgEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntAlgEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntAlgEquiv_apply, hx]⟩

end Rat.HeightOneSpectrum

open Rat.HeightOneSpectrum

namespace Padic

variable (p : ℕ) [Fact p.Prime]

@[simps!]
noncomputable def adicCompletionUniformEquiv :
    ℚ_[p] ≃ᵤ (primesEquiv.symm ⟨p, Fact.out⟩).adicCompletion ℚ :=
  (primesEquiv.apply_symm_apply ⟨p, _⟩ ▸ adicCompletion.padicUniformEquiv _).symm

noncomputable def adicCompletionAlgEquiv (p : ℕ) [Fact p.Prime] :
    ℚ_[p] ≃ₐ[ℚ] (primesEquiv.symm ⟨p, Fact.out⟩).adicCompletion ℚ :=
  (primesEquiv.apply_symm_apply ⟨p, _⟩ ▸ adicCompletion.padicAlgEquiv
    (primesEquiv.symm ⟨p, Fact.out⟩)).symm

end Padic

namespace PadicInt

open Padic

variable (p : ℕ) [Fact p.Prime]

@[simps!]
noncomputable def adicCompletionIntegersUniformEquiv :
    ℤ_[p] ≃ᵤ (primesEquiv.symm ⟨p, Fact.out⟩).adicCompletionIntegers ℚ :=
  (primesEquiv.apply_symm_apply ⟨p, _⟩ ▸ adicCompletionIntegers.padicIntUniformEquiv _).symm

noncomputable def adicCompletionIntegersRingEqui :
    ℤ_[p] ≃ₐ[ℤ] (primesEquiv.symm ⟨p, Fact.out⟩).adicCompletionIntegers ℚ :=
  (primesEquiv.apply_symm_apply ⟨p, _⟩ ▸ adicCompletionIntegers.padicIntAlgEquiv _).symm

end PadicInt
