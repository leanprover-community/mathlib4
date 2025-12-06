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

## Main definitions
- `Rat.HeightOneSpectrum.natGenerator v` : the generator in `ℕ` of a height-one prime ideal
  in `𝓞 ℚ`.
- `Rat.HeightOneSpectrum.padicUniformEquiv v` : `v.adicCompletion ℚ ≃ᵤ ℚ_[natGenerator v]`.
- `Rat.HeightOneSpectrum.padicAlgEquiv v` : `v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[natGenerator v]`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntUniformEquiv v` :
  `v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v]`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntRingEquiv v` :
  `v.adicCompletionIntegers ℚ ≃+* ℤ_[natGenerator v]`.
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
    natGenerator v ∣ n ↔ ↑n ∈ v.asIdeal.map Rat.ringOfIntegersEquiv := by
  rw [← span_natGenerator, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

local instance (v : HeightOneSpectrum (𝓞 ℚ)) : Fact (Nat.Prime (natGenerator v)) :=
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective ringOfIntegersEquiv.injective).not.2 v.ne_bot)⟩

theorem valuation_equiv_padicValuation (v : HeightOneSpectrum (𝓞 ℚ)) :
    (v.valuation ℚ).IsEquiv (Rat.padicValuation (natGenerator v)) := by
  simp [Valuation.isEquiv_iff_val_le_one, padicValuation_le_one_iff, valuation_le_one_iff_den,
    natGenerator_dvd_iff, ← Ideal.apply_mem_of_equiv_iff (f := ringOfIntegersEquiv)]

/-- The uniform space isomorphism `ℚ ≃ᵤ ℚ`, where the LHS has the uniformity from
`HeightOneSpectrum.valuation ℚ v` and the RHS has uniformity from
`Rat.padicValuation (natGenerator v)`, for a height-one prime ideal
`v : HeightOneSpectrum (𝓞 ℚ)`. -/
noncomputable def valuationEquivPadicValuation (v : HeightOneSpectrum (𝓞 ℚ)) :
    WithVal (v.valuation ℚ) ≃ᵤ WithVal (Rat.padicValuation (natGenerator v)) :=
  (valuation_equiv_padicValuation v).uniformEquiv (v.valuation_surjective ℚ)
    (surjective_padicValuation _)

/-- The uniform space isomorphism `v.adicCompletion ℚ ≃ᵤ ℚ_[natGenerator v]`. -/
noncomputable def adicCompletion.padicUniformEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃ᵤ ℚ_[natGenerator v] :=
  (mapEquiv (valuationEquivPadicValuation v)).trans Padic.withValUniformEquiv

/-- `adicCompletion.padicUniformEquiv` as a `ℚ`-algebra isomorphism. -/
noncomputable def adicCompletion.padicAlgEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[natGenerator v] where
  __ := (mapRingEquiv _ (valuationEquivPadicValuation v).continuous
      (valuationEquivPadicValuation v).symm.continuous).trans Padic.withValRingEquiv
  commutes' q := by simp

/-- The uniform space isomorphism `v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v]`. -/
noncomputable def adicCompletionIntegers.padicIntUniformEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v] :=
  let e : v.adicCompletionIntegers ℚ ≃ᵤ
      (Valued.v.valuationSubring : ValuationSubring (Rat.padicValuation _).Completion) :=
    (mapEquiv (valuationEquivPadicValuation v)).subtype fun _ ↦ by
      simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (v.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans withValIntegersUniformEquiv

/-- `adicCompletionIntegers.padicIntUniformEquiv` as a ring isomorphism. -/
noncomputable def adicCompletionIntegers.padicIntRingEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletionIntegers ℚ ≃+* ℤ_[natGenerator v] :=
  let e : v.adicCompletionIntegers ℚ ≃+*
      (Valued.v.valuationSubring : ValuationSubring (padicValuation _).Completion) :=
    (mapRingEquiv _ (valuationEquivPadicValuation v).continuous
      (valuationEquivPadicValuation v).symm.continuous).restrict _ _ fun _ ↦ by
      simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (v.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans withValIntegersRingEquiv

theorem adicCompletionIntegers.coe_padicIntRingEquiv_apply (v : HeightOneSpectrum (𝓞 ℚ))
    (x : v.adicCompletionIntegers ℚ) :
    padicIntRingEquiv v x = adicCompletion.padicAlgEquiv v x := rfl

theorem adicCompletion.padicAlgEquiv_bijOn (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set.BijOn (padicAlgEquiv v) (v.adicCompletionIntegers ℚ) (subring (natGenerator v)) := by
  refine ⟨fun x hx ↦ ?_, (padicAlgEquiv v).injective.injOn, fun y hy ↦ ?_⟩
  · rw [← adicCompletionIntegers.coe_padicIntRingEquiv_apply v ⟨x, hx⟩]
    exact norm_le_one ((adicCompletionIntegers.padicIntRingEquiv v) ⟨x, hx⟩)
  · obtain ⟨x, hx⟩ := (adicCompletionIntegers.padicIntRingEquiv v).surjective ⟨y, hy⟩
    refine ⟨x, x.2, by rw [← adicCompletionIntegers.coe_padicIntRingEquiv_apply, hx]⟩

end Rat.HeightOneSpectrum
