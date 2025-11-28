import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic

open IsDedekindDomain UniformSpace.Completion NumberField

namespace Rat.RingOfIntegers.HeightOneSpectrum

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

theorem _root_.Valuation.IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀'] {v' : Valuation K Γ₀'} (h : v.IsEquiv v')
    (hv : Function.Surjective v) (hv' : Function.Surjective v') {x : v.Completion} :
    Valued.v x ≤ 1 ↔ Valued.v (mapEquiv (h.uniformEquiv hv hv') x) ≤ 1 := by
  induction x using induction_on with
  | hp =>
    exact (mapEquiv (h.uniformEquiv hv hv')).toHomeomorph.isClosed_setOf_iff
      (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
  | ih a =>
    rw [Valued.valuedCompletion_apply, ← WithVal.apply_equiv, mapEquiv_coe]
    simpa using h.le_one_iff_le_one

/-- The uniform space isomorphism `v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v]`. -/
noncomputable def adicCompletionIntegers.padicIntUniformEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletionIntegers ℚ ≃ᵤ ℤ_[natGenerator v] :=
  let e : v.adicCompletionIntegers ℚ ≃ᵤ
      (Valued.v.valuationSubring : ValuationSubring (Rat.padicValuation _).Completion) :=
    (mapEquiv (valuationEquivPadicValuation v)).subtype fun _ ↦ by
      simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (v.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans PadicInt.withValIntegersUniformEquiv

/-- `adicCompletionIntegers.padicIntUniformEquiv` as a ring isomorphism. -/
noncomputable def adicCompletionIntegers.padicIntRingEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletionIntegers ℚ ≃+* ℤ_[natGenerator v] :=
  let e : v.adicCompletionIntegers ℚ ≃+*
      (Valued.v.valuationSubring : ValuationSubring (padicValuation _).Completion) :=
    (mapRingEquiv _ (valuationEquivPadicValuation v).continuous
      (valuationEquivPadicValuation v).symm.continuous).restrict _ _ fun _ ↦ by
      simpa using (valuation_equiv_padicValuation v).valuedCompletion_le_one_iff
        (v.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans PadicInt.withValIntegersRingEquiv

theorem adicCompletion.padicAlgEquiv_bijOn (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set.BijOn (padicAlgEquiv v) (v.adicCompletionIntegers ℚ)
      (PadicInt.subring (natGenerator v)) := by
  refine ⟨?_, (padicAlgEquiv v).injective.injOn, ?_⟩
  · intro x hx
    simp
    change ‖(adicCompletionIntegers.padicIntRingEquiv v ⟨x, hx⟩)‖ ≤ 1
    exact PadicInt.norm_le_one ((adicCompletionIntegers.padicIntRingEquiv v) ⟨x, hx⟩)
  · have := (adicCompletionIntegers.padicIntRingEquiv v).surjective
    intro y hy
    obtain ⟨x, hx⟩ := this ⟨y, hy⟩
    use x
    use x.2
    change (adicCompletionIntegers.padicIntRingEquiv v x) = y
    rw [hx]

end Rat.RingOfIntegers.HeightOneSpectrum
