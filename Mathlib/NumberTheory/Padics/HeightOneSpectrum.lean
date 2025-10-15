import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

open IsDedekindDomain

open scoped NumberField WithZero

noncomputable
def IsDedekindDomain.HeightOneSpectrum.natGenerator {R : Type*} [CommRing R]
    [h : Nonempty (R ≃+* ℤ)] (v : HeightOneSpectrum R) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map h.some) |>.natAbs

namespace IsDedekindDomain.HeightOneSpectrum

noncomputable instance {R : Type*} [CommRing R] [Nonempty (R ≃+* ℤ)] :
    CoeOut (HeightOneSpectrum R) ℕ where
  coe := natGenerator

theorem span_natGenerator {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) :
    Ideal.span {↑v} = v.asIdeal.map h.some := by
  simp [natGenerator]

theorem natGenerator_dvd_iff {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) {n : ℕ} :
    ↑v ∣ n ↔ ↑n ∈ v.asIdeal.map h.some := by
  rw [← span_natGenerator, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

instance {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) : Fact (Nat.Prime v) :=
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective h.some.injective).not.2 v.ne_bot)⟩

theorem valuation_equiv_padicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    (𝔭.valuation ℚ).IsEquiv (Rat.padicValuation 𝔭) := by
  simp [Valuation.isEquiv_iff_val_le_one, Rat.padicValuation_le_one_iff,
    Rat.valuation_le_one_iff_den, natGenerator_dvd_iff,
    ← Ideal.apply_mem_of_equiv_iff (f := Classical.arbitrary (R ≃+* ℤ))]

noncomputable def valuationEquivPadicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal (Rat.padicValuation 𝔭) :=
  Valuation.IsEquiv.uniformEquiv (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
    𝔭.valuation_equiv_padicValuation

noncomputable
def adicCompletionEquivPadic {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭] :=
  (UniformSpace.Completion.mapEquiv 𝔭.valuationEquivPadicValuation).trans Padic.withValUniformEquiv

open UniformSpace.Completion in
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

noncomputable def adicCompletionIntegersEquivPadicInt {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletionIntegers ℚ ≃ᵤ ℤ_[𝔭] :=
  let e : 𝔭.adicCompletionIntegers ℚ ≃ᵤ
      (Valued.v.valuationSubring : ValuationSubring (Rat.padicValuation 𝔭).Completion) :=
    (UniformSpace.Completion.mapEquiv 𝔭.valuationEquivPadicValuation).subtype fun _ ↦ by
      simpa using 𝔭.valuation_equiv_padicValuation.valuedCompletion_le_one_iff
        (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
  e.trans PadicInt.withValIntegersUniformEquiv

instance : Nonempty (𝓞 ℚ ≃+* ℤ) := ⟨Rat.ringOfIntegersEquiv⟩

instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation ℚ Γ₀} :
    Nonempty (𝓞 (WithVal v) ≃+* ℤ) := ⟨Rat.ringOfIntegersWithValEquiv v⟩

noncomputable example (𝔭 : HeightOneSpectrum (𝓞 ℚ)) : 𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭] :=
  𝔭.adicCompletionEquivPadic

noncomputable example (𝔭 : HeightOneSpectrum (𝓞 ℚ)) : CompactSpace (𝔭.adicCompletionIntegers ℚ) :=
  𝔭.adicCompletionIntegersEquivPadicInt.toHomeomorph.symm.compactSpace

end IsDedekindDomain.HeightOneSpectrum
