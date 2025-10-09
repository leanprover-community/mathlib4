import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Padics.ProperSpace

open IsDedekindDomain

open scoped NumberField WithZero

@[simps!]
noncomputable def UniformSpace.Completion.mapEquiv {α β : Type*} [UniformSpace α] [UniformSpace β]
    (h : α ≃ᵤ β) : UniformSpace.Completion α ≃ᵤ UniformSpace.Completion β where
  toFun := .map h
  invFun := .map h.symm
  uniformContinuous_toFun := uniformContinuous_map
  uniformContinuous_invFun := uniformContinuous_map
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    apply ext (.comp continuous_map continuous_map) continuous_id fun a ↦ ?_
    simp [map_coe h.uniformContinuous, map_coe h.symm.uniformContinuous]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    apply ext (.comp continuous_map continuous_map) continuous_id fun a ↦ ?_
    simp [map_coe h.symm.uniformContinuous, map_coe h.uniformContinuous]

@[simp]
theorem UniformSpace.Completion.mapEquiv_cast_apply {α β : Type*} [UniformSpace α] [UniformSpace β]
    (h : α ≃ᵤ β) (a : α) :
    UniformSpace.Completion.mapEquiv h (↑a : UniformSpace.Completion α) = ↑(h a) := by
  rw [mapEquiv_apply, map_coe h.uniformContinuous]

/-
def HeightOneSpectrum.mapEquiv {R S F : Type*} [CommRing R] [CommRing S] [EquivLike F R S]
    [RingEquivClass F R S] (f : F) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun v := ⟨v.asIdeal.map f, Ideal.map_isPrime_of_equiv f,
    mt (Ideal.map_eq_bot_iff_of_injective (EquivLike.injective f)).1 v.ne_bot⟩
  invFun v := ⟨v.asIdeal.map (RingEquiv.symm f), Ideal.map_isPrime_of_equiv _,
    mt (Ideal.map_eq_bot_iff_of_injective (EquivLike.injective _)).1 v.ne_bot⟩
  left_inv v := by
    simp only [Ideal.map_symm]
    congr
    exact Ideal.comap_map_of_bijective f (EquivLike.toEquiv f).bijective
  right_inv v := by
    simp only [Ideal.map_symm]
    congr
    exact Ideal.map_comap_of_surjective f (EquivLike.toEquiv f).surjective _

noncomputable
def Rat.ringOfIntegersSpectrumEquiv : HeightOneSpectrum (𝓞 ℚ) ≃ HeightOneSpectrum ℤ :=
    HeightOneSpectrum.mapEquiv ringOfIntegersEquiv
-/

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
    rw [Valued.valuedCompletion_apply, ← WithVal.apply_equiv, mapEquiv_cast_apply]
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
