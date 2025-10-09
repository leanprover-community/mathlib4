import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic

open IsDedekindDomain

open scoped NumberField WithZero

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

noncomputable
def IsDedekindDomain.HeightOneSpectrum.toNatGenerator {R : Type*} [CommRing R]
    [h : Nonempty (R ≃+* ℤ)] (v : HeightOneSpectrum R) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map h.some) |>.natAbs

namespace IsDedekindDomain.HeightOneSpectrum

theorem toNatGenerator_span {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) :
    v.asIdeal.map h.some = Ideal.span {↑v.toNatGenerator} := by
  simp [toNatGenerator]

theorem toNatGenerator_dvd_iff {R : Type*} [CommRing R] [h : Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) {n : ℕ} :
    v.toNatGenerator ∣ n ↔ ↑n ∈ v.asIdeal.map h.some := by
  rw [toNatGenerator_span, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

instance {R : Type*} [CommRing R] [Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) : Fact (v.toNatGenerator).Prime :=
  let f := Classical.arbitrary (R ≃+* ℤ)
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective f.injective).not.2 v.ne_bot)⟩

noncomputable def toRatpadicValuation {R : Type*} [CommRing R] [Nonempty (R ≃+* ℤ)]
    (v : HeightOneSpectrum R) : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation v.toNatGenerator

theorem valuation_equiv_toRatpadicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [h : Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    (𝔭.valuation ℚ).IsEquiv (𝔭.toRatpadicValuation) := by
  simp [Valuation.isEquiv_iff_val_le_one, Rat.padicValuation_le_one_iff,
    Rat.valuation_le_one_iff_den, toNatGenerator_dvd_iff, toRatpadicValuation,
    ← Ideal.apply_mem_of_equiv_iff (f := h.some)]

noncomputable def withValEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal 𝔭.toRatpadicValuation :=
  Valuation.IsEquiv.uniformEquiv (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
    𝔭.valuation_equiv_toRatpadicValuation

noncomputable
def _root_.Rat.adicCompletionEquivPadicCompletion {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭.toNatGenerator] := by
  apply UniformSpace.Completion.mapEquiv 𝔭.withValEquiv |>.trans Padic.withValUniformEquiv

open UniformSpace.Completion in
theorem _root_.Valuation.IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀'] {v' : Valuation K Γ₀'} (h : v.IsEquiv v')
    (hv : Function.Surjective v) (hv' : Function.Surjective v')
    {x : v.Completion} :
    Valued.v x ≤ 1 ↔ Valued.v (mapEquiv (h.uniformEquiv hv hv') x) ≤ 1 := by
  apply UniformSpace.Completion.induction_on
    (p := fun x ↦ Valued.v x ≤ 1 ↔ Valued.v (mapEquiv (h.uniformEquiv hv hv') x) ≤ 1) x
  · have : ⇑(mapEquiv (h.uniformEquiv hv hv')) =
        ⇑(mapEquiv (h.uniformEquiv hv hv')).toHomeomorph := rfl
    simp_rw [this]
    apply Homeomorph.isClosed_setOf_iff (q := fun x ↦ Valued.v x ≤ 1)
      (hs := Valued.isClopen_closedBall _ (by norm_num))
      (ht := Valued.isClopen_closedBall _ (by norm_num))
  · intro a
    simp [← WithVal.apply_equiv, mapEquiv]
    rw [UniformSpace.Completion.map_coe
      (Valuation.IsEquiv.uniformEquiv hv hv' h).uniformContinuous]
    simp [Valuation.IsEquiv.uniformEquiv, Equiv.toUniformEquivOfIsUniformInducing]
    exact h.le_one_iff_le_one (x := WithVal.equiv v a)

noncomputable
def _root_.Rat.adicCompletionIntegersEquivPadicInt {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletionIntegers ℚ ≃ᵤ
      (Valued.v : Valuation 𝔭.toRatpadicValuation.Completion _).valuationSubring := by
  apply (UniformSpace.Completion.mapEquiv 𝔭.withValEquiv).subtype
  intro
  simpa using 𝔭.valuation_equiv_toRatpadicValuation.valuedCompletion_le_one_iff
    (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)

noncomputable
def _root_.Rat.adicCompletionIntegersEquivPadicIntRingEquiv {R : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [Nonempty (R ≃+* ℤ)] (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletionIntegers ℚ ≃ᵤ ℤ_[𝔭.toNatGenerator] :=
  (Rat.adicCompletionIntegersEquivPadicInt 𝔭).trans PadicInt.withValIntegersUniformEquiv

instance : Nonempty (𝓞 ℚ ≃+* ℤ) := ⟨Rat.ringOfIntegersEquiv⟩

instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation ℚ Γ₀} :
    Nonempty (𝓞 (WithVal v) ≃+* ℤ) := ⟨Rat.ringOfIntegersWithValEquiv v⟩

noncomputable
example (𝔭 : HeightOneSpectrum (𝓞 ℚ)) : 𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭.toNatGenerator] :=
  Rat.adicCompletionEquivPadicCompletion 𝔭

end IsDedekindDomain.HeightOneSpectrum
