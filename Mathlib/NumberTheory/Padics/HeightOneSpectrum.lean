import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Int.Basic
import Mathlib

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
def IsDedekindDomain.HeightOneSpectrum.toNatGenerator (𝔭 : HeightOneSpectrum ℤ) : ℕ :=
    (Submodule.IsPrincipal.generator 𝔭.asIdeal).natAbs

namespace IsDedekindDomain.HeightOneSpectrum

theorem toNatGenerator_span {𝔭 : HeightOneSpectrum ℤ} :
    𝔭.asIdeal = Ideal.span {↑𝔭.toNatGenerator} := by
  simp [toNatGenerator]

theorem toNatGenerator_dvd_iff {𝔭 : HeightOneSpectrum ℤ} {n : ℕ} :
    𝔭.toNatGenerator ∣ n ↔ ↑n ∈ 𝔭.asIdeal := by
  rw [toNatGenerator_span, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

instance (𝔭 : HeightOneSpectrum ℤ) : Fact 𝔭.toNatGenerator.Prime :=
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _ 𝔭.ne_bot⟩

noncomputable def toRatpadicValuation {R : Type*} [CommRing R] (h : R ≃+* ℤ)
    (𝔭 : HeightOneSpectrum R) : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation (HeightOneSpectrum.mapEquiv h 𝔭).toNatGenerator

@[simp]
theorem toRatpadicValuation_rfl {𝔭 : HeightOneSpectrum ℤ} :
    𝔭.toRatpadicValuation (RingEquiv.refl ℤ) = Rat.padicValuation 𝔭.toNatGenerator := by
  simp [toRatpadicValuation, HeightOneSpectrum.mapEquiv, toNatGenerator, Ideal.map]

theorem _root_.Rat.surjective_padicValuation (p : ℕ) [Fact (p.Prime)] :
    Function.Surjective (Rat.padicValuation p) := by
  intro x
  induction x with
  | zero => simp
  | coe x =>
    simp [Rat.padicValuation, -WithZero.exp_neg]
    induction x with | ofAdd x
    simp [WithZero.exp, -ofAdd_neg]
    by_cases hx : 0 ≤ x
    · use (p ^ x.natAbs)⁻¹
      rcases eq_or_ne x 0 with (h | h)
      · simp [h]
      · have : ((p : ℚ) ^ x.natAbs)⁻¹  ≠ 0 := by
          apply inv_ne_zero
          apply pow_ne_zero
          simp
          exact (Fact.out : p.Prime).ne_zero
        simp [this, hx]
    · use p ^ x.natAbs
      rcases eq_or_ne x 0 with (h | h)
      · simp [h]
      · have : ((p : ℚ) ^ x.natAbs) ≠ 0 := by
          apply pow_ne_zero
          simpa using (Fact.out : p.Prime).ne_zero
        simp [this, padicValRat.pow (show (p : ℚ) ≠ 0 by simp [(Fact.out : p.Prime).ne_zero])]
        simp at hx
        have : |x| = -x := by
          simp
          linarith
        simp [this]

theorem valuation_toNatGenerator (𝔭 : HeightOneSpectrum ℤ) :
    𝔭.valuation ℚ 𝔭.toNatGenerator = .exp (-1) := by
  erw [valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
  · simpa [toNatGenerator] using (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).not.1
      𝔭.ne_bot
  · simp [toNatGenerator]

theorem intValuation_eq_one_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (x : R) : v.intValuation x = 1 ↔ x ∉ v.asIdeal := by
  refine ⟨fun h ↦ by simp [← (intValuation_lt_one_iff_mem _ _).not, h], fun h ↦ ?_⟩
  exact le_antisymm (v.intValuation_le_one x) <| by
    simp [← not_lt, (v.intValuation_lt_one_iff_mem _).not, h]

theorem valuation_le_one_iff {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (a : R) (b : nonZeroDivisors R)
    (h : b.1 ∈ v.asIdeal → a ∉ v.asIdeal) :
    v.valuation K (IsLocalization.mk' K a b) ≤ 1 ↔ ↑b ∉ v.asIdeal := by
  constructor
  · intro hv
    simp at hv
    contrapose! hv
    have : a ∉ v.asIdeal := h hv
    rw [valuation_of_algebraMap, valuation_of_algebraMap]
    rw [← intValuation_lt_one_iff_mem] at hv
    rw [← intValuation_eq_one_iff] at this
    rw [← WithZero.log_lt_log (by norm_num)]
    · rw [WithZero.log_div (by simp_all)]
      · simp [this]
        rw [← WithZero.log_lt_log (intValuation_ne_zero _ _ (by simp)) (by norm_num)] at hv
        simpa
      · apply intValuation_ne_zero
        simp
    · simp
      refine ⟨intValuation_ne_zero _ _ (fun _ ↦ by simp_all), intValuation_ne_zero _ _ (by simp)⟩
  · intro hb
    simp [valuation_of_algebraMap]
    rw [← intValuation_eq_one_iff] at hb
    simp [hb, intValuation_le_one]

theorem _root_.Rat.num_not_mem_ideal_of_den_mem {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (f : R ≃+* ℤ) {𝔭 : Ideal R} (hp : Prime 𝔭) (x : ℚ) :
    ↑x.den ∈ 𝔭 → ↑x.num ∉ 𝔭 := by
  have : Submodule.IsPrincipal (Ideal.map f 𝔭) := by
    exact IsPrincipalIdealRing.principal (Ideal.map f 𝔭)
  obtain ⟨p, hp'⟩ := Submodule.IsPrincipal.map_ringHom f.symm this
  simp [Ideal.comap_map_of_bijective _ f.bijective] at hp'
  rw [hp']
  simp [Ideal.mem_span_singleton]
  intro hden
  have := x.reduced
  haveI : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective _ f.symm.surjective
  have := Nat.Coprime.cast (R := R) x.reduced
  rw [← isRelPrime_iff_isCoprime] at this
  contrapose this
  rw [IsRelPrime]
  simp
  use p
  refine ⟨?_, hden, ?_⟩
  · simp_all
    by_cases h₀ : 0 ≤ x.num
    · rwa [abs_eq_self.2 h₀]
    · rw [abs_eq_neg_self.2 (le_of_lt (not_le.1 h₀))]
      simpa
  · rw [hp'] at hp
    simp at hp
    exact Prime.not_unit hp

theorem _root_.Rat.valuation_le_one_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (f : R ≃+* ℤ) (𝔭 : HeightOneSpectrum R) (x : ℚ) :
    𝔭.valuation ℚ x ≤ 1 ↔ ↑x.den ∉ 𝔭.asIdeal := by
  have : (x.den : R) ≠ 0 := by
    apply_fun f
    simp
  have := 𝔭.valuation_le_one_iff (K := ℚ) x.num ⟨x.den, by simp [this]⟩
  simp at this
  rw [← this]
  · nth_rw 1 [← x.num_div_den]
    simp
  · exact x.num_not_mem_ideal_of_den_mem f 𝔭.prime

theorem valuation_equiv_toRatpadicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (h : R ≃+* ℤ)
    (𝔭 : HeightOneSpectrum R) :
    (𝔭.valuation ℚ).IsEquiv (𝔭.toRatpadicValuation h) := by
  simp [Valuation.isEquiv_iff_val_le_one, toRatpadicValuation, Rat.padicValuation_le_one_iff,
    Rat.valuation_le_one_iff h, toNatGenerator_dvd_iff, HeightOneSpectrum.mapEquiv]
  intro x
  rw [← Ideal.apply_mem_of_equiv_iff (f := h.symm) (x := (x.den : ℤ))]
  rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ h.bijective]
  simp

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] [IsIntegralClosure R ℤ ℚ] (v : Ideal ℤ)

instance : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective _ Rat.ringOfIntegersEquiv.symm.surjective

noncomputable def withValEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (h : R ≃+* ℤ) (𝔭 : HeightOneSpectrum R) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal (𝔭.toRatpadicValuation h) :=
  Valuation.IsEquiv.uniformEquiv (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
    (𝔭.valuation_equiv_toRatpadicValuation h)

noncomputable
def adicCompletionRatEquivInt (𝔭 : HeightOneSpectrum ℤ) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭.toNatGenerator] := by
  apply UniformSpace.Completion.mapEquiv (𝔭.withValEquiv (RingEquiv.refl _)) |>.trans
  exact toRatpadicValuation_rfl ▸ Padic.withValUniformEquiv

noncomputable
def padicCompletionRatEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    let p : ℕ := (HeightOneSpectrum.mapEquiv Rat.ringOfIntegersEquiv v).toNatGenerator
    v.adicCompletion ℚ ≃ᵤ ℚ_[p] :=
  UniformSpace.Completion.mapEquiv (v.withValEquiv Rat.ringOfIntegersEquiv) |>.trans
    Padic.withValUniformEquiv

end IsDedekindDomain.HeightOneSpectrum
