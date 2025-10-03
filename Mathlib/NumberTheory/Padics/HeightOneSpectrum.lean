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
def IsDedekindDomain.HeightOneSpectrum.toNatGenerator {R : Type*} [CommRing R] {F : Type*}
    [EquivLike F R ℤ] [RingEquivClass F R ℤ] (f : F) (v : HeightOneSpectrum R) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map f) |>.natAbs

namespace IsDedekindDomain.HeightOneSpectrum

theorem toNatGenerator_span {R : Type*} [CommRing R] {F : Type*}
    [EquivLike F R ℤ] [RingEquivClass F R ℤ] (f : F) (v : HeightOneSpectrum R) :
    v.asIdeal.map f = Ideal.span {↑(v.toNatGenerator f)} := by
  simp [toNatGenerator]

theorem toNatGenerator_dvd_iff {R : Type*} [CommRing R] {F : Type*}
    [EquivLike F R ℤ] [RingEquivClass F R ℤ] (f : F) (v : HeightOneSpectrum R) {n : ℕ} :
    v.toNatGenerator f ∣ n ↔ ↑n ∈ v.asIdeal.map f := by
  rw [toNatGenerator_span, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

instance {R : Type*} [CommRing R] {F : Type*} [EquivLike F R ℤ] [RingEquivClass F R ℤ] (f : F)
    (v : HeightOneSpectrum R) : Fact (v.toNatGenerator f).Prime :=
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _
    ((Ideal.map_eq_bot_iff_of_injective (EquivLike.injective f)).not.2 v.ne_bot)⟩

noncomputable def toRatpadicValuation {R : Type*} [CommRing R] {F : Type*}
    [EquivLike F R ℤ] [RingEquivClass F R ℤ] (f : F)
    (v : HeightOneSpectrum R) : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation (v.toNatGenerator f)

theorem _root_.Rat.surjective_padicValuation (p : ℕ) [hp : Fact (p.Prime)] :
    Function.Surjective (Rat.padicValuation p) := by
  intro x
  induction x with
  | zero => simp
  | coe x =>
    induction x with | ofAdd x
    rcases le_or_gt 0 x with (hx | hx) <;> simp only [Rat.padicValuation, WithZero.exp]
    · use (p ^ x.natAbs)⁻¹
      simp [hp.out.ne_zero, padicValRat.pow, hx]
    · use p ^ x.natAbs
      simp [hp.out.ne_zero, padicValRat.pow, abs_eq_neg_self.2 (le_of_lt hx)]

theorem intValuation_eq_one_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    {v : HeightOneSpectrum R} {x : R} : v.intValuation x = 1 ↔ x ∉ v.asIdeal := by
  refine ⟨fun h ↦ by simp [← (intValuation_lt_one_iff_mem _ _).not, h], fun h ↦ ?_⟩
  exact le_antisymm (v.intValuation_le_one x) <| by
    simp [← not_lt, (v.intValuation_lt_one_iff_mem _).not, h]

open scoped algebraMap in
theorem valuation_le_one_iff {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (a : R) {b : R} (hb : b ≠ 0)
    (h : b ∈ v.asIdeal → a ∉ v.asIdeal) :
    v.valuation K (a / b) ≤ 1 ↔ b ∉ v.asIdeal := by
  refine ⟨fun hv ↦ ?_, fun hb ↦ by
    simp [valuation_of_algebraMap, intValuation_eq_one_iff.2 hb, intValuation_le_one]⟩
  contrapose! hv
  have ha₀ : a ≠ 0 := fun _ ↦ by simp_all
  have hva : v.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp [ha₀])
  have hvb : v.valuation K b ≠ 0 := (Valuation.ne_zero_iff _).2 (by simp [hb])
  rw [← WithZero.log_lt_log one_ne_zero ((Valuation.ne_zero_iff _).2 (by simp [ha₀, hb])),
    map_div₀, WithZero.log_div hva hvb, WithZero.log_one, Int.sub_pos,
    WithZero.log_lt_log hvb hva]
  simpa [valuation_of_algebraMap, intValuation_eq_one_iff.2 <| h hv, intValuation_lt_one_iff_mem]

theorem _root_.Rat.num_not_mem_ideal_of_den_mem {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (f : R ≃+* ℤ) {𝔭 : Ideal R} (hp : Prime 𝔭) (x : ℚ) :
    ↑x.den ∈ 𝔭 → ↑x.num ∉ 𝔭 := by
  obtain ⟨p, h𝔭⟩ := IsPrincipalIdealRing.principal (Ideal.map f 𝔭) |>.map_ringHom f.symm
  rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ f.bijective, Ideal.submodule_span_eq] at h𝔭
  simp_rw [h𝔭, Ideal.mem_span_singleton]
  intro hden
  have : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective _ f.symm.surjective
  have := isRelPrime_iff_isCoprime.2 <| Nat.Coprime.cast (R := R) x.reduced
  contrapose! this
  simp only [IsRelPrime, not_forall]
  refine ⟨p, ?_, hden, (Ideal.prime_span_singleton_iff.1 <| h𝔭 ▸ hp).not_unit⟩
  rcases lt_or_ge x.num 0 with (h₀ | h₀)
  · simpa [abs_eq_neg_self.2 (le_of_lt h₀)]
  · simpa [abs_eq_self.2 h₀]

theorem _root_.Rat.valuation_le_one_iff_den {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (f : R ≃+* ℤ) (𝔭 : HeightOneSpectrum R) (x : ℚ) :
    𝔭.valuation ℚ x ≤ 1 ↔ ↑x.den ∉ 𝔭.asIdeal := by
  have : (x.den : R) ≠ 0 := fun h ↦ by simpa using congrArg f h
  simp [← 𝔭.valuation_le_one_iff ℚ x.num this (x.num_not_mem_ideal_of_den_mem f 𝔭.prime),
    x.num_div_den]

theorem valuation_equiv_toRatpadicValuation {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (f : R ≃+* ℤ)
    (𝔭 : HeightOneSpectrum R) :
    (𝔭.valuation ℚ).IsEquiv (𝔭.toRatpadicValuation f) := by
  simp [Valuation.isEquiv_iff_val_le_one,  Rat.padicValuation_le_one_iff, Ideal.map_symm,
    Rat.valuation_le_one_iff_den f, toNatGenerator_dvd_iff, toRatpadicValuation,
    ← Ideal.apply_mem_of_equiv_iff (f := f.symm),  Ideal.comap_map_of_bijective _ f.bijective]

noncomputable def withValEquiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] (f : R ≃+* ℤ) (𝔭 : HeightOneSpectrum R) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal (𝔭.toRatpadicValuation f) :=
  Valuation.IsEquiv.uniformEquiv (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
    (𝔭.valuation_equiv_toRatpadicValuation f)

noncomputable
def _root_.Rat.adicCompletionEquivPadicCompletion {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R ℚ] [IsFractionRing R ℚ] {F : Type*} [EquivLike F R ℤ] [RingEquivClass F R ℤ]
    (f : F) (𝔭 : HeightOneSpectrum R) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭.toNatGenerator f] := by
  apply UniformSpace.Completion.mapEquiv (𝔭.withValEquiv f) |>.trans Padic.withValUniformEquiv

end IsDedekindDomain.HeightOneSpectrum
