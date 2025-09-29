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
def IsDedekindDomain.HeightOneSpectrum.toNatGenerator (𝔭 : HeightOneSpectrum ℤ) : ℕ :=
    (Submodule.IsPrincipal.generator 𝔭.asIdeal).natAbs

namespace IsDedekindDomain.HeightOneSpectrum

instance (𝔭 : HeightOneSpectrum ℤ) : Fact 𝔭.toNatGenerator.Prime :=
  ⟨Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _ 𝔭.ne_bot⟩

noncomputable
def toRatpadicValuation (𝔭 : HeightOneSpectrum ℤ) :
      Valuation ℚ ℤᵐ⁰ :=
    Rat.padicValuation 𝔭.toNatGenerator

set_option pp.proofs true in
theorem _root_.Valuation.IsEquiv.exists_orderMonoidIso {K : Type*} [Ring K] {Γ₀ Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    {v : Valuation K Γ₀} {v' : Valuation K Γ₀'} (h : v.IsEquiv v') :
    ∃ ϕ : Γ₀ ≃o Γ₀', ϕ ∘ v = v' := by
  have hv : Function.Surjective v := sorry
  have hv' : Function.Surjective v' := sorry
  let toFun : Γ₀ → Γ₀' := fun γ ↦ v' (hv γ).choose
  let invFun : Γ₀' → Γ₀ := fun γ' ↦ v (hv' γ').choose
  let ϕ : Γ₀ ≃o Γ₀' := {
    toFun := toFun
    invFun := invFun
    left_inv := by
      simp [toFun, invFun, Function.leftInverse_iff_comp]
      ext γ
      simp
      have := (hv γ).choose_spec
      rw [← this]
      sorry
    right_inv := sorry
    map_rel_iff' := by
      intro a b
      simp [toFun]
      rw [← h]
      rw [(hv a).choose_spec, (hv b).choose_spec]
  }
  use ϕ
  simp [ϕ, toFun]
  ext a
  have := (hv (v a)).choose_spec
  simp
  sorry

def _root_.Valued.uniformEquiv_of_isEquiv_v {K : Type*} [Ring K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    [i : Valued K Γ₀] [i' : Valued K Γ₀] (h : i.v.IsEquiv i'.v) :
    @UniformEquiv K K i.toUniformSpace i'.toUniformSpace := by
  apply @Equiv.toUniformEquivOfIsUniformInducing K K i.toUniformSpace i'.toUniformSpace
    (Equiv.refl _)
  rw [@isUniformInducing_iff_uniformSpace]
  obtain ⟨ϕ, hϕ⟩ := h.exists_orderMonoidIso
  ext u
  rw [uniformity_comap]
  simp
  simp_rw [i.hasBasis_uniformity.mem_iff, i'.hasBasis_uniformity.mem_iff]
  simp
  constructor
  · rintro ⟨t, ⟨γ, hγ⟩, htu⟩
    have : ϕ.symm γ ≠ 0 := by
      intro h
      rw [← i.v.map_zero] at h
      have h := congrArg ϕ h
      have := congrFun hϕ 0
      rw [Function.comp_apply] at this
      rw [this] at h
      simp at h
    use Units.mk0 _ this
    apply Set.Subset.trans _ htu
    intro p hp
    simp at hp
    apply hγ
    simp
    rw [← hϕ]
    simp
    exact ϕ.lt_symm_apply.1 hp
  · rintro ⟨γ, hγ⟩
    have : ϕ γ ≠ 0 := by
      intro h
      rw [← i'.v.map_zero] at h
      rw [← hϕ] at h
      simp at h
    use u
    refine ⟨?_, subset_rfl⟩
    use Units.mk0 _ this
    simp
    apply Set.Subset.trans _ hγ
    simp
    intro a b hab
    rw [← hϕ] at hab
    simp at hab
    exact hab

-- prove this by showing valuations are equivalent?
noncomputable def withValEquiv (𝔭 : HeightOneSpectrum ℤ) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal 𝔭.toRatpadicValuation := by
  apply @Valued.uniformEquiv_of_isEquiv_v ℚ _ _ _
    (inferInstanceAs (Valued (WithVal (𝔭.valuation ℚ)) ℤᵐ⁰))
    (inferInstanceAs (Valued (WithVal (𝔭.toRatpadicValuation)) ℤᵐ⁰))
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  change 𝔭.valuation ℚ x ≤ 1 ↔ 𝔭.toRatpadicValuation x ≤ 1
  rw [toRatpadicValuation]
  rw [Rat.padicValuation_le_one_iff]
  rw [toNatGenerator]
  rw [HeightOneSpectrum.valuation_def]
  rw [Valuation.extendToLocalization]
  sorry


noncomputable
def adicCompletionRatEquiv (𝔭 : HeightOneSpectrum ℤ) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭.toNatGenerator] :=
  UniformSpace.Completion.mapEquiv 𝔭.withValEquiv |>.trans Padic.withValUniformEquiv
