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

instance {K : Type*} [Ring K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} : Preorder (WithVal v) := v.toPreorder

theorem _root_.WithVal.le_def {K : Type*} [Ring K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (a b : WithVal v) :
    a ≤ b ↔ v (WithVal.equiv v a) ≤ v (WithVal.equiv v b) := .rfl

def _root_.WithVal.equivWithVal {K : Type*} [Ring K] {Γ₀ Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    (v : Valuation K Γ₀) (v' : Valuation K Γ₀') :
    WithVal v ≃+* WithVal v' :=
  (WithVal.equiv v).trans (WithVal.equiv v').symm

@[simp]
theorem _root_.WithVal.equiv_equivWithVal_apply {K : Type*} [Ring K] {Γ₀ Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    (v : Valuation K Γ₀) (v' : Valuation K Γ₀') (x : WithVal v) :
    (WithVal.equiv v' (WithVal.equivWithVal v v' x)) = (WithVal.equiv v x) := by
  rfl

def _root_.Valuation.IsEquiv.orderIso {K : Type*} [Ring K] {Γ₀ Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    {v : Valuation K Γ₀} {v' : Valuation K Γ₀'} (h : v.IsEquiv v') :
    WithVal v ≃+*o WithVal v' where
  __ := WithVal.equivWithVal v v'
  map_le_map_iff' := by
    intro a b
    have := h (WithVal.equiv v a) (WithVal.equiv v b)
    rw [WithVal.le_def a b]
    rw [this]
    rfl

theorem _root_.Valuation.IsEquiv.isUniformInducing_equivWithVal {K : Type*} [DivisionRing K]
    {Γ₀ Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    [Nontrivial Γ₀] [Nontrivial Γ₀'] {v : Valuation K Γ₀} {v' : Valuation K Γ₀'}
    (hv : Function.Surjective v) (hv' : Function.Surjective v')
    (h : v.IsEquiv v') :
    IsUniformInducing (WithVal.equivWithVal v v') := by
  rw [isUniformInducing_iff]
  ext u
  simp [(Valued.hasBasis_uniformity _ _).mem_iff]
  constructor
  · rintro ⟨t, ⟨γ, hγ⟩, htu⟩
    obtain ⟨a, ha⟩ := hv' γ
    have : Valued.v (h.orderIso.symm a) ≠ 0 := by
      rw [← WithVal.apply_equiv]

      simp

      have := Units.ne_zero γ

      rintro rfl
      simp at ha
      exact this ha.symm
    use Units.mk0 _ this
    simp
    apply Set.Subset.trans _ htu
    intro p hp
    simp at hp
    rw [← Function.Surjective.preimage_subset_preimage_iff
      (f := Prod.map ⇑(WithVal.equivWithVal v v') ⇑(WithVal.equivWithVal v v'))
      <| Function.RightInverse.surjective (congrFun rfl)] at hγ
    apply hγ
    simp
    rw [← ha]
    have : p.2 - p.1 < h.orderIso.symm a := hp
    rw [← WithVal.apply_equiv]
    have h'' := h.orderIso.toOrderIso.lt_symm_apply (x := p.2 - p.1) (y := a)
    have h' : h.orderIso.toOrderIso.symm = h.orderIso.symm.toOrderIso := rfl
    rw [h'] at h''
    simp at h''
    rw [h''] at this
    exact this
  · rintro ⟨γ, hγ⟩
    use Prod.map (WithVal.equivWithVal v v') (WithVal.equivWithVal v v') '' u
    have hinj :
        Function.Injective (Prod.map (WithVal.equivWithVal v v') (WithVal.equivWithVal v v')) := by
      rw [Prod.map_injective]
      exact ⟨RingEquiv.injective _, RingEquiv.injective _⟩
    constructor
    · obtain ⟨a, ha⟩ := hv γ
      have : Valued.v (h.orderIso a) ≠ 0 := by
        rw [← WithVal.apply_equiv]
        simp
        rintro rfl
        simp at ha
        exact  γ.ne_zero ha.symm
      use Units.mk0 _ this
      simp
      rw [← Set.image_subset_image_iff
        (f := Prod.map ⇑(WithVal.equivWithVal v v') ⇑(WithVal.equivWithVal v v'))
        <| hinj] at hγ
      apply Set.Subset.trans _ hγ
      intro p hp
      simp at hp
      --rw [← WithVal.apply_equiv] at hp
      --rw [← WithVal.apply_equiv] at hp
      have : p.2 - p.1 < h.orderIso a := hp
      use Prod.map (WithVal.equivWithVal v v').symm (WithVal.equivWithVal v v').symm p
      simp [Prod.map_apply']
      rw [← ha]
      change (WithVal.equivWithVal v v').symm p.2 - (WithVal.equivWithVal v v').symm p.1 < a
      have h' := OrderIso.symm_apply_lt (y := p.2 - p.1) (x := a) h.orderIso.toOrderIso
      --simp only [OrderRingIso.toOrderIso_eq_coe, OrderRingIso.coe_toOrderIso] at h'
      --rw [← h'] at this
      have h'' : h.orderIso.toOrderIso.symm = h.orderIso.symm.toOrderIso := rfl
      rw [h''] at h'
      simp at h'
      rw [← h'] at this
      exact this
    · rw [← Prod.map_def, Set.preimage_image_eq _ hinj]

def _root_.Valuation.IsEquiv.uniformEquiv {K : Type*} [DivisionRing K] {Γ₀ Γ₀' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀'] [Nontrivial Γ₀]
    {v : Valuation K Γ₀} {v' : Valuation K Γ₀'} (hv : Function.Surjective v)
    (hv' : Function.Surjective v') (h : v.IsEquiv v') :
    WithVal v ≃ᵤ WithVal v' :=
  Equiv.toUniformEquivOfIsUniformInducing (WithVal.equivWithVal v v')
    (h.isUniformInducing_equivWithVal hv hv')

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
  · simpa [toNatGenerator] using (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).not.1 𝔭.ne_bot
  · simp [toNatGenerator]

theorem intValuation_eq_one_iff (𝔭 : HeightOneSpectrum ℤ) (x : ℤ) :
    𝔭.intValuation x = 1 ↔ x ∉ 𝔭.asIdeal := by
  constructor
  · intro h
    simp at h
    rw [← intValuation_lt_one_iff_mem]
    simp
    simp [h]
  · intro h
    rw [← intValuation_lt_one_iff_mem] at h
    simp at h
    have := intValuation_le_one 𝔭 x
    exact le_antisymm this h

theorem valuation_le_one_iff (𝔭 : HeightOneSpectrum ℤ) (x : ℚ) :
    𝔭.valuation ℚ x ≤ 1 ↔ ¬ 𝔭.toNatGenerator ∣ x.den := by
  constructor
  · intro h
    contrapose! h
    have h' : ¬↑𝔭.toNatGenerator ∣ x.num := by
      have := x.reduced
      contrapose this
      apply Nat.not_coprime_of_dvd_of_dvd (d := 𝔭.toNatGenerator)
      · exact (Int.prime_iff_natAbs_prime.1 <| Submodule.IsPrincipal.prime_generator_of_isPrime _ 𝔭.ne_bot).one_lt
      · simp at this
        exact Int.ofNat_dvd_left.mp this
      · exact h
    rw [← x.num_div_den]
    simp
    erw [valuation_of_algebraMap, valuation_of_algebraMap]
    have : (𝔭.intValuation x.num) = 1 := by
      rw [intValuation_eq_one_iff]
      rw [Submodule.IsPrincipal.mem_iff_generator_dvd]
      simpa [toNatGenerator] using h'
    have h' : 𝔭.intValuation x.den < 1 := by
      rw [intValuation_lt_one_iff_mem]
      rw [Submodule.IsPrincipal.mem_iff_generator_dvd]
      rw [toNatGenerator] at h
      simpa using Int.ofNat_dvd.2 h
    rw [← WithZero.log_lt_log] at h'
    simp at h'
    rw [← WithZero.log_lt_log]
    simp
    rw [WithZero.log_div]
    simp [this]
    exact h'
    · simp_all
    · apply intValuation_ne_zero
      simp
    · norm_num
    · simp
      refine ⟨intValuation_ne_zero _ _ (fun _ ↦ by simp_all), intValuation_ne_zero _ _ (by simp)⟩
    · exact intValuation_ne_zero _ _ (by simp)
    · norm_num
  · intro h
    rw [← x.num_div_den]
    have : 𝔭.intValuation x.den = 1 := by
      rw [intValuation_eq_one_iff]
      rw [Submodule.IsPrincipal.mem_iff_generator_dvd]
      simpa [toNatGenerator] using Int.ofNat_dvd.not.2 h
    simp
    erw [valuation_of_algebraMap, valuation_of_algebraMap]
    rw [this]
    simp
    exact intValuation_le_one 𝔭 x.num

theorem valuation_equiv_toRatpadicValuation (𝔭 : HeightOneSpectrum ℤ) :
    (𝔭.valuation ℚ).IsEquiv (𝔭.toRatpadicValuation) := by
  simp [Valuation.isEquiv_iff_val_le_one, toRatpadicValuation, Rat.padicValuation_le_one_iff,
    valuation_le_one_iff]

noncomputable def withValEquiv (𝔭 : HeightOneSpectrum ℤ) :
    WithVal (𝔭.valuation ℚ) ≃ᵤ WithVal 𝔭.toRatpadicValuation :=
  Valuation.IsEquiv.uniformEquiv (𝔭.valuation_surjective ℚ) (Rat.surjective_padicValuation _)
    𝔭.valuation_equiv_toRatpadicValuation

noncomputable
def adicCompletionRatEquiv (𝔭 : HeightOneSpectrum ℤ) :
    𝔭.adicCompletion ℚ ≃ᵤ ℚ_[𝔭.toNatGenerator] :=
  UniformSpace.Completion.mapEquiv 𝔭.withValEquiv |>.trans Padic.withValUniformEquiv

end IsDedekindDomain.HeightOneSpectrum
