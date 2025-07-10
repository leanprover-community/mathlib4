/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.GroupWithZero.Range
import Mathlib.Algebra.Order.Group.Cyclic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime

/-!
# Discrete Valuations

Given a linearly ordered commutative group with zero `Γ`, a valuation `v : A → Γ` on a ring `A` is
*discrete*, if there is an element `γ : Γˣ` that is `< 1` and generated the range of `v`,
implemented as `MonoidWithZeroHom.valueGroup v`. When `Γ := ℤₘ₀` (defined in
`Multiplicative.termℤₘ₀`), `γ` = ofAdd (-1)` and the condition of being discrete is
equivalent to asking that `ofAdd (-1 : ℤ)` belongs to the image, in turn equivalent to asking that
`1 : ℤ` belongs to the image of the corresponding *additive* valuation.

Note that this definition of discrete implies that the valuation is nontrivial and of rank one, as
is commonly assumed in number theory. To avoid potential confusion with other definitions of
discrete, we use the name `IsRankOneDiscrete` to refer to discrete valuations in this setting.

## Main Definitions
* `Valuation.IsRankOneDiscrete`: We define a `Γ`-valued valuation `v` to be discrete if if there is
an element `γ : Γˣ` that is `< 1` and generates the range of `v`.
* `Valuation.IsUniformizer`: Given a `Γ`-valued valuation `v` on a ring `R`, an element `π : R` is
  a uniformizer if `v π` is a generator of the value group that is `<1`.
* `Valuation.Uniformizer`: A structure bundling an element of a ring and a proof that it is a
  uniformizer.
* `Valuation.valuationSubring_isDiscreteValuationRing_of_isCyclic_of_Nontrivial`: this instance is
  the formalization of Chapter I, Section 1, Proposition 1 in [serre1968] showing that
  the unit ball of a discretely-valued field is a DVR.

## Main Results
* `Valuation.IsUniformizer.of_associated`: An element associated to a uniformizer is itself a
  uniformizer.
* `Valuation.associated_of_isUniformizer`: If two elements are uniformizers, they are associated.
* `Valuation.IsUniformizer.is_generator` A generator of the maximal ideal is a uniformizer when
  the valuation is discrete.
* `Valuation.IsRankOneDiscrete.mk'`: if the `valueGroup` of the valuation `v` is cyclic and
  nontrivial, then `v` is discrete.
* `Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`: If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then there exists a uniformizer for `v`.
* `Valuation.isUniformizer_of_maximalIdeal_eq_span`: Given a discrete valuation `v` on a field `K`,
  a generator of the maximal ideal of `v.valuationSubring` is a uniformizer for `v`.
* `Valuation.valuationSubring_isDiscreteValuationRing` : If `v` is a valuation on a field `K`
  whose value group is cyclic and nontrivial, then `v.valuationSubring` is a discrete
  valuation ring.
* `IsDiscreteValuationRing.isRankOneDiscrete`: Given a DVR `A` and a field `K` satisfying
  `IsFractionRing A K`, the valuation induced on `K` is discrete.
* `IsDiscreteValuationRing.equivValuationSubring` The ring isomorphism between a DVR and the
  unit ball in its field of fractions endowed with the adic valuation of the maximal ideal.


## TODO
* Relate discrete valuations and discrete valuation rings (contained in the project
  <https://github.com/mariainesdff/LocalClassFieldTheory>)
-/

namespace Valuation

open LinearOrderedCommGroup MonoidWithZeroHom Set

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable {A : Type*} [Ring A] (v : Valuation A Γ)

/-- Given a linearly ordered commutative group with zero `Γ` such that `Γˣ` is
nontrivial cyclic, a valuation `v : A → Γ` on a ring `A` is *discrete*, if
`genLTOne Γˣ` belongs to the image. Note that the latter is equivalent to
asking that `1 : ℤ` belongs to the image of the corresponding additive valuation. -/
class IsRankOneDiscrete : Prop where
  exists_generator_lt_one' : ∃ (γ : Γˣ), Subgroup.zpowers γ = (valueGroup v) ∧ γ < 1

namespace IsRankOneDiscrete

variable [IsRankOneDiscrete v]

lemma exists_generator_lt_one : ∃ (γ : Γˣ), Subgroup.zpowers γ = valueGroup v ∧ γ < 1 :=
  exists_generator_lt_one'

/-- Given a discrete valuation `v`, `Valuation.IsRankOneDiscrete.generator` is a generator of
the value group that is `< 1`. -/
noncomputable def generator : Γˣ := (exists_generator_lt_one v).choose

lemma generator_zpowers_eq_valueGroup : (Subgroup.zpowers (generator v)) = valueGroup v :=
  (exists_generator_lt_one v).choose_spec.1

lemma generator_mem_valueGroup :
    (IsRankOneDiscrete.generator v) ∈ valueGroup v := by
  rw [← IsRankOneDiscrete.generator_zpowers_eq_valueGroup]
  exact Subgroup.mem_zpowers (IsRankOneDiscrete.generator v)

lemma generator_lt_one: (generator v) < 1 :=
  (exists_generator_lt_one v).choose_spec.2

lemma generator_ne_one : (generator v) ≠ 1 :=
  ne_of_lt <| generator_lt_one v

lemma generator_zpowers_eq_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    Units.val '' (Subgroup.zpowers (generator w)) = range w \ {0} := by
  rw [generator_zpowers_eq_valueGroup, valueGroup_eq_range]

lemma generator_mem_range (K : Type*) [Field K] (w : Valuation K Γ) [IsRankOneDiscrete w] :
    ↑(generator w) ∈ range w := by
  apply diff_subset
  rw [← generator_zpowers_eq_range]
  exact ⟨generator w, by simp⟩

lemma generator_ne_zero : (generator v : Γ) ≠ 0 := by simp

instance : IsCyclic <| valueGroup v := by
  rw [isCyclic_iff_exists_zpowers_eq_top, ← generator_zpowers_eq_valueGroup]
  use ⟨generator v, by simp⟩
  rw [eq_top_iff]
  rintro ⟨g, k, hk⟩
  simp only [Subgroup.mem_top, forall_const]
  use k
  ext
  simp [← hk]

instance : Nontrivial (valueGroup v) :=
  ⟨1, ⟨generator v, by simp [← generator_zpowers_eq_valueGroup]⟩, ne_of_gt <| generator_lt_one v⟩

instance [IsRankOneDiscrete v] : Nontrivial (valueMonoid v) := by
  by_contra H
  apply ((valueGroup v).nontrivial_iff_ne_bot).mp (by infer_instance)
  apply Subgroup.closure_eq_bot_iff.mpr
  rw [not_nontrivial_iff_subsingleton, subsingleton_iff] at H
  intro x hx
  specialize H ⟨x, hx⟩ ⟨1, one_mem_valueMonoid v⟩
  simpa using H

instance [IsRankOneDiscrete v] : v.IsNontrivial := by
  constructor
  obtain ⟨⟨γ, π, hπ⟩, hγ⟩ := (nontrivial_iff_exists_ne (1 : valueMonoid v)).mp (by infer_instance)
  use π
  constructor
  · simp [hπ]
  · rw [hπ]
    simp only [← MonoidWithZeroHom.coe_one, ne_eq, Subtype.mk.injEq] at hγ
    simp [hγ, Units.val_eq_one]

end IsRankOneDiscrete

theorem not_isField [Nontrivial ↥(valueGroup v)] [IsCyclic (valueGroup v)] : ¬ IsField K₀ := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  rintro ⟨-, -, h⟩
  have := hπ.ne_zero
  simp only [ne_eq, Subring.coe_eq_zero_iff] at this
  specialize h this
  rw [← isUnit_iff_exists_inv] at h
  exact hπ.not_isUnit h

theorem isUniformizer_of_maximalIdeal_eq_span [v.IsRankOneDiscrete] {r : K₀}
    (hr : maximalIdeal v.valuationSubring = Ideal.span {r}) :
    IsUniformizer v r := by
  have hr₀ : r ≠ 0 := by
    intro h
    rw [h, Set.singleton_zero, span_zero] at hr
    exact Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal v.valuationSubring)
      (not_isField v) hr
  obtain ⟨π, hπ⟩ := exists_isUniformizer_of_isCyclic_of_nontrivial v
  obtain ⟨n, u, hu⟩ := pow_Uniformizer hr₀ ⟨π, hπ⟩
  rw [Uniformizer.is_generator ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr
  exact hπ.of_associated hr

section CyclicNontrivial

variable [IsCyclic (valueGroup v)] [Nontrivial (valueGroup v)]

theorem ideal_isPrincipal (I : Ideal K₀) : I.IsPrincipal := by
  suffices ∀ P : Ideal K₀, P.IsPrime → Submodule.IsPrincipal P by
    exact (IsPrincipalIdealRing.of_prime this).principal I
  intro P hP
  by_cases h_ne_bot : P = ⊥
  · rw [h_ne_bot]; exact bot_isPrincipal
  · let π : Uniformizer v := Nonempty.some (by infer_instance)
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
    obtain ⟨n, ⟨u, hu⟩⟩ := pow_Uniformizer hx₀ π
    by_cases hn : n = 0
    · rw [← Subring.coe_mul, hn, pow_zero, one_mul, SetLike.coe_eq_coe] at hu
      refine (hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx_mem ?_)).elim
      simp only [hu, Units.isUnit]
    · rw [← Subring.coe_mul, SetLike.coe_eq_coe] at hu
      rw [hu, Ideal.mul_unit_mem_iff_mem P u.isUnit,
        IsPrime.pow_mem_iff_mem hP _ (pos_iff_ne_zero.mpr hn), ← Ideal.span_singleton_le_iff_mem,
        ← π.is_generator ] at hx_mem
      rw [← Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal K₀) hP.ne_top hx_mem]
      exact ⟨π.1, π.is_generator⟩

theorem valuationSubring_isPrincipalIdealRing : IsPrincipalIdealRing K₀ :=
  ⟨fun I ↦ ideal_isPrincipal v I⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
instance valuationSubring_isDiscreteValuationRing [IsCyclic (valueGroup v)]
    [Nontrivial (valueGroup v)] : IsDiscreteValuationRing K₀ where
  toIsPrincipalIdealRing := valuationSubring_isPrincipalIdealRing v
  toIsLocalRing := inferInstance
  not_a_field' := by rw [ne_eq, ← isField_iff_maximalIdeal_eq]; exact not_isField v

end CyclicNontrivial

end Field

end Valuation

namespace IsDiscreteValuationRing

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing MonoidWithZeroHom Multiplicative Subring Valuation

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The maximal ideal of a discrete valuation ring. -/
def maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

instance isRankOneDiscrete :
    IsRankOneDiscrete ((maximalIdeal A).valuation K) := by
  have : Nontrivial ↥(valueGroup (valuation K (maximalIdeal A))) := by
    let v := (maximalIdeal A).valuation K
    let π := valuation_exists_uniformizer K (maximalIdeal A)|>.choose
    have hπ : v π = ↑(ofAdd (-1 : ℤ)) :=
      valuation_exists_uniformizer K (maximalIdeal A)|>.choose_spec
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    use Units.mk0 (v π) (by simp [hπ])
    constructor
    · apply mem_valueGroup
      simp only [Units.val_mk0, Set.mem_range]
      use π
    · simp only [hπ]
      exact not_eq_of_beq_eq_false rfl
  infer_instance

variable {A K}

open scoped WithZero

theorem exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x ≤ (1 : ℤᵐ⁰)) :
    ∃ a : A, algebraMap A K a = x := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, ⟨b, ⟨hb, h_frac⟩⟩⟩ := IsFractionRing.div_surjective (A := A) x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha, map_zero, zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    replace hb := (mul_mem_nonZeroDivisors.mp hb).2
    rw [mul_comm (w : A) _, map_mul _ (u : A) _, map_mul _ _ (w : A), div_eq_mul_inv, mul_assoc,
      Valuation.map_mul, Integers.one_of_isUnit' u.isUnit (valuation_le_one _), one_mul,
      mul_inv, ← mul_assoc, Valuation.map_mul, map_mul, map_inv₀, map_inv₀,
      Integers.one_of_isUnit' w.isUnit (valuation_le_one _), inv_one, mul_one, ← div_eq_mul_inv,
      ← map_div₀, ← @IsFractionRing.mk'_mk_eq_div _ _ K _ _ _ (π ^ n) _ hb,
      valuation_of_mk', map_pow, map_pow] at H
    have h_mn : m ≤ n := by
      have v_π_lt_one := (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have v_π_ne_zero : (maximalIdeal A).intValuation π ≠ 0 := intValuation_ne_zero _ _ hπ.ne_zero
      zify
      rw [← WithZero.coe_one, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← ofAdd_zero,
        ← zpow_neg, ← zpow_add₀ v_π_ne_zero, ← sub_eq_add_neg] at H
      rwa [← sub_nonneg, ← zpow_le_one_iff_right_of_lt_one₀ (zero_lt_iff.mpr v_π_ne_zero)
        v_π_lt_one]
    use u * π ^ (n - m) * w.2
    simp only [← h_frac, Units.inv_eq_val_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebraMap A _) ↑u) _ _]
    congr 1
    rw [div_eq_mul_inv, mul_inv, mul_comm ((algebraMap A _) ↑w)⁻¹ _, ←
      mul_assoc _ _ ((algebraMap A _) ↑w)⁻¹]
    congr
    rw [pow_sub₀ _ _ h_mn]
    apply IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hπ.ne_zero

theorem map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ =
    ((maximalIdeal A).valuation K).valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR `A` and the valuation subring of a field of fractions
  of `A` endowed with the adic valuation of the maximal ideal. -/
noncomputable def equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

end IsDiscreteValuationRing
