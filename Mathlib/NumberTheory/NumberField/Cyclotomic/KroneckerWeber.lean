/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.NumberTheory.NumberField.Cyclotomic.KroneckerWeberPrereqs
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Stickelberger

/-!
# The Kronecker-Weber theorem

This file proves `kronecker_weber`: every abelian number field embeds in a cyclotomic field
`CyclotomicField n ℚ`.

The first part treats, for an odd prime `p` and `F = ℚ(ζ_p)`, a cyclic extension `L/F` of degree
`p` with `L/ℚ` abelian:
- `kw_kummer₀`: if `L/ℚ` is Galois of degree `p * (p - 1)`, then `L/F` is cyclic of degree `p`.
- `kw_kummer`: `L/F` is a Kummer extension `F(ᵖ√μ)` for some nonzero `μ ∈ F`.
- `kw_unit_eq_mul_pow`: a unit `η` of `F` with `η * conj η` a `p`-th power is a `p`-th root of
  unity times a `p`-th power.
- `kw_abelian_kummer`: the Kummer criterion for `L/ℚ` to be abelian.
- `kw_split_prime`: if `p ∤ v(μ)`, then the stabilizer of `v` in `Gal(F/ℚ)` is trivial.
- `kw_mu_val_p`: if `L/F` is unramified outside `p`, then `p ∣ v(μ)` for every prime `v` of `F`.
- `kw_mu_pth_power_ideal`: if `L/F` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for some
  fractional ideal `𝔞` of `F`.
- `kw_class_trivial`: such an ideal `𝔞` is principal (Stickelberger).
- `kw_unit_conj_pow`: then `μ = β ^ p * η` for a unit `η` with `η * conj η` a `p`-th power.
- `kw_unit_root_of_unity`: then `L` is the cyclotomic extension `ℚ(ζ_{p ^ 2})`.

The ramification results:
- `ramificationIdxIn_sup_eq_lcm`: tame Abhyankar, the ramification index in a compositum is the lcm
  of the ramification indices.
- `kw_ramification_reduction_of_sup_eq_top`: removing a tamely ramified prime `q ≠ p` from a cyclic
  extension of `p`-power degree, inside its compositum with `ℚ(ζ_q)`.

The remaining results concern subfields of a field `A` of characteristic zero. From
`kw_reduce_to_prime_power_aux` on, they are stated for a family `Qζ : ℕ → IntermediateField ℚ A`
with `Qζ n` cyclotomic of level `n`.
- `kw_eq_of_unique_prime_subfield`: two abelian extensions of degree `p ^ m` unramified outside `p`
  are equal if their compositum has only one subfield of degree `p`.
- `prop_kw_2_quadratic_real_unique`: `ℚ(√2)` is the only totally real quadratic field unramified
  outside `2` (its discriminant is `8`, `kw_2_quadratic_real_discr`).
- `exists_maximalReal`: an abelian CM field has a totally real abelian subfield of half its degree.
- `kw_reduce_to_prime_power_aux`: a finite compositum of subfields of cyclotomic fields is contained
  in a cyclotomic field.
- `kw_ramification_reduction`, `kw_reduce_to_unramified_outside_p`: a cyclic extension of
  `p`-power degree is contained in a cyclotomic field iff some cyclic extension of `p`-power degree
  unramified outside `p` is.
- `prop_kw_exponent_p`, `prop_kw_exponent_p_eq`: for `p` odd, a cyclic extension of degree `p`
  unramified outside `p` is contained in `ℚ(ζ_{p ^ 2})`, hence is unique.
- `prop_kw_odd_prime_power`: for `p` odd, an abelian extension of degree `p ^ m` unramified outside
  `p` is contained in `ℚ(ζ_{p ^ (m + 1)})`.
- `prop_kw_2_power'`, `prop_kw_2_power`: an abelian extension of degree `2 ^ m` unramified outside
  `2`, first totally real then arbitrary, is contained in `ℚ(ζ_{2 ^ (m + 2)})`.
- `kw_cyclic_odd_primePow_le_cyclotomic`, `kw_cyclic_two_pow_le_cyclotomic`: a cyclic extension of
  prime power degree is contained in a cyclotomic field.
- `kw_reduce_to_prime_power`: an abelian extension of `ℚ` is the compositum of such extensions,
  hence is contained in a cyclotomic field.
-/

@[expose] public section

open NumberField Ideal Polynomial Pointwise IntermediateField Module IsCyclotomicExtension
  nonZeroDivisors IsDedekindDomain FractionalIdeal

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

section

variable {F : Type*} [Field F] [NumberField F] {L : Type*} [Field L] [Algebra F L]

section ValuationAwayFromP

variable [NumberField L] {μ : F} [IsSplittingField F L (X ^ p - C μ)]

/-- If `L` is unramified outside `p` and `v` is a prime of `𝓞 F` above a prime `q ≠ p`, then
`p ∣ v(μ)`. -/
lemma kw_mu_val_p_of_liesOver_ne {q : ℕ} [hq : Fact q.Prime] (hqp : q ≠ p)
    {v : HeightOneSpectrum (𝓞 F)} [v.asIdeal.LiesOver (span {(q : ℤ)})]
    (hLRam : UnramifiedOutside L p) :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (S := 𝓞 L) v
  have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    have : w.asIdeal.LiesOver v.asIdeal := by
      rw [← hw, HeightOneSpectrum.under_asIdeal, liesOver_iff]
    have := hLRam q hq.out hqp w.asIdeal w.isPrime <| Ideal.LiesOver.trans w.asIdeal v.asIdeal _
    rw [← Ideal.ramificationIdx_eq_one_iff, ramificationIdx_tower v.asIdeal] at this
    exact Nat.eq_one_of_mul_eq_one_left this
  have h_main := FractionalIdeal.count_extendedHom F L w ((spanSingleton (𝓞 F)⁰) μ)
  rw [hram, Nat.cast_one, one_mul, hw, extendedHom_spanSingleton,
    IsFractionRing.map_algebraMap_apply, ← rootOfSplitsXPowSubC_pow μ L (n := p), map_pow,
    count_pow] at h_main
  exact dvd_of_mul_right_eq _ h_main

end ValuationAwayFromP

variable [IsCyclotomicExtension {p} ℚ F]

variable (F) in
/-- If `L/ℚ` is Galois of degree `p * (p - 1)`, then `L/F` is cyclic Galois of degree `p`. -/
lemma kw_kummer₀ [NumberField L] [IsGalois ℚ L] (hL : finrank ℚ L = p * (p - 1)) :
    IsGalois F L ∧ IsCyclic Gal(L/F) ∧ finrank F L = p := by
  have hF : finrank ℚ F = p - 1 := Nat.totient_prime hp.out ▸ Rat.finrank p F
  have hrF : finrank F L = p := by
    have h := finrank_mul_finrank ℚ F L
    rw [hF, hL, mul_comm p (p - 1)] at h
    exact Nat.eq_of_mul_eq_mul_left (by have := hp.out.one_lt; lia) h
  have : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  exact ⟨this, isCyclic_of_prime_card <| by rw [IsGalois.card_aut_eq_finrank, hrF], hrF⟩

open IsCMField in
/-- If `η * conj η` is a `p`-th power, then `η = ζ * δ ^ p` with `ζ ^ p = 1`. -/
lemma kw_unit_eq_mul_pow (hp' : Odd p) [IsCMField F] {η : (𝓞 F)ˣ} {w : F}
    (hη : ((η : 𝓞 F) : F) * complexConj F ((η : 𝓞 F) : F) = w ^ p) :
    ∃ ζ δ : F, ζ ^ p = 1 ∧ ((η : 𝓞 F) : F) = ζ * δ ^ p := by
  obtain ⟨ω, ε, hε, h⟩ := exists_torsion_realunits_pow_indexRealUnits_eq_mul η
  rw [Rat.indexRealUnits_eq_one' p _ (by grind), pow_one] at h
  obtain ⟨γ, hγ⟩ : ∃ γ : F, ε = γ ^ p := by
    have : η.val * (complexConj F) η.val = ε.val ^ 2 := by
      rw [← coe_ringOfIntegersComplexConj, ← coe_unitsComplexConj, ← Units.coe_mul, ← Units.coe_pow,
        RingOfIntegers.eq_iff, ← Units.ext_iff, h, map_mul, unitsComplexConj_torsion,
        (unitsComplexConj_eq_self_iff _ ε).mpr hε, Subgroup.coe_inv, mul_mul_mul_comm,
        mul_inv_cancel, one_mul, sq]
    refine ⟨w ^ Nat.gcdA 2 p * ε ^ Nat.gcdB 2 p, ?_⟩
    rw [mul_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ← hη, this, ← zpow_natCast, ← zpow_mul,
      ← zpow_natCast, ← zpow_mul', ← zpow_add₀ ε.coe_ne_zero, ← Nat.gcd_eq_gcd_ab,
      Nat.coprime_two_left.mpr hp', Nat.cast_one, zpow_one]
  have hω : (ω.val : F) ^ (2 * p) = 1 := by
    rw [show 2 * p = Nat.card (Units.torsion F) by
      rw [← Units.torsionOrder, Rat.torsionOrder_eq (n := p),
        ite_eq_right (Nat.not_even_iff_odd.mpr hp')], ← map_pow, ← Units.val_pow_eq_pow_val,
        ← SubmonoidClass.coe_pow, pow_card_eq_one', Subgroup.coe_one, Units.val_one, map_one]
  refine ⟨(ω.val : F) ^ (p + 1), ω.val * γ, ?_, ?_⟩
  · have h : (p + 1) * p = (2 * p) * ((p + 1) / 2) := by
      rw [mul_comm 2, mul_assoc, Nat.mul_div_eq_iff_dvd.mpr, mul_comm]
      grind
    rw [← pow_mul, h, pow_mul, hω, one_pow]
  · rw [mul_pow, ← mul_assoc, ← pow_add, show p + 1 + p = 2 * p + 1 by ring, pow_add, hω, one_mul,
      pow_one, ← hγ, ← map_mul, ← Units.val_mul, ← h]

section CyclicDegreeP

variable [FiniteDimensional F L] [IsGalois F L] [hCF : IsCyclic Gal(L/F)] (hrF : finrank F L = p)

include hrF in
/-- The extension `L/F` is a Kummer extension: `L` is the splitting field of `X ^ p - μ` for some
nonzero `μ ∈ F`. -/
theorem kw_kummer : ∃ μ : F, μ ≠ 0 ∧ IsSplittingField F L (X ^ p - C μ) := by
  have hne : (primitiveRoots (Module.finrank F L) F).Nonempty :=
    hrF ▸ primitiveRoots_nonempty p ℚ F
  obtain ⟨g, hg, ⟨μ, hμ₁⟩, hμ₂⟩ := exists_root_adjoin_eq_top_of_isCyclic' F L hne
  refine ⟨μ, ?_, ?_⟩
  · contrapose hg
    rwa [hg, map_zero, eq_comm, pow_eq_zero_iff finrank_pos.ne'] at hμ₁
  · exact hrF ▸ isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hne hμ₁.symm hμ₂

section Kummer

variable [NumberField L] [IsAbelianGalois ℚ L] {μ : F} [IsSplittingField F L (X ^ p - C μ)]
  (hIrr : Irreducible (X ^ p - C μ))

include hIrr hrF

/-- The Kummer criterion for `L/ℚ` to be abelian: every `σ ∈ Gal(F/ℚ)` sends `μ` to
`c ^ p * μ ^ a`, where `a` is the image of `σ` in `(ℤ/pℤ)ˣ`. -/
theorem kw_abelian_kummer (σ : Gal(F/ℚ)) :
    ∃ c : F, c ≠ 0 ∧ σ μ = c ^ p * μ ^ (Rat.galEquivZMod p F σ).val.val := by
  have hne : (primitiveRoots p F).Nonempty := primitiveRoots_nonempty p ℚ F
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hCF
  set a := rootOfSplitsXPowSubC hp.out.pos μ L
  have hμ : algebraMap F L μ = a ^ p := (rootOfSplitsXPowSubC_pow _ _).symm
  have ha₀ : a ≠ 0 := by
    contrapose hμ₀
    rw [← map_eq_zero (algebraMap F L), hμ, hμ₀, zero_pow hp.out.ne_zero]
  obtain ⟨c, j, hj, h⟩ := exists_eq_algebraMap_mul_pow_of_pow_eq_algebraMap hne hIrr (α := a)
    (β := σ.liftNormal L a) (by rw [rootOfSplitsXPowSubC_pow])
    (by rw [← map_pow, rootOfSplitsXPowSubC_pow, AlgEquiv.liftNormal_commutes])
  refine ⟨c, ?_, ?_⟩
  · contrapose ha₀
    rw [← map_eq_zero (σ.liftNormal L), h, ha₀, map_zero, zero_mul]
  · suffices (Rat.galEquivZMod p F σ).val = (j : ZMod p) by
      apply FaithfulSMul.algebraMap_injective F L
      rw [← AlgEquiv.liftNormal_commutes, hμ, map_pow, h, mul_pow, map_mul, map_pow, pow_right_comm,
        ← hμ, map_pow, this, ZMod.val_cast_of_lt hj]
    let ζ : F := (autEquivRootsOfUnity hne hIrr L τ).val
    have hζ : IsPrimitiveRoot ζ p := by
      rw [← hrF, ← IsGalois.card_aut_eq_finrank, ← hτ, IsPrimitiveRoot.iff_orderOf, orderOf_units,
        Subgroup.orderOf_coe]
      exact MulEquiv.orderOf_eq (autEquivRootsOfUnity hne hIrr L) τ
    rw [← Rat.apply_eq_pow_iff_galEquivZMod_eq hζ]
    have hτa : algebraMap F L ζ * a = τ.restrictScalars ℚ a := by
      rw [AlgEquiv.restrictScalars_apply, autEquivRootsOfUnity_apply_rootOfSplit hne hIrr,
        MulAction.subgroup_smul_def, Units.smul_def, Algebra.smul_def]
    apply FaithfulSMul.algebraMap_injective F L
    rw [ZMod.val_cast_of_lt hj, ← mul_left_inj' (by aesop : (σ.liftNormal L) a ≠ 0),
      ← AlgEquiv.liftNormal_commutes, ← map_mul, hτa, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      ← mul_smul, mul_comm', mul_smul, AlgEquiv.smul_def, AlgEquiv.smul_def, h, map_mul,
      AlgEquiv.restrictScalars_apply, AlgEquiv.commutes, map_pow, ← hτa, mul_pow, map_pow]
    ring

/-- If `v` is a prime of `𝓞 F` with `p ∤ v(μ)`, then every `σ ∈ Gal(F/ℚ)` fixing `v` is the
identity. -/
lemma kw_split_prime {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ)) {σ : Gal(F/ℚ)} (hσ : σ • v = v) :
    σ = 1 := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  apply (Rat.galEquivZMod p F).injective
  rw [map_one, Units.ext_iff, Units.val_one]
  obtain ⟨c, hc₀, hc₁⟩ := kw_abelian_kummer hrF hIrr σ
  have : count F v (spanSingleton (𝓞 F)⁰ μ) = count F v (spanSingleton (𝓞 F)⁰ (σ μ)) := by
    rw [← AlgEquiv.smul_def, ← spanSingleton_smul, ← FractionalIdeal.count_smul _ _ _ σ, hσ]
  have := congr_arg (· : ℤ → ZMod p) this
  rwa [hc₁, map_mul, map_pow, map_pow, count_mul _ _ (by simp [hc₀]) (by simp [hμ₀]), count_pow,
    count_pow, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
    Int.cast_mul, right_eq_mul₀, Int.cast_natCast, ZMod.natCast_zmod_val] at this
  rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If `v` is a prime of `𝓞 F` above `p`, then `p ∣ v(μ)`. -/
lemma kw_mu_val_p_of_liesOver (hp' : Odd p) {v : HeightOneSpectrum (𝓞 F)}
    [v.asIdeal.LiesOver (span {(p : ℤ)})] :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  have : IsGalois ℚ F := isGalois {p} ℚ F
  have : Nontrivial (MulAction.stabilizer Gal(F/ℚ) v.asIdeal) := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [Ideal.card_stabilizer_eq (span {(p : ℤ)}), Rat.ramificationIdxIn_eq_of_prime,
      Rat.inertiaDegIn_eq_of_prime, mul_one]
    lia [hp.out.odd_iff.mp hp']
  obtain ⟨σ, hσ⟩ := exists_ne (1 : MulAction.stabilizer Gal(F/ℚ) v.asIdeal)
  by_contra hv
  refine hσ <| Subtype.ext <| kw_split_prime hrF hIrr hv ?_
  rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.smul_asIdeal, σ.prop]

/-- If `L` is unramified outside `p`, then `p ∣ v(μ)` for every prime `v` of `𝓞 F`. -/
lemma kw_mu_val_p (hp' : Odd p) (v : HeightOneSpectrum (𝓞 F)) (hLRam : UnramifiedOutside L p) :
    (p : ℤ) ∣ count F v (spanSingleton (𝓞 F)⁰ μ) := by
  have : Fact (absNorm (under ℤ v.asIdeal)).Prime := ⟨Nat.absNorm_under_prime v.asIdeal⟩
  have hv : v.asIdeal.LiesOver (span {((absNorm (under ℤ v.asIdeal) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm v.asIdeal
  by_cases hqp : absNorm (under ℤ v.asIdeal) = p
  · rw [hqp] at hv
    exact kw_mu_val_p_of_liesOver hrF hIrr hp'
  · exact kw_mu_val_p_of_liesOver_ne hqp hLRam

/-- If `L` is unramified outside `p`, then `(μ) = 𝔞 ^ p` for a fractional ideal `𝔞` of `F`. -/
lemma kw_mu_pth_power_ideal (hp' : Odd p) (hLRam : UnramifiedOutside L p) :
    ∃ 𝔞 : FractionalIdeal (𝓞 F)⁰ F, 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have hfin : ∀ᶠ v in Filter.cofinite, count F v (spanSingleton (𝓞 F)⁰ μ) / p = 0 := by
    filter_upwards [finite_factors (spanSingleton (𝓞 F)⁰ μ)] with v hv
    rw [hv, Int.zero_ediv]
  let exps : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
    Finsupp.ofSupportFinite (fun v ↦ count F v (spanSingleton (𝓞 F)⁰ μ) / p) hfin
  refine ⟨Finsupp.prod exps fun v z ↦ v.asIdeal ^ z,
    (eq_iff_count_eq _ ?_ (by simp [hμ₀])).mpr fun v ↦ ?_⟩
  · exact pow_ne_zero p <| Finsupp.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero (exps v)
      <| coeIdeal_ne_zero.mpr v.ne_bot
  · simp only [count_pow, count_finsuppProd]
    exact Int.mul_ediv_cancel' <| kw_mu_val_p hrF hIrr hp' v hLRam

/-- If `𝔞 ^ p = (μ)` for a fractional ideal `𝔞`, then `𝔞` is principal. -/
lemma kw_class_trivial {𝔞 : FractionalIdeal (𝓞 F)⁰ F} (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    ∃ β : F, 𝔞 = spanSingleton (𝓞 F)⁰ β := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have h𝔞₀ : 𝔞 ≠ 0 := by
    rwa [← pow_ne_zero_iff hp.out.ne_zero, h𝔞, ne_eq, map_eq_zero]
  rw [← isPrincipal_iff, ← Units.val_mk0 h𝔞₀, ← ClassGroup.mk_eq_one_iff]
  let C := (ClassGroup.mk F) (Units.mk0 𝔞 h𝔞₀)
  have hC : C ^ p = 1 := by
    rw [← map_pow, ClassGroup.mk_eq_one_iff, Units.val_pow_eq_pow_val, Units.val_mk0, h𝔞]
    exact ⟨μ, rfl⟩
  have h₁ {a : (ZMod p)ˣ} : (Rat.galEquivZMod p F).symm a • C = C ^ a.val.val := by
    obtain ⟨c, hc₀, hc⟩ := kw_abelian_kummer hrF hIrr ((Rat.galEquivZMod p F).symm a)
    rw [ClassGroup.smul_mk', ← map_pow, eq_comm, ClassGroup.mk_eq_mk']
    refine ⟨Units.mk0 c hc₀, ?_⟩
    rw [Units.ext_iff, Units.val_mul, Units.coe_smul, Units.val_mk0, coe_toPrincipalIdeal,
      Units.val_mk0, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_left_inj hp.out.ne_zero,
      mul_pow, ← smul_pow', pow_right_comm, h𝔞, spanSingleton_smul, AlgEquiv.smul_def, hc,
      MulEquiv.apply_symm_apply, map_mul, map_pow, map_pow, mul_comm]
  have h₂ {a b : (ZMod p)ˣ} : C ^ (a.val.val * b.val.val) = C ^ (a * b).val.val := by
    rw [Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hC]
  have h_main := stickelberger_theorem F p C
  simp_rw [← map_inv, h₁, ← pow_mul, h₂, inv_mul_cancel, Units.val_one, ZMod.val_one,
    pow_one, Finset.prod_const, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime hp.out] at h_main
  rwa [← pow_sub_one_mul hp.out.ne_zero, h_main, one_mul] at hC

open IsCMField in
/-- If `𝔞 ^ p = (μ)`, then `μ = β ^ p * η` for a unit `η` such that `η * conj η` is a `p`-th
power. -/
theorem kw_unit_conj_pow [IsCMField F] {𝔞 : FractionalIdeal (𝓞 F)⁰ F}
    (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    ∃ (β w : F) (η : (𝓞 F)ˣ), μ = β ^ p * (η : 𝓞 F) ∧
      ((η : 𝓞 F) : F) * complexConj F ((η : 𝓞 F) : F) = w ^ p := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  obtain ⟨c, hc⟩ : ∃ c, c ^ p = complexConj F μ * μ⁻¹ ^ (p - 1) := by
    obtain ⟨c, hc₁, hc₂⟩ := kw_abelian_kummer hrF hIrr (IsCMField.ratComplexConj F)
    refine ⟨c, ?_⟩
    rw [Rat.galEquivZMod_ratComplexConj, IsCMField.ratComplexConj_apply] at hc₂
    rw [hc₂, mul_assoc, left_eq_mul₀ (pow_ne_zero p hc₁), inv_pow,
      mul_inv_eq_one₀ (pow_ne_zero (p - 1) hμ₀), Units.val_neg, Units.val_one,
      ZMod.val_neg_of_ne_zero, ZMod.val_one]
  obtain ⟨β, hβ⟩ := kw_class_trivial hrF hIrr h𝔞
  rw [← pow_left_inj hp.out.ne_zero, ← map_pow] at hβ
  obtain ⟨η, hη⟩ := spanSingleton_eq_spanSingleton.mp <| hβ.symm.trans h𝔞
  rw [Units.smul_def, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap] at hη
  refine ⟨β, c * μ * (β * complexConj F β)⁻¹, η, by rwa [mul_comm, eq_comm], ?_⟩
  have : β ≠ 0 := fun h ↦ hμ₀ <| by rw [← hη, h, zero_pow hp.out.ne_zero, mul_zero]
  have : complexConj F β ≠ 0 := by rwa [_root_.map_ne_zero]
  simp only [mul_pow, hc, ← hη, mul_inv, map_mul, map_pow, mul_pow, inv_pow]
  field_simp
  rw [← pow_succ', mul_assoc, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]

/-- If `𝔞 ^ p = (μ)` for a fractional ideal `𝔞`, then `L` is the cyclotomic extension
`ℚ(ζ_{p ^ 2})`. -/
lemma kw_unit_root_of_unity (hp' : Odd p) {𝔞 : FractionalIdeal (𝓞 F)⁰ F}
    (h𝔞 : 𝔞 ^ p = spanSingleton (𝓞 F)⁰ μ) :
    IsCyclotomicExtension {p ^ 2} ℚ L := by
  have hμ₀ : μ ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C' hp.out.ne_one hIrr
  have : IsCMField F := Rat.isCMField F ⟨p, Set.mem_singleton p, hp.out.odd_iff.mp hp'⟩
  obtain ⟨β, w, η, hμ, hη⟩ := kw_unit_conj_pow hrF hIrr h𝔞
  obtain ⟨ζ, δ, hζ, hη'⟩ := kw_unit_eq_mul_pow hp' hη
  have hμ₁ : μ = ζ * (β * δ) ^ p := by
    rw [hμ, hη']
    ring
  have hζ₁ : ζ ≠ 1 := fun h ↦ by
    rw [h, one_mul] at hμ₁
    exact pow_ne_of_irreducible_X_pow_sub_C hIrr dvd_rfl hp.out.ne_one (β * δ) hμ₁.symm
  let α := rootOfSplitsXPowSubC hp.out.pos μ L
  let ξ : L := α * algebraMap F L (β * δ)⁻¹
  have hξ : ξ ^ p = algebraMap F L ζ := by
    rw [mul_pow, rootOfSplitsXPowSubC_pow, hμ₁, ← map_pow, ← map_mul, mul_assoc, ← mul_pow,
      mul_inv_cancel₀, one_pow, mul_one]
    exact fun h ↦ hμ₀ <| by rwa [h, zero_pow hp.out.ne_zero, mul_zero] at hμ₁
  have h₁ : orderOf ξ = p ^ 2 := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rwa [pow_one, hξ, FaithfulSMul.algebraMap_eq_one_iff]
    · rw [pow_add, pow_one, pow_mul, hξ, ← map_pow, hζ, map_one]
  have h₂ : IsCyclotomicExtension {p ^ 2} ℚ ℚ⟮ξ⟯ :=
    (IsPrimitiveRoot.iff_orderOf.mpr h₁).intermediateField_adjoin_isCyclotomicExtension ℚ
  have h₃ : ℚ ⟮ξ⟯ = ⊤ := by
    refine eq_of_le_of_finrank_eq le_top ?_
    rw [Rat.finrank (p ^ 2) ℚ⟮ξ⟯, Nat.totient_prime_pow hp.out Nat.two_pos, Nat.succ_sub_one,
      pow_one, finrank_top', ← finrank_mul_finrank ℚ F L, Rat.finrank p, Nat.totient_prime hp.out,
      hrF, mul_comm]
  rw [h₃] at h₂
  exact IsCyclotomicExtension.equiv _ _ _ topEquiv

end Kummer

end CyclicDegreeP

end

section Ramification

/-- Tame Abhyankar: for a Galois `K/ℚ`, Galois intermediate fields `E`, `F` with `E ⊔ F = ⊤`, and
a prime `p ∤ [K:ℚ]`, the ramification index of `p` in `K` is the lcm of its ramification indices in
`E` and `F`. -/
theorem ramificationIdxIn_sup_eq_lcm {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    {E F : IntermediateField ℚ K} [IsGalois ℚ E] [IsGalois ℚ F] (hEF : E ⊔ F = ⊤)
    (htame : ¬ p ∣ finrank ℚ K) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) =
      Nat.lcm ((span {(p : ℤ)}).ramificationIdxIn (𝓞 E))
        ((span {(p : ℤ)}).ramificationIdxIn (𝓞 F)) := by
  obtain ⟨𝔓, _, h𝔓⟩ : ∃ 𝔓 : Ideal (𝓞 K), 𝔓.IsMaximal ∧ 𝔓.LiesOver (span {(p : ℤ)}) :=
    exists_maximal_ideal_liesOver_of_isIntegral (span {(p : ℤ)})
  have : IsCyclic (inertia Gal(K/ℚ) 𝔓) := by
    have : FaithfulSMul Gal(K/ℚ) (𝓞 K) := IsGaloisGroup.faithful ℤ
    apply isCyclic_inertia'
    rw [card_inertia_notMem_iff, ← over_def _ (span {(p : ℤ)}), absNorm_eq_natCard,
      Int.card_ideal_quot, ← ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) _ Gal(K/ℚ)]
    contrapose htame
    exact htame.trans <| RingOfIntegers.rank K ▸ ramificationIdxIn_dvd_finrank _ _ Gal(K/ℚ)
  have : E.fixingSubgroup.subgroupOf (inertia Gal(K/ℚ) 𝔓) ⊓
      F.fixingSubgroup.subgroupOf (inertia Gal(K/ℚ) 𝔓) = ⊥ := by
    rw [← Subgroup.subgroupOf_inf, ← fixingSubgroup_sup, hEF, fixingSubgroup_top,
      Subgroup.bot_subgroupOf]
  rw [← card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) _ 𝔓,
    ← Subgroup.lcm_index_eq_card_of_isCyclic_of_inf_eq_bot this]
  congr
  · rw [Subgroup.index_eq_iff_card_mul_eq_card,
      Nat.card_congr (E.fixingSubgroup.subgroupOfEquivComm (inertia Gal(K/ℚ) 𝔓)).toEquiv,
      subgroupOf_inertia, card_inertia_eq_ramificationIdxIn (under (𝓞 E) 𝔓),
      card_inertia_eq_ramificationIdxIn (span {(p : ℤ)}), mul_comm,
      ramificationIdxIn_mul_ramificationIdxIn _ Gal(E/ℚ) _ Gal(K/ℚ) Gal(K/E)]
  · rw [Subgroup.index_eq_iff_card_mul_eq_card,
      Nat.card_congr (F.fixingSubgroup.subgroupOfEquivComm (inertia Gal(K/ℚ) 𝔓)).toEquiv,
      subgroupOf_inertia, card_inertia_eq_ramificationIdxIn (under (𝓞 F) 𝔓),
      card_inertia_eq_ramificationIdxIn (span {(p : ℤ)}), mul_comm,
      ramificationIdxIn_mul_ramificationIdxIn _ Gal(F/ℚ) _ Gal(K/ℚ) Gal(K/F)]

section

variable {q : ℕ} [hq : Fact q.Prime] (hqp : q ≠ p) {L : Type*} [Field L] [NumberField L]
  [IsAbelianGalois ℚ L] {K E : IntermediateField ℚ L} [IsGalois ℚ K] [IsGalois ℚ E]
  [IsCyclotomicExtension {q} ℚ E] {m : ℕ} (hK : finrank ℚ K = p ^ m) (htop : K ⊔ E = ⊤)
  (htame : ¬ q ∣ finrank ℚ L) (𝔔 : Ideal (𝓞 L)) [𝔔.IsMaximal] [h𝔔 : 𝔔.LiesOver (span {(q : ℤ)})]

include hqp hK htop htame

/-- In an abelian `L/ℚ` with `E = ℚ(ζ_q) ⊆ L` and `K ⊆ L` of degree `p ^ m` such that `K ⊔ E = ⊤`, a
tame prime `q` has ramification index `q - 1` in `L`, and the prime of `E` below a prime `𝔔 ∣ q`
of `𝓞 L` has ramification index `1` in `L`. -/
lemma ramificationIdx_eq_of_sup_eq_top :
    (span {(q : ℤ)}).ramificationIdxIn (𝓞 L) = q - 1 ∧
      (under (𝓞 E) 𝔔).ramificationIdxIn (𝓞 L) = 1 := by
  suffices (span {(q : ℤ)}).ramificationIdxIn (𝓞 L) = q - 1 by
    refine ⟨this, ?_⟩
    rw [← mul_right_inj' (ramificationIdxIn_ne_zero Gal(E/ℚ) (p := span {(q : ℤ)}) (B := 𝓞 E)),
      ramificationIdxIn_mul_ramificationIdxIn _ Gal(E/ℚ) _ Gal(L/ℚ) Gal(L/E), this,
      Rat.ramificationIdxIn_eq_of_prime q, mul_one]
  have : FaithfulSMul Gal(K/ℚ) (𝓞 K) := IsGaloisGroup.faithful ℤ
  have := ramificationIdxIn_sup_eq_lcm htop htame
  rwa [Rat.ramificationIdxIn_eq_of_prime q E, Nat.lcm_eq_right] at this
  rw [← card_inertia_eq_ramificationIdxIn (span {(q : ℤ)}) (under (𝓞 K) 𝔔) (G := Gal(K/ℚ))]
  have := card_inertia_dvd_card_sub_one' (G := Gal(K/ℚ)) (S := 𝓞 K) (R := ℤ) (under (𝓞 K) 𝔔) ?_
  · rwa [under_under, ← (liesOver_iff _ _).mp h𝔔, Int.card_ideal_quot] at this
  rw [card_inertia_eq_ramificationIdxIn (span {(q : ℤ)})]
  rw [← Int.cast_natCast, Int.cast_mem_ideal_iff, under_under, ← (liesOver_iff _ _).mp h𝔔,
    absNorm_eq_natCard, Int.card_ideal_quot, Int.natCast_dvd_natCast]
  refine fun h ↦ hqp ?_
  have := h.trans <| ramificationIdxIn_dvd_finrank (span {(q : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [RingOfIntegers.rank, hK] at this
  exact Nat.prime_eq_prime_of_dvd_pow hq.out hp.out this

/-- In an abelian `L/ℚ` with `E = ℚ(ζ_q) ⊆ L` and `K ⊆ L` of degree `p ^ m` such that `K ⊔ E = ⊤`,
the inertia group of a tame prime `𝔔 ∣ q` of `𝓞 L` is a complement of `Gal(L/E)`. -/
lemma inertia_isComplement_fixingSubgroup :
    Subgroup.IsComplement' (Ideal.inertia Gal(L/ℚ) 𝔔) E.fixingSubgroup := by
  obtain ⟨_, _⟩ := ramificationIdx_eq_of_sup_eq_top hqp hK htop htame 𝔔
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rwa [IsGalois.card_aut_eq_finrank, ← finrank_mul_finrank ℚ E L,
      IsGalois.card_fixingSubgroup_eq_finrank, mul_left_inj' finrank_pos.ne',
      Rat.finrank q, Nat.totient_prime hq.out, card_inertia_eq_ramificationIdxIn (span {(q : ℤ)})]
  · rwa [← codisjoint_toDual_iff, codisjoint_comm,
      ← codisjoint_map_orderIso_iff IsGalois.intermediateFieldEquivSubgroup.symm,
      IsGalois.intermediateFieldEquivSubgroup_symm_apply, OrderDual.ofDual_toDual,
      IsGalois.intermediateFieldEquivSubgroup_symm_apply, OrderDual.ofDual_toDual,
      IsGalois.fixedField_fixingSubgroup, codisjoint_iff, ← inertiaField,
      ← restrictScalars_inertiaField, restrictScalars_eq_top_iff, ← finrank_eq_one_iff_eq_top,
      finrank_inertiaField_top E L 𝔔 (under (𝓞 E) 𝔔)]

end

set_option backward.isDefEq.respectTransparency false in
/-- Ramification reduction inside `L = K ⊔ ℚ(ζ_q)`: there is a cyclic `F ≤ L` of `p`-power degree,
unramified at `q` and at every prime where `K` is unramified, with `F ⊔ ℚ(ζ_q) = ⊤`. -/
lemma kw_ramification_reduction_of_sup_eq_top {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {L : Type*}
    [Field L] [NumberField L] [IsAbelianGalois ℚ L] {K E : IntermediateField ℚ L} [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] [IsGalois ℚ E] [IsCyclotomicExtension {q} ℚ E] {m : ℕ}
    (hK : finrank ℚ K = p ^ m) (htop : K ⊔ E = ⊤) :
    ∃ F : IntermediateField ℚ L, IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ (∃ k, finrank ℚ F = p ^ k) ∧
      Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)}) ∧
        (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (span {(q' : ℤ)}) →
          Algebra.IsUnramifiedIn (𝓞 F) (span {(q' : ℤ)})) ∧ F ⊔ E = ⊤ := by
  have : Fact q.Prime := ⟨hq⟩
  have htame : ¬ q ∣ finrank ℚ L := fun h ↦ by
    have := h.trans <| finrank_top' (F := ℚ) (E := L) ▸ (htop ▸ finrank_sup_dvd_mul_of_isGalois K E)
    rw [hK, Rat.finrank q, Nat.totient_prime hq] at this
    obtain h | h := hq.dvd_mul.mp this
    · exact hqp <| Nat.prime_eq_prime_of_dvd_pow hq hp.out h
    · grind [Nat.dvd_sub_self_left.mp h, hq.one_lt]
  obtain ⟨𝔔, _, _⟩ : ∃ 𝔔 : Ideal (𝓞 L), 𝔔.IsMaximal ∧ 𝔔.LiesOver (span {(q : ℤ)}) :=
    exists_maximal_ideal_liesOver_of_isIntegral (span {(q : ℤ)})
  obtain ⟨h₁, ⟨e⟩⟩ := IsGaloisGroup.fixedPoints_sup_eq_top_of_isComplement _ _ _ <|
    inertia_isComplement_fixingSubgroup hqp hK htop htame 𝔔
  let f := (restrictRestrictAlgEquivMapHom ℚ K E L).comp
    (((IsGalois.normalAutEquivQuotient (Ideal.inertia Gal(L/ℚ) 𝔔)).symm.trans e).trans
        (fixingSubgroupEquiv E)).toMonoidHom
  have hf : Function.Injective f := (restrictRestrictAlgEquivMapHom_injective _ _ htop).comp
    (((IsGalois.normalAutEquivQuotient (Ideal.inertia Gal(L/ℚ) 𝔔)).symm.trans e).trans
      (fixingSubgroupEquiv E)).injective
  have hdvd : finrank ℚ (fixedField (Ideal.inertia Gal(L/ℚ) 𝔔)) ∣ finrank ℚ K := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Subgroup.card_dvd_of_injective _ hf
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (hK ▸ hdvd)
  let F := fixedField (Ideal.inertia Gal(L/ℚ) 𝔔)
  have : IsGaloisGroup ((inertia Gal(L/ℚ) 𝔔)) F L := .of_fixedPoints_eq Gal(L/ℚ) ℚ L _ F rfl
  refine ⟨F, IsGalois.of_fixedField_normal_subgroup _, isCyclic_of_injective f hf, ⟨k, hk⟩, ?_,
      fun r hr hKr ↦ ?_, h₁⟩
  · exact Ideal.IsInertiaRing.isUnramifiedIn Gal(L/ℚ) 𝔔
  · have : Fact r.Prime := ⟨hr⟩
    obtain rfl | hrq := eq_or_ne q r
    · exact Ideal.IsInertiaRing.isUnramifiedIn Gal(L/ℚ) 𝔔
    · refine Algebra.IsUnramifiedIn.tower_bot <|
        isUnramifiedIn_sup' _ _ htop (by simpa using NeZero.ne _) hKr ?_
      exact isUnramifiedIn_of_isCyclotomicExtension r <|
        (Nat.prime_dvd_prime_iff_eq hr hq).not.mpr hrq.symm

end Ramification

section Subfields

variable {A : Type*} [Field A] [CharZero A]

local instance {K : IntermediateField ℚ A} (E : IntermediateField ℚ K) [NumberField E] :
    NumberField (lift E) :=
  .of_ringEquiv _ _ (liftAlgEquiv E).toRingEquiv

local instance {K : IntermediateField ℚ A} (E : IntermediateField ℚ K) [IsGalois ℚ E] :
    IsGalois ℚ (lift E) :=
  .of_algEquiv (liftAlgEquiv E)

local instance {K : IntermediateField ℚ A} (E : IntermediateField ℚ K) [IsAbelianGalois ℚ E] :
    IsAbelianGalois ℚ (lift E) :=
  .of_algHom (liftAlgEquiv E).symm.toAlgHom

local instance {K : IntermediateField ℚ A} (E : IntermediateField ℚ K) [IsCyclic Gal(E/ℚ)] :
    IsCyclic Gal(lift E/ℚ) :=
  isCyclic_of_surjective (AlgEquiv.autCongr (liftAlgEquiv E)).toMonoidHom
    (AlgEquiv.autCongr _).surjective

local instance {K : IntermediateField ℚ A} (E : IntermediateField ℚ K) [IsTotallyReal E] :
    IsTotallyReal (lift E) :=
  .ofRingEquiv (liftAlgEquiv E).toRingEquiv

local instance {F E : IntermediateField ℚ A} (h : F ≤ E) [NumberField F] :
    NumberField (restrict h) :=
  .of_ringEquiv _ _ (restrictAlgEquiv h).toRingEquiv

local instance {F E : IntermediateField ℚ A} (h : F ≤ E) [IsGalois ℚ F] :
    IsGalois ℚ (restrict h) :=
  .of_algEquiv (restrictAlgEquiv h)

local instance {F E : IntermediateField ℚ A} (h : F ≤ E) [IsAbelianGalois ℚ F] :
    IsAbelianGalois ℚ (restrict h) :=
  .of_algHom (restrictAlgEquiv h).symm.toAlgHom

local instance {F E : IntermediateField ℚ A} (h : F ≤ E) [IsCyclic Gal(F/ℚ)] :
    IsCyclic Gal(restrict h/ℚ) :=
  isCyclic_of_surjective (AlgEquiv.autCongr (restrictAlgEquiv h)).toMonoidHom
    (AlgEquiv.autCongr _).surjective

local instance {F E : IntermediateField ℚ A} (h : F ≤ E) [IsTotallyReal F] :
    IsTotallyReal (restrict h) :=
  .ofRingEquiv (restrictAlgEquiv h).toRingEquiv

/-- For a family `Qζ` of cyclotomic fields, `Qζ (lcm a b) = Qζ a ⊔ Qζ b` when `a, b ≠ 0`. -/
theorem cyclotomic_lcm (Qζ : ℕ → IntermediateField ℚ A) [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)]
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Qζ (a.lcm b) = Qζ a ⊔ Qζ b := by
  have : NeZero a := ⟨ha⟩
  have : NeZero b := ⟨hb⟩
  have := isCyclotomicExtension_lcm_sup ℚ A a b (Qζ a) (Qζ b)
  exact isCyclotomicExtension_eq {a.lcm b} ℚ A _ _

omit hp in
/-- Let `C/ℚ` be abelian and unramified outside `p`, and `H` a subgroup of `Gal(C/ℚ)` of index
`p ^ m`. Then the fixed field of `H`, seen in `A`, is a Galois extension of `ℚ` of degree `p ^ m`,
unramified outside `p`. -/
lemma fixedField_spec_of_index_eq_prime_pow {C : IntermediateField ℚ A} [NumberField C]
    [IsAbelianGalois ℚ C] (hCram : UnramifiedOutside C p) {m : ℕ} (H : Subgroup Gal(C/ℚ))
    (hindex : H.index = p ^ m) :
    finrank ℚ (lift (fixedField H)) = p ^ m ∧ IsGalois ℚ (lift (fixedField H)) ∧
      UnramifiedOutside (lift (fixedField H)) p := by
  let F := fixedField H
  refine ⟨?_, inferInstance, ?_⟩
  · rwa [finrank_lift, finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  · let : Algebra (lift F) C := (inclusion (lift_le _)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot p hCram

/-- A subfield of degree `p` of an abelian extension of `ℚ` is a number field, Galois over `ℚ`, with
cyclic Galois group. -/
lemma numberField_isGalois_isCyclic_of_finrank_eq {L F : IntermediateField ℚ A}
    [IsAbelianGalois ℚ L] (hFL : F ≤ L) (hF : finrank ℚ F = p) :
    NumberField F ∧ IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) := by
  have : FiniteDimensional ℚ F := Module.finite_of_finrank_pos (hF ▸ hp.out.pos)
  have : IsGalois ℚ F := IsGalois.of_algEquiv (restrictAlgEquiv hFL).symm
  exact ⟨{}, this, isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hF])⟩

/-- Two abelian extensions `K₁`, `K₂` of `ℚ` of the same degree `p ^ m`, both unramified outside
`p`, are equal if the compositum `K₁ ⊔ K₂` has only one subfield of degree `p`. (The hypothesis
`huniq` asks this only for subfields unramified outside `p`, which all degree `p` subfields of
`K₁ ⊔ K₂` are.) -/
lemma kw_eq_of_unique_prime_subfield {K₁ K₂ : IntermediateField ℚ A} [NumberField K₁]
    [IsAbelianGalois ℚ K₁] [NumberField K₂] [IsAbelianGalois ℚ K₂] {m : ℕ}
    (hK₁ : finrank ℚ K₁ = p ^ m) (hK₂ : finrank ℚ K₂ = p ^ m) (hK₁ram : UnramifiedOutside K₁ p)
    (hK₂ram : UnramifiedOutside K₂ p)
    (huniq : ∀ (F₁ F₂ : IntermediateField ℚ A) [NumberField F₁] [IsGalois ℚ F₁] [NumberField F₂]
      [IsGalois ℚ F₂], F₁ ≤ K₁ ⊔ K₂ → F₂ ≤ K₁ ⊔ K₂ → finrank ℚ F₁ = p → finrank ℚ F₂ = p →
      UnramifiedOutside F₁ p → UnramifiedOutside F₂ p → F₁ = F₂) :
    K₁ = K₂ := by
  let L := K₁ ⊔ K₂
  let K₁' : IntermediateField ℚ L := restrict le_sup_left
  let K₂' : IntermediateField ℚ L := restrict le_sup_right
  convert_to K₁' = K₂'
  · rw [← lift_inj, lift_restrict, lift_restrict]
  suffices IsCyclic Gal(L/ℚ) by
    rw [← IsGalois.fixingSubgroup_inj, IsCyclic.subgroup_eq_iff_index_eq,
      ← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index, finrank_restrict,
      finrank_restrict, hK₁, hK₂]
  have hP : IsPGroup p Gal(L/ℚ) := by
    have := finrank_sup_dvd_mul_of_isGalois K₁ K₂
    rw [hK₁, hK₂, ← pow_add, ← IsGalois.card_aut_eq_finrank] at this
    refine isPGroup_iff_card_dvd_pow.mpr ⟨m + m, this⟩
  have hLram : UnramifiedOutside L p := unramifiedOutside_sup p K₁ K₂ hK₁ram hK₂ram
  by_contra hCL
  obtain ⟨H₁, H₂, h, Hi₁, Hi₂⟩ := (IsPGroup.not_isCyclic_iff_exists_ne_index_eq_prime hP).mp hCL
  refine h ?_
  rw [← IsGalois.fixedField_inj, ← lift_inj]
  have hF₁ : finrank ℚ (lift (fixedField H₁)) = p := by
    rwa [finrank_lift, finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  have hF₂ : finrank ℚ (lift (fixedField H₂)) = p := by
    rwa [finrank_lift, finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  obtain ⟨_, _, -⟩ := numberField_isGalois_isCyclic_of_finrank_eq (lift_le _) hF₁
  obtain ⟨_, _, -⟩ := numberField_isGalois_isCyclic_of_finrank_eq (lift_le _) hF₂
  refine huniq (lift (fixedField H₁)) (lift (fixedField H₂)) (lift_le _) (lift_le _) hF₁ hF₂ ?_ ?_
  · let : Algebra (lift (fixedField H₁)) L := (inclusion (lift_le _)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot p hLram
  · let : Algebra (lift (fixedField H₂)) L := (inclusion (lift_le _)).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot p hLram

/-- A totally real quadratic field unramified outside `2` has discriminant `8`, that is, it is
`ℚ(√2)`. -/
theorem kw_2_quadratic_real_discr {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (hK : finrank ℚ K = 2) (hKram : UnramifiedOutside K 2) : discr K = 8 := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨k, hk⟩ : ∃ k, (discr K).natAbs = 2 ^ k := by
    refine ⟨(discr K).natAbs.primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd (by simpa using discr_ne_zero _) fun hp hpd ↦ ?_⟩
    contrapose hpd
    rw [← Int.natCast_dvd, not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)]
    exact hKram _ hp hpd
  replace hk := congr_arg ((↑) : ℕ → ℤ) hk
  rw [Int.natAbs_of_nonneg (QuadraticField.discr_pos K).le, Nat.cast_pow, Nat.cast_ofNat] at hk
  have hD := Int.isFundamentalDiscr_iff_forall_prime.mp
    (QuadraticField.isFundamentalDiscr_discr K)
  match k with
  | 0 => simpa [hk] using QuadraticField.discr_ne_one K
  | 1 => grind
  | 2 => exact (hD.2 2 Nat.prime_two ⟨1, by lia, by lia⟩).elim
  | 3 => simpa using hk
  | n + 4 => exact (hD.2 2 Nat.prime_two ⟨2 ^ (n + 2), by lia, by lia⟩).elim

/-- Two totally real quadratic extensions of `ℚ` unramified outside `2` are equal (both are
`ℚ(√2)`). -/
theorem prop_kw_2_quadratic_real_unique {K₁ K₂ : IntermediateField ℚ A} [NumberField K₁]
    [IsTotallyReal K₁] [NumberField K₂] [IsTotallyReal K₂] (hK₁ : finrank ℚ K₁ = 2)
    (hK₂ : finrank ℚ K₂ = 2) (hK₁ram : UnramifiedOutside K₁ 2) (hK₂ram : UnramifiedOutside K₂ 2) :
    K₁ = K₂ := by
  have : Algebra.IsQuadraticExtension ℚ K₁ := ⟨hK₁⟩
  have : Algebra.IsQuadraticExtension ℚ K₂ := ⟨hK₂⟩
  obtain ⟨e⟩ := (QuadraticField.nonempty_algEquiv_iff_discr_eq K₁ K₂).mpr <| by
    rw [kw_2_quadratic_real_discr hK₁ hK₁ram, kw_2_quadratic_real_discr hK₂ hK₂ram]
  rw [← lift_top _ K₂, ← e.fieldRange_eq_top, lift, AlgHom.map_fieldRange,
    AlgHom.fieldRange_of_normal]

/-- An abelian CM field `C` has a totally real abelian subfield `F` (its maximal real subfield)
with `[C : ℚ] = 2 [F : ℚ]`. -/
lemma exists_maximalReal (C : IntermediateField ℚ A) [NumberField C] [IsCMField C]
    [IsAbelianGalois ℚ C] :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsTotallyReal F)
      (_ : IsAbelianGalois ℚ F), F ≤ C ∧ finrank ℚ C = 2 * finrank ℚ F := by
  let H := Subgroup.zpowers (IsCMField.ratComplexConj C)
  let F := lift (fixedField H)
  have hFC : finrank ℚ C = 2 * finrank ℚ F := by
    rw [IsCMField.finrank_eq_two_mul C, finrank_lift,
      ← IsCMField.toSubfield_fixedField_ratComplexConj C]
    rfl
  exact ⟨F, inferInstance, inferInstance, inferInstance, lift_le _, hFC⟩

section CyclotomicFamily

variable (Qζ : ℕ → IntermediateField ℚ A) [∀ n, IsCyclotomicExtension {n} ℚ (Qζ n)]

/-- If `K` is the compositum of finitely many subfields, each contained in a cyclotomic field, then
`K` is contained in a cyclotomic field. -/
lemma kw_reduce_to_prime_power_aux {K : IntermediateField ℚ A} [NumberField K] [IsAbelianGalois ℚ K]
    {ι : Type*} (S : Finset ι) (C : ι → IntermediateField ℚ A) (hC : ∀ i, ∃ n, n ≠ 0 ∧ C i ≤ Qζ n)
    (h : K = ⨆ i ∈ S, C i) :
    ∃ n, n ≠ 0 ∧ K ≤ Qζ n := by
  classical
  induction S using Finset.induction generalizing K with
  | empty => exact ⟨1, one_ne_zero, by simp [h]⟩
  | insert i S hi h_ind =>
    let : Algebra ↑(⨆ i ∈ S, C i) K :=
      (inclusion (h ▸ iSup_le_iSup_of_subset (Finset.subset_insert _ _))).toRingHom.toAlgebra
    have : NumberField ↑(⨆ i ∈ S, C i) := NumberField.of_tower ℚ K _
    have : IsAbelianGalois ℚ ↑(⨆ i ∈ S, C i) := IsAbelianGalois.tower_bot ℚ _ K
    obtain ⟨m, hm₀, hm₁⟩ := h_ind rfl
    obtain ⟨n, hn₀, hn₁⟩ := hC i
    refine ⟨n.lcm m, Nat.lcm_ne_zero hn₀ hm₀, ?_⟩
    rw [h, Finset.iSup_insert, cyclotomic_lcm Qζ hn₀ hm₀]
    exact sup_le_sup hn₁ hm₁

variable [∀ n, NumberField (Qζ n)] [∀ n, IsAbelianGalois ℚ (Qζ n)]

/-- Ramification reduction: given `K/ℚ` cyclic of degree `p ^ m` with `q ≠ p` ramified, there is a
cyclic `F/ℚ` of `p`-power degree, unramified at `q` and at every prime where `K` is unramified,
such that `K ⊔ ℚ(ζ_q) = F ⊔ ℚ(ζ_q)`. -/
lemma kw_ramification_reduction {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) {K : IntermediateField ℚ A}
    [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)] (hK : ∃ k, finrank ℚ K = p ^ k) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F),
      IsGalois ℚ F ∧ IsCyclic Gal(F/ℚ) ∧ (∃ k, finrank ℚ F = p ^ k) ∧
      Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)}) ∧
      (∀ q' : ℕ, q'.Prime → Algebra.IsUnramifiedIn (𝓞 K) (span {(q' : ℤ)}) →
        Algebra.IsUnramifiedIn (𝓞 F) (span {(q' : ℤ)})) ∧ K ⊔ Qζ q = F ⊔ Qζ q := by
  let L := K ⊔ (Qζ q)
  obtain ⟨k, hK⟩ := hK
  have : IsAbelianGalois ℚ L := by
    have : IsAbelianGalois ℚ K := .of_isCyclic ℚ ↥K
    exact IsAbelianGalois.sup _ _
  let K₀ : IntermediateField ℚ L := restrict le_sup_left
  let E₀ : IntermediateField ℚ L := restrict le_sup_right
  have htop : K₀ ⊔ E₀ = ⊤ := by
    rw [← lift_inj, lift_sup, lift_restrict, lift_restrict, lift_top]
  have : IsCyclotomicExtension {q} ℚ E₀ := .equiv _ ℚ (Qζ q) (restrictAlgEquiv le_sup_right)
  obtain ⟨F₀, _, _, _, h₂, h₃, h₄⟩ := kw_ramification_reduction_of_sup_eq_top hq hqp
    (by rwa [finrank_restrict]) htop
  refine ⟨lift F₀, inferInstance, inferInstance, inferInstance, by simpa [finrank_lift], ?_,
    fun r hr hr' ↦ ?_, ?_⟩
  · exact Algebra.IsUnramifiedIn.of_algEquiv
      (RingOfIntegers.mapIntAlgEquiv (liftAlgEquiv F₀).toRingEquiv) h₂
  · exact Algebra.IsUnramifiedIn.of_algEquiv
      (RingOfIntegers.mapIntAlgEquiv (liftAlgEquiv F₀).toRingEquiv) <|
      h₃ r hr <| Algebra.IsUnramifiedIn.of_algEquiv
      (RingOfIntegers.mapIntAlgEquiv (restrictAlgEquiv le_sup_left).toRingEquiv) hr'
  · have := congr_arg lift <| htop.trans h₄.symm
    rwa [lift_sup, lift_sup, lift_restrict, lift_restrict] at this

/-- Iterating the ramification reduction over the finitely many primes `q ≠ p` ramified in `K`,
one obtains a cyclic `F/ℚ` of `p`-power degree, unramified outside `p`, with
`K ⊔ Qζ n = F ⊔ Qζ n` for some `n ≠ 0` (so `K` is cyclotomic iff `F` is). -/
lemma kw_reduce_to_unramified_outside_p {K : IntermediateField ℚ A} [NumberField K] [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] (hK : ∃ k, finrank ℚ K = p ^ k) :
    ∃ (F : IntermediateField ℚ A) (_ : NumberField F) (_ : IsGalois ℚ F) (_ : IsCyclic Gal(F/ℚ)),
      (∃ k, finrank ℚ F = p ^ k) ∧
      (∀ q : ℕ, q.Prime → q ≠ p → Algebra.IsUnramifiedIn (𝓞 F) (span {(q : ℤ)})) ∧
      ∃ n, n ≠ 0 ∧ K ⊔ Qζ n = F ⊔ Qζ n := by
  have hfin (E : IntermediateField ℚ A) [NumberField E] :
      {q : ℕ | q.Prime ∧ q ≠ p ∧ ¬ Algebra.IsUnramifiedIn (𝓞 E) (span {(q : ℤ)})}.Finite := by
    refine (Nat.primeFactors (discr E).natAbs).finite_toSet.subset fun q ⟨hq, hqp, hram⟩ ↦ ?_
    rwa [SetLike.mem_coe, Nat.mem_primeFactors_of_ne_zero, and_iff_right hq,
      ← Int.natCast_dvd, ← not_not (a := (q : ℤ) ∣ discr E),
      not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) (Nat.prime_iff_prime_int.mp hq)]
    simpa using discr_ne_zero _
  induction h : {q | q.Prime ∧ q ≠ p ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})}.ncard
      using Nat.strong_induction_on generalizing K with
  | _ N h_ind =>
    obtain hS | ⟨r, hr, hrp, hrram⟩ := Set.eq_empty_or_nonempty
      {q : ℕ | q.Prime ∧ q ≠ p ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (span {(q : ℤ)})}
    · refine ⟨K, inferInstance, inferInstance, inferInstance, hK,
          fun q hq hqp ↦ ?_, 1, one_ne_zero, rfl⟩
      contrapose! hS
      exact ⟨q, hq, hqp, hS⟩
    · obtain ⟨E, _, _, _, hE, hEr, hEram, hKE⟩ := kw_ramification_reduction Qζ hr hrp hK
      have hlt : {q | q.Prime ∧ q ≠ p ∧
          ¬ Algebra.IsUnramifiedIn (𝓞 E) (span {(q : ℤ)})}.ncard < N :=
        h ▸ Set.ncard_lt_ncard ⟨by grind, by aesop⟩ (hfin K)
      obtain ⟨F, _, _, _, hF, hFram, n, hn, hEF⟩ := h_ind _ hlt hE rfl
      refine ⟨F, ‹_›, ‹_›, ‹_›, hF, hFram, r.lcm n, Nat.lcm_ne_zero hr.ne_zero hn, ?_⟩
      rw [cyclotomic_lcm Qζ hr.ne_zero hn, ← sup_assoc, hKE, sup_assoc, sup_comm (Qζ r),
        ← sup_assoc, hEF, sup_assoc]

/-- Every cyclic extension of `ℚ` of prime degree `p` (odd) unramified outside `p` is contained in
`ℚ(ζ_{p ^ 2}) = Qζ (p ^ 2)`. -/
theorem prop_kw_exponent_p (hp' : Odd p) {K : IntermediateField ℚ A} [NumberField K] [IsGalois ℚ K]
    (hK : finrank ℚ K = p) (hKram : UnramifiedOutside K p) :
    K ≤ Qζ (p ^ 2) := by
  have : IsCyclic Gal(K/ℚ) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hK])
  have : IsAbelianGalois ℚ K := .of_isCyclic ℚ K
  let L := K ⊔ Qζ p
  have : IsCyclotomicExtension {p ^ 2} ℚ L := by
    let : Algebra (Qζ p) L := (inclusion (le_sup_right : Qζ p ≤ L)).toRingHom.toAlgebra
    have : Module.finrank ℚ ↑(K ⊓ Qζ p) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes ?_ (finrank_dvd_of_le_right inf_le_left)
        (finrank_dvd_of_le_right inf_le_right)
      rw [hK, Rat.finrank p, Nat.totient_prime hp.out]
      exact (Nat.coprime_self_sub_right hp.out.one_le).mpr (Nat.coprime_one_right p)
    have hL : Module.finrank ℚ L = p * (p - 1) := by
      rw [IntermediateField.LinearDisjoint.finrank_sup, hK, Rat.finrank p, Nat.totient_prime hp.out]
      rwa [LinearDisjoint.iff_inf_eq_bot, ← IntermediateField.finrank_eq_one_iff]
    obtain ⟨_, _, hrF⟩ := kw_kummer₀ (Qζ p) hL
    obtain ⟨μ, hμ₀, _⟩ := kw_kummer hrF
    have hIrr : Irreducible (X ^ p - C μ) :=
      irreducible_X_pow_sub_C_of_isSplittingField (primitiveRoots_nonempty p ℚ (Qζ p)) hrF
    have hramL : UnramifiedOutside L p :=
      unramifiedOutside_sup p _ _ hKram (UnramifiedOutside.of_isCyclotomicExtension' p (Qζ p))
    obtain ⟨𝔞, h𝔞⟩ := kw_mu_pth_power_ideal hrF hIrr hp' hramL
    exact kw_unit_root_of_unity hrF hIrr hp' h𝔞
  rw [isCyclotomicExtension_eq {p ^ 2} ℚ _ (Qζ (p ^ 2)) L]
  exact le_sup_left

include Qζ in
/-- Two cyclic extensions of `ℚ` of prime degree `p` (odd) unramified outside `p` are equal. -/
theorem prop_kw_exponent_p_eq (hp' : Odd p) {K₁ K₂ : IntermediateField ℚ A} [NumberField K₁]
    [IsGalois ℚ K₁] [NumberField K₂] [IsGalois ℚ K₂] (hK₁ : finrank ℚ K₁ = p)
    (hK₂ : finrank ℚ K₂ = p) (hKram₁ : UnramifiedOutside K₁ p) (hKram₂ : UnramifiedOutside K₂ p) :
    K₁ = K₂ := by
  have h₁ := prop_kw_exponent_p Qζ hp' hK₁ hKram₁
  have h₂ := prop_kw_exponent_p Qζ hp' hK₂ hKram₂
  suffices restrict h₁ = restrict h₂ by
    rwa [← lift_inj, lift_restrict h₁, lift_restrict h₂] at this
  have : IsCyclic Gal(Qζ (p ^ 2)/ℚ) :=
    Rat.isCyclic_of_prime_pow _ 2 <| hp'.ne_two_of_dvd_nat dvd_rfl
  rw [← IsGalois.fixingSubgroup_inj, IsCyclic.subgroup_eq_iff_index_eq,
    ← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index, finrank_restrict,
    finrank_restrict, hK₁, hK₂]

/-- Every abelian extension of `ℚ` of odd prime power degree `p ^ m` unramified outside `p` is
cyclotomic: it is contained in `ℚ(ζ_{p ^ (m + 1)})`. -/
theorem prop_kw_odd_prime_power [hp' : Fact (Odd p)] {m : ℕ} {K : IntermediateField ℚ A}
    [NumberField K] [IsAbelianGalois ℚ K] (hK : finrank ℚ K = p ^ m)
    (hKram : UnramifiedOutside K p) :
    K ≤ Qζ (p ^ (m + 1)) := by
  let C := Qζ (p ^ (m + 1))
  have hC : IsCyclic Gal(C/ℚ) :=
    Rat.isCyclic_of_prime_pow (p := p) C (m + 1) (hp'.out.ne_two_of_dvd_nat dvd_rfl)
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hC
  let H := Subgroup.zpowers (g ^ (p ^ m : ℤ))
  have Hi : H.index = p ^ m := by
    rw [Subgroup.index_zpowers_zpow hg, orderOf_eq_card_of_zpowers_eq_top hg,
      IsGalois.card_aut_eq_finrank, Rat.finrank (p ^ (m + 1)), Nat.totient_prime_pow hp.out
      m.succ_pos]
    simp
  obtain ⟨hF, _, hFram⟩ := fixedField_spec_of_index_eq_prime_pow
    (UnramifiedOutside.of_isCyclotomicExtension p (m + 1) C) H Hi
  set F := lift (fixedField H)
  suffices K = F by
    rw [this]
    exact lift_le (fixedField H)
  exact kw_eq_of_unique_prime_subfield hK hF hKram hFram
    fun F₁ F₂ _ _ _ _ hF₁ hF₂ hrF₁ hrF₂ hF₁ram hF₂ram ↦
      prop_kw_exponent_p_eq Qζ hp'.out hrF₁ hrF₂ hF₁ram hF₂ram

/-- Every totally real abelian extension of `ℚ` of degree `2 ^ m` unramified outside `2` is
cyclotomic: it is contained in `ℚ(ζ_{2 ^ (m + 2)})`. -/
theorem prop_kw_2_power' {m : ℕ} {K : IntermediateField ℚ A} [NumberField K] [IsAbelianGalois ℚ K]
    [IsTotallyReal K] (hK : finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ Qζ (2 ^ (m + 2)) := by
  let C := Qζ (2 ^ (m + 2))
  have : IsCMField C := Rat.isCMField C (S := {(2 ^ (m + 2) :)}) ⟨_, rfl, by grind⟩
  obtain ⟨F, _, _, _, hFC, hdeg⟩ := exists_maximalReal C
  have hF : finrank ℚ F = 2 ^ m := by
    rw [Rat.finrank (2 ^ (m + 2)), Nat.totient_prime_pow Nat.prime_two (by norm_num),
      Nat.add_one_sub_one, Nat.add_one_sub_one, mul_one, pow_succ, mul_comm] at hdeg
    exact (Nat.eq_of_mul_eq_mul_left zero_lt_two hdeg).symm
  have hFram : UnramifiedOutside F 2 := by
    let : Algebra F C := (inclusion hFC).toRingHom.toAlgebra
    exact UnramifiedOutside.tower_bot 2 (UnramifiedOutside.of_isCyclotomicExtension 2 (m + 2) C)
  suffices K = F by
    rw [this]
    exact hFC
  have : IsTotallyReal ↑(K ⊔ F) := by
    change IsTotallyReal ↑(K ⊔ F).toSubfield
    rw [sup_toSubfield]
    exact isTotallyReal_sup
  exact kw_eq_of_unique_prime_subfield hK hF hKram hFram
    fun F₁ F₂ _ _ _ _ hF₁ hF₂ hrF₁ hrF₂ hF₁ram hF₂ram ↦ by
      have : IsTotallyReal F₁ := by
        let : Algebra F₁ ↑(K ⊔ F) := (inclusion hF₁).toRingHom.toAlgebra
        exact IsTotallyReal.of_algebra F₁ ↑(K ⊔ F)
      have : IsTotallyReal F₂ := by
        let : Algebra F₂ ↑(K ⊔ F) := (inclusion hF₂).toRingHom.toAlgebra
        exact IsTotallyReal.of_algebra F₂ ↑(K ⊔ F)
      exact prop_kw_2_quadratic_real_unique hrF₁ hrF₂ hF₁ram hF₂ram

/-- Every abelian extension of `ℚ` of degree `2 ^ m` unramified outside `2` is cyclotomic: it is
contained in `ℚ(ζ_{2 ^ (m + 2)})`. -/
theorem prop_kw_2_power {m : ℕ} {K : IntermediateField ℚ A} [NumberField K] [IsAbelianGalois ℚ K]
    (hK : finrank ℚ K = 2 ^ m) (hKram : UnramifiedOutside K 2) :
    K ≤ Qζ (2 ^ (m + 2)) := by
  by_cases hreal : IsTotallyReal K
  · exact prop_kw_2_power' Qζ hK hKram
  have : IsTotallyComplex K := isTotallyComplex_iff_not_isTotallyReal.mpr hreal
  let F := K ⊔ (Qζ 4)
  suffices F ≤ Qζ (2 ^ (m + 2)) from le_trans le_sup_left this
  have : IsTotallyComplex F := by
    let : Algebra K F := (inclusion le_sup_left).toRingHom.toAlgebra
    exact isTotallyComplex_of_algebra K F
  obtain ⟨F', _, hF'₀, _, hF'₁, hF'₂⟩ := exists_maximalReal F
  suffices F' ≤ Qζ (2 ^ (m + 2)) by
    have hFF' : F' ⊔ Qζ 4 = F := by
      have : Nat.Prime (relfinrank F' F) := by
        have := finrank_bot_mul_relfinrank hF'₁
        rw [hF'₂, mul_comm, mul_left_inj' finrank_pos.ne'] at this
        exact this ▸ Nat.prime_two
      refine (eq_or_eq_of_relfinrank_prime (M := F' ⊔ Qζ 4) le_sup_left
          (sup_le hF'₁ le_sup_right) this).resolve_left fun h ↦
            isTotallyReal_iff_not_isTotallyComplex.mp hF'₀ ?_
      let : Algebra (Qζ 4) ↑(F' ⊔ Qζ 4) := (inclusion le_sup_right).toRingHom.toAlgebra
      have : IsTotallyComplex (Qζ 4) := Rat.isTotallyComplex _ (by norm_num : 2 < 4)
      exact h ▸ isTotallyComplex_of_algebra (Qζ 4) _
    rw [← hFF', sup_le_iff]
    refine ⟨this, isCyclotomicExtension_le_of_dvd ℚ A 4 (2 ^ (m + 2)) _ _ (by lia)⟩
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k ≤ m, finrank ℚ F' = 2 ^ k := by
    have : finrank ℚ F ∣ 2 ^ (m + 1) := by
      calc
        _ ∣ finrank ℚ K * finrank ℚ (Qζ 4) := finrank_sup_dvd_mul_of_isGalois K (Qζ 4)
        _ = 2 ^ m * Nat.totient (2 ^ 2) := by rw [hK, Rat.finrank 4 (Qζ 4), show 4 = 2 ^ 2 by rfl]
        _ = 2 ^ (m + 1) := by
          rw [Nat.totient_prime_pow Nat.prime_two zero_lt_two]
          ring
    rw [hF'₂, pow_succ', Nat.mul_dvd_mul_iff_left zero_lt_two] at this
    exact (Nat.dvd_prime_pow Nat.prime_two).mp <| this
  have : Qζ (2 ^ (k + 2)) ≤ Qζ (2 ^ (m + 2)) := by
    refine isCyclotomicExtension_le_of_dvd ℚ _ (2 ^ (k + 2)) (2 ^ (m + 2)) _ _ ?_
    exact (Nat.pow_dvd_pow_iff_le_right one_lt_two).mpr (by lia)
  refine le_trans (prop_kw_2_power' (K := F') Qζ hk₂ ?_) this
  let : Algebra F' F := (inclusion hF'₁).toRingHom.toAlgebra
  exact UnramifiedOutside.tower_bot 2 (L := F) <|
    unramifiedOutside_sup _ _ _ hKram <| UnramifiedOutside.of_isCyclotomicExtension 2 2 _

/-- Every cyclic extension of `ℚ` of odd prime power degree `p ^ m` is contained in a cyclotomic
field `ℚ(ζ_n)` for some nonzero `n`. -/
theorem kw_cyclic_odd_primePow_le_cyclotomic [Fact (Odd p)] {K : IntermediateField ℚ A}
    [NumberField K] [IsGalois ℚ K] [IsCyclic Gal(K/ℚ)] {m : ℕ} (hK : finrank ℚ K = p ^ m) :
    ∃ n, n ≠ 0 ∧ K ≤ Qζ n := by
  obtain ⟨F, _, _, _, ⟨k, hF⟩, hFram, n, hn, hKF⟩ := kw_reduce_to_unramified_outside_p Qζ ⟨m, hK⟩
  have : IsAbelianGalois ℚ F := .of_isCyclic ℚ F
  refine ⟨(p ^ (k + 1)).lcm n, Nat.lcm_ne_zero (NeZero.ne _) hn, ?_⟩
  calc
    K ≤ K ⊔ Qζ n := le_sup_left
    _ = F ⊔ Qζ n := hKF
    _ ≤ Qζ (p ^ (k + 1)) ⊔ Qζ n := sup_le_sup_right (prop_kw_odd_prime_power Qζ hF hFram) _
    _ = Qζ ((p ^ (k + 1)).lcm n) := (cyclotomic_lcm Qζ (NeZero.ne _) hn).symm

/-- Every cyclic extension of `ℚ` of degree `2 ^ m` is contained in a cyclotomic field `ℚ(ζ_n)`
for some nonzero `n`. -/
theorem kw_cyclic_two_pow_le_cyclotomic {K : IntermediateField ℚ A} [NumberField K] [IsGalois ℚ K]
    [IsCyclic Gal(K/ℚ)] {m : ℕ} (hK : finrank ℚ K = 2 ^ m) :
    ∃ n, n ≠ 0 ∧ K ≤ Qζ n := by
  obtain ⟨F, _, _, _, ⟨k, hF⟩, hFram, n, hn, hKF⟩ := kw_reduce_to_unramified_outside_p Qζ ⟨m, hK⟩
  have : IsAbelianGalois ℚ F := .of_isCyclic ℚ F
  refine ⟨Nat.lcm (2 ^ (k + 2)) n, Nat.lcm_ne_zero (NeZero.ne _) hn, ?_⟩
  calc
    K ≤ K ⊔ Qζ n := le_sup_left
    _ = F ⊔ Qζ n := hKF
    _ ≤ Qζ (2 ^ (k + 2)) ⊔ Qζ n := sup_le_sup_right (prop_kw_2_power Qζ hF hFram) _
    _ = Qζ (Nat.lcm (2 ^ (k + 2)) n) := (cyclotomic_lcm Qζ (NeZero.ne _) hn).symm

/-- Every abelian extension of `ℚ` inside `A` is contained in a cyclotomic field `ℚ(ζ_n)` for some
nonzero `n`. -/
lemma kw_reduce_to_prime_power (K : IntermediateField ℚ A) [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n, n ≠ 0 ∧ K ≤ Qζ n := by
  obtain ⟨ι, _, C, hC, h⟩ := IsAbelianGalois.exists_isCyclic_primePow_iSup_eq_top ℚ K
  refine kw_reduce_to_prime_power_aux Qζ Finset.univ (fun i ↦ lift (C i)) (fun i ↦ ?_) ?_
  · obtain ⟨_, _, ⟨q, m, hq, hm, hrC⟩⟩ := hC i
    replace hrC : finrank ℚ (lift (C i)) = q ^ m := by
      rw [finrank_lift, hrC]
    replace hq : q.Prime := Nat.prime_iff.mpr hq
    obtain rfl | hq' := Nat.Prime.eq_two_or_odd' hq
    · exact kw_cyclic_two_pow_le_cyclotomic Qζ hrC
    · have : Fact q.Prime := ⟨hq⟩
      have : Fact (Odd q) := ⟨hq'⟩
      exact kw_cyclic_odd_primePow_le_cyclotomic Qζ hrC
  · have := (lift_inj _ _).mpr h
    rwa [← iSup_univ, ← Finset.coe_univ, Finset.iSup_coe, lift_iSup _ _ _ Finset.univ,
      lift_top, eq_comm] at this

end CyclotomicFamily

end Subfields

set_option backward.isDefEq.respectTransparency false in
/-- **Kronecker-Weber theorem**: every abelian extension of `ℚ` is contained in a cyclotomic
field. -/
theorem kronecker_weber (K : Type*) [Field K] [NumberField K] [IsAbelianGalois ℚ K] :
    ∃ n : ℕ, Nonempty (K →+* CyclotomicField n ℚ) := by
  let Qζ : ℕ → IntermediateField ℚ ℂ :=
    fun n ↦ if hn : n = 0 then ⊥ else ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯
  have {n : ℕ} : IsCyclotomicExtension {n} ℚ (Qζ n) := by
    unfold Qζ
    obtain rfl | hn := eq_or_ne n 0
    · rw [dite_eq_left rfl]
      exact IsCyclotomicExtension.isCyclotomicExtension_zero_iff.mpr (botEquiv ℚ ℂ).symm.surjective
    · have : NeZero n := ⟨hn⟩
      rw [dite_eq_right hn]
      exact (Complex.isPrimitiveRoot_exp n hn).intermediateField_adjoin_isCyclotomicExtension ℚ
  have {n : ℕ} : NumberField (Qζ n) := IsCyclotomicExtension.numberField {n} ℚ _
  have {n : ℕ} : IsAbelianGalois ℚ (Qζ n) := IsCyclotomicExtension.isAbelianGalois {n} ℚ _
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  let K₀ := (RingHom.fieldRange φ).toIntermediateField fun x ↦ SubfieldClass.ratCast_mem _ x
  have : NumberField K₀ := of_ringEquiv _ _ (RingHom.rangeRestrictFieldEquiv φ)
  have : IsAbelianGalois ℚ K₀ :=
    .of_algHom (RingHom.rangeRestrictFieldEquiv φ).symm.toRatAlgEquiv.toAlgHom
  obtain ⟨n, hn₀, hK₀⟩ := kw_reduce_to_prime_power Qζ K₀
  exact ⟨n, ⟨((IsCyclotomicExtension.algEquiv {n} ℚ (Qζ n) (CyclotomicField n ℚ)).toRingHom.comp
    (inclusion hK₀).toRingHom).comp φ.rangeRestrict⟩⟩
