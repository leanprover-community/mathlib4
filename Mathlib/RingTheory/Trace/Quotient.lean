/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/

import Mathlib.RingTheory.Localization.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!

We gather results about the relations between the trace map on `B → A` and the trace map on
quotients and localizations.

## Main Results
  `Algebra.trace_quotient_eq_of_isDedekindDomain` : The trace map on `B → A` coincides with the
    trace map on `B⧸pB → A⧸p`.

-/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [LocalRing R]

open LocalRing FiniteDimensional Submodule

section LocalRing

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

variable [Module.Free R S] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

theorem quotient_span_eq_top_iff_span_eq_top_of_localRing (s : Set S) :
    span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s) = ⊤ ↔
    span R s = ⊤ := by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS)) := by
    rw [map_span, ← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective]
    rfl
  constructor
  · intro hs
    rw [← top_le_iff]
    apply le_of_le_smul_of_le_jacobson_bot
    · exact Module.finite_def.mp ‹_›
    · exact (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [Ideal.smul_top_eq_map]
      rintro x -
      have : LinearMap.ker (IsScalarTower.toAlgHom R S (S ⧸ pS)) =
          restrictScalars R pS := by
        ext; simp [Ideal.Quotient.eq_zero_iff_mem]
      rw [← this, ← comap_map_eq, mem_comap, ← H, hs]
      trivial
  · intro hs
    rw [hs, Submodule.map_top] at H
    change _ = LinearMap.range (Ideal.Quotient.mkₐ _ _) at H
    rwa [LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective _ _),
      restrictScalars_eq_top_iff] at H

theorem finrank_quotient_map_of_localRing :
    finrank (R ⧸ p) (S ⧸ pS) = finrank R S := by
  classical
  have : Module.Finite R (S ⧸ pS) := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R S (S ⧸ pS)).toLinearMap (Ideal.Quotient.mk_surjective (I := pS))
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    rw [Set.range_comp]
    apply (quotient_span_eq_top_iff_span_eq_top_of_localRing _).mpr b.span_eq
  · let b := Module.Free.chooseBasis (R ⧸ p) (S ⧸ pS)
    choose b' hb' using fun i ↦ Ideal.Quotient.mk_surjective (b i)
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    apply (quotient_span_eq_top_iff_span_eq_top_of_localRing _).mp
    rw [← Set.range_comp, show Ideal.Quotient.mk pS ∘ b' = ⇑b from funext hb']
    exact b.span_eq

/-- Given a basis of `S`, the induced basis of `S / Ideal.map (algebraMap R S) p`. -/
noncomputable
def basisQuotientOfLocalRing {ι} [Fintype ι] (b : Basis ι R S) : Basis ι (R ⧸ p) (S ⧸ pS) :=
  basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b) (by
    rw [Set.range_comp]
    exact ((quotient_span_eq_top_iff_span_eq_top_of_localRing _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map_of_localRing, finrank_eq_card_basis b])

lemma basisQuotientOfLocalRing_apply {ι} [Fintype ι] (b : Basis ι R S) (i) :
    (basisQuotientOfLocalRing b) i = Ideal.Quotient.mk pS (b i) := by
  delta basisQuotientOfLocalRing
  rw [coe_basisOfTopLeSpanOfCardEqFinrank, Function.comp_apply]

lemma basisQuotientOfLocalRing_repr {ι} [Fintype ι] (b : Basis ι R S) (x) (i) :
    (basisQuotientOfLocalRing b).repr (Ideal.Quotient.mk pS x) i =
    Ideal.Quotient.mk p (b.repr x i) := by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotientOfLocalRing b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.total_eq_fintype_total_apply _ (R ⧸ p), Fintype.total_apply]
  simp only [Function.comp_apply, basisQuotientOfLocalRing_apply,
    Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum, Basis.sum_repr b x]

lemma Algebra.trace_quotient_mk (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.trace R S x) := by
  classical
  let ι := Module.Free.ChooseBasisIndex R S
  let b : Basis ι R S := Module.Free.chooseBasis R S
  rw [trace_eq_matrix_trace b, trace_eq_matrix_trace (basisQuotientOfLocalRing b)]
  show _ = (Ideal.Quotient.mk p).toAddMonoidHom _
  rw [AddMonoidHom.map_trace]
  congr 1
  ext i j
  simp only [leftMulMatrix_apply, coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotientOfLocalRing_apply, LinearMap.mul_apply', RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.mapMatrix_apply, AddMonoidHom.coe_coe, Matrix.map_apply, ← map_mul,
    basisQuotientOfLocalRing_repr]

end LocalRing

section IsDedekindDomain

variable (p : Ideal R) [p.IsMaximal]
variable {Rₚ Sₚ : Type*} [CommRing Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
variable [LocalRing Rₚ] [CommRing Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [Algebra Rₚ Sₚ]
variable [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]

variable (Rₚ)

attribute [local instance] Ideal.Quotient.field

/-- The isomorphism `R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ`, where `Rₚ` satisfies
`IsLocalization.AtPrime Rₚ p`. -/
noncomputable
def equivQuotMaximalIdealOfIsLocalization : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p s)⁻¹
    simp only [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _),
      Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
    use x * s'
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap R Rₚ s ∉ maximalIdeal Rₚ := by
      rw [← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
      exact s.prop
    refine ((inferInstanceAs <| (maximalIdeal Rₚ).IsPrime).mem_or_mem ?_).resolve_left this
    rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
      ← map_mul, ← map_sub, ← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p,
      mul_left_comm,
      ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hs, mul_inv_cancel, mul_one,
      sub_self]
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact s.prop

lemma IsLocalization.AtPrime.map_eq_maximalIdeal :
    p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert congr_arg (Ideal.map (algebraMap R Rₚ))
    (IsLocalization.AtPrime.comap_maximalIdeal Rₚ p).symm
  rw [map_comap p.primeCompl]

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)

lemma comap_map_eq_map_of_isLocalization_algebraMapSubmonoid :
    (Ideal.map (algebraMap R Sₚ) p).comap (algebraMap S Sₚ) = pS := by
  rw [IsScalarTower.algebraMap_eq R S Sₚ, ← Ideal.map_map, eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : ∃ α ∉ p, α • x ∈ pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).mp hx
    rw [← map_mul,
      IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S p.primeCompl)] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨α, hα, e⟩ := (c * s).prop
    refine ⟨α, hα, ?_⟩
    rw [Algebra.smul_def, e, Submonoid.coe_mul, mul_assoc, mul_comm _ x, hc]
    exact Ideal.mul_mem_left _ _ y.prop
  obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ β * α = 1 + γ := by
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
    refine ⟨β, β * α - 1, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
        map_mul, hβ, inv_mul_cancel, sub_self]
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [add_sub_cancel]
  have := Ideal.mul_mem_left _ (algebraMap _ _ β) hαx
  rw [← Algebra.smul_def, smul_smul, hβ, add_smul, one_smul] at this
  refine (Submodule.add_mem_iff_left _ ?_).mp this
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ hγ

variable (S Sₚ)

/-- The isomorphism `S ⧸ pS ≃+* Sₚ ⧸ pSₚ`. -/
noncomputable
def quotMapEquivQuotMapMaximalIdealOfIsLocalization : S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rₚ, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      comap_map_eq_map_of_isLocalization_algebraMapSubmonoid]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid S p.primeCompl) x
    obtain ⟨α, hα : α ∉ p, e⟩ := s.prop
    obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ α * β = 1 + γ := by
      obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
      refine ⟨β, α * β - 1, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
          map_mul, hβ, mul_inv_cancel, sub_self]
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [add_sub_cancel]
    use β • x
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ pSₚ), Ideal.Quotient.algebraMap_eq,
      RingHom.comp_apply, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [h, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    refine ⟨⟨⟨γ • x, ?_⟩, s⟩, ?_⟩
    · rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ hγ
    simp only
    rw [mul_comm, mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_mul_cancel_left, ← map_mul, ← e, ← Algebra.smul_def, smul_smul,
      hβ, ← map_sub, add_smul, one_smul, add_comm x, add_sub_cancel_right]

lemma trace_quotient_eq_trace_localization_quotient (x) :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      (equivQuotMaximalIdealOfIsLocalization p Rₚ).symm
        (Algebra.trace (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) (algebraMap S _ x)) := by
  have : IsScalarTower R (Rₚ ⧸ maximalIdeal Rₚ) (Sₚ ⧸ pSₚ) := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _), IsScalarTower.algebraMap_eq R Rₚ (Sₚ ⧸ _),
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq Rₚ]
  rw [Algebra.trace_eq_of_equiv_equiv (equivQuotMaximalIdealOfIsLocalization p Rₚ)
    (quotMapEquivQuotMapMaximalIdealOfIsLocalization S p Rₚ Sₚ)]
  · congr
  · ext x
    simp only [equivQuotMaximalIdealOfIsLocalization, RingHom.quotientKerEquivOfSurjective,
      RingEquiv.coe_ringHom_trans, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk,
      quotMapEquivQuotMapMaximalIdealOfIsLocalization,
      Ideal.Quotient.algebraMap_quotient_map_quotient]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

open nonZeroDivisors in
/-- The trace map on `B → A` coincides with the trace map on `B⧸pB → A⧸p`. -/
lemma Algebra.trace_quotient_eq_of_isDedekindDomain (x) [IsDedekindDomain R] [IsDomain S]
    [NoZeroSMulDivisors R S] [Module.Finite R S] [IsIntegrallyClosed S] :
    Algebra.trace (R ⧸ p) (S ⧸ pS) (Ideal.Quotient.mk pS x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  letI : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  haveI : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (NoZeroSMulDivisors.algebraMap_injective _ _))
  haveI : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors S e
  haveI : NoZeroSMulDivisors Rₚ Sₚ := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
      RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    simp only [RingHom.algebraMap_toAlgebra, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
      mul_eq_zero, Subtype.exists, exists_prop] at hx ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, H⟩ := hx
    simp only [(injective_iff_map_eq_zero' _).mp (NoZeroSMulDivisors.algebraMap_injective R S)] at H
    refine ⟨a, ha, H⟩
  haveI : Module.Finite Rₚ Sₚ := Module.Finite_of_isLocalization R S _ _ p.primeCompl
  haveI : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : IsPrincipalIdealRing Rₚ := by
    by_cases hp : p = ⊥
    · have : IsFractionRing R Rₚ := by
        delta IsFractionRing
        convert inferInstanceAs (IsLocalization p.primeCompl Rₚ)
        ext; simp [hp, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      letI : Field Rₚ := IsFractionRing.toField R
      infer_instance
    · have := (IsDedekindDomain.isDedekindDomainDvr R).2 p hp inferInstance
      infer_instance
  haveI : Module.Free Rₚ Sₚ := Module.free_of_finite_type_torsion_free'
  apply (equivQuotMaximalIdealOfIsLocalization p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    RingEquiv.apply_symm_apply, ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [equivQuotMaximalIdealOfIsLocalization, RingHom.quotientKerEquivOfSurjective,
    RingEquiv.coe_trans, Function.comp_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfRightInverse.apply, RingHom.kerLift_mk]

end IsDedekindDomain
