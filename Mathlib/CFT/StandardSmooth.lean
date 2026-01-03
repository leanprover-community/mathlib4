module
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

@[expose] public section

open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsLocalization

lemma Away.mul_of_isUnit (x y : R) [IsLocalization.Away x S] (h : IsUnit (algebraMap R S y)) :
    IsLocalization.Away (x * y) S :=
  have : Away ((algebraMap R S) y) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul' S _ _ _

lemma Away.mul_of_isUnit' (x y : R) [IsLocalization.Away y S] (h : IsUnit (algebraMap R S x)) :
    IsLocalization.Away (x * y) S :=
  have : Away ((algebraMap R S) x) S := away_of_isUnit_of_bijective _ h Function.bijective_id
  .mul S _ _ _

lemma Away.mul_of_associated (x z : R) (y : S) [IsLocalization.Away x S]
    {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization.Away y T]
    (h : Associated (algebraMap R S z) y) : IsLocalization.Away (x * z) T := by
  obtain ⟨u, hu⟩ := h.symm
  have : Away ((algebraMap R S) z) T := by
    rw [← hu]
    exact .mul_of_isUnit _ _ (u.isUnit.map _)
  exact .mul' S _ _ _

end IsLocalization

lemma LocalizedModule.coe_map_eq {S : Submonoid R}
    {M N M' N' : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M'] [Module R N'] (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂]
    (l : M →ₗ[R] N) :
    ⇑(map S l) = (IsLocalizedModule.iso S g₂).symm ∘
      IsLocalizedModule.map S g₁ g₂ l ∘ IsLocalizedModule.iso S g₁ := by
  rw [← LinearMap.coe_restrictScalars R, restrictScalars_map_eq _ g₁ g₂ l]
  simp

namespace IsLocalizedModule

variable {R M N M' N' : Type*} [CommRing R] {S : Submonoid R}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')
  [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] {l : M →ₗ[R] N}

lemma map_injective_iff_localizedModuleMap_injective :
    Function.Injective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Injective (LocalizedModule.map S l) := by
  simp [LocalizedModule.coe_map_eq g₁ g₂]

lemma map_surjective_iff_localizedModuleMap_surjective :
    Function.Surjective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Surjective (LocalizedModule.map S l) := by
  simp [LocalizedModule.coe_map_eq g₁ g₂]

lemma map_bijective_iff_localizedModuleMap_bijective :
    Function.Bijective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Bijective (LocalizedModule.map S l) := by
  simp [LocalizedModule.coe_map_eq g₁ g₂]

lemma subsingleton_of_subsingleton (S : Submonoid R) (g : M →ₗ[R] M') [IsLocalizedModule S g]
    [Subsingleton M] : Subsingleton M' := by
  rw [subsingleton_iff S g]
  intro m
  use 1
  simp [one_mem, Subsingleton.elim m 0]

end IsLocalizedModule

namespace Algebra

instance (M : Submonoid R) : FormallySmooth R (Localization M) :=
  .of_isLocalization M

instance (priority := 900) SmoothAt.of_formallySmooth
    [FormallySmooth R S] (p : Ideal S) [p.IsPrime] : IsSmoothAt R p :=
  .comp _ S _

variable (R) in
open PrimeSpectrum in
lemma IsSmoothAt.exists_notMem_smooth [FinitePresentation R S] (p : Ideal S) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ f ∉ p, Smooth R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open ‹⟨p, ‹_›⟩ ∈ smoothLocus R S› isOpen_smoothLocus
  refine ⟨f, by simpa using hxf, ⟨?_, inferInstance⟩⟩
  rwa [basicOpen_subset_smoothLocus_iff] at hf

lemma _root_.Ideal.mem_iff_of_associated {I : Ideal R} {x y : R} (h : Associated x y) :
    x ∈ I ↔ y ∈ I := by
  obtain ⟨u, rfl⟩ := h.symm
  exact I.mul_unit_mem_iff_mem u.isUnit

lemma _root_.KaehlerDifferential.span_range_map_derivation_of_isLocalization
    {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T] :
    Submodule.span T (Set.range <| fun s ↦ map R R S T (D R S s)) = ⊤ := by
  convert span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
    (span_range_derivation R S)
  rw [← Set.range_comp, Function.comp_def]

lemma Module.FinitePresentation.exists_notMem_bijective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM] [IsLocalizedModule p.primeCompl fN]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g) f) := by
  obtain ⟨g, hg, h⟩ := exists_bijective_map_powers p.primeCompl fM fN f hf
  exact ⟨g, hg, h g (by rfl)⟩

set_option synthInstance.maxHeartbeats 0 in
variable (R) in
/-- If `S` is `R`-smooth at a prime `p`, then `S` is `R`-standard-smooth in a neighbourhood of `p`:
there exists a basic open `p ∈ D(f)` of `Spec S` such that `S[1/f]` is standard smooth. -/
theorem IsSmoothAt.exists_notMem_isStandardSmooth [FinitePresentation R S] (p : Ideal S) [p.IsPrime]
    [IsSmoothAt R p] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth R (Localization.Away f) := by
  -- By replacing `S` by some `S[1/g]` we may assume `S` is globally smooth.
  wlog h : Smooth R S
  · obtain ⟨g, hg, hsm⟩ := IsSmoothAt.exists_notMem_smooth R p
    have _ : (Ideal.map (algebraMap S (Localization.Away g)) p).IsPrime := by
      apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
      rwa [Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)]
    obtain ⟨g', hg', hstd⟩ := this (R := R) (p.map (algebraMap S (Localization.Away g))) hsm
    have : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : Localization.Away (g * (IsLocalization.Away.sec g g').1) ≃ₐ[S] Localization.Away g' :=
      Localization.algEquiv _ _
    refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, .of_algEquiv (e.restrictScalars R).symm⟩
    refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem ↦ hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap S (Localization.Away g)) hmem
  -- `Ω[Localization.AtPrime p⁄R]` is projective, so free over the local ring `Sₚ` and
  -- a basis extends to a neighbourhood `D(g)`.
  let v (s : S) : (Ω[Localization.AtPrime p⁄R]) :=
    map R R S (Localization.AtPrime p) (D R S s)
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ :=
    span_range_map_derivation_of_isLocalization p.primeCompl
  have : Algebra.EssFiniteType R (Localization.AtPrime p) :=
    Algebra.EssFiniteType.comp R S (Localization.AtPrime p)
  have : Module.FinitePresentation (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R]) :=
    Module.finitePresentation_of_projective (Localization.AtPrime p) (Ω[Localization.AtPrime p⁄R])
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  let e : (κ →₀ S) →ₗ[S] (Ω[S ⁄R]) :=
    Finsupp.basisSingleOne.constr S (fun i : κ ↦ D R S (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalizedModule p.primeCompl l₁ := inferInstance
  let l₂ : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.AtPrime p⁄R]) := map R R S (Localization.AtPrime p)
  have : IsLocalizedModule p.primeCompl l₂ := inferInstance
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p] (Ω[Localization.AtPrime p⁄R]) :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have : eₚ = b.repr.symm := by
    refine Finsupp.basisSingleOne.ext fun i ↦ ?_
    have : Finsupp.basisSingleOne i = l₁ (Finsupp.basisSingleOne i) := by simp [l₁]
    simp only [this, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      Module.Basis.constr_basis, map_D, Module.Basis.coe_repr_symm, eₚ, l₂, e]
    simp [l₁, hb, v]
  have heₚ : Function.Bijective eₚ := by
    rw [this]
    exact b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂
    (Rₚ := Localization.AtPrime p) heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.Away g⁄R]) :=
    map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] (Ω[Localization.Away g⁄R]) :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  use g, hg
  have : Subsingleton (H1Cotangent R (Localization.Away g)) :=
    IsLocalizedModule.subsingleton_of_subsingleton (Submonoid.powers g)
      (Algebra.H1Cotangent.map R R S (Localization.Away g))
  have : FinitePresentation R (Localization.Away g) :=
    .trans R S (Localization.Away g)
  refine .of_basis_kaehlerDifferential (.ofRepr (LinearEquiv.ofBijective eₜ' h).symm) ?_
  rintro - ⟨i, rfl⟩
  use algebraMap S (Localization.Away g) (a i)
  have : Finsupp.single i 1 = l₁ₜ (Finsupp.basisSingleOne i) := by simp [l₁ₜ]
  simp [eₜ', this, -Finsupp.coe_basisSingleOne, l₂ₜ, e]

variable (R S) in
/-- If `S` is `R`-smooth, there exists a cover by basic opens `D(sᵢ)` such that
`S[1/sᵢ]` is `R`-standard-smooth. -/
theorem Smooth.exists_span_eq_top_isStandardSmooth [Smooth R S] :
    ∃ (s : Set S), Ideal.span s = ⊤ ∧ ∀ x ∈ s, IsStandardSmooth R (Localization.Away x) := by
  choose f hf₁ hf₂ using IsSmoothAt.exists_notMem_isStandardSmooth R (S := S)
  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, ?_⟩
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, _root_.eq_top_iff]
    rintro p -
    rw [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion]
    use p
    apply hf₁
  · simp_rw [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro p
    apply hf₂

end Algebra
