import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Topology.LocallyConstant.Basic

section

variable {R : Type*} [CommSemiring R] (S T : Submonoid R)
variable (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
variable {M N : Type*}
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

lemma isLocalizedModule_extendScalarsOfIsLocalization
    (f : M →ₗ[R] N) [IsLocalizedModule T f] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A T)
      (f.extendScalarsOfIsLocalization S A) where
  map_units x := by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units f ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End_isUnit_iff] at this ⊢
    exact this
  surj' y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj T f y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩

lemma isLocalizedModule_of_exists_mul_mem
    (h : S ≤ T)
    (h' : ∀ x : T, ∃ m : R, m * x ∈ S)
    (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    IsLocalizedModule T f where
  map_units x := by
    obtain ⟨m, mx⟩ := h' x
    have := IsLocalizedModule.map_units f ⟨_, mx⟩
    rw [map_mul, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at this
    exact this.2
  surj' y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨t, h t.2⟩⟩, e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) e
    exact ⟨⟨c, h c.2⟩, hc⟩

end

universe uR uM

variable (R : Type uR) (M : Type uM) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma Module.Free.of_ringEquiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    (e₁ : R ≃+* R') (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] M') [Module.Free R M] :
    Module.Free R' M' := by
  let I := Module.Free.ChooseBasisIndex R M
  obtain ⟨e₃ : M ≃ₗ[R] I →₀ R⟩ := Module.Free.chooseBasis R M
  let e : M' ≃+ (I →₀ R') :=
    (e₂.symm.trans e₃).toAddEquiv.trans (Finsupp.mapRange.addEquiv (α := I) e₁.toAddEquiv)
  have he (x) : e x = Finsupp.mapRange.addEquiv (α := I) e₁.toAddEquiv (e₃ (e₂.symm x)) := rfl
  let e' : M' ≃ₗ[R'] (I →₀ R') :=
    { __ := e, map_smul' := fun m x ↦ Finsupp.ext fun i ↦ by simp [he, map_smulₛₗ] }
  exact Module.Free.of_equiv e'.symm

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma Module.Free.iff_of_ringEquiv {R R' M M'} [Semiring R] [AddCommMonoid M] [Module R M]
    [Semiring R'] [AddCommMonoid M'] [Module R' M']
    (e₁ : R ≃+* R') (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] M') :
    Module.Free R M ↔ Module.Free R' M' :=
  ⟨fun _ ↦ of_ringEquiv e₁ e₂, fun _ ↦ of_ringEquiv e₁.symm e₂.symm⟩

theorem Module.free_of_isLocalizedModule {Rₛ Mₛ} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (S) (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M] :
      Module.Free Rₛ Mₛ :=
    Free.of_equiv (IsLocalizedModule.isBaseChange S Rₛ f).equiv

variable {R M} in
universe uR' uM' in
theorem Module.lift_rank_of_isLocalizedModule_of_free
    (Rₛ : Type uR') {Mₛ : Type uM'} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
      Cardinal.lift.{uM} (Module.rank Rₛ Mₛ) = Cardinal.lift.{uM'} (Module.rank R M) := by
  apply Cardinal.lift_injective.{max uM' uR'}
  have := (algebraMap R Rₛ).domain_nontrivial
  have := (IsLocalizedModule.isBaseChange S Rₛ f).equiv.lift_rank_eq.symm
  simp only [rank_tensorProduct, rank_self,
    Cardinal.lift_one, one_mul, Cardinal.lift_lift] at this ⊢
  convert this
  exact Cardinal.lift_umax

variable {R M} in
universe uR' uM' in
theorem Module.finrank_of_isLocalizedModule_of_free
    (Rₛ : Type uR') {Mₛ : Type uM'} [AddCommGroup Mₛ] [Module R Mₛ]
    [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (S : Submonoid R)
    (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Free R M]
    [Nontrivial Rₛ] :
      Module.finrank Rₛ Mₛ = Module.finrank R M := by
  simpa using congr(Cardinal.toNat $(Module.lift_rank_of_isLocalizedModule_of_free Rₛ S f))

#min_imports

namespace Module

open PrimeSpectrum

def freeLocus : Set (PrimeSpectrum R) :=
  { p | Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) }

variable {R M}

lemma mem_freeLocus {p} : p ∈ freeLocus R M ↔
  Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) := Iff.rfl

attribute [local instance] RingHomInvPair.of_ringEquiv in
lemma mem_freeLocus_of_isLocalization (p : PrimeSpectrum R)
    (Rₚ Mₚ) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p.asIdeal]
    [AddCommGroup Mₚ] [Module R Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule p.asIdeal.primeCompl f]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] :
    p ∈ freeLocus R M ↔ Module.Free Rₚ Mₚ := by
  apply Module.Free.iff_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) Rₚ).toRingEquiv
  refine { __ := IsLocalizedModule.iso p.asIdeal.primeCompl f, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl r
  apply ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    algebraMap_end_apply, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, IsLocalization.algEquiv_apply,
    IsLocalization.map_id_mk']
  simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
    IsLocalization.map_id_mk']


lemma Submodule.FG.of_restrictScalars (R) {A M} [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M] (S : Submodule A M)
    (hS : (S.restrictScalars R).FG) : S.FG := by
  obtain ⟨s, e⟩ := hS
  refine ⟨s, Submodule.restrictScalars_injective R _ _ (le_antisymm ?_ ?_)⟩
  · show Submodule.span A s ≤ S
    have := Submodule.span_le.mp e.le
    rwa [Submodule.span_le]
  · rw [← e]
    exact Submodule.span_le_restrictScalars _ _ _

open TensorProduct in
instance {A} [CommRing A] [Algebra R A] [Module.FinitePresentation R M] :
    Module.FinitePresentation A (A ⊗[R] M) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have inst := Module.finitePresentation_of_free A (A ⊗[R] (Fin n → R))
  apply Module.finitePresentation_of_surjective (f.baseChange A)
    (LinearMap.lTensor_surjective A hf)
  have : Function.Exact ((LinearMap.ker f).subtype.baseChange A) (f.baseChange A) :=
    lTensor_exact A f.exact_subtype_ker_map hf
  rw [LinearMap.exact_iff] at this
  rw [this, ← Submodule.map_top]
  apply Submodule.FG.map
  have : Module.Finite R (LinearMap.ker f) :=
    ⟨(Submodule.fg_top _).mpr (Module.FinitePresentation.fg_ker f hf)⟩
  exact Module.Finite.out (R := A) (M := A ⊗[R] LinearMap.ker f)

open TensorProduct in
lemma FinitePresentation.of_isBaseChange
    {A} [CommRing A] [Algebra R A] {N} [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) (h : IsBaseChange A f) [Module.FinitePresentation R M] :
    Module.FinitePresentation A N :=
  Module.finitePresentation_of_surjective
    h.equiv.toLinearMap h.equiv.surjective (by simpa using Submodule.fg_bot)

open TensorProduct in
instance (S : Submonoid R) [Module.FinitePresentation R M] :
    Module.FinitePresentation (Localization S) (LocalizedModule S M) :=
  FinitePresentation.of_isBaseChange (LocalizedModule.mkLinearMap S M)
    ((isLocalizedModule_iff_isBaseChange S _ _).mp inferInstance)

lemma freeLocus_localizationAway [Module.FinitePresentation R M] {f : R} :
    freeLocus (Localization.Away f) (LocalizedModule (.powers f) M) =
      comap (algebraMap R _) ⁻¹' freeLocus R M := by
  ext p
  simp only [Set.mem_preimage]
  have hp : algebraMap R (Localization.Away f) f ∉ p.asIdeal :=
    fun H ↦ p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ H
      (IsLocalization.Away.algebraMap_isUnit f))
  let p' := p.asIdeal.comap (algebraMap R _)
  have hp' : Submonoid.powers f ≤ p'.primeCompl := by
    simpa [Submonoid.powers_le, p', Ideal.primeCompl]
  let Rₚ := Localization.AtPrime p'
  let Mₚ := LocalizedModule p'.primeCompl M
  letI : Algebra (Localization.Away f) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p'.primeCompl hp'
  have : IsScalarTower R (Localization.Away f) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime Rₚ p.asIdeal := by
    have := IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
    apply IsLocalization.isLocalization_of_is_exists_mul_mem _
      (Submonoid.map (algebraMap R (Localization.Away f)) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective (.powers f) x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  letI : Module (Localization.Away f) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization.Away f) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • _ by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap p'.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
    (Localization.Away f)
  have : IsLocalizedModule p.asIdeal.primeCompl l := by
    have : IsLocalizedModule _ l :=
      isLocalizedModule_extendScalarsOfIsLocalization _ p'.primeCompl ..
    apply isLocalizedModule_of_exists_mul_mem
      (Algebra.algebraMapSubmonoid (Localization.Away f) p'.primeCompl)
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · rintro ⟨x, hx⟩
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective (.powers f) x
      refine ⟨algebraMap _ _ s.1, x, fun H ↦ hx ?_, by simp⟩
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ H
  rw [mem_freeLocus_of_isLocalization (R := Localization.Away f) p Rₚ Mₚ l]
  rfl

lemma freeLocus_eq_univ_iff [Module.FinitePresentation R M] :
    freeLocus R M = Set.univ ↔ Module.Projective R M := by
  simp_rw [Set.eq_univ_iff_forall, mem_freeLocus]
  exact ⟨fun H ↦ Module.projective_of_localization_maximal fun I hI ↦
    have := H ⟨I, hI.isPrime⟩; .of_free, fun H x ↦ Module.free_of_flat_of_localRing⟩

lemma basicOpen_subset_freeLocus_iff [Module.FinitePresentation R M] {f : R} :
    (basicOpen f : Set (PrimeSpectrum R)) ⊆ freeLocus R M ↔
      Module.Projective (Localization.Away f) (LocalizedModule (.powers f) M) := by
  rw [← freeLocus_eq_univ_iff, freeLocus_localizationAway,
    Set.preimage_eq_univ_iff, localization_away_comap_range _ f]

lemma isOpen_freeLocus [Module.FinitePresentation R M] :
    IsOpen (freeLocus R M) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨r, hr, hr', _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  exact ⟨basicOpen r, basicOpen_subset_freeLocus_iff.mpr inferInstance, (basicOpen r).2, hr⟩

variable (M) in
noncomputable
def rankAtStalk (p : PrimeSpectrum R) : ℕ :=
  Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)

lemma isLocallyConstant_rankAtStalk_freeLocus [Module.FinitePresentation R M] :
    IsLocallyConstant (fun x : freeLocus R M ↦ rankAtStalk M x.1) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun ⟨x, hx⟩ ↦ ?_
  have : Module.Free _ _ := hx
  obtain ⟨f, hf, hf', hf''⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    x.asIdeal.primeCompl (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)
    (Localization.AtPrime x.asIdeal)
  refine ⟨Subtype.val ⁻¹' basicOpen f, (basicOpen f).2.preimage continuous_subtype_val, hf, ?_⟩
  rintro ⟨p, hp''⟩ hp
  let p' := Algebra.algebraMapSubmonoid (Localization (.powers f)) p.asIdeal.primeCompl
  have hp' : Submonoid.powers f ≤ p.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl]
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule p.asIdeal.primeCompl M
  letI : Algebra (Localization.Away f) Rₚ :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (.powers f) p.asIdeal.primeCompl hp'
  have : IsScalarTower R (Localization.Away f) Rₚ :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  letI : Module (Localization.Away f) Mₚ := Module.compHom Mₚ (algebraMap _ Rₚ)
  have : IsScalarTower R (Localization.Away f) Mₚ :=
    ⟨fun r r' m ↦ show algebraMap _ Rₚ (r • r') • m = _ by
      simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_smul]; rfl⟩
  have : IsScalarTower (Localization.Away f) Rₚ Mₚ :=
    ⟨fun r r' m ↦ show _ = algebraMap _ Rₚ r • _ by rw [← mul_smul, ← Algebra.smul_def]⟩
  let l := (IsLocalizedModule.liftOfLE _ _ hp' (LocalizedModule.mkLinearMap (.powers f) M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).extendScalarsOfIsLocalization (.powers f)
    (Localization.Away f)
  have : IsLocalization p' Rₚ :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) Rₚ _ _ hp'
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl) l :=
    isLocalizedModule_extendScalarsOfIsLocalization _ p.asIdeal.primeCompl ..
  have := Module.finrank_of_isLocalizedModule_of_free Rₚ p' l
  simp [rankAtStalk, this, hf'']

lemma isLocallyConstant_rankAtStalk [Module.FinitePresentation R M] [Module.Projective R M] :
    IsLocallyConstant (rankAtStalk (R := R) M) := by
  let e : freeLocus R M ≃ₜ PrimeSpectrum R :=
    (Homeomorph.setCongr (freeLocus_eq_univ_iff.mpr inferInstance)).trans
      (Homeomorph.Set.univ (PrimeSpectrum R))
  convert isLocallyConstant_rankAtStalk_freeLocus.comp_continuous e.symm.continuous

end Module
