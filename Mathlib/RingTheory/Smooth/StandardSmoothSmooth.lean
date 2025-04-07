/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.FreeKaehler
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Smooth and locally standard smooth
-/

suppress_compilation

universe w t u v

section Upstream

namespace Algebra

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

@[simps (config := .lemmasOnly) vars]
def Generators.reindex (P : Generators.{w} R S) {ι : Type*} (e : ι ≃ P.vars) :
    Generators R S where
  vars := ι
  val := P.val ∘ e
  σ' := rename e.symm ∘ P.σ
  aeval_val_σ' s := by
    conv_rhs => rw [← P.aeval_val_σ s]
    rw [← MvPolynomial.aeval_rename]
    simp

lemma Generators.reindex_val (P : Generators.{w} R S) {ι : Type*} (e : ι ≃ P.vars) :
    (P.reindex e).val = P.val ∘ e :=
  rfl

lemma _root_.MvPolynomial.aeval_comp_rename {σ τ R S : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] (k : σ → τ) (g : τ → S) :
    (aeval (R := R) g).comp (rename k) = MvPolynomial.aeval (g ∘ k) := by
  ext
  simp

lemma _root_.MvPolynomial.rename_comp_rename {σ τ α R : Type*} [CommSemiring R]
    (f : σ → τ) (g : τ → α) :
    (MvPolynomial.rename (R := R) g).comp (MvPolynomial.rename f) =
      MvPolynomial.rename (g ∘ f) := by
  ext
  simp

lemma _root_.MvPolynomial.rename_id' {σ R : Type*} [CommSemiring R] :
    MvPolynomial.rename (σ := σ) (R := R) _root_.id = AlgHom.id R _ := by
  ext
  simp

@[simp]
lemma _root_.Ideal.comap_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (I : Ideal S) :
    Ideal.comap (AlgHom.id R S) I = I :=
  Ideal.comap_id I

@[simps toGenerators, simps (config := .lemmasOnly) relation rels]
def Presentation.reindex (P : Presentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    Presentation R S where
  __ := P.toGenerators.reindex e
  rels := κ
  relation := rename e.symm ∘ P.relation ∘ f
  span_range_relation_eq_ker := by
    rw [Generators.ker_eq_ker_aeval_val, Generators.reindex_val, ← aeval_comp_rename,
      ← AlgHom.comap_ker, ← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker,
      Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Set.image_univ,
      ← Ideal.map_span (rename ⇑e.symm)]
    have hf : Function.Bijective (MvPolynomial.rename e.symm) := (renameEquiv R e.symm).bijective
    apply Ideal.comap_injective_of_surjective _ hf.2
    simp_rw [Ideal.comap_comapₐ, rename_comp_rename, Generators.reindex_vars, Equiv.self_comp_symm]
    simp [Ideal.comap_map_of_bijective _ hf, rename_id']

@[simp]
lemma Presentation.isFinite_reindex_iff (P : Presentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    (P.reindex e f).IsFinite ↔ P.IsFinite :=
  ⟨fun h ↦ ⟨e.finite_iff.mp h.1, f.finite_iff.mp h.2⟩,
    fun h ↦ ⟨e.finite_iff.mpr h.1, f.finite_iff.mpr h.2⟩⟩

@[simps toPresentation, simps (config := .lemmasOnly) map]
def PreSubmersivePresentation.reindex (P : PreSubmersivePresentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    PreSubmersivePresentation R S where
  __ := P.toPresentation.reindex e f
  map := e.symm ∘ P.map ∘ f
  map_inj := by
    rw [Function.Injective.of_comp_iff e.symm.injective, Function.Injective.of_comp_iff P.map_inj]
    exact f.injective
  relations_finite := f.finite_iff.mpr P.relations_finite

lemma PreSubmersivePresentation.jacobiMatrix_reindex (P : PreSubmersivePresentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels)
    [Fintype P.rels] [DecidableEq P.rels] [Fintype (P.reindex e f).rels]
    [DecidableEq P.rels] [DecidableEq (P.reindex e f).rels]  :
    (P.reindex e f).jacobiMatrix =
      (P.jacobiMatrix.reindex f.symm f.symm).map (MvPolynomial.rename e.symm) := by
  ext i j : 1
  simp [jacobiMatrix_apply, PreSubmersivePresentation.reindex_map, Presentation.reindex_relation,
    Generators.reindex_vars, MvPolynomial.pderiv_rename e.symm.injective]

@[simp]
lemma PreSubmersivePresentation.jacobian_reindex (P : PreSubmersivePresentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    (P.reindex e f).jacobian = P.jacobian := by
  classical
  cases nonempty_fintype P.rels
  cases nonempty_fintype (P.reindex e f).rels
  letI : Fintype κ := inferInstanceAs (Fintype ((P.reindex e f).rels))
  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
    Matrix.reindex_apply, Equiv.symm_symm, Generators.algebraMap_apply, Generators.reindex_val]
  simp_rw [← MvPolynomial.aeval_rename, Generators.reindex_vars, Presentation.reindex_rels,
    ← AlgHom.mapMatrix_apply, ← Matrix.det_submatrix_equiv_self f, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map_map]
  simp [← AlgHom.coe_comp, rename_comp_rename, rename_id']

@[simps toPreSubmersivePresentation]
def SubmersivePresentation.reindex (P : SubmersivePresentation.{w, t} R S)
    {ι κ : Type*} (e : ι ≃ P.vars) (f : κ ≃ P.rels) :
    SubmersivePresentation R S where
  __ := P.toPreSubmersivePresentation.reindex e f
  jacobian_isUnit := by simp [P.jacobian_isUnit]
  isFinite := by simp [P.isFinite]

lemma isStandardSmooth_iff_univ :
    IsStandardSmooth.{u, v} R S ↔ IsStandardSmooth.{0, 0} R S := by
  refine ⟨fun ⟨⟨P⟩⟩ ↦ ?_, fun ⟨⟨P⟩⟩ ↦ ⟨⟨P.reindex Equiv.ulift Equiv.ulift⟩⟩⟩
  cases nonempty_fintype P.vars
  cases nonempty_fintype P.rels
  let eq1 : P.vars ≃ Fin (Fintype.card P.vars) := Fintype.equivFin P.vars
  let eq2 : P.rels ≃ Fin (Fintype.card P.rels) := Fintype.equivFin P.rels
  exact ⟨⟨P.reindex eq1.symm eq2.symm⟩⟩

end Algebra

instance Localization.Away.finitePresentation {R : Type*} [CommRing R] (r : R) :
    Algebra.FinitePresentation R (Localization.Away r) :=
  IsLocalization.Away.finitePresentation r

instance Localization.essFiniteType {R : Type*} [CommRing R] (S : Submonoid R) :
    Algebra.EssFiniteType R (Localization S) :=
  Algebra.EssFiniteType.of_isLocalization _ S

section

variable {R M M' : Type*} [CommRing R]
    (S : Submonoid R) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

lemma IsLocalizedModule.subsingleton [IsLocalizedModule S f] (h : 0 ∈ S) :
    Subsingleton M' := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨⟨a, s⟩, (rfl : mk' f a s = _)⟩ := IsLocalizedModule.mk'_surjective S f a
  obtain ⟨⟨b, t⟩, (rfl : mk' f b t = _)⟩ := IsLocalizedModule.mk'_surjective S f b
  exact (IsLocalizedModule.mk'_eq_mk'_iff f a b s t).mpr ⟨⟨0, h⟩, by simp⟩

lemma IsLocalizedModule.subsingleton_of_subsingleton [IsLocalizedModule S f] [Subsingleton M] :
    Subsingleton M' := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨⟨a, s⟩, (rfl : mk' f a s = _)⟩ := IsLocalizedModule.mk'_surjective S f a
  obtain ⟨⟨b, t⟩, (rfl : mk' f b t = _)⟩ := IsLocalizedModule.mk'_surjective S f b
  rw [IsLocalizedModule.mk'_eq_mk'_iff f a b s t]
  use 1
  apply Subsingleton.elim

lemma IsLocalizedModule.exists_subsingleton_away {R M M' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup M'] [Module R M'] (l : M →ₗ[R] M')
    (p : Ideal R) [p.IsPrime] [IsLocalizedModule p.primeCompl l] [Subsingleton M'] :
    ∃ f ∉ p, Subsingleton (LocalizedModule (Submonoid.powers f) M) := by
  let e := IsLocalizedModule.iso p.primeCompl l
  have : Subsingleton (LocalizedModule p.primeCompl M) := e.subsingleton
  apply LocalizedModule.exists_subsingleton_away

section

variable {R M N M' N' : Type*} [CommSemiring R] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
  (g₁ : M →ₗ[R] M') (g₂ : N →ₗ[R] N')

lemma IsLocalizedModule.map_injective_iff_localizedModule_map_injective
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    Function.Injective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Injective (LocalizedModule.map S l) := by
  have : ⇑(LocalizedModule.map S l) =
      ⇑((IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁) := by
    rw [← LocalizedModule.restrictScalars_map_eq S g₁ g₂ l]
    simp only [LinearMap.coe_restrictScalars]
  rw [this]
  simp

lemma IsLocalizedModule.map_surjective_iff_localizedModule_map_surjective
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    Function.Surjective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Surjective (LocalizedModule.map S l) := by
  have : ⇑(LocalizedModule.map S l) =
      ⇑((IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁) := by
    rw [← LocalizedModule.restrictScalars_map_eq S g₁ g₂ l]
    simp only [LinearMap.coe_restrictScalars]
  rw [this]
  simp

lemma IsLocalizedModule.map_bijective_iff_localizedModule_map_bijective
    [IsLocalizedModule S g₁] [IsLocalizedModule S g₂] (l : M →ₗ[R] N) :
    Function.Bijective (IsLocalizedModule.map S g₁ g₂ l) ↔
      Function.Bijective (LocalizedModule.map S l) := by
  have : ⇑(LocalizedModule.map S l) =
      ⇑((IsLocalizedModule.iso S g₂).symm ∘ₗ
      IsLocalizedModule.map S g₁ g₂ l ∘ₗ IsLocalizedModule.iso S g₁) := by
    rw [← LocalizedModule.restrictScalars_map_eq S g₁ g₂ l]
    simp only [LinearMap.coe_restrictScalars]
  rw [this]
  simp

end

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M M' M'' : Type*}
  [AddCommMonoid M] [AddCommMonoid M']
  [AddCommMonoid M''] [Module R M] [Module R M'] [Module R M'']
  (f : M →ₗ[R] M') (g : M →ₗ[R] M'') [IsLocalizedModule S f]

@[simp]
lemma IsLocalizedModule.iso_symm_apply'' (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 := by
  show ((iso S f).symm.toLinearMap.comp f) x = _
  --have := iso_symm_comp S f
  rw [iso_symm_comp]
  simp

@[simp]
lemma LocalizedModule.lift_mk_one (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) :
    (lift S g h) (mk m 1) = g m := by
  conv_rhs => rw [← LocalizedModule.lift_comp S g h]
  simp

@[simp]
lemma IsLocalizedModule.lift_comp_iso
    (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) :
    IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h := by
  apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M) h
  ext x
  simp

@[simp]
lemma IsLocalizedModule.lift_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (x) :
    IsLocalizedModule.lift S f g h ((iso S f) x) =
      LocalizedModule.lift _ g h x := by
  rw [← IsLocalizedModule.lift_comp_iso S f]
  dsimp

end

section

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M M' M'' : Type*} [AddCommMonoid M]
  [AddCommMonoid M'] [AddCommMonoid M'']
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]
  [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']
  (f : M →ₗ[R] M') (g : M →ₗ[R] M'') [IsLocalizedModule S f]

@[simp]
lemma IsLocalizedModule.linearEquiv_apply [IsLocalizedModule S g] (x) :
    (linearEquiv S f g) (f x) = g x := by
  simp only [linearEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    iso_symm_apply'']
  simp

@[simp]
lemma IsLocalizedModule.linearEquiv_symm_apply [IsLocalizedModule S g] (x) :
    (linearEquiv S f g).symm (g x) = f x := by
  simp only [linearEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    iso_symm_apply'']
  simp

end

end

end Upstream

namespace RingHom

def Smooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Smooth R _ S _ f.toAlgebra

lemma Smooth.stableUnderComposition : StableUnderComposition Smooth := by
  introv R hf hg
  algebraize [f, g, g.comp f]
  have : Algebra.Smooth R S := hf
  have : Algebra.Smooth S T := hg
  rw [Smooth]
  exact Algebra.Smooth.comp R S T

lemma Smooth.respectsIso : RespectsIso Smooth := by
  apply Smooth.stableUnderComposition.respectsIso
  introv
  algebraize [e.toRingHom]
  rw [Smooth]
  have : IsLocalization.Away (1 : R) S := by
    apply IsLocalization.away_of_isUnit_of_bijective
    simp only [isUnit_one]
    exact e.bijective
  exact Algebra.Smooth.of_isLocalization_Away 1

lemma Smooth.ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth := by
  introv R hs hf
  have hfin : f.FinitePresentation := by
    apply finitePresentation_ofLocalizationSpanTarget _ s hs
    intro r
    apply (hf r).finitePresentation
  algebraize [f]
  rw [Smooth]
  refine ⟨?_, hfin⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_smoothLocus_iff.mpr ?_ hrx
  convert (hf ⟨r, hr⟩).1
  dsimp
  ext
  dsimp
  rw [Algebra.smul_def]
  rfl

end RingHom

namespace LinearMap

variable {R M N : Type*} [CommRing R]

end LinearMap

namespace Module

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R)
    {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')
    [IsLocalizedModule S f]
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ]
    [Module Rₛ M'] [IsScalarTower R Rₛ M']
    [IsLocalization S Rₛ]
    (Mₜ : R → Type*) [∀ t, AddCommGroup (Mₜ t)] [∀ t, Module R (Mₜ t)]
    (fₜ : ∀ t, M →ₗ[R] Mₜ t)
    [∀ t, IsLocalizedModule (.powers t) (fₜ t)]
    (Rₜ : R → Type*) [∀ t, CommRing (Rₜ t)] [∀ t, Algebra R (Rₜ t)]
    [∀ t, IsLocalization.Away t (Rₜ t)]
    [∀ t, Module (Rₜ t) (Mₜ t)]
    [∀ t, IsScalarTower R (Rₜ t) (Mₜ t)]
    [FinitePresentation R M] {I : Type*} [Finite I]
    (b : Basis I Rₛ M')

include b

lemma FinitePresentation.exists_basis_of_isLocalizedModule_powers :
    ∃ (t : R) (ht : t ∈ S) (b' : Basis I (Rₜ t) (Mₜ t)),
      ∀ (i : I), (IsLocalizedModule.lift (.powers t) (fₜ t) f
        (fun x ↦ IsLocalizedModule.map_units f
          ⟨x.1, SetLike.le_def.mp (Submonoid.powers_le.mpr ht) x.2⟩) (b' i) = b i) := by
  obtain ⟨t, ht, b', hb'⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers S f Rₛ b
  use t, ht
  let eM : LocalizedModule (.powers t) M ≃ₗ[R] Mₜ t := IsLocalizedModule.iso (.powers t) (fₜ t)
  let eb'' : Mₜ t ≃ₗ[R] I →₀ Rₜ t :=
    eM.symm ≪≫ₗ b'.repr.restrictScalars R ≪≫ₗ
      IsLocalizedModule.linearEquiv (.powers t)
        (Finsupp.mapRange.linearMap (Algebra.linearMap R _))
        (Finsupp.mapRange.linearMap (Algebra.linearMap R _))
  let eb : Mₜ t ≃ₗ[Rₜ t] I →₀ Rₜ t :=
    .ofLinear (.extendScalarsOfIsLocalizationEquiv (.powers t) (Rₜ t) eb'')
      (.extendScalarsOfIsLocalizationEquiv (.powers t) (Rₜ t) eb''.symm)
      (by ext; simp) (by ext; simp)
  refine ⟨Basis.ofRepr eb, fun i ↦ ?_⟩
  simp only [LinearMap.extendScalarsOfIsLocalizationEquiv_apply, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, Basis.coe_ofRepr, LinearEquiv.ofLinear_symm_apply,
    LinearMap.extendScalarsOfIsLocalization_apply', LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_symm_apply, Basis.repr_symm_apply, eb, eb'']
  have : Finsupp.single i 1 =
    (Finsupp.mapRange.linearMap (Algebra.linearMap R (Rₜ t))) (Finsupp.basisSingleOne i) := by simp
  rw [this]
  rw [IsLocalizedModule.linearEquiv_symm_apply]
  simp only [Finsupp.coe_basisSingleOne, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, map_one, Finsupp.linearCombination_single, one_smul,
    eM, eb'', eb]
  rw [IsLocalizedModule.lift_iso, hb']

end

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

open LinearMap in
lemma exists_of_surjective [Module.Finite R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] (hf : Function.Surjective (LocalizedModule.map p.primeCompl f)) :
    ∃ g ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers g) f) := by
  have : Submodule.localized p.primeCompl (range f) = range (LocalizedModule.map p.primeCompl f) :=
    localized'_range_eq_range_localizedMap _ _ _ _ _
  let fₚ : N ⧸ LinearMap.range f →ₗ[R]
      LocalizedModule p.primeCompl N ⧸ LinearMap.range (LocalizedModule.map p.primeCompl f) :=
    (LinearEquiv.toLinearMap <| (Submodule.quotEquivOfEq _ _ this).restrictScalars R) ∘ₗ
      (range f).toLocalizedQuotient p.primeCompl
  have : IsLocalizedModule p.primeCompl fₚ := by
    apply IsLocalizedModule.of_linearEquiv
  have : Subsingleton
      (LocalizedModule p.primeCompl N ⧸ LinearMap.range (LocalizedModule.map p.primeCompl f)) := by
    rwa [Submodule.subsingleton_quotient_iff_eq_top, LinearMap.range_eq_top]
  obtain ⟨g, hg, _⟩ := IsLocalizedModule.exists_subsingleton_away fₚ p
  use g, hg
  let p : Submodule (Localization (Submonoid.powers g)) (LocalizedModule (Submonoid.powers g) N) :=
    LinearMap.range ((LocalizedModule.map (Submonoid.powers g)) f)
  let q : Submodule (Localization (Submonoid.powers g)) (LocalizedModule (Submonoid.powers g) N) :=
      Submodule.localized (Submonoid.powers g) (LinearMap.range f)
  have : p = q := by
    symm
    apply LinearMap.localized'_range_eq_range_localizedMap
  let eq : (LocalizedModule (Submonoid.powers g) N ⧸
      range ((LocalizedModule.map (Submonoid.powers g)) f)) ≃ₗ[R]
        (LocalizedModule (Submonoid.powers g) (N ⧸ range f)) :=
    (p.quotEquivOfEq q this).restrictScalars R ≪≫ₗ (IsLocalizedModule.iso (Submonoid.powers g)
      ((range f).toLocalizedQuotient (Submonoid.powers g))).symm
  rw [← LinearMap.range_eq_top, ← Submodule.subsingleton_quotient_iff_eq_top]
  apply eq.subsingleton

lemma exists_of_surjective' [Module.Finite R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Mₚ Nₚ : Type*}
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    (hf : Function.Surjective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ g ∉ p, Function.Surjective (LocalizedModule.map (Submonoid.powers g) f) := by
  simp_rw [IsLocalizedModule.map_surjective_iff_localizedModule_map_surjective] at hf ⊢
  exact exists_of_surjective f p hf

lemma exists_of_bijective' [Module.Finite R M] [Module.FinitePresentation R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    {Mₜ Nₜ : R → Type*}
    [∀ r, AddCommGroup (Mₜ r)] [∀ r, Module R (Mₜ r)]
    [∀ r, AddCommGroup (Nₜ r)] [∀ r, Module R (Nₜ r)]
    (fₜ : ∀ r, M →ₗ[R] Mₜ r) [∀ r, IsLocalizedModule (Submonoid.powers r) (fₜ r)]
    (gₜ : ∀ r, N →ₗ[R] Nₜ r) [∀ r, IsLocalizedModule (Submonoid.powers r) (gₜ r)]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧
      Function.Bijective (IsLocalizedModule.map (Submonoid.powers g) (fₜ g) (gₜ g) f) := by
  simp_rw [IsLocalizedModule.map_bijective_iff_localizedModule_map_bijective]
  obtain ⟨g, hg, h⟩ := exists_bijective_map_powers p.primeCompl fM fN f hf
  exact ⟨g, hg, h g (by rfl)⟩

lemma exists_of_bijective [Module.Finite R M] [Module.FinitePresentation R N] (f : M →ₗ[R] N)
    (p : Ideal R) [p.IsPrime] {Rₚ Mₚ Nₚ : Type*}
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [AddCommGroup Mₚ] [AddCommGroup Nₚ] [Module R Mₚ] [Module R Nₚ]
    (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM]
    [IsLocalizedModule p.primeCompl fN]
    (hf : Function.Bijective (IsLocalizedModule.map p.primeCompl fM fN f)) :
    ∃ (g : R), g ∉ p ∧ Function.Bijective (LocalizedModule.map (Submonoid.powers g) f) := by
  obtain ⟨g, hg, h⟩ := exists_bijective_map_powers p.primeCompl fM fN f hf
  exact ⟨g, hg, h g (by rfl)⟩

end Module

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S]

section

variable [Algebra R S]

variable (R) in
lemma isSmoothAt_of_smooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    IsSmoothAt R p := by
  have : smoothLocus R S = Set.univ := by
    rw [smoothLocus_eq_univ_iff]
    infer_instance
  show ⟨p, inferInstance⟩ ∈ smoothLocus R S
  rw [this]
  trivial

open KaehlerDifferential

lemma _root_.KaehlerDifferential.span_range_map_derivation_of_isLocalization
    (R : Type u) {S : Type u} (T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (M : Submonoid S) [IsLocalization M T] :
    Submodule.span T (Set.range <| fun s ↦ map R R S T (D R S s)) = ⊤ := by
  convert span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
    (span_range_derivation R S)
  rw [← Set.range_comp, Function.comp_def]

theorem exists_isStandardSmooth [Smooth R S] (p : Ideal S) [p.IsPrime] :
    ∃ (f : S), f ∉ p ∧ IsStandardSmooth.{u, u} R (Localization.Away f) := by
  have : FormallySmooth R (Localization.AtPrime p) := isSmoothAt_of_smooth R p
  let v (s : S) : (Ω[Localization.AtPrime p⁄R]) :=
    map R R S (Localization.AtPrime p) (D R S s)
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ :=
    span_range_map_derivation_of_isLocalization R (Localization.AtPrime p) p.primeCompl
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
    apply Finsupp.basisSingleOne.ext
    intro i
    have : Finsupp.basisSingleOne i = l₁ (Finsupp.basisSingleOne i) := by simp [l₁]
    simp only [this, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
      Basis.constr_basis, map_D, Basis.coe_repr_symm, eₚ, l₂, e]
    simp [l₁, hb, v]
  have heₚ : Function.Bijective eₚ := by
    rw [this]
    exact b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  let l₁ₜ (s : S) : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away s) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ (s : S) : (Ω[S⁄R]) →ₗ[S] (Ω[Localization.Away s⁄R]) :=
    map R R S (Localization.Away s)
  obtain ⟨g, hg, h⟩ := Module.exists_of_bijective' e p l₁ l₂ (Rₚ := Localization.AtPrime p)
    l₁ₜ l₂ₜ heₚ
  let eₜ' : (κ →₀ Localization.Away g) →ₗ[Localization.Away g] (Ω[Localization.Away g⁄R]) :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) (l₁ₜ g) (l₂ₜ g) (Localization.Away g) e
  use g, hg
  have : Subsingleton (H1Cotangent R (Localization.Away g)) :=
    IsLocalizedModule.subsingleton_of_subsingleton (Submonoid.powers g)
      (Algebra.H1Cotangent.map R R S (Localization.Away g))
  have : FinitePresentation R (Localization.Away g) :=
    FinitePresentation.trans R S (Localization.Away g)
  refine isStandardSmooth_of (I := κ) (Basis.ofRepr (LinearEquiv.ofBijective eₜ' h).symm) ?_
  rintro - ⟨i, rfl⟩
  simp only [Basis.coe_ofRepr, LinearEquiv.symm_symm, LinearEquiv.ofBijective_apply,
    IsLocalizedModule.mapExtendScalars_apply_apply, Set.mem_range, eₜ']
  use algebraMap S (Localization.Away g) (a i)
  have : Finsupp.single i 1 = (l₁ₜ g) (Finsupp.basisSingleOne i) := by simp [l₁ₜ]
  rw [this]
  simp [-Finsupp.coe_basisSingleOne, l₂ₜ, e]

theorem exists_cover [Smooth R S] : ∃ (s : Set S),
    Ideal.span s = ⊤ ∧ ∀ x ∈ s, IsStandardSmooth.{0, 0} R (Localization.Away x) := by
  have (p : Ideal S) [p.IsPrime] :
      ∃ (f : S), f ∉ p ∧ IsStandardSmooth.{0, 0} R (Localization.Away f) := by
    obtain ⟨g, hg, h⟩ := exists_isStandardSmooth (R := R) p
    use g, hg
    rwa [isStandardSmooth_iff_univ] at h
  choose f hf₁ hf₂ using this
  refine ⟨Set.range (fun p : PrimeSpectrum S ↦ f p.asIdeal), ?_, ?_⟩
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [_root_.eq_top_iff]
    rintro p -
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
      Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    use p
    apply hf₁
  · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    intro p
    apply hf₂

end

end Algebra

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

lemma smooth_of_isStandardSmooth (f : R →+* S) (hf : IsStandardSmooth f) :
    Smooth f := by
  algebraize [f]
  rw [RingHom.Smooth]
  infer_instance

theorem locally_isStandardSmooth_of_smooth (f : R →+* S)
    (hf : f.Smooth) : Locally IsStandardSmooth.{0, 0} f := by
  algebraize [f]
  have : Algebra.Smooth R S := hf
  obtain ⟨s, hs, h⟩ := Algebra.exists_cover (R := R) (S := S)
  use s, hs
  intro t ht
  suffices h : Algebra.IsStandardSmooth.{0, 0} R (Localization.Away t) by
    rw [RingHom.IsStandardSmooth]
    convert h
    ext
    rw [Algebra.smul_def]
    rfl
  convert h t ht

theorem smooth_iff_locally_isStandardSmooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Smooth f ↔ Locally IsStandardSmooth.{0, 0} f := by
  constructor
  · intro hf
    exact locally_isStandardSmooth_of_smooth f hf
  · intro hf
    have : Locally Smooth f := by
      refine RingHom.locally_of_locally ?_ hf
      introv
      apply smooth_of_isStandardSmooth
    rwa [RingHom.locally_iff_of_localizationSpanTarget Smooth.respectsIso
      Smooth.ofLocalizationSpanTarget] at this

end RingHom
