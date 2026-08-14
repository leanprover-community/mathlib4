/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Functoriality of Proj -/

@[expose] public section

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : 𝒞₊ ≤ ℬ₊.map g)

namespace ProjectiveSpectrum

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def comapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| hf.trans <| map_le_of_le_comap _ le

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

end ProjectiveSpectrum

namespace Proj

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨.comap f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyFraction_comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapStructureSheafFun]

set_option backward.isDefEq.respectTransparency false in
/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨comapStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFun]
  map_zero' := by ext; simp [comapStructureSheafFun]
  map_add' x y := by ext; simp [comapStructureSheafFun]
  map_mul' x y := by ext; simp [comapStructureSheafFun]

end Proj

end universe_polymorphic

section universe_monomorphic

namespace Proj

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : 𝒞₊ ≤ ℬ₊.map g)

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| comap f hf
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f hf _ _ Set.Subset.rfl } }

lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (p.comap f hf).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (ProjectiveSpectrum.comap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  -- I sincerely apologise for your eyes.
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj`. -/
noncomputable def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (p.comap f hf)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A) :
    map f hf ⁻¹ᵁ basicOpen 𝒜 s = basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem ι_comp_map (s : A) : (basicOpen ℬ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜 s).ι := by simp

@[reassoc] lemma awayToSection_comp_appLE {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (map f hf) (basicOpen 𝒜 s) (basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]

/-- Given a graded ring hom `f : 𝒜 →+*ᵍ ℬ` satisfying the hypothesis `ℬ₊ ≤ 𝒜₊.map f`, we obtain
an affine open cover of `Proj ℬ` consisting of `D(f(s))` for `s ∈ A` positive degree. -/
@[simps! I₀ f] noncomputable def mapAffineOpenCover : (Proj ℬ).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜).I₀ ↦ f s.2) (fun s ↦ f.2 s.2.2)
    (fun s ↦ s.1.2) <| (toIdeal_le_toIdeal_iff.mpr hf).trans <|
    Ideal.map_le_of_le_comap <| (toIdeal_irrelevant_le _).mpr fun i hi x hx ↦
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem map_comp : map (g.comp f) (irrelevant_le_map_comp hf hg) = map g hg ≫ map f hf := by
  refine (mapAffineOpenCover _ <| irrelevant_le_map_comp hf hg).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map (g.comp f) _ s.1.2 _ s.2.2]
  simp [awayι_comp_map_assoc _ _ _ _ (map_mem f s.2.2), awayι_comp_map _ _ _ _ s.2.2]

set_option backward.isDefEq.respectTransparency false in
theorem map_id : map (.id 𝒜) (by simp) = 𝟙 (Proj 𝒜) := by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s ↦ ?_
  convert! awayι_comp_map (.id 𝒜) _ _ _ s.2.2 using 1
  simp

end Proj

end universe_monomorphic

end AlgebraicGeometry
