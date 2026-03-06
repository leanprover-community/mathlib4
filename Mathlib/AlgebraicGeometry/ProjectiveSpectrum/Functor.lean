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

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (f_le_map : ℬ₊ ≤ 𝒜₊.map f)

namespace ProjectiveSpectrum

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def comapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| f_le_map.trans <| map_le_of_le_comap _ le

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapFun f f_le_map
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

end ProjectiveSpectrum

namespace Proj

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f f_le_map ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨.comap f f_le_map y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isLocallyFraction_comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapStructureSheafFun f f_le_map U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f f_le_map p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f f_le_map) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
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
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (f_le_map : ℬ₊ ≤ 𝒜₊.map f)

/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| comap f f_le_map
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f f_le_map _ _ Set.Subset.rfl } }

lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (p.comap f f_le_map).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap f f_le_map).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f f_le_map).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (ProjectiveSpectrum.comap f f_le_map p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMap f f_le_map).hom.stalkMap p := by
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
  __ := (sheafedSpaceMap f f_le_map).hom
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (p.comap f f_le_map)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

end Proj

end universe_monomorphic

end AlgebraicGeometry
