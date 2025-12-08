import Mathlib.AlgebraicGeometry.Normalization.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Scheme

def Scheme.Hom.quasiFiniteLocus : Set X := { x : X | (f.stalkMap x).hom.QuasiFinite }

lemma Scheme.Hom.quasiFiniteAt_of_memQuasiFiniteLocus
    [LocallyOfFiniteType f] [IsAffineHom f]
    (x : X) (hx : x ∈ f.quasiFiniteLocus) (V : X.affineOpens) (U : Y.affineOpens)
    (hVU : V ≤ f ⁻¹ᵁ U.1) (hxV : x ∈ V.1) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    Algebra.QuasiFiniteAt Γ(Y, U) (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  letI := (f.appLE U V hVU).hom.toAlgebra
  have H : (Y.presheaf.germ U.1 _ (hVU hxV)).hom.QuasiFinite := by
    let := (Y.presheaf.germ U.1 _ (hVU hxV)).hom.toAlgebra
    have := U.2.isLocalization_stalk ⟨f x, (hVU hxV)⟩
    rw [← (Y.presheaf.germ U.1 _ (hVU hxV)).hom.algebraMap_toAlgebra,
      RingHom.quasiFinite_algebraMap]
    exact .of_isLocalization (U.2.primeIdealOf ⟨_, hVU hxV⟩).asIdeal.primeCompl
  let := (X.presheaf.germ V.1 x hxV).hom.toAlgebra
  have := V.2.isLocalization_stalk ⟨x, hxV⟩
  let e := IsLocalization.algEquiv (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk (⟨x, hxV⟩ : V.1)) (Localization.AtPrime (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal)
  rw [Algebra.QuasiFiniteAt, ← RingHom.quasiFinite_algebraMap]
  convert (RingHom.QuasiFinite.of_surjective (f := e.toRingHom) e.surjective).comp
    (hx.comp H)
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE hVU) _ hxV,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc, CommRingCat.hom_comp, ← RingHom.comp_assoc,
    IsScalarTower.algebraMap_eq Γ(Y, U) Γ(X, V)]
  congr 1
  exact e.toAlgHom.comp_algebraMap.symm

lemma Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization_of_isAffineHom
    [LocallyOfFiniteType f] [IsAffineHom f]
    (x : X) (hx : x ∈ f.quasiFiniteLocus) (U : Y.affineOpens) (hU : f x ∈ U.1) :
    ∃ r : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U),
      f.toNormalization x ∈ f.normalization.basicOpen r ∧
      IsIso (f.toNormalization ∣_ f.normalization.basicOpen r) := by
  let := (f.app U).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    RingHom.finiteType_algebraMap.mp (by simpa [← app_eq_appLE] using
      (LocallyOfFiniteType.finiteType_of_affine_subset (f := f) _ ⟨_, U.2.preimage f⟩ le_rfl))
  let q := (U.2.preimage f).isoSpec.hom ⟨x, hU⟩
  have : Algebra.QuasiFiniteAt Γ(Y, U) q.asIdeal := by
    convert f.quasiFiniteAt_of_memQuasiFiniteLocus x hx ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ U le_rfl hU
    simp [app_eq_appLE]
  have H := ZariskiMainProperty.of_finiteType (R := Γ(Y, U)) q.asIdeal
  obtain ⟨r, hrq, hr⟩ := H
  have := f.toNormalization
  let e : Γ(_, f.fromNormalization ⁻¹ᵁ U) ≅ (normalizationDiagram f).obj (.op U) :=
    (normalization f).presheaf.mapIso (eqToIso (by simp [f.fromNormalization_preimage])).op ≪≫
      (f.normalizationOpenCover.f U).appIso ⊤ ≪≫ Scheme.ΓSpecIso _
  have hfr : X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op r.1 =
      f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) (e.inv r) := by
    rw [Scheme.Hom.toNormalization_app_preimage]
    simp [- CommRingCat.hom_comp, ← ConcreteCategory.comp_apply, e]
    rfl
  refine ⟨e.inv r, ?_, ?_⟩
  · rw [← Scheme.Hom.mem_preimage, preimage_basicOpen, ← hfr, X.basicOpen_res_eq,
      ← (U.2.preimage f).fromSpec_image_basicOpen r.1]
    refine ⟨_, hrq, (?_ : ((U.2.preimage f).isoSpec.hom ≫ (U.2.preimage f).fromSpec) _ = _)⟩
    simp only [IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec, Opens.ι_apply]
  · have heq : f ⁻¹ᵁ U = f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U := by
      simp [← Hom.comp_preimage]
    have := (U.2.preimage f.fromNormalization).isLocalization_basicOpen (e.inv r)
    let e₁ : Localization.Away r ≃+* Γ(normalization f, (normalization f).basicOpen (e.inv r)) :=
      IsLocalization.ringEquivOfRingEquiv (M := .powers r) (T := .powers (e.inv r))
        _ _ e.symm.commRingCatIsoToRingEquiv (Submonoid.map_powers _ _)
    have hle : f.toNormalization ⁻¹ᵁ f.normalization.basicOpen (e.inv r) ≤
        f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U := by simpa using X.basicOpen_le _
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    have := ((U.2.preimage f.fromNormalization).preimage
        f.toNormalization).isLocalization_of_eq_basicOpen
      (f.toNormalization.app _ (e.inv r)) (homOfLE hle) (by simp)
    let e₂ : Localization.Away (Subalgebra.val _ r) ≃+*
        Γ(X, f.toNormalization ⁻¹ᵁ f.normalization.basicOpen (e.inv r)) :=
      IsLocalization.ringEquivOfRingEquiv (M := .powers (Subalgebra.val _ r))
        (T := .powers (f.toNormalization.app _ (e.inv r))) _ _ (X.presheaf.mapIso (eqToIso
          (by simp [← Hom.comp_preimage])).op).commRingCatIsoToRingEquiv (by
        rw [Submonoid.map_powers]
        congr 1)
    have : IsIso (f.toNormalization.app ((normalization f).basicOpen (e.inv r))) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      convert (e₂.bijective.comp hr).comp e₁.symm.bijective
      simp only [← RingEquiv.coe_toRingHom, ← RingHom.coe_comp]
      congr 1
      apply IsLocalization.ringHom_ext (M := .powers (e.inv r))
      ext x
      suffices (normalization f).presheaf.map (homOfLE
          ((normalization f).basicOpen_le (e.inv r))).op ≫ (toNormalization f).app _ =
          (e.hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom ≫
            X.presheaf.map (eqToHom congr(.op $heq)) ≫ X.presheaf.map (homOfLE hle).op) by
        simpa [e₁, IsLocalization.Away.map, e₂, -NatTrans.naturality] using congr($this x)
      simp [Scheme.Hom.toNormalization_app_preimage, e]
    have inst : IsAffine ((normalization f).basicOpen (e.inv r)) := (U.2.preimage _).basicOpen _
    refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).mpr
      ⟨((U.2.preimage _).basicOpen _).preimage _, ?_⟩
    simp only [app_eq_appLE, TopologicalSpace.Opens.map_top, morphismRestrict_appLE,
      Scheme.Opens.toScheme_presheaf_obj] at this ⊢
    convert this <;> simp

/--
**Zariski's main theorem** for affine morphisms.

Recall that any qcqs morphism `f : X ⟶ Y` factors through the relative normalization via
`f.toNormalization : X ⟶ f.normalization` (a dominant morphism) and
`f.fromNormalization : f.normalization ⟶ Y` (an integral morphism).

Let `f : X ⟶ Y` be an affine morphism locally of finite type.

then there exists `U : f.normalization.Opens`, such that
1. `f.toNormalization ∣_ U` is an isomorphism
2. `f.toNormalization ⁻¹ᵁ U` is the quasi-finite locus of `f`

The full version for non-affine morphisms is much harder.
-/
@[stacks 03GT]
lemma Scheme.Hom.exists_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsAffineHom f] :
    ∃ U : f.normalization.Opens, IsIso (f.toNormalization ∣_ U) ∧
      (f.toNormalization ⁻¹ᵁ U).1 = f.quasiFiniteLocus := by
  choose U hU using fun x ↦ TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top Y).ge (Set.mem_univ x))
  choose r hr hxr using fun x hx ↦
    f.exists_mem_and_isIso_morphismRestrict_toNormalization_of_isAffineHom x hx (U _) (hU _)
  let V (x : f.quasiFiniteLocus) := (normalization f).basicOpen (r x x.2)
  let 𝒰 := Opens.iSupOpenCover V
  have : IsIso (f.toNormalization ∣_ ⨆ x, V x) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
    refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
    have : Opens.ι _ ''ᵁ (𝒰.f x).opensRange = V x := by
      simp only [Opens.iSupOpenCover, 𝒰, ← opensRange_comp, homOfLE_ι, Opens.opensRange_ι]
    convert hxr x.1 x.2
  refine ⟨⨆ x : f.quasiFiniteLocus, V x, this, ?_⟩
  ext x
  suffices (∃ i : quasiFiniteLocus f, toNormalization f x ∈ V i) ↔ x ∈ quasiFiniteLocus f by
    simpa
  refine ⟨?_, fun h ↦ ⟨⟨x, h⟩, hr x h⟩⟩
  rintro ⟨y, hxVy⟩
  have hfVy : IsAffineOpen (toNormalization f ⁻¹ᵁ V y) :=
    (((U _).2.preimage  _).basicOpen _).preimage _
  have H : toNormalization f ⁻¹ᵁ V y ≤ f ⁻¹ᵁ ↑(U ((ConcreteCategory.hom f.base) y)) := by
    conv_rhs => enter [1]; rw [← f.toNormalization_fromNormalization]
    rw [Scheme.Hom.comp_preimage]
    exact (toNormalization f).preimage_mono ((normalization f).basicOpen_le _)
  have H' : f.fromNormalization.appLE (U (f y)) _ ((normalization f).basicOpen_le _) ≫
    f.toNormalization.app (V y) = f.appLE (U (f y)) (toNormalization f ⁻¹ᵁ V y) H := by
    simp only [app_eq_appLE]
    exact (appLE_comp_appLE _ _ _ _ _ _ _).trans (by simp)
  have : IsIso ((toNormalization f).app (V y)) := by
    have := (inferInstanceAs (IsIso ((toNormalization f ∣_ V y).appTop)))
    simp only [app_eq_appLE, TopologicalSpace.Opens.map_top, morphismRestrict_appLE,
      Scheme.Opens.toScheme_presheaf_obj] at this ⊢
    convert this <;> simp
  have : (f.appLE (U (f y)) (toNormalization f ⁻¹ᵁ V y) H).hom.QuasiFinite := by
    have : (f.appLE (U (f y)) (toNormalization f ⁻¹ᵁ V y) H).hom.FiniteType :=
      LocallyOfFiniteType.finiteType_of_affine_subset _ ⟨_, hfVy⟩ H
    rw [← H', CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_right_isIso] at this
    rw [← H', CommRingCat.hom_comp, RingHom.QuasiFinite.respectsIso.cancel_right_isIso]
    have inst := ((U (f y)).2.preimage f.fromNormalization).isLocalization_basicOpen
    exact RingHom.QuasiFinite.of_isIntegral_of_finiteType
      (IsIntegralHom.isIntegral_app f.fromNormalization _ (U (f y)).2) this (r y y.2) rfl
  have hxU : f x ∈ (U (f y)).1 := by
    convert show _ ∈ (U (f y)).1 from (normalization f).basicOpen_le _ hxVy
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization]
  refine .of_comp (g := (Y.presheaf.germ (U (f y)) _ hxU).hom) ?_
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE H) _ hxVy,
    app_eq_appLE, appLE_map_assoc, CommRingCat.hom_comp]
  refine .comp ?_ this
  have := hfVy.isLocalization_stalk ⟨x, hxVy⟩
  let := X.presheaf.algebra_section_stalk (U := toNormalization f ⁻¹ᵁ V y) ⟨x, hxVy⟩
  rw [← RingHom.algebraMap_toAlgebra (X.presheaf.germ _ _ _).hom, RingHom.quasiFinite_algebraMap]
  exact .of_isLocalization (hfVy.primeIdealOf ⟨x, hxVy⟩).asIdeal.primeCompl

end AlgebraicGeometry
