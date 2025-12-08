import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.RingTheory.ZariskiMain
import Mathlib.Tactic.DepRewrite
-- import Mathlib.CategoryTheory.EffectiveEpi.Comp
-- import Mathlib.CategoryTheory.ExtremalEpi
-- import Mathlib.Combinatorics.Quiver.ReflQuiver
-- import Mathlib.Order.BourbakiWitt

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open Scheme

variable (X) in
@[simps]
noncomputable def Scheme.AffineZariskiSite.cocone :
    Limits.Cocone (toOpensFunctor X ⋙ (X.presheaf).rightOp ⋙ Scheme.Spec) where
  pt := X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp

def PreservesLocalization (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F) : Prop :=
  ∀ (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
    letI := (F.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
    IsLocalization.Away (α.app (.op U) f) (F.obj (.op (U.basicOpen f)))

lemma PreservesLocalization.isLocallyDirected (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : PreservesLocalization F α) :
    ((F.rightOp ⋙ Scheme.Spec) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  rintro ⟨U, hU⟩ ⟨V, hV⟩ W ⟨⟨a, (rfl : _ = U)⟩⟩ ⟨⟨b, (rfl : _ = V)⟩⟩ (xi xj : PrimeSpectrum _)
    (e : xi.comap (F.map (homOfLE (W.basicOpen_le a)).op).hom =
      xj.comap (F.map (homOfLE (W.basicOpen_le b)).op).hom)
  let x := xi.comap (F.map (homOfLE (W.basicOpen_le a)).op).hom
  have := H W
  let (c : _) := (F.map (homOfLE (W.basicOpen_le c)).op).hom.toAlgebra
  have hx : x ∈ PrimeSpectrum.basicOpen (α.app (.op W) (a * b)) := by
    rw [map_mul, PrimeSpectrum.basicOpen_mul]
    exact ⟨(PrimeSpectrum.localization_away_comap_range _ (α.app (.op W) a)).le ⟨_, rfl⟩,
      (PrimeSpectrum.localization_away_comap_range _ (α.app (.op W) b)).le ⟨_, e.symm⟩⟩
  obtain ⟨y, hy⟩ :=
    (PrimeSpectrum.localization_away_comap_range (F.obj (.op (W.basicOpen (a * b)))) _).ge hx
  refine ⟨W.basicOpen (a * b), ⟨(X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom b, ?_⟩,
    ⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a, ?_⟩, y, ?_, ?_⟩
  · simp [AffineZariskiSite.toOpens, AffineZariskiSite.basicOpen, basicOpen_mul]
  · simp [AffineZariskiSite.toOpens, AffineZariskiSite.basicOpen, basicOpen_mul, inf_comm]
  · refine PrimeSpectrum.localization_comap_injective (F.obj (.op (W.basicOpen a)))
      (.powers <| α.app (.op W) a) ?_
    change (Spec.map (F.map _) ≫ Spec.map (F.map _)) _ = _
    rw [← Spec.map_comp, ← F.map_comp]
    exact hy
  · refine PrimeSpectrum.localization_comap_injective (F.obj (.op (W.basicOpen b)))
      (.powers <| α.app (.op W) b) ?_
    change (Spec.map (F.map _) ≫ Spec.map (F.map _)) _ = _
    rw [← Spec.map_comp, ← F.map_comp]
    exact hy.trans e

lemma PreservesLocalization.isOpenImmersion (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : PreservesLocalization F α) :
    ∀ ⦃U V⦄ (f : U ⟶ V), IsOpenImmersion ((F.rightOp ⋙ Scheme.Spec).map f) := by
  rintro ⟨U, _⟩ V ⟨⟨a, (rfl : _ = U)⟩⟩
  have := H V a
  let := (F.map (homOfLE (V.basicOpen_le a)).op).hom.toAlgebra
  exact IsOpenImmersion.of_isLocalization (α.app (.op V) a) (S := F.obj (.op (V.basicOpen a)))

lemma PreservesLocalization.opensRange_map (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : PreservesLocalization F α) {U : X.AffineZariskiSite} (r : Γ(X, U.1)) :
    letI := H.isOpenImmersion _ _ (homOfLE (U.basicOpen_le r))
    ((F.rightOp ⋙ Scheme.Spec).map (homOfLE (U.basicOpen_le r))).opensRange =
      PrimeSpectrum.basicOpen (α.app (.op U) r) := by
  have := H U r
  let := (F.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  apply TopologicalSpace.Opens.coe_inj.mp ?_
  refine PrimeSpectrum.localization_away_comap_range (F.obj (.op <| U.basicOpen r))
    (α.app (.op U) r)

attribute [local simp] IsAffineOpen.isoSpec_hom Scheme.AffineZariskiSite.toOpensFunctor
  Scheme.AffineZariskiSite.basicOpen IsAffineOpen.basicOpen in
attribute [local simp← ] Hom.comp_apply in
attribute [-simp] Hom.comp_base in
lemma PreservesLocalization.colimitDesc_preimage (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : PreservesLocalization F α) (U : X.AffineZariskiSite) :
    haveI := H.isLocallyDirected
    haveI := H.isOpenImmersion
    (colimit.desc (F.rightOp ⋙ Scheme.Spec) ⟨X, Functor.whiskerRight α.rightOp _ ≫
      (Scheme.AffineZariskiSite.cocone X).ι⟩) ⁻¹ᵁ U.1 =
    (colimit.ι (F.rightOp ⋙ Scheme.Spec) U).opensRange := by
  haveI := H.isLocallyDirected
  haveI := H.isOpenImmersion
  let G := F.rightOp ⋙ Scheme.Spec
  let β : G ⟶ (Functor.const X.AffineZariskiSite).obj X :=
    Functor.whiskerRight α.rightOp _ ≫ (Scheme.AffineZariskiSite.cocone X).ι
  change (colimit.desc G ⟨X, β⟩) ⁻¹ᵁ U.1 = (colimit.ι G U).opensRange
  apply le_antisymm
  · rintro x hx
    obtain ⟨V, x, rfl⟩ := (IsLocallyDirected.openCover G).exists_eq x
    dsimp at V x hx
    replace hx : β.app V x ∈ U.1 := by simpa using hx
    have hx' : β.app V x ∈ V.1 :=
      V.2.opensRange_fromSpec.le ⟨Spec.map (α.app (.op V)) x, by simp [β, G]⟩
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ ⟨hx, hx'⟩
    obtain ⟨y, hy⟩ : x ∈ (G.map (homOfLE (V.basicOpen_le g))).opensRange := by
      suffices (G.obj V).basicOpen ((β.app V).app V.1 g) ≤
          (G.obj V).basicOpen ((ΓSpecIso (F.obj (.op V))).inv (α.app (.op V) g)) by
        rw [H.opensRange_map, ← basicOpen_eq_of_affine]
        rw [← preimage_basicOpen] at this
        exact this (show x ∈ (β.app V) ⁻¹ᵁ X.basicOpen g by rwa [← e])
      refine Eq.trans_le ?_ (((G.obj V).basicOpen_res (V := β.app V ⁻¹ᵁ V.1) _
        (homOfLE le_top).op).trans_le inf_le_right)
      congr 1
      change _ = (α.app (.op V) ≫ (ΓSpecIso (F.obj (.op V))).inv ≫
        (G.obj V).presheaf.map (homOfLE le_top).op) g
      congr 2
      simp [β, G, homOfLE_leOfHom, ΓSpecIso_inv_naturality_assoc,
        IsAffineOpen.fromSpec_app_of_le V.2 V.1 le_rfl]
    refine ⟨_, (Scheme.IsLocallyDirected.ι_eq_ι_iff _).mpr
      ⟨.basicOpen V g, ⟨f, e⟩, ⟨g, rfl⟩, y, rfl, hy⟩⟩
  · rintro _ ⟨x, rfl⟩
    simpa using U.2.opensRange_fromSpec.le ⟨Spec.map (α.app (.op U)) x, by simp [β, G]⟩

noncomputable
def Scheme.Hom.normalizationDiagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U :=
    letI := (f.app U.unop).hom.toAlgebra
    .of (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop))
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx ↦ by
      obtain ⟨U, rfl⟩ := Opposite.op_surjective U
      obtain ⟨V, rfl⟩ := Opposite.op_surjective V
      algebraize [(f.app U).hom, (f.app V).hom, (Y.presheaf.map i).hom,
        (X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom,
        (f.appLE V (f ⁻¹ᵁ U) (f.preimage_mono i.unop.le)).hom]
      have : IsScalarTower Γ(Y, V) Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' <| by
        simp [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp]; rfl
      have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
      exact (hx.map (IsScalarTower.toAlgHom Γ(Y, V) _ Γ(X, f ⁻¹ᵁ U))).tower_top)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

def Scheme.Hom.normalizationDiagramMap : Y.presheaf ⟶ f.normalizationDiagram where
    app U :=
      letI := (f.app U.unop).hom.toAlgebra
      CommRingCat.ofHom (algebraMap Γ(Y, U.unop) (integralClosure Γ(Y, U.unop) Γ(X, f ⁻¹ᵁ U.unop)))
    naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

lemma Scheme.Hom.isCompact_preimage [QuasiCompact f] {U : Opens Y}
    (hU : IsCompact (U : Set Y)) : IsCompact (f ⁻¹ᵁ U : Set X) :=
  f.isSpectralMap.2 U.2 hU

lemma Scheme.Hom.isQuasiSeparated_preimage [QuasiSeparated f] {U : Opens Y}
    (hU : IsQuasiSeparated (U : Set Y)) : IsQuasiSeparated (f ⁻¹ᵁ U : Set X) := by
  have : QuasiSeparatedSpace U := (isQuasiSeparated_iff_quasiSeparatedSpace _ U.2).mp hU
  exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (f ⁻¹ᵁ U).2).mpr
    (quasiSeparatedSpace_of_quasiSeparated (f ∣_ U))

variable [QuasiCompact f] [QuasiSeparated f]

protected lemma IsLocalization.Away.integralClosure
    {R S Rf Sf : Type*} [CommRing R] [CommRing S] [CommRing Rf]
    [CommRing Sf] [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
    [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (f : R) [IsLocalization.Away f Rf] [IsLocalization.Away (algebraMap R S f) Sf]
    [Algebra (integralClosure R S) (integralClosure Rf Sf)]
    [IsScalarTower (integralClosure R S) (integralClosure Rf Sf) Sf]
    [IsScalarTower R (integralClosure R S) (integralClosure Rf Sf)] :
    IsLocalization.Away (algebraMap R (integralClosure R S) f) (integralClosure Rf Sf) := by
  have : IsScalarTower R ↥(integralClosure Rf Sf) Sf := .to₁₃₄ _ Rf _ _
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · convert (IsLocalization.Away.algebraMap_isUnit (S := Rf) f).map
      (algebraMap Rf (integralClosure Rf Sf))
    simp [← IsScalarTower.algebraMap_apply]
  · rintro ⟨s, hs⟩
    obtain ⟨⟨x, _, n₁, rfl⟩, e⟩ := IsLocalization.surj (.powers (algebraMap R S f)) s
    simp only [map_pow, ← IsScalarTower.algebraMap_apply] at e
    obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (.powers f) _ hs
    simp only [Submonoid.smul_def, Algebra.smul_def, map_pow] at hn₂
    obtain ⟨_, ⟨n₃, rfl⟩, hn₃⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map
      (Sₘ := Sf) (.powers f) (x := f ^ n₂ • x) (by
        simp only [Algebra.smul_def, map_pow, map_mul, ← IsScalarTower.algebraMap_apply, ← e,
          ← mul_assoc]
        exact hn₂.mul (.pow (.algebraMap (Algebra.IsIntegral.isIntegral f)) _))
    refine ⟨n₁ + n₂ + n₃, ⟨_, hn₃⟩, ?_⟩
    · apply (FaithfulSMul.algebraMap_injective (integralClosure Rf Sf) Sf)
      simp [← IsScalarTower.algebraMap_apply, e, ← mul_assoc, pow_add, Algebra.smul_def]
      ring
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ e
    have := congr(algebraMap _ Sf $e)
    have : algebraMap S Sf a = algebraMap S Sf b := by
      simpa only [← IsScalarTower.algebraMap_apply] using this
    obtain ⟨⟨_, n, ⟨⟩⟩, hn⟩ := (IsLocalization.eq_iff_exists (.powers (algebraMap R S f)) _).mp this
    refine ⟨n, FaithfulSMul.algebraMap_injective (integralClosure R S) S ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply]

lemma Scheme.Hom.preservesLocalization_normalizationDiagramMap :
    PreservesLocalization _
      ((AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft f.normalizationDiagramMap) := by
  intro U r
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.app (U.basicOpen r).1).hom.toAlgebra
  let : Algebra (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) :=
    ((normalizationDiagram f).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    U.2.isLocalization_basicOpen _
  have : IsLocalization.Away ((algebraMap ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ U.1)) r)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  change IsLocalization.Away ((algebraMap Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) r)
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
  letI : Algebra ↑Γ(Y, U.1) ↑Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.appLE _ _ (f.preimage_mono (Y.basicOpen_le _))).hom.toAlgebra
  have : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    .of_algebraMap_eq' <| by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.map_appLE, AffineZariskiSite.basicOpen]
  have : IsScalarTower (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r))
    Γ(X, f ⁻¹ᵁ Y.basicOpen r) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
    (integralClosure Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := .of_algebraMap_eq' rfl
  exact IsLocalization.Away.integralClosure r

instance :
    ((((AffineZariskiSite.toOpensFunctor Y).op ⋙ f.normalizationDiagram).rightOp ⋙ Scheme.Spec) ⋙
      Scheme.forget).IsLocallyDirected :=
  f.preservesLocalization_normalizationDiagramMap.isLocallyDirected

instance {U V} (i : U ⟶ V) :
    IsOpenImmersion (((((AffineZariskiSite.toOpensFunctor Y).op ⋙
      f.normalizationDiagram).rightOp ⋙ Scheme.Spec)).map i) :=
  f.preservesLocalization_normalizationDiagramMap.isOpenImmersion _ _ _

noncomputable
def Scheme.Hom.normalization : Scheme :=
  colimit (((AffineZariskiSite.toOpensFunctor Y).op ⋙ f.normalizationDiagram).rightOp ⋙ Scheme.Spec)

noncomputable
def Scheme.Hom.normalizationOpenCover : f.normalization.OpenCover :=
  Scheme.IsLocallyDirected.openCover _

lemma Scheme.preservesLocalization_toOpensFunctor :
    PreservesLocalization ((AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf) (𝟙 _) :=
  fun U f ↦ U.2.isLocalization_basicOpen f

variable (X) in
@[simps]
abbrev Scheme.AffineZariskiSite.directedCover : X.OpenCover where
  I₀ := X.AffineZariskiSite
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨U, ⟨x, hxU⟩, rfl⟩

noncomputable
instance : (Scheme.AffineZariskiSite.directedCover X).LocallyDirected where
  trans f := X.homOfLE (((Scheme.AffineZariskiSite.toOpensFunctor _).map f).le)
  trans_id := by cat_disch
  trans_comp := by cat_disch
  w := by cat_disch
  directed {U V} x := by
    let a := (pullback.fst _ _ ≫ U.1.ι) x
    have haU : a ∈ U.1 := (pullback.fst U.1.ι V.1.ι x).2
    have haV : a ∈ V.1 := by unfold a; rw [pullback.condition]; exact (pullback.snd U.1.ι V.1.ι x).2
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ ⟨haU, haV⟩
    refine ⟨U.basicOpen f, homOfLE (U.basicOpen_le f), eqToHom (Subtype.ext (by exact e)) ≫
      homOfLE (V.basicOpen_le g), ⟨a, hxf⟩, ?_⟩
    apply (pullback.fst _ _ ≫ U.1.ι).isOpenEmbedding.injective
    dsimp
    change (pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ U.1.ι) _ = _
    simp only [pullback.lift_fst_assoc, homOfLE_ι, Opens.ι_apply]
    rfl
  property_trans := inferInstance

variable (X) in
attribute [local simp] IsAffineOpen.isoSpec_hom Scheme.AffineZariskiSite.toOpensFunctor
  Scheme.AffineZariskiSite.basicOpen IsAffineOpen.basicOpen in
attribute [local simp← ] Hom.comp_apply in
attribute [-simp] Hom.comp_base in
noncomputable
def Scheme.AffineZariskiSite.isColimitCocone :
    IsColimit (cocone X) :=
  letI := X.preservesLocalization_toOpensFunctor.isLocallyDirected
  letI {U V : X.AffineZariskiSite} (i : U ⟶ V) :=
    X.preservesLocalization_toOpensFunctor.isOpenImmersion _ _ i
  let F := ((AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf).rightOp ⋙ Scheme.Spec
  haveI : IsIso ((colimit.isColimit F).desc (cocone X)) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X))).mpr fun U ↦ ?_
    change IsIso (pullback.snd (colimit.desc F (cocone X)) U.1.ι)
    let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (colimit.desc F (cocone X)) U.1.ι)
      (U.2.isoSpec.hom ≫ colimit.ι F U) <| by
      rw [Pullback.range_fst, Opens.range_ι, ← Hom.coe_opensRange, Hom.opensRange_comp_of_isIso,
        ← Scheme.Hom.coe_preimage]
      have := X.preservesLocalization_toOpensFunctor.colimitDesc_preimage
      convert congr($(this U).1) <;> simp
    convert inferInstanceAs (IsIso e.hom)
    rw [← cancel_mono U.1.ι, ← Iso.inv_comp_eq]
    simp [e, ← pullback.condition]
  .ofPointIso (colimit.isColimit F)

noncomputable
def Scheme.Hom.toNormalization : X ⟶ f.normalization :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover Y).pullback₁ f)
    (fun U ↦ letI := (f.app U.1).hom.toAlgebra
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      |>.val.toRingHom) ≫ f.normalizationOpenCover.f U) fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((Scheme.AffineZariskiSite.directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (AffineZariskiSite.toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp [normalizationOpenCover]
  rw [← colimit.w (((AffineZariskiSite.toOpensFunctor Y).op ⋙
    normalizationDiagram f).rightOp ⋙ Scheme.Spec) i]
  dsimp
  rw [← Spec.map_comp_assoc]
  rfl

@[reassoc]
lemma Scheme.Hom.ι_toNormalization (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    (f ⁻¹ᵁ U.1).ι ≫ f.toNormalization = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom <| integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) |>.val.toRingHom) ≫
        f.normalizationOpenCover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((Scheme.AffineZariskiSite.directedCover Y).pullback₁ f).f U ≫ f.toNormalization
  · congr 1; simp
  delta Scheme.Hom.toNormalization
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

noncomputable
def Scheme.Hom.fromNormalization : f.normalization ⟶ Y :=
  colimit.desc _
  { pt := _
    ι := Functor.whiskerRight ((AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft
      f.normalizationDiagramMap).rightOp Scheme.Spec ≫ (Scheme.AffineZariskiSite.cocone Y).ι }

@[reassoc]
lemma Scheme.Hom.ι_fromNormalization (U : Y.affineOpens) :
    f.normalizationOpenCover.f U ≫ f.fromNormalization =
      Spec.map (f.normalizationDiagramMap.app (.op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

lemma Scheme.Hom.fromNormalization_preimage (U : Y.affineOpens) :
    f.fromNormalization ⁻¹ᵁ U = (f.normalizationOpenCover.f U).opensRange :=
  f.preservesLocalization_normalizationDiagramMap.colimitDesc_preimage _ _ _

@[reassoc (attr := simp)]
lemma Scheme.Hom.toNormalization_fromNormalization :
    f.toNormalization ≫ f.fromNormalization = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (f.ι_toNormalization_assoc _ _).trans ?_
  rw [f.ι_fromNormalization, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

instance : IsIntegralHom f.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (f.fromNormalization ⁻¹ᵁ U).ι (f.normalizationOpenCover.f U)
      (by simpa using congr($(f.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsIntegralHom _ U.2.isoSpec.hom]
  have : (f.normalizationDiagramMap.app (.op U)).hom.IsIntegral := by
    letI := (f.app U).hom.toAlgebra
    change (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  convert IsIntegralHom.SpecMap_iff.mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

lemma Scheme.Hom.toNormalization_app_preimage
    (U : Y.affineOpens) [QuasiCompact f] [QuasiSeparated f] :
    let := (f.app U.1).hom.toAlgebra
    f.toNormalization.app (f.fromNormalization ⁻¹ᵁ ↑U) =
      f.normalization.presheaf.map (eqToHom (by simp [Scheme.Hom.fromNormalization_preimage])).op ≫
      ((f.normalizationOpenCover.f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (integralClosure ↑Γ(Y, ↑U) ↑Γ(X, f ⁻¹ᵁ ↑U)).val.toRingHom ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  have H : f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ f.toNormalization) ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert congr($(Scheme.Hom.congr_app (f.ι_toNormalization U) (f.fromNormalization ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H).op) using 1
  · simp [Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← Functor.map_inv, inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

instance [IsIntegralHom f] : IsIso f.toNormalization := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    f.normalizationOpenCover).mpr fun U ↦ ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pullbackFst, ← f.fromNormalization_preimage, ← Scheme.Hom.comp_preimage])
  rw [← MorphismProperty.cancel_left_of_respectsIso (.isomorphisms _)
    (e ≪≫ (U.2.preimage f).isoSpec).inv]
  letI := (f.app U.1).hom.toAlgebra
  convert_to IsIso (Spec.map (CommRingCat.ofHom
      (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom))
  · rw [← cancel_mono (f.normalizationOpenCover.f U), ← cancel_epi (U.2.preimage f).isoSpec.hom]
    simp [e, -Iso.cancel_iso_hom_left, IsAffineOpen.isoSpec_hom,
      Hom.ι_toNormalization]
  have : integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) = ⊤ := by
    rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
    exact IsIntegralHom.isIntegral_app _ _ U.2
  rw [this]
  exact inferInstanceAs (IsIso (Scheme.Spec.mapIso (Subalgebra.topEquiv
    (R := Γ(Y, U.1)) (A := ↑Γ(X, f ⁻¹ᵁ U.1))).toCommRingCatIso.op).hom)

instance [IsAffineHom f] : IsAffineHom f.toNormalization := by
  have (i : _) : IsAffine ((Hom.normalizationOpenCover f).X i) := by
    dsimp [Hom.normalizationOpenCover]; infer_instance
  refine (HasAffineProperty.iff_of_openCover (P := @IsAffineHom)
    f.normalizationOpenCover).mpr fun U ↦ ?_
  let e := IsOpenImmersion.isoOfRangeEq (pullback.fst f.toNormalization
    (f.normalizationOpenCover.f U)) (f ⁻¹ᵁ U.1).ι (by simp [← Hom.coe_opensRange,
      Hom.opensRange_pullbackFst, ← f.fromNormalization_preimage, ← Scheme.Hom.comp_preimage])
  have : IsAffine (f ⁻¹ᵁ U.1) := U.2.preimage f
  exact isAffine_of_isAffineHom e.hom

end AlgebraicGeometry
