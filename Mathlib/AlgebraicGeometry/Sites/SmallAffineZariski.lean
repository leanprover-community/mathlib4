/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!

# The small affine Zariski site

`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Every presieve on `U` is then given by a `Set Γ(X, U)` (`presieveOfSections_surjective`), and
we endow `X.AffineZariskiSite` with `grothendieckTopology X`, such that `s : Set Γ(X, U)` is
a cover if and only if `Ideal.span s = ⊤` (`generate_presieveOfSections_mem_grothendieckTopology`).

This is a dense subsite of `X.Opens` (with respect to `Opens.grothendieckTopology X`) via the
inclusion functor `toOpensFunctor X`,
which gives an equivalence of categories of sheaves (`sheafEquiv`).

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.
-/
def Scheme.AffineZariskiSite (X : Scheme.{u}) : Type u := { U : X.Opens // IsAffineOpen U }

namespace Scheme.AffineZariskiSite

/-- The inclusion from `X.AffineZariskiSite` to `X.Opens`. -/
abbrev toOpens (U : X.AffineZariskiSite) : X.Opens := U.1

instance : Preorder X.AffineZariskiSite where
  le U V := ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact hW.basicOpen_basicOpen_is_basicOpen g f

lemma toOpens_mono :
    Monotone (toOpens (X := X)) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨f, rfl⟩
  exact X.basicOpen_le _

lemma toOpens_injective : Function.Injective (toOpens (X := X)) := Subtype.val_injective

instance : PartialOrder X.AffineZariskiSite where
  le_antisymm _ _ hUV hVU := Subtype.ext ((toOpens_mono hUV).antisymm (toOpens_mono hVU))

/-- The basic open set of a section, as an element of `AffineZariskiSite`. -/
@[simps] def basicOpen (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : X.AffineZariskiSite :=
  ⟨X.basicOpen f, U.2.basicOpen f⟩

lemma basicOpen_le (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f ≤ U :=
  ⟨f, rfl⟩

variable (X) in
/-- The inclusion functor from `X.AffineZariskiSite` to `X.Opens`. -/
@[simps! obj]
def toOpensFunctor : X.AffineZariskiSite ⥤ X.Opens := toOpens_mono.functor

instance : (toOpensFunctor X).Faithful where

variable (X) in
/-- The forgetful functor from `X.AffineZariskiSite` to `Scheme` is isomorphic to `Spec Γ(X, -)`. -/
@[simps! hom_app inv_app]
def restrictIsoSpec : toOpensFunctor X ⋙ X.restrictFunctor ⋙ Over.forget _ ≅
    toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun U ↦ U.2.isoSpec)
    fun _ ↦ (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map ..).symm

/-- An open immersion covariantly induces a functor between `AffineZariskiSite`. -/
@[simps] def image [IsOpenImmersion f] : X.AffineZariskiSite ⥤ Y.AffineZariskiSite where
  obj U := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  map {U V} f := homOfLE <| by obtain ⟨r, hr⟩ := f; exact ⟨(f.appIso V.1).inv r,
    by simp_all [toOpens, ← hr, image_basicOpen]⟩

section GrothendieckTopology

instance : (toOpensFunctor X).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V h x hx
    obtain ⟨f, hfU, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩ (h.le hx)
    exact ⟨X.basicOpen f, homOfLE hfU, ⟨V.basicOpen f,
      ⟨_, (X.basicOpen_res f h.op).trans (inf_eq_right.mpr hfU)⟩, 𝟙 _,
      ⟨⟨f, rfl⟩, rfl⟩, rfl⟩, hxf⟩

instance : (toOpensFunctor X).IsCoverDense (Opens.grothendieckTopology X) where
  is_cover := by
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

variable (X) in
/-- The Grothendieck topology on `X.AffineZariskiSite` induced from the topology on `X.Opens`.
Also see `mem_grothendieckTopology_iff_sectionsOfPresieve`. -/
def grothendieckTopology : GrothendieckTopology X.AffineZariskiSite :=
  (toOpensFunctor X).inducedTopology (Opens.grothendieckTopology X)

lemma mem_grothendieckTopology {U : X.AffineZariskiSite} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔
      ∀ x ∈ U.toOpens, ∃ (V : _) (f : V ⟶ U), S.arrows f ∧ x ∈ V.toOpens := by
  apply forall₂_congr fun x hxU ↦ ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, h.le hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨W.toOpens, homOfLE (toOpens_mono g.le), ⟨W, g, 𝟙 _, hg, rfl⟩, hxW⟩

instance : (toOpensFunctor X).IsDenseSubsite
    (grothendieckTopology X) (Opens.grothendieckTopology X) where
  functorPushforward_mem_iff := Iff.rfl

/-- The presieve associated to a set of sections.
This is a surjection, see `presieveOfSections_surjective`. -/
def presieveOfSections (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) : Presieve U :=
  fun V _ ↦ ∃ f ∈ s, X.basicOpen f = V.toOpens

/-- The set of sections associated to a presieve. -/
def sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) : Set Γ(X, U.toOpens) :=
  { f | P (homOfLE (U.basicOpen_le f)) }

lemma presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) :
    presieveOfSections U (sectionsOfPresieve P) = P := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ ↦ eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨_, H, rfl⟩
    exact H
  · intro H
    obtain rfl : _ = V := hf
    exact ⟨_, H, rfl⟩

lemma presieveOfSections_surjective {U : X.AffineZariskiSite} :
    Function.Surjective (presieveOfSections U) :=
  fun _ ↦ ⟨_, presieveOfSections_sectionsOfPresieve _⟩

lemma presieveOfSections_eq_ofArrows (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) :
    presieveOfSections U s = .ofArrows _ (fun i : s ↦ homOfLE (U.basicOpen_le i.1)) := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ ↦ eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨f, hfs, rfl⟩
    exact .mk (ι := s) ⟨f, hfs⟩
  · rintro ⟨⟨f, hfs⟩⟩
    exact ⟨f, hfs, rfl⟩

lemma generate_presieveOfSections
    {U V : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} {f : V ⟶ U} :
    Sieve.generate (presieveOfSections U s) f ↔ ∃ f ∈ s, ∃ g, X.basicOpen (f * g) = V.toOpens := by
  obtain ⟨V, hV⟩ := V
  constructor
  · rintro ⟨⟨W, hW⟩, ⟨f₁, hf₁⟩, -, ⟨f₂, hf₂s, rfl⟩, rfl⟩
    subst hf₁
    obtain ⟨f₃, hf₃⟩ := U.2.basicOpen_basicOpen_is_basicOpen f₂ f₁
    refine ⟨f₂, hf₂s, f₃, ?_⟩
    rw [X.basicOpen_mul, hf₃, inf_eq_right]
    exact X.basicOpen_le _
  · rintro ⟨f₁, hf₁s, f₂, rfl⟩
    refine ⟨U.basicOpen f₁, ⟨f₂ |_ _, ?_⟩, ⟨f₁, rfl⟩, ⟨f₁, hf₁s, rfl⟩, rfl⟩
    exact (X.basicOpen_res _ _).trans (X.basicOpen_mul _ _).symm

lemma generate_presieveOfSections_mem_grothendieckTopology
    {U : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} :
    Sieve.generate (presieveOfSections U s) ∈ grothendieckTopology X U ↔ Ideal.span s = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff, mem_grothendieckTopology, SetLike.le_def]
  refine forall₂_congr fun x hx ↦ ?_
  simp only [exists_and_left, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.carrier_eq_coe, Set.iUnion_coe_set, TopologicalSpace.Opens.mem_mk,
    Set.mem_iUnion, SetLike.mem_coe, exists_prop, generate_presieveOfSections]
  constructor
  · simp only [basicOpen_mul]
    rintro ⟨⟨V, hV⟩, ⟨f, hfs, g, rfl⟩, -, hxV⟩
    exact ⟨f, hfs, hxV.1⟩
  · rintro ⟨f, hfs, hxf⟩
    refine ⟨U.basicOpen _, ⟨f, hfs, 1, rfl⟩, ⟨_, rfl⟩, by simpa using hxf⟩

lemma mem_grothendieckTopology_iff_sectionsOfPresieve
    {U : X.AffineZariskiSite} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔ Ideal.span (sectionsOfPresieve S.1) = ⊤ := by
  rw [← generate_presieveOfSections_mem_grothendieckTopology, presieveOfSections_sectionsOfPresieve,
    Sieve.generate_sieve]

variable {A} [Category* A]
variable [∀ (U : X.Opensᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow U (toOpensFunctor X).op) A]

/-- The category of sheaves on `X.AffineZariskiSite` is equivalent to the categories of sheaves
over `X`. -/
abbrev sheafEquiv : Sheaf (grothendieckTopology X) A ≌ TopCat.Sheaf A X :=
    (toOpensFunctor X).sheafInducedTopologyEquivOfIsCoverDense _ _

end GrothendieckTopology

variable (X) in
/-- The directed cover of a scheme indexed by `X.AffineZariskiSite`.
Note the related `Scheme.directedAffineCover`, which has the same (defeq) cover but a different
category instance on the indices. -/
@[simps] abbrev directedCover : X.OpenCover where
  I₀ := X.AffineZariskiSite
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨U, ⟨x, hxU⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (Scheme.AffineZariskiSite.directedCover X).LocallyDirected where
  trans f := X.homOfLE (((Scheme.AffineZariskiSite.toOpensFunctor _).map f).le)
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

section PreservesLocalization

/-!
## "Quasi-coherent `𝒪ₓ`-algebras"

A presheaf `F` of rings on `X.AffineZariskiSite` with a structural morphism `α : 𝒪ₓ ⟶ F`
is said to be `Coequifibered` if `F(D(f)) = F(U)[1/f]`
for every open `U` and any section `f : Γ(X, U)`.
(See `coequifibered_iff_forall_isLocalizationAway`)

Under this condition we can construct a family of gluing data (See `relativeGluingData`) and glue
`F` into a scheme over `X` via `(relativeGluingData _).glued`,
Also see the relative gluing API in `Mathlib/AlgebraicGeometry/RelativeGluing.lean`.

This is closely related to the notion of quasi-coherent `𝒪ₓ`-algebras, and we shall link them
together once the theory of quasi-coherent `𝒪ₓ`-algebras are developed.
-/

variable (X) in
/-- `X` is the colimit of its affine opens. See `isColimit_cocone` below. -/
@[simps] noncomputable def cocone :
    Limits.Cocone (toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec) where
  pt := X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp

set_option backward.isDefEq.respectTransparency false in
lemma coequifibered_iff_forall_isLocalizationAway {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} :
    α.Coequifibered ↔ ∀ (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
      letI := (F.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
      IsLocalization.Away (α.app (.op U) f) (F.obj (.op (U.basicOpen f))) := by
  trans ∀ (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
    IsPushout (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)
      (α.app _) (α.app (.op (U.basicOpen f))) (F.map (homOfLE (U.basicOpen_le f)).op)
  · refine ⟨fun H U f ↦ H (homOfLE (U.basicOpen_le f)).op, fun H ⟨V⟩ ⟨U⟩ ⟨f, hf⟩ ↦ ?_⟩
    obtain rfl : V.basicOpen f = U := Subtype.ext hf
    exact H V f
  refine forall₂_congr fun U f ↦ ?_
  set αU : Γ(X, U.toOpens) ⟶ F.obj (.op U) := α.app (.op U)
  set αUf : Γ(X, X.basicOpen f) ⟶ F.obj (.op (U.basicOpen f)) := α.app (.op (U.basicOpen f))
  algebraize [(X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom, αU.hom, αUf.hom,
    (F.map (U.basicOpen_le f).hom.op).hom, (F.map (U.basicOpen_le f).hom.op).hom.comp αU.hom]
  have : IsScalarTower Γ(X, U.toOpens) Γ(X, X.basicOpen f) (F.obj (.op (U.basicOpen f))) :=
    .of_algebraMap_eq' congr($(α.naturality (U.basicOpen_le f).hom.op).hom).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen _
  refine (CommRingCat.isPushout_iff_isPushout ..).trans ?_
  rw [Algebra.IsPushout.comm]
  refine (Algebra.isLocalization_iff_isPushout (.powers f) Γ(X, X.basicOpen f)).symm.trans ?_
  simp [RingHom.algebraMap_toAlgebra]

@[deprecated (since := "2026-02-01")] alias PreservesLocalization := NatTrans.Coequifibered

/-- The relative gluing data associated to a quasi-coherent `𝒪ₓ` algebra. -/
def relativeGluingData {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
    (H : α.Coequifibered) :
    (AffineZariskiSite.directedCover X).RelativeGluingData where
  functor := F.rightOp ⋙ Scheme.Spec
  natTrans := Functor.whiskerRight α.rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := (H.rightOp.whiskerRight _).comp (.of_isIso _)

@[deprecated "By `inferInstance`." (since := "2026-02-01")]
lemma PreservesLocalization.isLocallyDirected (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) :
    ((F.rightOp ⋙ Scheme.Spec) ⋙ Scheme.forget).IsLocallyDirected :=
  (relativeGluingData H).instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

@[deprecated "By `inferInstance`." (since := "2026-02-01")]
lemma PreservesLocalization.isOpenImmersion (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) :
    ∀ ⦃U V⦄ (f : U ⟶ V), IsOpenImmersion ((F.rightOp ⋙ Scheme.Spec).map f) := by
  exact fun U V ↦ (relativeGluingData H).instIsOpenImmersionMapI₀Functor

lemma opensRange_relativeGluingData_map (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) {U : X.AffineZariskiSite} (r : Γ(X, U.1)) :
    ((relativeGluingData H).functor.map (homOfLE (U.basicOpen_le r))).opensRange =
      PrimeSpectrum.basicOpen (α.app (.op U) r) := by
  have := coequifibered_iff_forall_isLocalizationAway.mp H U r
  let := (F.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  apply TopologicalSpace.Opens.coe_inj.mp ?_
  refine PrimeSpectrum.localization_away_comap_range (F.obj (.op <| U.basicOpen r))
    (α.app (.op U) r)

@[deprecated (since := "2026-02-01")]
alias PreservesLocalization.opensRange_map := opensRange_relativeGluingData_map

lemma relativeGluingData_toBase_preimage (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) (U : X.Opens) (hU : IsAffineOpen U) :
    (relativeGluingData H).toBase ⁻¹ᵁ U = ((relativeGluingData H).cover.f ⟨U, hU⟩).opensRange := by
  simpa using (relativeGluingData H).toBase_preimage_eq_opensRange_ι ⟨U, hU⟩

@[deprecated (since := "2026-02-06")]
alias PreservesLocalization.colimitDesc_preimage := relativeGluingData_toBase_preimage

@[deprecated (since := "2026-02-01")]
alias _root_.AlgebraicGeometry.Scheme.preservesLocalization_toOpensFunctor :=
  NatTrans.Coequifibered.of_isIso

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/-- `X` is the colimit of its affine opens. -/
noncomputable def isColimitCocone : IsColimit (cocone X) :=
  letI D := relativeGluingData (X := X) (.of_isIso (𝟙 _))
  letI F := D.functor
  haveI : IsIso ((colimit.isColimit F).desc (cocone X:)) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X))).mpr fun U ↦ ?_
    change IsIso (pullback.snd (colimit.desc F (cocone X)) U.1.ι)
    let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (colimit.desc F (cocone X)) U.1.ι)
      (U.2.isoSpec.hom ≫ colimit.ι F U) <| by
      rw [Pullback.range_fst, Opens.range_ι, ← Hom.coe_opensRange, Hom.opensRange_comp_of_isIso,
        ← Scheme.Hom.coe_preimage]
      convert congr($(D.toBase_preimage_eq_opensRange_ι U).1)
      · delta cocone
        congr with U
        simp [D, relativeGluingData, restrictIsoSpec]
      · simp
    convert (inferInstance : IsIso e.hom)
    rw [← cancel_mono U.1.ι, ← Iso.inv_comp_eq]
    simp [e, ← pullback.condition, IsAffineOpen.isoSpec_hom]
  .ofPointIso (colimit.isColimit F)

end PreservesLocalization

end Scheme.AffineZariskiSite

end AlgebraicGeometry
