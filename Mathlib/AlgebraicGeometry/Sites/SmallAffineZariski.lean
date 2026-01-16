/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Directed
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

variable {X : Scheme.{u}}

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

variable (X) in
/-- `X` is the colimit of its affine opens. See `isColimit_cocone` below. -/
@[simps] noncomputable def cocone :
    Limits.Cocone (toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec) where
  pt := X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp

/--
A presheaf `F` of rings on `X.AffineZariskiSite` with a structural morphism `α : 𝒪ₓ ⟶ F`
is said to `PreservesLocalization` if `F(D(f)) = F(U)[1/f]`
for every open `U` and any section `f : Γ(X, U)`.

Under this condition we can glue `F` into a scheme over `X` via `colimit F.rightOp ⋙ Scheme.Spec`,
if one first `have := H.isLocallyDirected; have := H.isOpenImmersion`.
Also see the locally directed gluing API in `Mathlib/AlgebraicGeometry/Gluing.lean`.

This is closely related to the notion of quasi-coherent `𝒪ₓ`-algebras, and we shall link them
together once the theory of quasi-coherent `𝒪ₓ`-algebras are developed.
-/
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

attribute [local simp] IsAffineOpen.isoSpec_hom IsAffineOpen.basicOpen in
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

lemma _root_.AlgebraicGeometry.Scheme.preservesLocalization_toOpensFunctor :
    PreservesLocalization ((AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf) (𝟙 _) :=
  fun U f ↦ U.2.isLocalization_basicOpen f

variable (X) in
/-- `X` is the colimit of its affine opens. -/
noncomputable def isColimitCocone : IsColimit (cocone X) :=
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
    simp [e, ← pullback.condition, IsAffineOpen.isoSpec_hom]
  .ofPointIso (colimit.isColimit F)

end PreservesLocalization

end Scheme.AffineZariskiSite

end AlgebraicGeometry
