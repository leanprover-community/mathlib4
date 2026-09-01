/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Monad.Limits

/-!

# Inverse limits of schemes with affine transition maps

In this file, we develop API for inverse limits of schemes with affine transition maps,
following EGA IV 8 and https://stacks.math.columbia.edu/tag/01YT.

-/

@[expose] public section

universe w uI u

open CategoryTheory Limits

namespace AlgebraicGeometry

-- We refrain from considering diagrams in the over category since inverse limits in the over
-- category is isomorphic to limits in `Scheme`. Instead we use `D ⟶ (Functor.const I).obj S` to
-- say that the diagram is over the base scheme `S`.
variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) (c : Cone D) (hc : IsLimit c)

set_option backward.isDefEq.respectTransparency false in
include hc in
/--
Suppose we have a cofiltered diagram of nonempty quasi-compact schemes,
whose transition maps are affine. Then the limit is also nonempty.
-/
@[stacks 01Z2]
lemma Scheme.nonempty_of_isLimit [IsCofilteredOrEmpty I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, Nonempty (D.obj i)]
    [∀ i, CompactSpace (D.obj i)] :
    Nonempty c.pt := by
  classical
  cases isEmpty_or_nonempty I
  · have e := (isLimitEquivIsTerminalOfIsEmpty _ _ hc).uniqueUpToIso specULiftZIsTerminal
    exact Nonempty.map e.inv inferInstance
  · have i := Nonempty.some ‹Nonempty I›
    have : IsCofiltered I := ⟨⟩
    let 𝒰 := (D.obj i).affineCover.finiteSubcover
    have (i' : _) : IsAffine (𝒰.X i') := inferInstanceAs (IsAffine (Spec _))
    obtain ⟨j, H⟩ :
        ∃ j : 𝒰.I₀, ∀ {i'} (f : i' ⟶ i), Nonempty ((𝒰.pullback₁ (D.map f)).X j) := by
      by_contra! H
      choose i' f hf using H
      let g (j) := IsCofiltered.infTo (insert i (Finset.univ.image i'))
        (Finset.univ.image fun j : 𝒰.I₀ ↦ ⟨_, _, by simp, by simp, f j⟩) (X := j)
      have (j : 𝒰.I₀) : IsEmpty ((𝒰.pullback₁ (D.map (g i (by simp)))).X j) := by
        let F : (𝒰.pullback₁ (D.map (g i (by simp)))).X j ⟶
            (𝒰.pullback₁ (D.map (f j))).X j :=
          pullback.map _ _ _ _ (D.map (g _ (by simp))) (𝟙 _) (𝟙 _) (by
            rw [← D.map_comp, IsCofiltered.infTo_commutes]
            · simp [g]
            · simp
            · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) (by simp)
        exact Function.isEmpty F
      obtain ⟨x, -⟩ :=
        Cover.covers (𝒰.pullback₁ (D.map (g i (by simp)))) (Nonempty.some inferInstance)
      exact (this _).elim x
    let F := Over.post D ⋙ Over.pullback (𝒰.f j) ⋙ Over.forget _
    have (i' : _) : IsAffine (F.obj i') :=
      have : IsAffineHom (pullback.snd (D.map i'.hom) (𝒰.f j)) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      isAffine_of_isAffineHom (pullback.snd (D.map i'.hom) (𝒰.f j))
    have (i' : _) : Nonempty (F.obj i') := H i'.hom
    let e : F ⟶ (F ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := Functor.whiskerLeft F ΓSpec.adjunction.unit
    have (i : _) : IsIso (e.app i) := IsAffine.affine
    have : IsIso e := NatIso.isIso_of_isIso_app e
    let c' : LimitCone F := ⟨_, (IsLimit.postcomposeInvEquiv (asIso e) _).symm
      (isLimitOfPreserves Scheme.Spec (limit.isLimit (F ⋙ Scheme.Γ.rightOp)))⟩
    have : Nonempty c'.1.pt := by
      apply +allowSynthFailures PrimeSpectrum.instNonemptyOfNontrivial
      have (i' : _) : Nontrivial ((F ⋙ Scheme.Γ.rightOp).leftOp.obj i') := by
        apply +allowSynthFailures Scheme.component_nontrivial
        simp
      exact CommRingCat.FilteredColimits.nontrivial
        (isColimitCoconeLeftOpOfCone _ (limit.isLimit (F ⋙ Scheme.Γ.rightOp)))
    let α : F ⟶ Over.forget _ ⋙ D := Functor.whiskerRight
      (Functor.whiskerLeft (Over.post D) (Over.mapPullbackAdj (𝒰.f j)).counit) (Over.forget _)
    exact this.map (((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc).lift
        ((Cone.postcompose α).obj c'.1))

set_option backward.defeqAttrib.useBackward true in
include hc in
open Scheme.IdealSheafData in
/--
Suppose we have a cofiltered diagram of schemes whose transition maps are affine. The limit of
a family of compatible nonempty quasicompact closed sets in the diagram is also nonempty.
-/
lemma exists_mem_of_isClosed_of_nonempty
    [IsCofilteredOrEmpty I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (Z : ∀ (i : I), Set (D.obj i))
    (hZc : ∀ (i : I), IsClosed (Z i))
    (hZne : ∀ i, (Z i).Nonempty)
    (hZcpt : ∀ i, IsCompact (Z i))
    (hmapsTo : ∀ {i i' : I} (f : i ⟶ i'), Set.MapsTo (D.map f) (Z i) (Z i')) :
    ∃ (s : c.pt), ∀ i, c.π.app i s ∈ Z i := by
  let D' : I ⥤ Scheme :=
  { obj i := (vanishingIdeal ⟨Z i, hZc i⟩).subscheme
    map {X Y} f := subschemeMap _ _ (D.map f) (by
      rw [map_vanishingIdeal, ← le_support_iff_le_vanishingIdeal]
      simpa [(hZc _).closure_subset_iff] using (hmapsTo f).subset_preimage)
    map_id _ := by simp [← cancel_mono (subschemeι _)]
    map_comp _ _ := by simp [← cancel_mono (subschemeι _)] }
  let ι : D' ⟶ D := { app i := subschemeι _, naturality _ _ _ := by simp [D'] }
  have {i j} (f : i ⟶ j) : IsAffineHom (D'.map f) := by
    suffices IsAffineHom (D'.map f ≫ ι.app j) from .of_comp _ (ι.app j)
    simp only [subschemeMap_subschemeι, D', ι]
    infer_instance
  have _ (i) : Nonempty (D'.obj i) := Set.nonempty_coe_sort.mpr (hZne i)
  have _ (i) : CompactSpace (D'.obj i) := isCompact_iff_compactSpace.mp (hZcpt i)
  let c' : Cone D' :=
  { pt := (⨆ i, (vanishingIdeal ⟨Z i, hZc i⟩).comap (c.π.app i)).subscheme
    π :=
    { app i := subschemeMap _ _ (c.π.app i) (by simp [le_map_iff_comap_le, le_iSup_of_le i])
      naturality {i j} f := by simp [D', ← cancel_mono (subschemeι _)] } }
  let hc' : IsLimit c' :=
  { lift s := IsClosedImmersion.lift (subschemeι _) (hc.lift ((Cone.postcompose ι).obj s)) (by
      suffices ∀ i, vanishingIdeal ⟨Z i, hZc i⟩ ≤ (s.π.app i ≫ ι.app i).ker by
        simpa [← le_map_iff_comap_le, ← Scheme.Hom.ker_comp]
      refine fun i ↦ .trans ?_ (Scheme.Hom.le_ker_comp _ _)
      simp [ι])
    fac s i := by simp [← cancel_mono (subschemeι _), c', ι]
    uniq s m hm := by
      rw [← cancel_mono (subschemeι _)]
      refine hc.hom_ext fun i ↦ ?_
      simp [ι, c', ← hm] }
  have : Nonempty (⨆ i, (vanishingIdeal ⟨Z i, hZc i⟩).comap (c.π.app i)).support :=
    Scheme.nonempty_of_isLimit D' c' hc'
  simpa using this

set_option backward.defeqAttrib.useBackward true in
include hc in
/--
A variant of `exists_mem_of_isClosed_of_nonempty` where the closed sets are only defined
for the objects over a given `j : I`.
-/
@[stacks 01Z3]
lemma exists_mem_of_isClosed_of_nonempty'
    [IsCofilteredOrEmpty I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {j : I}
    (Z : ∀ (i : I), (i ⟶ j) → Set (D.obj i))
    (hZc : ∀ i hij, IsClosed (Z i hij))
    (hZne : ∀ i hij, (Z i hij).Nonempty)
    (hZcpt : ∀ i hij, IsCompact (Z i hij))
    (hstab : ∀ (i i' : I) (hi'i : i' ⟶ i) (hij : i ⟶ j),
      Set.MapsTo (D.map hi'i) (Z i' (hi'i ≫ hij)) (Z i hij)) :
    ∃ (s : c.pt), ∀ i hij, c.π.app i s ∈ Z i hij := by
  have {i₁ i₂ : Over j} (f : i₁ ⟶ i₂) : IsAffineHom ((Over.forget j ⋙ D).map f) := by
    dsimp; infer_instance
  simpa [Over.forall_iff] using! exists_mem_of_isClosed_of_nonempty (Over.forget j ⋙ D) _
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) c).symm hc)
    (fun i ↦ Z i.left i.hom) (fun _ ↦ hZc _ _) (fun _ ↦ hZne _ _) (fun _ ↦ hZcpt _ _)
    (fun {i₁ i₂} f ↦ by dsimp; rw [← Over.w f]; exact hstab ..)

section Opens

include hc in
/-- Let `{ Dᵢ }` be a cofiltered diagram of compact schemes with affine transition maps.
If `U ⊆ Dⱼ` contains the image of `limᵢ Dᵢ ⟶ Dⱼ`, then it contains the image of some `Dₖ ⟶ Dⱼ`. -/
lemma exists_map_eq_top
    [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)]
    {i : I} (U : (D.obj i).Opens) (hU : c.π.app i ⁻¹ᵁ U = ⊤) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹ᵁ U = ⊤ := by
  by_contra! H
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' D c hc (fun j f ↦ (D.map f ⁻¹ᵁ U)ᶜ)
    (fun j f ↦ (D.map f ⁻¹ᵁ U).2.isClosed_compl) (fun j f ↦ by
      simp only [TopologicalSpace.Opens.map_coe, Set.nonempty_compl, ne_eq]
      exact SetLike.coe_injective.ne (H j f))
    (fun j f ↦ (D.map f ⁻¹ᵁ U).2.isClosed_compl.isCompact)
    (fun j k fkj fji x (hx : _ ∉ U) ↦ by rwa [Functor.map_comp] at hx)
  exact absurd (hU.ge (Set.mem_univ s)) (by simpa using hs i (𝟙 i))

@[simp]
lemma π_app_preimage_map_preimage {i j : I} (fji : j ⟶ i) (U : (D.obj i).Opens) :
    c.π.app j ⁻¹ᵁ D.map fji ⁻¹ᵁ U = c.π.app i ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, c.w]

attribute [local simp] Scheme.Hom.resLE_comp_resLE

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a diagram `{ Dᵢ }` of schemes and an open `U ⊆ Dᵢ`,
this is the diagram of `{ Dⱼᵢ⁻¹ U }_{j ≤ i}`. -/
@[simps] noncomputable
def opensDiagram (i : I) (U : (D.obj i).Opens) : Over i ⥤ Scheme where
  obj j := D.map j.hom ⁻¹ᵁ U
  map {j k} f := (D.map f.left).resLE _ _
    (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w f])

set_option backward.defeqAttrib.useBackward true in
/-- The map `Dⱼᵢ⁻¹ U ⟶ Dᵢ` from the restricted diagram to the original diagram. -/
@[simps] noncomputable
def opensDiagramι (i : I) (U : (D.obj i).Opens) : opensDiagram D i U ⟶ Over.forget _ ⋙ D where
  app j := Scheme.Opens.ι _

set_option backward.isDefEq.respectTransparency false in
instance (i : I) (U : (D.obj i).Opens) (j : Over i) :
    IsOpenImmersion ((opensDiagramι D i U).app j) := by
  delta opensDiagramι; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `{ Dᵢ }` of schemes and an open `U ⊆ Dᵢ`,
the preimage of `U ⊆ Dᵢ` under the map `lim Dᵢ ⟶ Dᵢ` is the limit of `{ Dⱼᵢ⁻¹ U }_{j ≤ i}`.
This is the underlying cone, and it is limiting as witnessed by `isLimitOpensCone` below. -/
@[simps] noncomputable
def opensCone (i : I) (U : (D.obj i).Opens) : Cone (opensDiagram D i U) where
  pt := c.π.app i ⁻¹ᵁ U
  π.app j := (c.π.app j.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, c.w])

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

set_option backward.isDefEq.respectTransparency false in
/-- Given a diagram `{ Dᵢ }_{i ∈ I}` of schemes and an open `U ⊆ Dᵢ`,
the preimage of `U ⊆ Dᵢ` under the map `lim Dᵢ ⟶ Dᵢ` is the limit of `{ Dⱼᵢ⁻¹ U }_{j ≤ i}`. -/
noncomputable
def isLimitOpensCone [IsCofiltered I] (i : I) (U : (D.obj i).Opens) :
    IsLimit (opensCone D c i U) :=
  isLimitOfIsPullbackOfIsConnected (opensDiagramι D i U) _ _
    (by exact { hom := (c.π.app i ⁻¹ᵁ U).ι })
    (fun j ↦ IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp [← Scheme.Hom.comp_preimage]))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {i : I}
    (U : (D.obj i).Opens) {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((opensDiagram D i U).map f) := by
  refine ⟨fun V hV ↦ ?_⟩
  convert!
    ((hV.image_of_isOpenImmersion (D.map k.hom ⁻¹ᵁ U).ι).preimage
          (D.map f.left)).preimage_of_isOpenImmersion
      (D.map j.hom ⁻¹ᵁ U).ι ?_
  · ext x
    change _ ∈ V ↔ _
    refine ⟨fun h ↦ ⟨⟨(D.map f.left).base x.1, ?_⟩, ?_, rfl⟩, ?_⟩
    · change (D.map f.left ≫ D.map k.hom).base x.1 ∈ U
      rw [← D.map_comp, Over.w f]
      exact x.2
    · convert! h
      exact Subtype.ext (by simp)
    · rintro ⟨⟨_, hU⟩, hV, rfl⟩
      convert! hV
      exact Subtype.ext (by simp)
  · simp only [opensDiagram_obj, Scheme.Opens.opensRange_ι]
    rintro x ⟨⟨y, h₁ : (D.map k.hom).base y ∈ U⟩, h₂, e⟩
    obtain rfl : y = (D.map f.left).base x := congr($e)
    dsimp at h₁
    rw [← Scheme.Hom.comp_apply] at h₁
    rwa [← D.map_comp, Over.w f] at h₁

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
lemma exists_map_preimage_le_map_preimage
    [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U V : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (H : c.π.app i ⁻¹ᵁ U ≤ c.π.app i ⁻¹ᵁ V) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹ᵁ U ≤ D.map fji ⁻¹ᵁ V := by
  have (j : Over i) : CompactSpace ↥((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := (D.map j.hom)) _ U.2 hU)
  have H : ((c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app i) ⁻¹ᵁ V = ⊤ := by
    rw [Scheme.Hom.comp_preimage, ← top_le_iff]
    exact .trans (by simp) (Scheme.Hom.preimage_mono _ H)
  obtain ⟨j, fji, hj⟩ := exists_map_eq_top _ _ (isLimitOpensCone D c hc i U) (i := .mk (𝟙 i))
    (((Scheme.isoOfEq _ (by simp)).hom ≫ U.ι) ⁻¹ᵁ V)
    (by simpa [← Scheme.Hom.comp_preimage, -Scheme.Hom.comp_base])
  refine ⟨j.left, j.hom, ?_⟩
  replace hj : (D.map j.hom ⁻¹ᵁ U).ι ⁻¹ᵁ D.map fji.left ⁻¹ᵁ V = ⊤ := by
    simpa [← Scheme.Hom.comp_preimage, -Scheme.Hom.comp_base] using hj
  replace hj : (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ D.map fji.left ⁻¹ᵁ V := Set.image_subset_iff.mpr hj.ge
  simpa [show fji.left = j.hom by simpa using fji.w] using hj

include hc in
@[stacks 01Z4 "(2)"]
lemma exists_map_preimage_eq_map_preimage
    [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U V : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (hV : IsCompact (V : Set (D.obj i))) (H : c.π.app i ⁻¹ᵁ U = c.π.app i ⁻¹ᵁ V) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹ᵁ U = D.map fji ⁻¹ᵁ V := by
  obtain ⟨j₁, fj₁i, e₁⟩ := exists_map_preimage_le_map_preimage D c hc hU H.le
  obtain ⟨j₂, fj₂i, e₂⟩ := exists_map_preimage_le_map_preimage D c hc hV H.ge
  obtain ⟨k, fkj₁, fkj₂, e⟩ := IsCofiltered.cospan fj₁i fj₂i
  refine ⟨k, fkj₁ ≫ fj₁i, le_antisymm ?_ ?_⟩
  · simpa only [Scheme.Hom.comp_preimage, Functor.map_comp] using Scheme.Hom.preimage_mono _ e₁
  · rw [e]
    simpa only [Scheme.Hom.comp_preimage, Functor.map_comp] using Scheme.Hom.preimage_mono _ e₂

set_option backward.defeqAttrib.useBackward true in
include hc in
lemma exists_appTop_π_eq_of_isAffine_of_isLimit [IsCofiltered I]
    [∀ i, IsAffine (D.obj i)] (s : Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), (c.π.app i).appTop t = s := by
  have : ∀ i, IsAffine (D.op.obj i).unop := by dsimp; infer_instance
  exact ⟨_, (Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (Scheme.Γ ⋙ forget _) hc.op) s).choose_spec⟩

include hc in
lemma exists_appLE_π_eq_of_isAffineOpen [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (u : j ⟶ i) (t : Γ(D.obj j, D.map u ⁻¹ᵁ U)),
      (c.π.app j).appLE _ _ (π_app_preimage_map_preimage D c u U).ge t = s := by
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
  obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
    (isLimitOpensCone D c hc i U) ((c.π.app i ⁻¹ᵁ U).topIso.inv s)
  obtain ⟨t, rfl⟩ := (D.map j.hom ⁻¹ᵁ U).topIso.symm.commRingCatIsoToRingEquiv.surjective t
  refine ⟨j.left, j.hom, t, ?_⟩
  replace ht : ((c.π.app j.left).resLE (D.map j.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U)
      (π_app_preimage_map_preimage D c j.hom U).ge).appTop
      ((D.map j.hom ⁻¹ᵁ U).topIso.inv t) = (c.π.app i ⁻¹ᵁ U).topIso.inv s := ht
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ConcreteCategory.comp_apply,
    Iso.inv_hom_id_apply] at ht
  exact (c.π.app i ⁻¹ᵁ U).topIso.commRingCatIsoToRingEquiv.symm.injective ht

include hc in
lemma isBasis_preimage_isAffineOpen [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : I) (V : (D.obj i).Opens) (_ : IsAffineOpen V) } := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (c.π.app i x)) isOpen_univ
  have (j : _) : IsAffine ((opensDiagram D i V).obj j) := hV.preimage _
  obtain ⟨r, hrU, hxr⟩ := IsAffineOpen.exists_basicOpen_le
    (Scheme.isAffine_of_isLimit _ (isLimitOpensCone D c hc i V)) (V := U) ⟨x, hxU⟩ hxV
  obtain ⟨j, u, s, hs⟩ := exists_appLE_π_eq_of_isAffineOpen D c hc hV r
  refine ⟨_, ⟨j, _, (hV.preimage _).basicOpen s, rfl⟩, ?_⟩
  simp only [Functor.const_obj_obj, Scheme.preimage_basicOpen] at hs ⊢
  rw [← c.pt.basicOpen_res_eq _ (eqToHom (π_app_preimage_map_preimage D c u V).symm).op,
    ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, hs]
  exact ⟨hxr, hrU⟩

set_option backward.defeqAttrib.useBackward true in
include hc in
@[stacks 01Z4 "(1)"]
lemma exists_preimage_eq
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U := by
  classical
  obtain ⟨s, hs, hsf, rfl⟩ := (isBasis_preimage_isAffineOpen D c hc).exists_finite_of_isCompact hU
  have : Finite s := hsf
  choose i V hV hVi using fun x : s ↦ hs x.2
  obtain ⟨j, ⟨fj⟩⟩ := IsCofiltered.exists_hom_forall i
  refine ⟨j, ⨆ (k : s), D.map (fj _) ⁻¹ᵁ V k, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk]
    exact isCompact_iUnion fun i ↦ ((hV i).preimage _).isCompact
  · simp [-TopologicalSpace.Opens.iSup_mk, Scheme.Hom.preimage_iSup,
      ← Scheme.Hom.comp_preimage, c.w, hVi, sSup_eq_iSup']

end Opens

include hc in
lemma isAffineHom_π_app [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (i : I) :
    IsAffineHom (c.π.app i) where
  isAffine_preimage U hU := have (j : _) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage _
    Scheme.isAffine_of_isLimit _ (isLimitOpensCone D c hc i U)

include hc in
lemma Scheme.compactSpace_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)] :
    CompactSpace c.pt := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have := isAffineHom_π_app _ _ hc
  exact QuasiCompact.compactSpace_of_compactSpace (c.π.app i)

/-!

## Cofiltered Limits and Schemes of Finite Type

Given a cofiltered diagram `D` of quasi-compact `S`-schemes with affine transition maps,
and another scheme `X` of finite type over `S`.
Then the canonical map `colim Homₛ(Dᵢ, X) ⟶ Homₛ(lim Dᵢ, X)` is injective.
In other words, for each pair of `a : Homₛ(Dᵢ, X)` and `b : Homₛ(Dⱼ, X)` that give rise to the
same map `Homₛ(lim Dᵢ, X)`, there exists a `k` with `fᵢ : k ⟶ i` and `fⱼ : k ⟶ j` such that
`D(fᵢ) ≫ a = D(fⱼ) ≫ b`.
This results is formalized in `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`.

We first reduce to the case `i = j`, and the goal is to reduce to the case where `X` and `S`
are affine, where the result follows from commutative algebra.

To achieve this, we show that there exists some `i₀ ⟶ i` such that for each `x`, `a x` and `b x`
are contained in the same component (i.e. given an open cover `𝒰ₛ` of `S`,
and `𝒰ₓ` of `X` refining `𝒰ₛ`, the range of `x ↦ (a x, b x)` falls in the diagonal part
`⋃ᵢⱼ 𝒰ₓⱼ ×[𝒰ₛᵢ] 𝒰ₓⱼ`).
Then we may restrict to the sub-diagram over `i₀` (which is cofinal because `D` is cofiltered),
and check locally on `X`, reducing to the affine case.

For the actual implementation, we wrap `i`, `a`, `b`, the limit cone `lim Dᵢ`, and open covers
of `X` and `S` into a structure `ExistsHomHomCompEqCompAux` for convenience.

See the injective part of (1) => (3) of https://stacks.math.columbia.edu/tag/01ZC.
-/

section LocallyOfFiniteType

variable [∀ i, CompactSpace (D.obj i)] [LocallyOfFiniteType f] [IsCofiltered I]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/-- Subsumed by `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`. -/
private nonrec lemma Scheme.exists_hom_hom_comp_eq_comp_of_isAffine_of_locallyOfFiniteType
    [IsAffine S] [IsAffine X] [∀ i, IsAffine (D.obj i)] [IsAffine c.pt]
    {i : I} (a : D.obj i ⟶ X) (ha : t.app i = a ≫ f)
    {j : I} (b : D.obj j ⟶ X) (hb : t.app j = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : I) (hik : k ⟶ i) (hjk : k ⟶ j),
      D.map hik ≫ a = D.map hjk ≫ b := by
  wlog hS : ∃ R, S = Spec R generalizing S
  · exact this (t ≫ ((Functor.const I).mapIso S.isoSpec).hom)
      (f ≫ S.isoSpec.hom) (by simp [ha]) (by simp [hb]) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hS
  wlog hX : ∃ S, X = Spec S generalizing X
  · simpa using! this (a ≫ X.isoSpec.hom) (b ≫ X.isoSpec.hom) (by simp [hab]) (X.isoSpec.inv ≫ f)
      (by simp [ha]) (by simp [hb]) ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  wlog hD : ∃ D' : I ⥤ CommRingCatᵒᵖ, D = D' ⋙ Scheme.Spec generalizing D
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
    have inst (i) : IsIso (e.app i) := by dsimp [e]; infer_instance
    have inst : IsIso e := NatIso.isIso_of_isIso_app e
    have inst (i) : IsAffine ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj i) := by
      dsimp; infer_instance
    have inst : IsAffine ((Cone.postcompose (asIso e).hom).obj c).pt := by
      dsimp; infer_instance
    have := this (D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) ((Cone.postcompose (asIso e).hom).obj c)
      ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc) (inv e ≫ t)
      ((inv e).app _ ≫ a) ((inv e).app _ ≫ b) (by simp [hab]) (by simp [ha]) (by simp [hb])
      ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    simp_rw [(inv e).naturality_assoc] at this
    simpa using! this
  obtain ⟨D, rfl⟩ := hD
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  let e : ((Functor.const Iᵒᵖ).obj R).rightOp ⋙ Scheme.Spec ≅ (Functor.const I).obj (Spec R) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp)
  obtain ⟨t, rfl⟩ : ∃ t' : (Functor.const Iᵒᵖ).obj R ⟶ D.leftOp,
      t = Functor.whiskerRight (NatTrans.rightOp t') Scheme.Spec ≫ e.hom :=
    ⟨⟨fun i ↦ Spec.preimage (t.app i.unop), fun _ _ f ↦ Spec.map_injective
      (by simpa using! (t.naturality f.unop).symm)⟩, by ext : 2; simp [e]⟩
  have := monadicCreatesLimits Scheme.Spec
  obtain ⟨k, hik, hjk, H⟩ := (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType (Spec.map φ)›)
    |>.essFiniteType.exists_comp_map_eq_of_isColimit _ D.leftOp t _
    (coconeLeftOpOfCone (liftLimit hc))
    (isColimitCoconeLeftOpOfCone _ (liftedLimitIsLimit _))
    a (Spec.map_injective (by simpa using! ha.symm))
    b (Spec.map_injective (by simpa using! hb.symm))
    (Spec.map_injective (by
      simp only [coconeLeftOpOfCone_pt, Functor.const_obj_obj,
        Functor.leftOp_obj, coconeLeftOpOfCone_ι_app, Spec.map_comp]
      simp only [← Scheme.Spec_map, ← liftedLimitMapsToOriginal_hom_π, Category.assoc, hab]))
  exact ⟨k.unop, hik.unop, hjk.unop, by simpa [← Spec.map_comp, Spec.map_inj] using! H⟩

/-- (Implementation)
An auxiliary structure used to prove `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`.
See the section docstring. -/
structure ExistsHomHomCompEqCompAux where
  /-- (Implementation) The limit cone. See the section docstring. -/
  c : Cone D
  /-- (Implementation) The limit cone is a limit. See the section docstring. -/
  hc : IsLimit c
  /-- (Implementation) The index on which `a` and `b` lives. See the section docstring. -/
  i : I
  /-- (Implementation) `a`. See the section docstring. -/
  a : D.obj i ⟶ X
  ha : t.app i = a ≫ f
  /-- (Implementation) `b`. See the section docstring. -/
  b : D.obj i ⟶ X
  hb : t.app i = b ≫ f
  hab : c.π.app i ≫ a = c.π.app i ≫ b
  /-- (Implementation) An open cover on `S`. See the section docstring. -/
  𝒰S : Scheme.OpenCover.{u} S
  [h𝒰S : ∀ i, IsAffine (𝒰S.X i)]
  /-- (Implementation) A family of open covers refining `𝒰S`. See the section docstring. -/
  𝒰X (i : (𝒰S.pullback₁ f).I₀) : Scheme.OpenCover.{u} ((𝒰S.pullback₁ f).X i)
  [h𝒰X : ∀ i j, IsAffine ((𝒰X i).X j)]

attribute [instance] ExistsHomHomCompEqCompAux.h𝒰S ExistsHomHomCompEqCompAux.h𝒰X

namespace ExistsHomHomCompEqCompAux

noncomputable section

variable {D t f c} [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable (A : ExistsHomHomCompEqCompAux D t f)

set_option backward.isDefEq.respectTransparency false in
omit [LocallyOfFiniteType f] in
lemma exists_index : ∃ (i' : I) (hii' : i' ⟶ A.i),
    ((D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)) ⁻¹'
      ((Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X : Set <|
        ↑(pullback f f))ᶜ)) = ∅ := by
  let W := Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X
  by_contra! h
  let Z (i' : I) (hii' : i' ⟶ A.i) :=
    (D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)) ⁻¹' Wᶜ
  have hZ (i') (hii' : i' ⟶ A.i) : IsClosed (Z i' hii') :=
    (W.isOpen.isClosed_compl).preimage <| Scheme.Hom.continuous _
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' D A.c A.hc Z hZ h
    (fun _ _ ↦ (hZ _ _).isCompact) (fun i i' hii' hij ↦ by simp [Z, Set.MapsTo])
  refine hs A.i (𝟙 A.i) (Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ?_)
  use (A.c.π.app A.i ≫ A.a) s
  have H : A.c.π.app A.i ≫ A.a ≫ pullback.diagonal f =
      A.c.π.app A.i ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb) := by ext <;> simp [hab]
  simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, H]

/-- (Implementation)
The index `i'` such that `a` and `b` restricted onto `i'` maps into the diagonal components.
See the section docstring. -/
def i' : I := A.exists_index.choose

/-- (Implementation) The map from `i'` to `i`. See the section docstring. -/
def hii' : A.i' ⟶ A.i := A.exists_index.choose_spec.choose

/-- (Implementation)
The map sending `x` to `(a x, b x)`, which should fall in the diagonal component.
See the section docstring. -/
def g : D.obj A.i' ⟶ pullback f f :=
  (D.map A.hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb))

set_option backward.isDefEq.respectTransparency false in
omit [LocallyOfFiniteType f] in
lemma range_g_subset :
    Set.range A.g ⊆ Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X := by
  simpa [ExistsHomHomCompEqCompAux.hii', g] using! A.exists_index.choose_spec.choose_spec

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation)
The covering of `D(i')` by the pullback of the diagonal components of `X ×ₛ X`.
See the section docstring. -/
noncomputable def 𝒰D₀ : Scheme.OpenCover.{u} (D.obj A.i') :=
  Scheme.Cover.mkOfCovers (Σ i : A.𝒰S.I₀, (A.𝒰X i).I₀) _
    (fun i ↦ ((Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullback₁ A.g).f ⟨i.1, i.2, i.2⟩)
    (fun x ↦ by simpa [← Set.mem_range, Scheme.Pullback.range_fst,
        Scheme.Pullback.diagonalCoverDiagonalRange] using A.range_g_subset ⟨x, rfl⟩)

/-- (Implementation) An affine open cover refining `𝒰D₀`. See the section docstring. -/
noncomputable def 𝒰D : Scheme.OpenCover.{u} (D.obj A.i') :=
  A.𝒰D₀.bind fun _ ↦ Scheme.affineCover _

attribute [-simp] cast_eq eq_mpr_eq_cast

/-- (Implementation) The diagram restricted to `Over i'`. See the section docstring. -/
def D' (j : A.𝒰D.I₀) : Over A.i' ⥤ Scheme :=
  Over.post D ⋙ Over.pullback (A.𝒰D.f j) ⋙ Over.forget _

/-- (Implementation) The limit cone restricted to `Over i'`. See the section docstring. -/
def c' (j : A.𝒰D.I₀) : Cone (A.D' j) :=
  (Over.pullback (A.𝒰D.f j) ⋙ Over.forget _).mapCone ((Over.conePost _ _).obj A.c)

attribute [local instance] IsCofiltered.isConnected

/-- (Implementation)
The limit cone restricted to `Over i'` is still a limit because the diagram is cofiltered.
See the section docstring. -/
def hc' (j : A.𝒰D.I₀) : IsLimit (A.c' j) :=
  isLimitOfPreserves (Over.pullback (A.𝒰D.f j) ⋙ Over.forget _) (Over.isLimitConePost _ A.hc)

variable [∀ i, IsAffineHom (A.c.π.app i)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma exists_eq (j : A.𝒰D.I₀) : ∃ (k : I) (hki' : k ⟶ A.i'),
    (A.𝒰D.pullback₁ (D.map hki')).f j ≫ D.map (hki' ≫ A.hii') ≫ A.a =
      (A.𝒰D.pullback₁ (D.map hki')).f j ≫ D.map (hki' ≫ A.hii') ≫ A.b := by
  have : IsAffine (A.𝒰D.X j) := by dsimp [𝒰D]; infer_instance
  have (i : _) : IsAffine ((Over.post D ⋙ Over.pullback (A.𝒰D.f j) ⋙ Over.forget _).obj i) := by
    dsimp; infer_instance
  have : IsAffine ((Over.pullback (A.𝒰D.f j) ⋙ Over.forget (A.𝒰D.X j)).mapCone
      ((Over.conePost D A.i').obj A.c)).pt := by
    dsimp; infer_instance
  have : LocallyOfFiniteType ((A.𝒰X j.fst.fst).f j.fst.snd ≫ A.𝒰S.pullbackHom f j.fst.fst) := by
    dsimp [Scheme.Cover.pullbackHom]; infer_instance
  have H₁ := congr($(pullback.condition (f := A.g) (g := (Scheme.Pullback.diagonalCover f
    A.𝒰S A.𝒰X).f ⟨j.1.1, (j.1.2, j.1.2)⟩)) ≫ pullback.fst _ _)
  have H₂ := congr($(pullback.condition (f := A.g) (g := (Scheme.Pullback.diagonalCover f
    A.𝒰S A.𝒰X).f ⟨j.1.1, (j.1.2, j.1.2)⟩)) ≫ pullback.snd _ _)
  simp only [Scheme.Pullback.openCoverOfBase_I₀, Scheme.Pullback.openCoverOfBase_X,
    Scheme.Cover.pullbackHom, Scheme.Pullback.openCoverOfLeftRight_I₀,
    g, Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
    Scheme.Pullback.diagonalCover_map] at H₁ H₂
  obtain ⟨k, hik, hjk, H⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_isAffine_of_locallyOfFiniteType
    (Over.post D ⋙ Over.pullback (A.𝒰D.f j) ⋙ Over.forget _)
    ((Over.post D ⋙ Over.pullback (A.𝒰D.f j)).whiskerLeft (Comma.natTrans _ _) ≫
      (Functor.const _).map ((A.𝒰D₀.X j.1).affineCover.f j.2 ≫
      (Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackHom _ _ ≫
      pullback.fst _ _ ≫
      (A.𝒰X j.fst.fst).f j.fst.snd ≫ Scheme.Cover.pullbackHom A.𝒰S f j.fst.fst))
    (((A.𝒰X j.1.1).f j.1.2 ≫ A.𝒰S.pullbackHom f j.1.1))
    ((Over.pullback (A.𝒰D.f j) ⋙ Over.forget _).mapCone ((Over.conePost _ _).obj A.c))
    (by
      refine isLimitOfPreserves (Over.pullback (A.𝒰D.f j) ⋙ Over.forget _) ?_
      apply isLimitOfReflects (Over.forget (D.obj A.i'))
      exact (Functor.Initial.isLimitWhiskerEquiv (Over.forget A.i') A.c).symm A.hc)
    (i := Over.mk (𝟙 _))
    (pullback.snd _ _ ≫ (A.𝒰D₀.X j.1).affineCover.f j.2 ≫
      (Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackHom _ _ ≫
      pullback.fst _ _)
    (by simp)
    (j := Over.mk (𝟙 _))
    (pullback.snd _ _ ≫ (A.𝒰D₀.X j.1).affineCover.f j.2 ≫
      (Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackHom _ _ ≫
      pullback.snd _ _)
    (by simp [pullback.condition])
    (by
      rw [← cancel_mono ((A.𝒰X j.1.1).f j.1.2), ← cancel_mono (pullback.fst f (A.𝒰S.f j.1.1))]
      have H₃ := congr(pullback.fst (A.c.π.app A.i') (A.𝒰D.f j) ≫ $(A.hab))
      simp only [pullback.condition_assoc, 𝒰D, ← A.c.w A.hii', Category.assoc] at H₃
      simpa [Scheme.Cover.pullbackHom, g, ← H₁, ← H₂, -Cone.w, -Cone.w_assoc] using! H₃)
  refine ⟨k.left, k.hom, ?_⟩
  simpa [← cancel_mono ((A.𝒰X j.1.1).f j.1.2), ← cancel_mono (pullback.fst f (A.𝒰S.f j.1.1)),
    Scheme.Cover.pullbackHom, g, ← H₁, ← H₂, pullback.condition_assoc] using! H

end

end ExistsHomHomCompEqCompAux

variable [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
lemma Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    {i : I} (a b : D.obj i ⟶ X) (ha : t.app i = a ≫ f) (hb : t.app i = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app i ≫ b) :
    ∃ (k : I) (hik : k ⟶ i), D.map hik ≫ a = D.map hik ≫ b := by
  classical
  have := isAffineHom_π_app _ _ hc
  let A : ExistsHomHomCompEqCompAux D t f :=
    { c := c, hc := hc, i := i, a := a, ha := ha, b := b, hb := hb, hab := hab
      𝒰S := S.affineCover, 𝒰X i := Scheme.affineCover _ }
  let 𝒰 := Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X
  let W := Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X
  choose k hki' heq using A.exists_eq
  let 𝒰Df := A.𝒰D.finiteSubcover
  rcases isEmpty_or_nonempty (D.obj A.i') with h | h
  · exact ⟨A.i', A.hii', isInitialOfIsEmpty.hom_ext _ _⟩
  let O : Finset I := {A.i'} ∪ Finset.univ.image (fun i : 𝒰Df.I₀ ↦ k <| A.𝒰D.idx i.1)
  let o := Nonempty.some (inferInstance : Nonempty 𝒰Df.I₀)
  have ho : k (A.𝒰D.idx o.1) ∈ O := by
    simp [O]
  obtain ⟨l, hl1, hl2⟩ := IsCofiltered.inf_exists O
    (Finset.univ.image (fun i : 𝒰Df.I₀ ↦
      ⟨k <| A.𝒰D.idx i.1, A.i', by simp [O], by simp [O], hki' <| A.𝒰D.idx i.1⟩))
  have (w v : 𝒰Df.I₀) :
      hl1 (by simp [O]) ≫ hki' (A.𝒰D.idx w.1) = hl1 (by simp [O]) ≫ hki' (A.𝒰D.idx v.1) := by
    trans hl1 (show A.i' ∈ O by simp [O])
    · exact hl2 _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact .symm <| hl2 _ _ (Finset.mem_image_of_mem _ (by simp))
  refine ⟨l, hl1 ho ≫ hki' _ ≫ A.hii', ?_⟩
  apply Cover.hom_ext (𝒰Df.pullback₁ (D.map <| hl1 ho ≫ hki' _))
  intro u
  let F : pullback (D.map (hl1 ho ≫ hki' (A.𝒰D.idx o.1))) (𝒰Df.f u) ⟶
      pullback (D.map (hki' <| A.𝒰D.idx u.1)) (A.𝒰D.f <| A.𝒰D.idx u.1) :=
    pullback.map _ _ _ _ (D.map <| hl1 (by simp [O]))
      (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← D.map_comp, this]) rfl
  have hF : F ≫ pullback.fst (D.map (hki' _)) (A.𝒰D.f _) =
      pullback.fst _ _ ≫ D.map (hl1 (by simp [O])) := by simp [F]
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f, Functor.map_comp, Category.assoc]
    at heq ⊢
  simp_rw [← D.map_comp_assoc, reassoc_of% this o u, D.map_comp_assoc]
  rw [← reassoc_of% hF, ← reassoc_of% hF, heq]

set_option backward.defeqAttrib.useBackward true in
include hc in
/--
Given a cofiltered diagram `D` of quasi-compact `S`-schemes with affine transition maps,
and another scheme `X` of finite type over `S`.
Then the canonical map `colim Homₛ(Dᵢ, X) ⟶ Homₛ(lim Dᵢ, X)` is injective.

In other words, for each pair of `a : Homₛ(Dᵢ, X)` and `b : Homₛ(Dⱼ, X)` that give rise to the
same map `Homₛ(lim Dᵢ, X)`, there exists a `k` with `fᵢ : k ⟶ i` and `fⱼ : k ⟶ j` such that
`D(fᵢ) ≫ a = D(fⱼ) ≫ b`.
-/
@[stacks 01ZC "Injective part of (1) => (3)"]
lemma Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType
    {i : I} (a : D.obj i ⟶ X) (ha : t.app i = a ≫ f)
    {j : I} (b : D.obj j ⟶ X) (hb : t.app j = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : I) (hik : k ⟶ i) (hjk : k ⟶ j),
      D.map hik ≫ a = D.map hjk ≫ b := by
  let o := IsCofiltered.min i j
  obtain ⟨k, hik, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D t f c hc
    (D.map (IsCofiltered.minToLeft i j) ≫ a) (D.map (IsCofiltered.minToRight i j) ≫ b)
    (by simp [← ha])
    (by simp [← hb]) (by simpa)
  use k, hik ≫ IsCofiltered.minToLeft i j, hik ≫ IsCofiltered.minToRight i j
  simpa using heq

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
lemma Scheme.exists_resLE_comp_eq_resLE_comp_of_locallyOfFiniteType
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (a b : ↑U ⟶ X)
    (ha : U.ι ≫ t.app i = a ≫ f) (hb : U.ι ≫ t.app i = b ≫ f)
    (hab : (c.π.app i).resLE U _ le_rfl ≫ a = (c.π.app i).resLE U _ le_rfl ≫ b) :
    ∃ (k : I) (hik : k ⟶ i),
      (D.map hik).resLE U _ le_rfl ≫ a = (D.map hik).resLE U _ le_rfl ≫ b := by
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU)
  let U₀ : (D.obj i).Opens := D.map (𝟙 i) ⁻¹ᵁ U
  let a₀ : ↑U₀ ⟶ X := Scheme.homOfLE _ (by simp [U₀]) ≫ a
  let b₀ : ↑U₀ ⟶ X := Scheme.homOfLE _ (by simp [U₀]) ≫ b
  have ha₀ : U₀.ι ≫ t.app i = a₀ ≫ f := by simp [a₀, ← ha]
  have hb₀ : U₀.ι ≫ t.app i = b₀ ≫ f := by simp [b₀, ← hb]
  have hab₀ : (c.π.app i).resLE U₀ (c.π.app i ⁻¹ᵁ U) (by simp [U₀]) ≫ a₀ =
      (c.π.app i).resLE U₀ (c.π.app i ⁻¹ᵁ U) (by simp [U₀]) ≫ b₀ := by
    simp only [a₀, b₀, Scheme.Hom.resLE_map_assoc]
    exact hab
  obtain ⟨⟨k, _, u⟩, ⟨u', _, hu⟩, e⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    _ (opensDiagramι .. ≫ (Over.forget i).whiskerLeft t) f _ (isLimitOpensCone D c hc i U)
    (i := .mk (𝟙 i)) a₀ b₀ ha₀ hb₀ hab₀
  obtain rfl : u = u' := by simpa using! hu.symm
  replace e : (D.map u).resLE U₀ (D.map u ⁻¹ᵁ U) (by simp [U₀]) ≫ a₀ =
      (D.map u).resLE U₀ (D.map u ⁻¹ᵁ U) (by simp [U₀]) ≫ b₀ := e
  exact ⟨k, u, by simpa [a₀, b₀] using e⟩

end LocallyOfFiniteType

/-!
### Sections of the limit

Let `D` be a cofiltered diagram of schemes with affine transition maps.
Consider the canonical map `colim Γ(Dᵢ, ⊤) ⟶ Γ(lim Dᵢ, ⊤)`.

If `D` consists of quasicompact schemes, then this map is injective. More generally, we show
that if `s t : Γ(Dᵢ, U)` have equal image in `lim Dᵢ`, then they are equal at some `Γ(Dⱼ, Dⱼᵢ⁻¹ U)`.
See `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit`.

If `D` consists of qcqs schemes, then this map is surjective. Specifically, we show that
any `s : Γ(lim Dᵢ, ⊤)` comes from `Γ(Dᵢ, ⊤)` for some `i`.
See `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit`.

These two results imply that `PreservesLimit D Scheme.Γ.rightOp`, which is available as an instance.

-/
section sections

variable [IsCofiltered I]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
lemma exists_appTop_map_eq_zero_of_isAffine_of_isLimit
    [∀ i, IsAffine (D.obj i)]
    (i : I) (s : Γ(D.obj i, ⊤)) (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).appTop s = 0 := by
  have : ∀ i, IsAffine (D.op.obj i).unop := by dsimp; infer_instance
  obtain ⟨j, f, hj⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (Scheme.Γ ⋙ forget _) hc.op) s (0 : Γ(D.obj i, ⊤))).mp
    (by dsimp at hs ⊢; simpa)
  dsimp at hj
  exact ⟨j.unop, f.unop, by simpa using hj⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
lemma exists_app_map_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = 0 := by
  have key {W : (D.obj i).Opens} (hW : IsAffineOpen W) (hWU : W ≤ U) :
      ∃ (j : I) (f : j ⟶ i), (D.map f).app W (s |_ W) = 0 := by
    have (j : Over i) : IsAffine ((opensDiagram D i W).obj j) := hW.preimage (D.map _)
    have H : (D.map (𝟙 _) ⁻¹ᵁ W).ι ''ᵁ ⊤ ≤ W := by simp
    obtain ⟨j, f, hf⟩ := exists_appTop_map_eq_zero_of_isAffine_of_isLimit _ _
      (isLimitOpensCone D c hc i W) (.mk (𝟙 i))
      ((D.obj i).presheaf.map (homOfLE H).op (s |_ W)) (by
        rw [← map_zero (c.pt.presheaf.map (homOfLE (show (c.π.app i ⁻¹ᵁ W).ι ''ᵁ ⊤ ≤
          c.π.app i ⁻¹ᵁ U from le_trans (by simp) ((c.π.app i).preimage_mono hWU))).op).hom, ← hs]
        dsimp [Scheme.Opens.toScheme_presheaf_obj, TopCat.Presheaf.restrictOpen,
          TopCat.Presheaf.restrict]
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← ConcreteCategory.comp_apply]
        congr! 2
        simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE])
    dsimp at hf
    refine ⟨j.left, f.left, ?_⟩
    have hf' : f.left = j.hom := by simpa using Over.w f
    convert!
      congr((D.obj j.left).presheaf.map
        (homOfLE (show D.map f.left ⁻¹ᵁ W ≤ (D.map j.hom ⁻¹ᵁ W).ι ''ᵁ ⊤ by simp [hf'])).op $hf)
    · dsimp [Scheme.Opens.toScheme_presheaf_obj]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
      congr! 2
      simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
    · simp
  obtain ⟨Us, hUs, hUsf, hsup⟩ := (D.obj i).isBasis_affineOpens.exists_finite_of_isCompact hU
  have : Finite Us := hUsf
  have hle (W : Us) : (W : (D.obj i).Opens) ≤ U := (le_sSup W.2).trans hsup.ge
  choose j u H using fun W : Us ↦ key (hUs W.2) (hle W)
  obtain ⟨k, v, w, hw⟩ := IsCofiltered.wideCospan u
  refine ⟨k, v, TopCat.Sheaf.eq_of_locally_eq' ⟨_, (D.obj k).IsSheaf⟩
    (fun W : Us ↦ D.map v ⁻¹ᵁ (W : (D.obj i).Opens)) _
    (fun W ↦ homOfLE ((D.map v).preimage_mono (hle W))) ?_ _ _ fun W ↦ ?_⟩
  · rw [hsup, sSup_eq_iSup', Scheme.Hom.preimage_iSup]
  · have h₂ : D.map v ⁻¹ᵁ (W : (D.obj i).Opens) ≤
        D.map (w W) ⁻¹ᵁ D.map (u W) ⁻¹ᵁ (W : (D.obj i).Opens) := by
      rw [← Scheme.Hom.comp_preimage, ← D.map_comp, hw W]
    convert! congr((D.map (w W)).appLE _ _ h₂ $(H W))
    · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, -CommRingCat.hom_comp,
        Scheme.Hom.appLE_comp_appLE, ← Functor.map_comp, hw W]
    · simp

set_option backward.defeqAttrib.useBackward true in
include hc in
lemma exists_appTop_map_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} [CompactSpace (D.obj i)] (s : Γ(D.obj i, ⊤)) (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).appTop s = 0 :=
  exists_app_map_eq_zero_of_isLimit D c hc (by simpa using isCompact_univ) s hs

include hc in
lemma exists_app_map_eq_map_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s t : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = (c.π.app i).app U t) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = (D.map f).app U t := by
  simpa [sub_eq_zero] using exists_app_map_eq_zero_of_isLimit _ _ hc hU (s - t)
    (by simpa +instances [map_sub, sub_eq_zero])

include hc in
private lemma exists_appLE_eq_restrict_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Γ(c.pt, ⊤)) (x : c.pt) :
    ∃ (i : I) (U : (D.obj i).Opens) (_ : IsAffineOpen U) (_ : (c.π.app i).base x ∈ U)
      (t : Γ(D.obj i, U)), ∀ (V : c.pt.Opens) (e : V ≤ c.π.app i ⁻¹ᵁ U),
        (c.π.app i).appLE U V e t = s |_ V := by
  obtain ⟨_, ⟨i, U, hU, rfl⟩, hxU, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_preimage_isAffineOpen D c hc)
      (U := ⊤) (x := x) trivial
  obtain ⟨j, u, t, ht⟩ := exists_appLE_π_eq_of_isAffineOpen D c hc hU (s |_ (c.π.app i ⁻¹ᵁ U))
  have h := π_app_preimage_map_preimage D c u U
  refine ⟨j, D.map u ⁻¹ᵁ U, hU.preimage _, h.ge hxU, t, fun V e ↦ ?_⟩
  simp_rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply] at ht ⊢
  rw [← TopCat.Presheaf.restrict_restrict (e.trans_eq h) le_top s, ← ht]
  exact (TopCat.Presheaf.restrict_restrict (e.trans_eq h) h.ge _).symm

include hc in
private lemma exists_forall_map_appLE_eq_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {s : Γ(c.pt, ⊤)} {J : Type*} [Finite J] {j : I}
    {i : J → I} {U : ∀ x, (D.obj (i x)).Opens} (hU : ∀ x, IsAffineOpen (U x))
    {t : ∀ x, Γ(D.obj (i x), U x)} (ht : ∀ x (V : c.pt.Opens) (e : V ≤ c.π.app (i x) ⁻¹ᵁ U x),
      (c.π.app (i x)).appLE (U x) V e (t x) = s |_ V) (u : ∀ x, j ⟶ i x) :
    ∃ (k : I) (v : k ⟶ j), ∀ x y (V : (D.obj k).Opens) (h₁ : V ≤ D.map (v ≫ u x) ⁻¹ᵁ U x)
      (h₂ : V ≤ D.map (v ≫ u y) ⁻¹ᵁ U y),
        (D.map (v ≫ u x)).appLE _ V h₁ (t x) = (D.map (v ≫ u y)).appLE _ V h₂ (t y) := by
  refine IsCofiltered.exists_forall₂ _ ?_ ?_
  · exact fun w v x y hv V h₁ h₂ ↦ by
      have e : V ≤ D.map w ⁻¹ᵁ (D.map (v ≫ u x) ⁻¹ᵁ U x ⊓ D.map (v ≫ u y) ⁻¹ᵁ U y) := by
        simpa [Scheme.Hom.preimage_inf] using le_inf h₁ h₂
      simpa [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE, -Scheme.Hom.comp_appLE]
        using congr((D.map w).appLE _ V e $(hv _ inf_le_left inf_le_right))
  intro x y
  have hcpt : IsCompact (X := D.obj j) ↑(D.map (u x) ⁻¹ᵁ U x ⊓ D.map (u y) ⁻¹ᵁ U y) :=
    ((hU x).preimage (D.map (u x))).isCompact.inter_of_isOpen
      ((hU y).preimage (D.map (u y))).isCompact (D.map (u x) ⁻¹ᵁ U x).2 (D.map (u y) ⁻¹ᵁ U y).2
  obtain ⟨k, v, hv⟩ := exists_app_map_eq_map_of_isLimit D c hc hcpt
    ((D.map (u x)).app _ (t x) |_ _) ((D.map (u y)).app _ (t y) |_ _) (by
    dsimp +instances [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
    simp only [← ConcreteCategory.comp_apply,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, Cone.w]
    exact (ht x _ _).trans (ht y _ _).symm)
  refine ⟨k, v, fun V h₁ h₂ ↦ ?_⟩
  have H : V ≤ D.map v ⁻¹ᵁ (D.map (u x) ⁻¹ᵁ U x ⊓ D.map (u y) ⁻¹ᵁ U y) := by
    simpa [Scheme.Hom.preimage_inf] using le_inf h₁ h₂
  apply_fun (D.obj k).presheaf.map (homOfLE H).op at hv
  dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at hv ⊢
  simpa [← ConcreteCategory.comp_apply, -Scheme.Hom.comp_appLE,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE] using hv

include hc in
lemma exists_appTop_π_eq_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Γ(c.pt, ⊤)) [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), s = (c.π.app i).appTop t := by
  classical
  have := Scheme.compactSpace_of_isLimit _ _ hc
  choose i U hU hxU t ht using exists_appLE_eq_restrict_of_isLimit D c hc s
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x ↦ ((c.π.app (i x)) ⁻¹ᵁ U x).1)
    (fun x ↦ ((c.π.app (i x)) ⁻¹ᵁ U x).2.mem_nhds (by exact hxU x))
  obtain ⟨j, fj, hfj⟩ : ∃ (j : I) (fj : ∀ x : σ, j ⟶ i x), ⨆ x : σ, D.map (fj x) ⁻¹ᵁ U x = ⊤ := by
    obtain ⟨j₀, ⟨fj₀⟩⟩ := IsCofiltered.exists_hom_forall fun x : σ ↦ i x
    obtain ⟨j, w, hw⟩ := exists_map_eq_top D c hc (⨆ x : σ, D.map (fj₀ x) ⁻¹ᵁ U x) (by
      apply SetLike.coe_injective
      simpa [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
        Set.iUnion_subtype] using hσ)
    exact ⟨j, fun x ↦ w ≫ fj₀ x, by simpa [Scheme.Hom.preimage_iSup] using hw⟩
  obtain ⟨k, v, hv⟩ := exists_forall_map_appLE_eq_of_isLimit D c hc (J := σ)
    (fun x ↦ hU x) (fun x ↦ ht x) fj
  have hcov : ⨆ x : σ, D.map (v ≫ fj x) ⁻¹ᵁ U x = ⊤ := by
    simpa [Scheme.Hom.comp_preimage] using (D.map v).iSup_preimage_eq_top hfj
  have H (x : σ) := (π_app_preimage_map_preimage D c (v ≫ fj x) (U x)).symm
  obtain ⟨t₀, ht₀, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨_, (D.obj k).IsSheaf⟩ _ ⊤
    (fun _ ↦ homOfLE le_top) hcov.ge (fun x ↦ (D.map (v ≫ fj x)).app (U x) (t x)) fun x y ↦ by
      dsimp [TopologicalSpace.Opens.infLELeft, TopologicalSpace.Opens.infLERight]
      simpa [← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE, -Scheme.Hom.comp_appLE]
        using hv x y _ inf_le_left inf_le_right
  replace ht₀ (x : σ) : t₀ |_ (D.map (v ≫ fj x) ⁻¹ᵁ U x) = (D.map (v ≫ fj x)).app (U x) (t x) :=
    ht₀ x
  refine ⟨k, t₀, TopCat.Sheaf.eq_of_locally_eq' ⟨_, c.pt.IsSheaf⟩
    (fun x : σ ↦ c.π.app (i x) ⁻¹ᵁ U x) ⊤ (fun _ ↦ homOfLE le_top) ?_ _ _ fun x ↦ ?_⟩
  · simpa only [H] using ((c.π.app k).iSup_preimage_eq_top hcov).ge
  refine (ht x _ le_rfl).symm.trans (Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _))
  have key := congr((c.π.app k).appLE _ (c.π.app (i x) ⁻¹ᵁ U x) (H x).le $(ht₀ x))
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, ← ConcreteCategory.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Cone.w] at key
  exact key.symm

include hc in
lemma nonempty_isColimit_Γ_mapCocone [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] :
    Nonempty (IsColimit (Scheme.Γ.mapCocone c.op)) := by
  have : ReflectsFilteredColimits (forget CommRingCat) :=
    ⟨fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms⟩
  refine ReflectsColimit.reflects (F := forget _) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · exact fun s ↦ ⟨.op _, (exists_appTop_π_eq_of_isLimit D c hc s).choose_spec⟩
  · exact fun i s t e ↦ ⟨_, Quiver.Hom.op _,
      (exists_app_map_eq_map_of_isLimit _ _ hc isCompact_univ s t e).choose_spec.choose_spec⟩

instance [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] :
    PreservesLimit D Scheme.Γ.rightOp :=
  have : PreservesColimit D.op Scheme.Γ := ⟨fun hc ↦ nonempty_isColimit_Γ_mapCocone D _ hc.unop⟩
  preservesLimit_rightOp _ _

end sections

section IsAffine

include hc in
/-- Suppose `{ Xᵢ }` is an inverse system of qcqs schemes with affine transition maps.
If `lim Xᵢ` is quasi-affine, then some `Xᵢ` is quasi-affine. -/
@[stacks 01Z5]
lemma Scheme.exists_isQuasiAffine_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    [IsQuasiAffine c.pt] :
    ∃ i, IsQuasiAffine (D.obj i) := by
  classical
  have (x : c.pt) : ∃ (i : I) (f : Γ(D.obj i, ⊤)),
      IsAffineOpen (Scheme.basicOpen _ f) ∧ c.π.app i x ∈ (Scheme.basicOpen _ f) := by
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (c.π.app i x)) isOpen_univ
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, hrU⟩ :=
      (IsQuasiAffine.isBasis_basicOpen c.pt).exists_subset_of_mem_open hxU (c.π.app i ⁻¹ᵁ U).isOpen
    obtain ⟨j, r, rfl⟩ := exists_appTop_π_eq_of_isLimit D c hc r
    obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨l, flk, hl⟩ := exists_map_preimage_le_map_preimage D c hc (isCompact_basicOpen _
      isCompact_univ ((D.map fkj).appTop r)) (V := D.map fki ⁻¹ᵁ U) (by
        rwa [← preimage_basicOpen_top, ← Hom.comp_preimage, ← Hom.comp_preimage,
          c.w, c.w, preimage_basicOpen_top])
    refine ⟨l, (D.map (flk ≫ fkj)).appTop r, ?_, ?_⟩
    · convert!
      (hU.preimage (D.map (flk ≫ fki))).basicOpen
        ((D.obj _).presheaf.map (homOfLE le_top).op ((D.map (flk ≫ fkj)).appTop r)) using 1
      rwa [Scheme.basicOpen_res, eq_comm, inf_eq_right, Functor.map_comp,
        elementwise_of% Scheme.Hom.comp_appTop, ← Scheme.preimage_basicOpen_top, Functor.map_comp,
        Scheme.Hom.comp_preimage]
    · change x ∈ c.π.app l ⁻¹ᵁ (D.obj l).basicOpen _
      rwa [Scheme.preimage_basicOpen_top, ← elementwise_of% Scheme.Hom.comp_appTop, Cone.w]
  choose i f hf hi using this
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover
    (fun x ↦ (((c.π.app (i x)) ⁻¹ᵁ (D.obj (i x)).basicOpen (f x)).1))
    (fun x ↦ ((c.π.app (i x)) ⁻¹ᵁ (D.obj (i x)).basicOpen (f x)).2.mem_nhds (by exact hi x))
  choose σi hσiσ hσi using fun x ↦ Set.mem_iUnion₂.mp (hσ.ge (Set.mem_univ x))
  obtain ⟨j, fj⟩ := IsCofiltered.inf_objs_exists (σ.image i)
  replace fj := fun i h ↦ (@fj i h).some
  obtain ⟨k, fkj, hk⟩ := exists_map_eq_top D c hc
    (⨆ k, D.map (fj _ (Finset.mem_image_of_mem i (hσiσ k))) ⁻¹ᵁ (D.obj (i _)).basicOpen (f _)) (by
      refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, ?_⟩
      change (c.π.app j ≫ D.map _).base x ∈ (D.obj (i (σi x))).basicOpen (f (σi x))
      rw [Cone.w]
      exact hσi _)
  refine ⟨k, .of_forall_exists_mem_basicOpen _ fun x ↦ ?_⟩
  obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp (hk.ge (Set.mem_univ x))
  use (D.map fkj).appTop ((D.map (fj _ (Finset.mem_image_of_mem i (hσiσ y)))).appTop (f _))
  rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top]
  exact ⟨((hf _).preimage _).preimage _, hy⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/-- Suppose `{ Xᵢ }` is an inverse system of qcqs schemes with affine transition maps.
If `lim Xᵢ` is affine, then some `Xᵢ` is affine. -/
@[stacks 01Z6]
lemma Scheme.exists_isAffine_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    [IsAffine c.pt] :
    ∃ i, IsAffine (D.obj i) := by
  have := isAffineHom_π_app _ _ hc
  obtain ⟨i, hi⟩ := Scheme.exists_isQuasiAffine_of_isLimit D c hc
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom ((D ⋙ Γ.rightOp ⋙ Scheme.Spec).map f) := by
    dsimp; infer_instance
  have (j : _) : CompactSpace ((D ⋙ Γ.rightOp ⋙ Scheme.Spec).obj j) := by dsimp; infer_instance
  obtain ⟨j, fij, hj⟩ := exists_map_eq_top _ _
    (isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc) (D.obj i).toSpecΓ.opensRange
    ((preimage_opensRange_toSpecΓ (X := c.pt) (c.π.app i)).trans
      (by simp [Hom.opensRange_of_isIso]))
  have := IsQuasiAffine.of_isAffineHom (D.map fij)
  exact ⟨j, ⟨isIso_of_isOpenImmersion_of_opensRange_eq_top _
    ((preimage_opensRange_toSpecΓ (D.map fij)).symm.trans hj)⟩⟩

set_option backward.defeqAttrib.useBackward true in
include hc in
@[stacks 01Z4 "(1)"]
lemma exists_isAffineOpen_preimage_eq
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, QuasiSeparatedSpace (D.obj i)]
    (U : c.pt.Opens) (hU : IsAffineOpen U) :
    ∃ (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧ c.π.app i ⁻¹ᵁ V = U := by
  obtain ⟨i, U, hU', rfl⟩ := exists_preimage_eq D c hc U hU.isCompact
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU')
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i U).pt := hU
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i U)
  exact ⟨_, _, hj, by simp [← Scheme.Hom.comp_preimage]⟩

open TopologicalSpace in
include hc in
lemma Scheme.exists_isOpenCover_and_isAffine_of_finite [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    {J : Type*} [Finite J] (U : J → c.pt.Opens) (hU : IsOpenCover U)
    (hU' : ∀ i, IsAffineOpen (U i)) :
    ∃ (i : I) (V : J → (D.obj i).Opens),
      IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  classical
  choose j V hV hVU using fun k ↦ exists_isAffineOpen_preimage_eq D c hc (U k) (hU' k)
  obtain ⟨i, ⟨fi⟩⟩ := IsCofiltered.exists_hom_forall j
  obtain ⟨k, fkj, e⟩ := exists_map_eq_top D c hc (⨆ (k), D.map (fi k) ⁻¹ᵁ V k) (by
    simp_rw [Hom.preimage_iSup, ← Hom.comp_preimage, c.w, hVU]
    exact hU)
  refine ⟨k, fun x ↦ D.map (fkj ≫ fi x) ⁻¹ᵁ V _, ?_, fun k ↦ ⟨(hV k).preimage _, ?_⟩⟩
  · refine top_le_iff.mp (e.symm.trans_le ?_)
    simp_rw [Hom.preimage_iSup, ← Hom.comp_preimage, ← D.map_comp]
    simp
  · rw [← hVU, ← Hom.comp_preimage, c.w]

open TopologicalSpace in
include hc in
/-- Suppose `{ Xᵢ }` is an inverse system of qcqs schemes with affine transition maps.
Then any affine open cover of `lim Xᵢ` comes from a finite level. -/
lemma Scheme.exists_isOpenCover_and_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    {J : Type*} (U : J → c.pt.Opens) (hU : IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    ∃ (i : I) (s : Finset J) (V : s → (D.obj i).Opens),
      IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by
  have := compactSpace_of_isLimit D c hc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _
    (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  have hU : IsOpenCover fun j : s ↦ U ↑j := by
    simpa only [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe, Opens.coe_top, Opens.iSup_mk,
      Opens.carrier_eq_coe, Opens.coe_mk, Set.iUnion_subtype]
  obtain ⟨i, V, hV, heq⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite _ _ hc _ hU (hU' ·)
  use i, s, V, hV

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/-- Variant of `Scheme.exists_isOpenCover_and_isAffine_of_finite` in terms of `Scheme.OpenCover`. -/
lemma Scheme.OpenCover.exists_of_isCofiltered_of_finite [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    (𝒰 : OpenCover.{w} c.pt) [∀ i, IsAffine (𝒰.X i)] [Finite 𝒰.I₀] :
    ∃ (i : I) (R : 𝒰.I₀ → CommRingCat.{u}) (f : ∀ (a : 𝒰.I₀), Spec (R a) ⟶ (D.obj i))
      (_ : Presieve.ofArrows _ f ∈ zariskiPrecoverage _) (g : ∀ (j : 𝒰.I₀), 𝒰.X j ⟶ Spec (R j)),
      ∀ (j : 𝒰.I₀), IsPullback (g j) (𝒰.f j) (f j) (c.π.app i) := by
  obtain ⟨i, V, hV, hV'⟩ := Scheme.exists_isOpenCover_and_isAffine_of_finite _ _ hc _
    𝒰.isOpenCover_opensRange fun k ↦ isAffineOpen_opensRange (𝒰.f k)
  have hV'' (k) := dsimp% congr($((hV' k).right).carrier)
  refine ⟨i, fun k ↦ Γ(_, V k), fun k ↦ (hV' k).left.isoSpec.inv ≫ (V k).ι, ?_, ?_, ?_⟩
  · simp only [IsAffineOpen.isoSpec_inv_ι, ofArrows_mem_precoverage_iff,
      IsAffineOpen.range_fromSpec, SetLike.mem_coe]
    exact ⟨fun x ↦ hV.exists_mem x, inferInstance⟩
  · intro k
    exact IsOpenImmersion.lift (V k).ι (𝒰.f _ ≫ c.π.app i) (by simp [hV'', Set.range_comp]) ≫
      (hV' k).left.isoSpec.hom
  · intro k
    dsimp
    refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · simp [← IsAffineOpen.isoSpec_inv_ι]
    · intro s
      refine IsOpenImmersion.lift (𝒰.f k) s.snd ?_
      simp only [hV'', Set.range_subset_iff, Set.mem_preimage, SetLike.mem_coe]
      intro y
      rw [← Scheme.Hom.comp_apply, ← s.condition]
      simp [← IsAffineOpen.isoSpec_inv_ι]
    · simp [← cancel_mono (hV' _).left.isoSpec.inv, ← cancel_mono (V k).ι, PullbackCone.condition]
    · simp
    · simp [← cancel_mono (𝒰.f k)]

end IsAffine

section LocallyOfFinitePresentation

variable [IsCofiltered I] (a : c.pt ⟶ X)
  (ha : c.π ≫ t = (Functor.const _).map (a ≫ f))

private lemma Scheme.exists_appTop_eq {Y Z : Scheme.{u}} [IsAffine Z] (φ : Γ(Z, ⊤) ⟶ Γ(Y, ⊤)) :
    ∃ g : Y ⟶ Z, g.appTop = φ := by
  have h : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ, Scheme.Hom.id_appTop]
  refine ⟨Y.toSpecΓ ≫ Spec.map φ ≫ Z.isoSpec.inv, ?_⟩
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, h, Scheme.toSpecΓ_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

include hc ha in
/-- See `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` for the general case. -/
private nonrec lemma Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine
    [LocallyOfFinitePresentation f] [IsAffine S] [IsAffine X] [∀ i, IsAffine (D.obj i)] :
    ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = t.app i := by
  -- Every scheme involved is affine, so the proof is merely translate to commutative algebra and
  -- use `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`.
  have : ∀ i, IsAffine (D.op.obj i).unop := fun i ↦ by dsimp; infer_instance
  let α : (Functor.const Iᵒᵖ).obj Γ(S, ⊤) ⟶ D.op ⋙ Scheme.Γ :=
    { app := fun i ↦ (t.app i.unop).appTop
      naturality := fun _ _ u ↦ by
        have h := congr(Scheme.Hom.appTop $(t.naturality u.unop))
        simp only [Scheme.Hom.comp_appTop, Functor.const_obj_map, Scheme.Hom.id_appTop] at h ⊢
        exact h.symm }
  obtain ⟨i, φ, hφ, hφ'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    Γ(S, ⊤) (D.op ⋙ Scheme.Γ) α f.appTop _ (isColimitOfPreserves Scheme.Γ hc.op)
    (HasRingHomProperty.iff_of_isAffine.mp ‹LocallyOfFinitePresentation f›) a.appTop fun i ↦ by
      simpa [α] using congr(Scheme.Hom.appTop $(congr(($ha).app i.unop))).symm
  obtain ⟨g, rfl⟩ := Scheme.exists_appTop_eq φ
  exact ⟨i.unop, g, ext_of_isAffine (by simpa using hφ'.symm),
    ext_of_isAffine (by simpa [α] using hφ)⟩

open TopologicalSpace in
private lemma isBasis_affineOpens_le_preimage {Y Z T : Scheme.{u}} (a : Y ⟶ Z) (g : Z ⟶ T) :
    Opens.IsBasis {U : Y.Opens | IsAffineOpen U ∧ ∃ (V : Z.affineOpens) (W : T.affineOpens),
      U ≤ a ⁻¹ᵁ (V : Z.Opens) ∧ (V : Z.Opens) ≤ g ⁻¹ᵁ (W : T.Opens)} := by
  refine Opens.isBasis_iff_nbhd.mpr fun {O y} hy ↦ ?_
  obtain ⟨W, hW, hyW, -⟩ := Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (U := ⊤) (x := g (a y)) trivial
  obtain ⟨V, hV, hyV, hVW⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (U := g ⁻¹ᵁ W) (x := a y) hyW
  obtain ⟨U, hU, hyU, hUV⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := O ⊓ a ⁻¹ᵁ V) (x := y) ⟨hy, hyV⟩
  exact ⟨U, ⟨hU, ⟨V, hV⟩, ⟨W, hW⟩, hUV.trans inf_le_right, hVW⟩, hyU, hUV.trans inf_le_left⟩

variable [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc ha in
private lemma exists_forall_resLE_comp_eq_of_isAffineOpen [LocallyOfFinitePresentation f]
    {i : I} {J : Type*} [Finite J] {U : J → (D.obj i).Opens} (hU : ∀ j, IsAffineOpen (U j))
    (hUV : ∀ j, ∃ (V : X.affineOpens) (W : S.affineOpens),
      c.π.app i ⁻¹ᵁ U j ≤ a ⁻¹ᵁ (V : X.Opens) ∧ (V : X.Opens) ≤ f ⁻¹ᵁ (W : S.Opens)) :
    ∃ (k : I) (u : k ⟶ i), ∀ j, ∃ g : ↑(D.map u ⁻¹ᵁ U j) ⟶ X,
      g ≫ f = (D.map u ⁻¹ᵁ U j).ι ≫ t.app k ∧
        ∀ (O : c.pt.Opens) (h : O ≤ c.π.app k ⁻¹ᵁ D.map u ⁻¹ᵁ U j),
          (c.π.app k).resLE _ O h ≫ g = O.ι ≫ a := by
  have hnat {j k : I} (v : j ⟶ k) : D.map v ≫ t.app k = t.app j := by simp
  have hπ (j : I) : c.π.app j ≫ t.app j = a ≫ f := congr(($ha).app j)
  choose V W hUV hVW using hUV
  refine IsCofiltered.exists_forall _ ?_ fun j ↦ ?_
  · rintro k₁ k₂ v u j ⟨g, hg, hg'⟩
    have e : D.map (v ≫ u) ⁻¹ᵁ U j ≤ D.map v ⁻¹ᵁ D.map u ⁻¹ᵁ U j := by simp
    exact ⟨(D.map v).resLE _ _ e ≫ g, by simpa using congr((D.map v).resLE _ _ e ≫ $hg),
      fun O h ↦ by simpa [Scheme.Hom.resLE_comp_resLE_assoc] using hg' O (by simpa using h)⟩
  obtain ⟨i', u, hu⟩ := exists_map_preimage_le_map_preimage D c hc (hU j).isCompact
    (V := t.app i ⁻¹ᵁ (W j : S.Opens)) (by
      rw [← Scheme.Hom.comp_preimage, hπ, Scheme.Hom.comp_preimage]
      exact (hUV j).trans (a.preimage_mono (hVW j)))
  replace hu : D.map u ⁻¹ᵁ U j ≤ t.app i' ⁻¹ᵁ (W j : S.Opens) :=
    hu.trans_eq (by rw [← Scheme.Hom.comp_preimage, hnat])
  have _ (k : Over i') : IsAffine ((opensDiagram D i' (D.map u ⁻¹ᵁ U j)).obj k) :=
    ((hU j).preimage _).preimage _
  let τ : opensDiagram D i' (D.map u ⁻¹ᵁ U j) ⟶ (Functor.const (Over i')).obj (W j) :=
    { app k := (t.app k.left).resLE _ _ ((Scheme.Hom.preimage_mono _ hu).trans_eq
        (by rw [← Scheme.Hom.comp_preimage, hnat]))
      naturality k l v := ((D.map v.left).resLE_comp_resLE _ (t.app l.left) _).trans
        (Eq.trans ((cancel_mono (W j : S.Opens).ι).mp (by simp [hnat]))
          (Category.comp_id _).symm) }
  obtain ⟨k, g, hg, hg'⟩ :
      ∃ (k : Over i') (g : (D.map k.hom ⁻¹ᵁ D.map u ⁻¹ᵁ U j).toScheme ⟶ (V j : X.Opens).toScheme),
        (c.π.app k.left).resLE _ (c.π.app i' ⁻¹ᵁ D.map u ⁻¹ᵁ U j) (by simp) ≫ g =
            a.resLE _ _ (by simpa using hUV j) ∧ g ≫ f.resLE _ _ (hVW j) = τ.app k :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine
      _ τ (f.resLE _ _ (hVW j)) _ (isLimitOpensCone D c hc i' _)
      (a.resLE _ _ (by simpa using hUV j)) (by
        ext k
        exact ((c.π.app k.left).resLE_comp_resLE _ (t.app k.left) _).trans
          (Eq.trans ((cancel_mono (W j : S.Opens).ι).mp (by simp [hπ]))
            (a.resLE_comp_resLE _ f _).symm))
  have e : D.map (k.hom ≫ u) ⁻¹ᵁ U j ≤ D.map k.hom ⁻¹ᵁ D.map u ⁻¹ᵁ U j := by simp
  refine ⟨k.left, k.hom ≫ u, Scheme.homOfLE _ e ≫ g ≫ (V j : X.Opens).ι, ?_, fun O h ↦ ?_⟩
  · simpa [τ] using congr(Scheme.homOfLE _ e ≫ $hg' ≫ (W j : S.Opens).ι)
  · have h' : O ≤ c.π.app i' ⁻¹ᵁ D.map u ⁻¹ᵁ U j := by simpa using h
    simpa using congr(Scheme.homOfLE _ h' ≫ $hg ≫ (V j : X.Opens).ι)

variable [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc ha in
private lemma exists_forall_homOfLE_comp_eq_of_isAffineOpen [LocallyOfFinitePresentation f]
    {i : I} {J : Type*} [Finite J] {U : J → (D.obj i).Opens} (hU : ∀ j, IsAffineOpen (U j))
    (hUV : ∀ j, ∃ (V : X.affineOpens) (W : S.affineOpens),
      c.π.app i ⁻¹ᵁ U j ≤ a ⁻¹ᵁ (V : X.Opens) ∧ (V : X.Opens) ≤ f ⁻¹ᵁ (W : S.Opens)) :
    ∃ (k : I) (u : k ⟶ i) (g : ∀ j, ↑(D.map u ⁻¹ᵁ U j) ⟶ X),
      (∀ j, g j ≫ f = (D.map u ⁻¹ᵁ U j).ι ≫ t.app k) ∧
      (∀ j (O : c.pt.Opens) (h : O ≤ c.π.app k ⁻¹ᵁ D.map u ⁻¹ᵁ U j),
        (c.π.app k).resLE _ O h ≫ g j = O.ι ≫ a) ∧
      ∀ j₁ j₂ (O : (D.obj k).Opens) (e₁ : O ≤ D.map u ⁻¹ᵁ U j₁) (e₂ : O ≤ D.map u ⁻¹ᵁ U j₂),
        Scheme.homOfLE _ e₁ ≫ g j₁ = Scheme.homOfLE _ e₂ ≫ g j₂ := by
  choose k u g hg hg' using exists_forall_resLE_comp_eq_of_isAffineOpen D t f c hc a ha hU hUV
  obtain ⟨l, v, hl⟩ : ∃ (l : I) (v : l ⟶ k), ∀ j₁ j₂ (O : (D.obj l).Opens)
      (e₁ : O ≤ D.map v ⁻¹ᵁ D.map u ⁻¹ᵁ U j₁) (e₂ : O ≤ D.map v ⁻¹ᵁ D.map u ⁻¹ᵁ U j₂),
        (D.map v).resLE _ O e₁ ≫ g j₁ = (D.map v).resLE _ O e₂ ≫ g j₂ := by
    refine IsCofiltered.exists_forall₂ _ ?_ fun j₁ j₂ ↦ ?_
    · exact fun w v j₁ j₂ hv O e₁ e₂ ↦ by
        simpa [Scheme.Hom.resLE_comp_resLE_assoc] using congr((D.map w).resLE _ O
          (show O ≤ D.map w ⁻¹ᵁ _ by simpa [Scheme.Hom.preimage_inf] using le_inf e₁ e₂) ≫
            $(hv _ inf_le_left inf_le_right))
    have hcpt : IsCompact (X := D.obj k) ↑(D.map u ⁻¹ᵁ U j₁ ⊓ D.map u ⁻¹ᵁ U j₂) :=
      ((hU j₁).preimage (D.map u)).isCompact.inter_of_isOpen
        ((hU j₂).preimage (D.map u)).isCompact (D.map u ⁻¹ᵁ U j₁).2 (D.map u ⁻¹ᵁ U j₂).2
    obtain ⟨l, v, e⟩ := Scheme.exists_resLE_comp_eq_resLE_comp_of_locallyOfFiniteType D t f c hc
      hcpt (Scheme.homOfLE _ inf_le_left ≫ g j₁) (Scheme.homOfLE _ inf_le_right ≫ g j₂)
      (by simp [hg]) (by simp [hg])
      (by rw [Scheme.Hom.resLE_map_assoc, Scheme.Hom.resLE_map_assoc]
          exact (hg' j₁ _ _).trans (hg' j₂ _ _).symm)
    exact ⟨l, v, fun O e₁ e₂ ↦ by
      simpa using congr(Scheme.homOfLE _ (show O ≤ D.map v ⁻¹ᵁ _ by
        simpa [Scheme.Hom.preimage_inf] using le_inf e₁ e₂) ≫ $e)⟩
  have e (j : J) : D.map (v ≫ u) ⁻¹ᵁ U j ≤ D.map v ⁻¹ᵁ D.map u ⁻¹ᵁ U j := by simp
  refine ⟨l, v ≫ u, fun j ↦ (D.map v).resLE _ _ (e j) ≫ g j, fun j ↦ ?_, fun j O h ↦ ?_,
    fun j₁ j₂ O e₁ e₂ ↦ ?_⟩
  · simpa using congr((D.map v).resLE _ _ (e j) ≫ $(hg j))
  · simpa [Scheme.Hom.resLE_comp_resLE_assoc] using hg' j O (by simpa using h)
  · simpa using hl j₁ j₂ O (by simpa using e₁) (by simpa using e₂)

open TopologicalSpace in
include hc ha in
/--
Given a cofiltered diagram of qcqs schemes `Dᵢ` over `S` with affine transition maps.
If `X` is locally of finite presentation over `S`, then any `S`-morphism `lim Dᵢ ⟶ X` factors
through some `lim Dᵢ ⟶ Dⱼ ⟶ X` for some `j`.
-/
lemma Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    [LocallyOfFinitePresentation f] [∀ i, CompactSpace (D.obj i)] :
    ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = t.app i := by
  -- The open cover of `c := lim Dᵢ` by the affine opens `U ⊆ c` such that `U` maps into an affine
  -- `V ⊆ X` which in turn maps into an affine `W ⊆ S`.
  have h𝒰 := (isBasis_affineOpens_le_preimage a f).isOpenCover
  obtain ⟨i, s, 𝒱, h𝒱, h𝒱𝒰⟩ := Scheme.exists_isOpenCover_and_isAffine D c hc _ h𝒰 fun U ↦ U.2.1
  -- Each `𝒱 j` factors after passing to some `l`, compatibly on overlaps.
  obtain ⟨l, u, g, hg, hπg, hglue⟩ := exists_forall_homOfLE_comp_eq_of_isAffineOpen D t f c hc a ha
    (fun j ↦ (h𝒱𝒰 j).1) fun j ↦ (h𝒱𝒰 j).2 ▸ j.1.2.2
  -- We may glue the morphisms into `Dₗ ⟶ X` and verify that it indeed satisfies the hypothesis.
  have h𝒲 : IsOpenCover (D.map u ⁻¹ᵁ 𝒱 ·) := .mk ((D.map u).iSup_preimage_eq_top h𝒱)
  let F := (Scheme.openCoverOfIsOpenCover _ _ h𝒲).glueMorphisms g fun j₁ j₂ ↦ by
    show pullback.fst (D.map u ⁻¹ᵁ 𝒱 j₁).ι (D.map u ⁻¹ᵁ 𝒱 j₂).ι ≫ _ = pullback.snd _ _ ≫ _
    rw [← cancel_epi (isPullback_opens_inf _ _).isoPullback.hom]
    simpa using hglue j₁ j₂ _ inf_le_left inf_le_right
  have hF (j : s) : (D.map u ⁻¹ᵁ 𝒱 j).ι ≫ F = g j := Scheme.Cover.ι_glueMorphisms ..
  refine ⟨l, F, Scheme.hom_ext_of_isOpenCover (.mk ((c.π.app l).iSup_preimage_eq_top h𝒲)) _ _
      fun j ↦ ?_, Scheme.hom_ext_of_isOpenCover h𝒲 _ _ fun j ↦ ?_⟩
  · rw [← Hom.resLE_comp_ι_assoc (c.π.app l) le_rfl, hF]
    exact hπg j _ _
  · simp [reassoc_of% hF, hg]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Hom_S(-, X)` sends a cofiltered limit of qcqs `S`-schemes with affine transition maps
to a filtered colimit if `X` is locally of finite presentation over `X`. -/
instance Scheme.preservesColimit_yoneda (D : I ⥤ Over S)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ (i : I), CompactSpace (D.obj i).left] [∀ (i : I), QuasiSeparatedSpace (D.obj i).left]
    (X : Over S) [LocallyOfFinitePresentation X.hom] :
    PreservesColimit D.op (yoneda.obj X) where
  preserves {c hc} := by
    rw [Limits.Types.isColimit_iff_coconeTypesIsColimit]
    have (i : I) : CompactSpace ((D ⋙ Over.forget S).obj i) := by dsimp; infer_instance
    have (i : I) : QuasiSeparatedSpace ((D ⋙ Over.forget S).obj i) := by dsimp; infer_instance
    have {i j : I} (f : i ⟶ j) : IsAffineHom ((D ⋙ Over.forget S).map f) := by
      dsimp; infer_instance
    refine ⟨⟨?_, ?_⟩⟩
    · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered']
      intro k g₁ g₂ hg
      obtain ⟨k, hik, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
        (D ⋙ Over.forget _) (.mk (fun _ ↦ (D.obj _).hom)) X.hom _ (isLimitOfPreserves _ hc.unop)
        g₁.left g₂.left (Over.w g₁).symm (Over.w g₂).symm congr($(hg).left)
      use .op k, hik.op
      cat_disch
    · intro g
      obtain ⟨k, u, h, h'⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
        (D ⋙ Over.forget _) (.mk (fun _ ↦ (D.obj _).hom)) X.hom _ (isLimitOfPreserves _ hc.unop)
        g.left (by ext; simp)
      use Functor.ιColimitType _ (.op k) (Over.homMk u)
      cat_disch

end LocallyOfFinitePresentation

end AlgebraicGeometry
