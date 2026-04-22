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
public import Mathlib.CategoryTheory.Monad.Limits

/-!

# Inverse limits of schemes with affine transition maps

In this file, we develop API for inverse limits of schemes with affine transition maps,
following EGA IV 8 and https://stacks.math.columbia.edu/tag/01YT.

-/

@[expose] public section

universe uI u

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
set_option backward.isDefEq.respectTransparency false in
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
  haveI {i j} (f : i ⟶ j) : IsAffineHom (D'.map f) := by
    suffices IsAffineHom (D'.map f ≫ ι.app j) from .of_comp _ (ι.app j)
    simp only [subschemeMap_subschemeι, D', ι]
    infer_instance
  haveI _ (i) : Nonempty (D'.obj i) := Set.nonempty_coe_sort.mpr (hZne i)
  haveI _ (i) : CompactSpace (D'.obj i) := isCompact_iff_compactSpace.mp (hZcpt i)
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
  simpa [Over.forall_iff] using exists_mem_of_isClosed_of_nonempty (Over.forget j ⋙ D) _
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

attribute [local simp] Scheme.Hom.resLE_comp_resLE

set_option backward.isDefEq.respectTransparency false in
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
  convert ((hV.image_of_isOpenImmersion (D.map k.hom ⁻¹ᵁ U).ι).preimage
    (D.map f.left)).preimage_of_isOpenImmersion (D.map j.hom ⁻¹ᵁ U).ι ?_
  · ext x
    change _ ∈ V ↔ _
    refine ⟨fun h ↦ ⟨⟨(D.map f.left).base x.1, ?_⟩, ?_, rfl⟩, ?_⟩
    · change (D.map f.left ≫ D.map k.hom).base x.1 ∈ U
      rw [← D.map_comp, Over.w f]
      exact x.2
    · convert h
      exact Subtype.ext (by simp)
    · rintro ⟨⟨_, hU⟩, hV, rfl⟩
      convert hV
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
set_option backward.isDefEq.respectTransparency false in
open Scheme.Opens in
include hc in
lemma isBasis_preimage_isAffineOpen [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : I) (V : (D.obj i).Opens) (_ : IsAffineOpen V) } := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (c.π.app i x)) isOpen_univ
  have (j : _) : IsAffine ((opensDiagram D i V).op.obj j).unop := hV.preimage _
  have (j : _) : IsAffine ((opensDiagram D i V).obj j) := hV.preimage _
  obtain ⟨r, hrU, hxr⟩ := IsAffineOpen.exists_basicOpen_le
    (Scheme.isAffine_of_isLimit _ (isLimitOpensCone D c hc i V)) (V := U) ⟨x, hxU⟩ hxV
  obtain ⟨⟨j⟩, s, hs⟩ := (Types.jointly_surjective_of_isColimit (isColimitOfPreserves
    (Scheme.Γ ⋙ forget _) (isLimitOpensCone D c hc i V).op) ((c.π.app i ⁻¹ᵁ V).topIso.inv r))
  obtain ⟨s, rfl⟩ := (D.map j.hom ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.surjective s
  have h : c.π.app j.left ⁻¹ᵁ D.map j.hom ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V := congr($(c.w j.hom) ⁻¹ᵁ V)
  have : r = (c.π.app j.left).appLE (D.map j.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) h.ge s := by
    convert show r = ((topIso _).inv ≫ ((opensCone D c i V).π.app j).appTop ≫ (topIso _).hom) s
      from (c.π.app i ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp hs.symm using 3
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  refine ⟨_, ⟨j.left, _, (hV.preimage _).basicOpen s, rfl⟩, ?_⟩
  simp only [Functor.const_obj_obj, Scheme.preimage_basicOpen] at this ⊢
  rw [← c.pt.basicOpen_res_eq _ (eqToHom h.symm).op, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, ← this]
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
  obtain ⟨j, fj⟩ := IsCofiltered.inf_objs_exists (hsf.toFinset.attach.image
    fun x ↦ i ⟨x.1, (by simpa only [Set.Finite.mem_toFinset] using x.2)⟩:)
  replace fj : ∀ b : s, j ⟶ i b := fun b ↦ (@fj (i b) (by simpa using ⟨b.1, b.2, rfl⟩)).some
  refine ⟨j, ⨆ (k : s), D.map (fj _) ⁻¹ᵁ V k, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk]
    exact isCompact_iUnion fun i ↦ ((hV i).preimage _).isCompact
  · simp [-TopologicalSpace.Opens.iSup_mk, Scheme.Hom.preimage_iSup,
      ← Scheme.Hom.comp_preimage, c.w, hVi, sSup_eq_iSup']

end Opens

set_option backward.isDefEq.respectTransparency false in
include hc in
lemma isAffineHom_π_app [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] (i : I) :
    IsAffineHom (c.π.app i) where
  isAffine_preimage U hU := have (j : _) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage _
    Scheme.isAffine_of_isLimit _ (isLimitOpensCone D c hc i U)

set_option backward.isDefEq.respectTransparency false in
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
  · simpa using this (a ≫ X.isoSpec.hom) (b ≫ X.isoSpec.hom) (by simp [hab]) (X.isoSpec.inv ≫ f)
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
    simpa using this
  obtain ⟨D, rfl⟩ := hD
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  let e : ((Functor.const Iᵒᵖ).obj R).rightOp ⋙ Scheme.Spec ≅ (Functor.const I).obj (Spec R) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp)
  obtain ⟨t, rfl⟩ : ∃ t' : (Functor.const Iᵒᵖ).obj R ⟶ D.leftOp,
      t = Functor.whiskerRight (NatTrans.rightOp t') Scheme.Spec ≫ e.hom :=
    ⟨⟨fun i ↦ Spec.preimage (t.app i.unop), fun _ _ f ↦ Spec.map_injective
      (by simpa using (t.naturality f.unop).symm)⟩, by ext : 2; simp [e]⟩
  have := monadicCreatesLimits Scheme.Spec
  obtain ⟨k, hik, hjk, H⟩ := (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType (Spec.map φ)›)
    |>.essFiniteType.exists_comp_map_eq_of_isColimit _ D.leftOp t _
    (coconeLeftOpOfCone (liftLimit hc))
    (isColimitCoconeLeftOpOfCone _ (liftedLimitIsLimit _))
    a (Spec.map_injective (by simpa using ha.symm))
    b (Spec.map_injective (by simpa using hb.symm))
    (Spec.map_injective (by
      simp only [coconeLeftOpOfCone_pt, Functor.const_obj_obj,
        Functor.leftOp_obj, coconeLeftOpOfCone_ι_app, Spec.map_comp]
      simp only [← Scheme.Spec_map, ← liftedLimitMapsToOriginal_hom_π, Category.assoc, hab]))
  exact ⟨k.unop, hik.unop, hjk.unop, by simpa [← Spec.map_comp, Spec.map_inj] using H⟩

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
  simpa [ExistsHomHomCompEqCompAux.hii', g] using A.exists_index.choose_spec.choose_spec

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
      simpa [Scheme.Cover.pullbackHom, g, ← H₁, ← H₂, -Cone.w, -Cone.w_assoc] using H₃)
  refine ⟨k.left, k.hom, ?_⟩
  simpa [← cancel_mono ((A.𝒰X j.1.1).f j.1.2), ← cancel_mono (pullback.fst f (A.𝒰S.f j.1.1)),
    Scheme.Cover.pullbackHom, g, ← H₁, ← H₂, pullback.condition_assoc] using H

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
set_option backward.isDefEq.respectTransparency false in
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
lemma exists_appTop_map_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} [CompactSpace (D.obj i)] (s : Γ(D.obj i, ⊤)) (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).appTop s = 0 := by
  classical
  have (x : D.obj i) : ∃ (U : (D.obj i).Opens) (hU : IsAffineOpen U)
      (hU : x ∈ U) (j : I) (f : j ⟶ i), (D.map f).app U (s |_ U) = 0 := by
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
      (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
    obtain ⟨j, f, hj⟩ := exists_appTop_map_eq_zero_of_isAffine_of_isLimit _ _
      (isLimitOpensCone D c hc i U) (.mk (𝟙 i)) (((opensDiagramι D i U).app _).appTop s) (by
        convert congr((c.pt.presheaf.map (homOfLE le_top).op).hom $hs) using 1
        · simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE, ← ConcreteCategory.comp_apply]; rfl
        · simp)
    refine ⟨U, hU, hxU, j.left, j.hom, ?_⟩
    have hf : f.left = j.hom := by simpa using Over.w f
    let t' : Γ(D.map j.hom ⁻¹ᵁ U, ⊤) ⟶ Γ(D.obj j.left, D.map j.hom ⁻¹ᵁ U) :=
      (D.obj _).presheaf.map (eqToHom ((D.map j.hom ⁻¹ᵁ U).ι_image_top.symm)).op
    convert congr(t' $hj)
    · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp only [Scheme.Hom.app_eq_appLE, homOfLE_leOfHom, ← ConcreteCategory.comp_apply, hf,
        Scheme.Hom.map_appLE, TopologicalSpace.Opens.map_top, Scheme.Hom.resLE_appLE]
      simp [t']
    · simp
  choose U hU hxU j f H using this
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (U ·) (fun x ↦ (U x).2.mem_nhds (hxU x))
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists (insert i <| t.image j) (by
    exact t.attach.image fun x ↦ ⟨j x.1, i, Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ x.2), by simp, f x.1⟩)
  refine ⟨k, fk (by simp), ?_⟩
  apply (D.obj k).IsSheaf.section_ext
  rintro x -
  obtain ⟨l, hl, hlU⟩ := Set.mem_iUnion₂.mp (ht.ge (Set.mem_univ ((D.map (fk (by simp))).base x)))
  refine ⟨D.map (fk (by simp)) ⁻¹ᵁ U l, le_top, hlU, ?_⟩
  dsimp
  simp only [homOfLE_leOfHom, map_zero]
  have h₁ : fk (by simp) = fk (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hl)) ≫ f l :=
    (hk _ (by simp) (Finset.mem_image.mpr ⟨⟨l, hl⟩, by simp, by simp⟩)).symm
  have h₂ : D.map (fk (Finset.mem_insert_self _ _)) ⁻¹ᵁ U l ≤ D.map (fk (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ hl))) ⁻¹ᵁ D.map (f l) ⁻¹ᵁ U l := by
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, h₁]
  convert congr((D.map (fk _)).appLE _ _ h₂ $(H l))
  · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
    simp [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, -CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, ← Functor.map_comp, h₁]
  · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
lemma exists_app_map_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = 0 := by
  have : CompactSpace ↥((opensDiagram D i U).obj (Over.mk (𝟙 i))) :=
    isCompact_iff_compactSpace.mp (by simpa)
  have H : (D.map (𝟙 _) ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ U := by simp
  obtain ⟨j, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit _ _
    (isLimitOpensCone D c hc i U) (i := .mk (𝟙 i))
    ((D.obj i).presheaf.map (homOfLE (show (D.map (𝟙 _) ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ U by simp)).op s) (by
      rw [← map_zero (c.pt.presheaf.map (homOfLE
        (show (c.π.app i ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app i ⁻¹ᵁ U by simp)).op).hom, ← hs]
      dsimp [Scheme.Opens.toScheme_presheaf_obj]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
      congr! 2
      simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE])
  dsimp at hf
  refine ⟨j.left, f.left, ?_⟩
  have hf' : f.left = j.hom := by simpa using Over.w f
  convert congr((D.obj j.left).presheaf.map (homOfLE
    (show D.map f.left ⁻¹ᵁ U ≤ (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp [hf'])).op $hf)
  · dsimp [Scheme.Opens.toScheme_presheaf_obj]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    congr! 2
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  · simp

set_option backward.isDefEq.respectTransparency false in
include hc in
lemma exists_app_map_eq_map_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s t : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = (c.π.app i).app U t) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = (D.map f).app U t := by
  simpa [sub_eq_zero] using exists_app_map_eq_zero_of_isLimit _ _ hc hU (s - t)
    (by simpa +instances [map_sub, sub_eq_zero])

set_option backward.defeqAttrib.useBackward true in
include hc in
lemma exists_appTop_π_eq_of_isAffine_of_isLimit
    [∀ i, IsAffine (D.obj i)] (s : Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), (c.π.app i).appTop t = s := by
  have : ∀ i, IsAffine (D.op.obj i).unop := by dsimp; infer_instance
  exact ⟨_, (Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (Scheme.Γ ⋙ forget _) hc.op) s).choose_spec⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
lemma exists_appTop_π_eq_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Γ(c.pt, ⊤)) [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), s = (c.π.app i).appTop t := by
  classical
  have := Scheme.compactSpace_of_isLimit _ _ hc
  have (x : c.pt) : ∃ (i : I) (U : (D.obj i).Opens) (hU : IsAffineOpen U)
      (hU : (c.π.app i).base x ∈ U) (t : Γ(D.obj i, U)), (c.π.app i).app U t = s |_ _ := by
    have i := IsCofiltered.nonempty (C := I).some
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
      (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((c.π.app i).base x)) isOpen_univ
    have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
    obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
      (isLimitOpensCone D c hc i U) (s |_ _)
    refine ⟨j.left, (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤, by simpa using hU.preimage (D.map _), ?_, t, ?_⟩
    · suffices (c.π.app j.1 ≫ D.map j.hom).base x ∈ U by simpa [-Cone.w] using this
      rwa [Cone.w]
    · have H : c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ (c.π.app i ⁻¹ᵁ U).ι ''ᵁ ⊤ := by
        simp [← Scheme.Hom.comp_preimage]
      convert congr(c.pt.presheaf.map (homOfLE H).op $hj)
      · convert ConcreteCategory.comp_apply _ _ _
        congr
        simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
      · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
        change _ = (c.pt.presheaf.map (homOfLE _).op ≫ c.pt.presheaf.map (homOfLE _).op) s
        rw [← Functor.map_comp]
        rfl
  choose i U hU hxU t ht using this
  dsimp at ht
  have (x y : c.pt) : ∃ (j : I) (fjx : j ⟶ i x) (fjy : j ⟶ i y),
      (D.map fjx).app (U x) (t x) |_ (D.map fjx ⁻¹ᵁ U x ⊓ D.map fjy ⁻¹ᵁ U y) =
      (D.map fjy).app (U y) (t y) |_ (D.map fjx ⁻¹ᵁ U x ⊓ D.map fjy ⁻¹ᵁ U y) := by
    obtain ⟨j, fjx, fjy, -⟩ := IsCofilteredOrEmpty.cone_objs (i x) (i y)
    obtain ⟨k, fkj, hk⟩ := exists_app_map_eq_zero_of_isLimit D c hc
      (((hU x).preimage (D.map fjx)).isCompact.inter_of_isOpen
        ((hU y).preimage (D.map fjy)).isCompact ((U x).2.preimage (D.map fjx).continuous)
        ((U y).2.preimage (D.map fjy).continuous))
      ((D.map fjx).app (U x) (t x) |_ (D.map fjx ⁻¹ᵁ U x ⊓ D.map fjy ⁻¹ᵁ U y) -
        (D.map fjy).app (U y) (t y) |_ (D.map fjx ⁻¹ᵁ U x ⊓ D.map fjy ⁻¹ᵁ U y)) (by
      dsimp +instances [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp only [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply,
        Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE,
        Cone.w]
      simp_rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, ht, TopCat.Presheaf.restrictOpen,
        TopCat.Presheaf.restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
    refine ⟨k, fkj ≫ fjx, fkj ≫ fjy, ?_⟩
    have H : (D.map (fkj ≫ fjx) ⁻¹ᵁ U x ⊓ D.map (fkj ≫ fjy) ⁻¹ᵁ U y) ≤
        D.map fkj ⁻¹ᵁ ((D.map fjx ⁻¹ᵁ U x ⊓ D.map fjy ⁻¹ᵁ U y)) := by simp; rfl
    apply_fun (D.obj k).presheaf.map (homOfLE H).op at hk
    dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at hk ⊢
    simpa [sub_eq_zero, ← ConcreteCategory.comp_apply, -Scheme.Hom.comp_appLE,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE] using hk
  choose j fjx fjy hj using this
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x ↦ ((c.π.app (i x)) ⁻¹ᵁ U x).1)
    (fun x ↦ ((c.π.app (i x)) ⁻¹ᵁ U x).2.mem_nhds (by exact hxU x))
  choose σi hσiσ hσi using fun x ↦ Set.mem_iUnion₂.mp (hσ.ge (Set.mem_univ x))
  let S : Finset _ := σ.image i ∪ Finset.image₂ j σ σ
  have hiS {x} (hx : x ∈ σ) : i x ∈ S := Finset.subset_union_left (Finset.mem_image_of_mem i hx)
  have hjS {x y} (hx : x ∈ σ) (hy : y ∈ σ) : j x y ∈ S :=
    Finset.subset_union_right (Finset.mem_image₂_of_mem hx hy)
  obtain ⟨k, fk, hk⟩ := IsCofiltered.inf_exists S
    (σ.attach.image₂ (fun (x y : σ) ↦ ⟨j x.1 y.1, i x.1, hjS x.2 y.2, hiS x.2, fjx x y⟩) σ.attach ∪
    σ.attach.image₂ (fun (x y : σ) ↦ ⟨j x.1 y.1, i y.1, hjS x.2 y.2, hiS y.2, fjy x y⟩) σ.attach)
  have hk₁ {x y} (hx : x ∈ σ) (hy : y ∈ σ) := hk (hjS hx hy) (hiS hx) (f := fjx x y)
    (Finset.subset_union_left (Finset.mem_image₂.mpr ⟨⟨x, hx⟩, by simp, ⟨y, hy⟩, by simp, rfl⟩))
  have hk₂ {x y} (hx : x ∈ σ) (hy : y ∈ σ) := hk (hjS hx hy) (hiS hy) (f := fjy x y)
    (Finset.subset_union_right (Finset.mem_image₂.mpr ⟨⟨x, hx⟩, by simp, ⟨y, hy⟩, by simp, rfl⟩))
  obtain ⟨k', fk'k, hk'⟩ := exists_map_eq_top D c hc
    (⨆ (x : _) (hx : x ∈ σ), D.map (fk (hiS hx)) ⁻¹ᵁ U x) (by
    apply SetLike.coe_injective
    simpa [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base])
  have := ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mp (D.obj k').IsSheaf).isSheafFor
    (.ofArrows (fun x : σ ↦ D.map (fk'k ≫ fk (hiS x.2)) ⁻¹ᵁ U x.1) fun x ↦ homOfLE le_top)
    (fun x _ ↦ by
      obtain ⟨ix, hix, h⟩ : ∃ ix, ∃ (h : ix ∈ σ), (D.map (fk'k ≫ fk (hiS h))).base x ∈ U ix := by
        simpa using hk'.ge (Set.mem_univ x)
      refine ⟨D.map (fk'k ≫ fk (hiS hix)) ⁻¹ᵁ U ix, homOfLE le_top,
        Sieve.ofArrows_mk (I := σ) _ _ ⟨ix, hix⟩, h⟩)
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at this
  obtain ⟨t₀, ht₀, -⟩ := this (fun x ↦ (D.map _).app _ (t x)) fun x y V fVx fVy _ ↦ by
    have H : V ≤ D.map (fk'k ≫ fk (hjS x.2 y.2)) ⁻¹ᵁ
        (D.map (fjx ↑x ↑y) ⁻¹ᵁ U ↑x ⊓ D.map (fjy ↑x ↑y) ⁻¹ᵁ U ↑y) := by
      change V ≤ (D.map (fk'k ≫ fk (hjS x.2 y.2)) ≫ D.map (fjx ↑x ↑y)) ⁻¹ᵁ U x ⊓
        (D.map (fk'k ≫ fk (hjS x.2 y.2)) ≫ D.map (fjy x y)) ⁻¹ᵁ U y
      rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc,
        hk₁ x.2 y.2, hk₂ x.2 y.2, le_inf_iff]
      exact ⟨fVx.le, fVy.le⟩
    convert congr(((D.map (fk'k ≫ fk (hjS x.2 y.2))).app _ ≫
      (D.obj k').presheaf.map (homOfLE H).op) $(hj x y)) using 1
    · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp only [← ConcreteCategory.comp_apply]
      congr 2
      simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        -Scheme.Hom.comp_appLE, ← Functor.map_comp, hk₁]
    · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp only [← ConcreteCategory.comp_apply]
      congr 2
      simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        -Scheme.Hom.comp_appLE, ← Functor.map_comp, hk₂]
  refine ⟨k', t₀, TopCat.Presheaf.section_ext c.pt.sheaf _ _ _ fun y hy ↦ c.pt.presheaf.germ_ext
    (c.π.app _ ⁻¹ᵁ U (σi y)) (hσi y) (homOfLE le_top) (homOfLE le_top) ?_⟩
  have H : c.π.app (i (σi y)) ⁻¹ᵁ U (σi y) ≤
      c.π.app k' ⁻¹ᵁ D.map (fk'k ≫ fk (hiS (hσiσ _))) ⁻¹ᵁ U (σi y) := by
    rw [← Scheme.Hom.comp_preimage, Cone.w]
  convert congr(c.pt.presheaf.map (homOfLE H).op ((c.π.app k').app _ $(ht₀ ⟨_, hσiσ y⟩))).symm
  · refine (ht (σi y)).symm.trans ?_
    dsimp [Scheme.Opens.toScheme_presheaf_obj]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    congr 2
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, -Scheme.Hom.comp_appLE]
  · dsimp [Scheme.Opens.toScheme_presheaf_obj]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply]
    congr 2
    simp [Scheme.Hom.app_eq_appLE]

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

set_option backward.isDefEq.respectTransparency false in
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
    · convert (hU.preimage (D.map (flk ≫ fki))).basicOpen
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
  classical
  obtain ⟨i, U, hU', rfl⟩ := exists_preimage_eq D c hc U hU.isCompact
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU')
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i U).pt := hU
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i U)
  exact ⟨_, _, hj, by simp [← Scheme.Hom.comp_preimage]⟩

set_option backward.isDefEq.respectTransparency false in
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
  classical
  have := compactSpace_of_isLimit D c hc
  choose j V hV hVU using fun k ↦ exists_isAffineOpen_preimage_eq D c hc (U k) (hU' k)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _
    (fun i ↦ (U i).isOpen) hU.iSup_set_eq_univ.ge
  obtain ⟨i, fi⟩ := IsCofiltered.inf_objs_exists (s.image j)
  replace fi : ∀ k ∈ s, i ⟶ j k := fun k hk ↦ (fi (Finset.mem_image_of_mem _ hk)).some
  obtain ⟨k, fkj, e⟩ := exists_map_eq_top D c hc (⨆ (k) (hk : k ∈ s), D.map (fi k hk) ⁻¹ᵁ V k) (by
    simp_rw [Hom.preimage_iSup, ← Hom.comp_preimage, c.w, hVU]
    exact top_le_iff.mp fun x _ ↦ by simpa using hs (Set.mem_univ x))
  refine ⟨k, s, fun x ↦ D.map (fkj ≫ fi x.1 x.2) ⁻¹ᵁ V _, ?_, fun k ↦ ⟨(hV k).preimage _, ?_⟩⟩
  · refine top_le_iff.mp (e.symm.trans_le ?_)
    simp_rw [Hom.preimage_iSup, ← Hom.comp_preimage, iSup_subtype, ← D.map_comp]
    simp
  · rw [← hVU, ← Hom.comp_preimage, c.w]

end IsAffine

section LocallyOfFinitePresentation

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/-- See `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` for the general case. -/
private nonrec lemma Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine
    [IsCofiltered I] [LocallyOfFinitePresentation f]
    [IsAffine S] [IsAffine X] [∀ i, IsAffine (D.obj i)]
    (a : c.pt ⟶ X) (ha : c.π ≫ t = (Functor.const _).map (a ≫ f)) :
    ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = t.app i := by
  -- Every scheme involved is affine, so the proof is merely translate to commutative algebra and
  -- use `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`.
  -- Unfortunately the translation takes 45 lines.
  wlog hS : ∃ R, S = Spec R generalizing S
  · obtain ⟨i, g, hg, hg'⟩ := this (t ≫ ((Functor.const I).mapIso S.isoSpec).hom)
      (f ≫ S.isoSpec.hom) (by simp [reassoc_of% ha]) ⟨_, rfl⟩
    exact ⟨i, g, hg, by simpa using congr($hg' ≫ S.isoSpec.inv)⟩
  obtain ⟨R, rfl⟩ := hS
  wlog hX : ∃ S, X = Spec S generalizing X
  · obtain ⟨i, f, hf⟩ := this (a ≫ X.isoSpec.hom) (X.isoSpec.inv ≫ f)
      (by simp [ha, - Functor.map_comp]) ⟨_, rfl⟩
    exact ⟨i, f ≫ X.isoSpec.inv, by simpa [← Iso.comp_inv_eq] using hf⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  wlog hD : ∃ D' : I ⥤ CommRingCatᵒᵖ, D = D' ⋙ Scheme.Spec generalizing D
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
    have inst (i) : IsIso (e.app i) := by dsimp [e]; infer_instance
    have inst : IsIso e := NatIso.isIso_of_isIso_app e
    have inst (i) : IsAffine ((D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec).obj i) := by
      dsimp; infer_instance
    obtain ⟨i, g, hg, hg'⟩ := this _ _ ((IsLimit.postcomposeHomEquiv (asIso e) c).symm hc)
      (inv e ≫ t) a (by simpa using ha) ⟨D ⋙ Scheme.Γ.rightOp, rfl⟩
    exact ⟨i, e.app i ≫ g, by rwa [← Category.assoc], by simp [hg']⟩
  obtain ⟨D, rfl⟩ := hD
  let e : ((Functor.const Iᵒᵖ).obj R).rightOp ⋙ Scheme.Spec ≅ (Functor.const I).obj (Spec R) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp)
  obtain ⟨t, rfl⟩ : ∃ t' : (Functor.const Iᵒᵖ).obj R ⟶ D.leftOp,
      t = Functor.whiskerRight (NatTrans.rightOp t') Scheme.Spec ≫ e.hom :=
    ⟨⟨fun i ↦ Spec.preimage (t.app i.unop), fun _ _ f ↦ Spec.map_injective
      (by simpa using (t.naturality f.unop).symm)⟩, by ext : 2; simp [e]⟩
  wlog hc' : ∃ c' : Cocone D.leftOp, c = Scheme.Spec.mapCone (coneOfCoconeLeftOp c') generalizing c
  · have inst : IsAffine c.pt := isAffine_of_isLimit _ hc
    let e' : (D ⋙ Scheme.Spec).op ⋙ Γ ≅ D.leftOp := D.leftOp.isoWhiskerLeft SpecΓIdentity
    let c' := coneOfCoconeLeftOp ((Cocone.precompose e'.inv).obj (Γ.mapCocone c.op))
    have inst : ∀ i, IsAffine ((D ⋙ Scheme.Spec).op.obj i).unop := by dsimp; infer_instance
    obtain ⟨i, f, hf⟩ := this (Scheme.Spec.mapCone c') (isLimitOfPreserves _
      (isLimitConeOfCoconeLeftOp _ ((IsColimit.precomposeHomEquiv e'.symm _).symm
        (isColimitOfPreserves _ hc.op)))) (c.pt.isoSpec.inv ≫ a) (by
        ext i
        have : c.π.app i ≫ Spec.map (t.app (.op i)) = a ≫ Spec.map φ := by
          simpa using congr((($ha).app i))
        simp [c', e, e', ← this, Iso.eq_inv_comp, isoSpec_hom_naturality_assoc]) ⟨_, rfl⟩
    refine ⟨i, f, ?_⟩
    simpa [Iso.eq_inv_comp, c', isoSpec_hom_naturality_assoc, e'] using hf
  obtain ⟨c', rfl⟩ := hc'
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective a
  replace hc := isColimitOfConeOfCoconeLeftOp _ (isLimitOfReflects _ hc)
  obtain ⟨i, g, hg, hg'⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit _ D.leftOp t _ _ hc
    (HasRingHomProperty.Spec_iff.mp ‹LocallyOfFinitePresentation (Spec.map φ)›) ψ fun i ↦ by
    apply Spec.map_injective; simpa using congr(($ha).app i.unop).symm
  exact ⟨i.unop, Spec.map g, by simpa using congr(Spec.map $hg').symm,
    by simpa using congr(Spec.map $hg)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TopologicalSpace in
include hc in
/--
Given a cofiltered diagram of qcqs schemes `Dᵢ` over `S` with affine transition maps.
If `X` is locally of finite presentation over `S`, then any `S`-morphism `lim Dᵢ ⟶ X` factors
through some `lim Dᵢ ⟶ Dⱼ ⟶ X` for some `j`.
-/
lemma Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    [IsCofiltered I] [LocallyOfFinitePresentation f]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (a : c.pt ⟶ X) (ha : c.π ≫ t = (Functor.const _).map (a ≫ f)) :
    ∃ (i : I) (g : D.obj i ⟶ X), c.π.app i ≫ g = a ∧ g ≫ f = t.app i := by
  classical
  -- The open cover of `c := lim Dᵢ` indexed by triplets of affine opens `(U, V, W)` with
  -- `U ⊆ c`, `V ⊆ X`, `W ⊆ S` such that `U` maps to `V` maps to `W`.
  have 𝒰 := (c.pt.isBasis_affineOpens).isOpenCover_mem_and_le
    (((X.isBasis_affineOpens).isOpenCover_mem_and_le
    ((S.isBasis_affineOpens).isOpenCover.comap f.base.hom)).comap a.base.hom)
  -- By qcqs, this cover descends to some finite affine open cover `𝒱` of `Dᵢ`.
  obtain ⟨i, s, 𝒱, h𝒱, h𝒱𝒰⟩ := Scheme.exists_isOpenCover_and_isAffine D c hc _ 𝒰 fun U ↦ U.2.1
  obtain ⟨i', fi'i, hi'⟩ : ∃ (i' : I) (fi'i : i' ⟶ i),
      ∀ j, D.map fi'i ⁻¹ᵁ 𝒱 j ≤ t.app i' ⁻¹ᵁ j.1.1.2.1.2.1 := by
    choose k fk hk using fun j ↦ exists_map_preimage_le_map_preimage D c hc (h𝒱𝒰 j).1.isCompact
      (V := t.app i ⁻¹ᵁ j.1.1.2.1.2.1) (by
      rw [← Hom.comp_preimage, ← NatTrans.comp_app, ha]
      exact (h𝒱𝒰 j).2.symm.trans_le (j.1.prop.2.trans (a.preimage_mono j.1.1.2.prop.2)))
    obtain ⟨i', fi'i, fi', hfi'⟩ := IsCofiltered.wideCospan fk
    refine ⟨i', fi'i, fun j ↦ ?_⟩
    rw [← hfi', Functor.map_comp, Hom.comp_preimage]
    refine (Hom.preimage_mono _ (hk _)).trans ?_
    simp only [← Hom.comp_preimage, t.naturality, Functor.const_obj_obj,
      Functor.const_obj_map, Category.comp_id, le_refl]
  -- Using the affine version `exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine`,
  -- one can now factor `Dⱼ ⁻¹ 𝒱ⱼ ⟶ lim Dᵢ ⟶ X` through some `Dⱼₖ ⁻¹ 𝒱ⱼ` for each `𝒱ⱼ`,
  -- and by finite-ness we may chose a fixed `k` that works for every `j`.
  have : ∃ k, ∃ (fk : k ⟶ i), ∀ j, ∃ (ak : ↑(D.map fk ⁻¹ᵁ 𝒱 j) ⟶ X),
      ak ≫ f = Opens.ι _ ≫ t.app k ∧ c.π.app _ ∣_ _ ≫ ak = Opens.ι _ ≫ a := by
    let 𝒱' := (D.map fi'i ⁻¹ᵁ 𝒱 ·)
    have h𝒱'𝒰 (j : s) : c.π.app i' ⁻¹ᵁ 𝒱' j = j.1.1.1 := by
      rw [← Hom.comp_preimage, c.w fi'i]; exact (h𝒱𝒰 j).2.symm
    have _ (j k) : IsAffine ((opensDiagram D i' (𝒱' j)).obj k) := ((h𝒱𝒰 _).1.preimage _).preimage _
    let t𝒱 (j : _) : opensDiagram D i' (𝒱' j) ⟶ (Functor.const (Over i')).obj j.1.1.2.1.2 :=
    { app k := (t.app k.left).resLE _ _ <| by
        refine (Hom.preimage_mono _ (hi' _)).trans ?_
        simp only [Functor.const_obj_obj, ← Hom.comp_preimage, t.naturality,
          Functor.const_obj_map, Category.comp_id, le_refl]
      naturality {k₁ k₂} f₁₂ := by simp [Hom.resLE_comp_resLE] }
    have (j : s) : IsAffine j.1.1.2.1.1 := j.1.1.2.prop.1
    choose k ak hk hk' using fun j ↦ exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine
      _ (t𝒱 j) (f.resLE _ _ j.1.1.2.prop.2) _ (isLimitOpensCone D c hc i' (𝒱' j))
      (a.resLE _ _ ((h𝒱'𝒰 _).trans_le j.1.prop.2)) (by
      ext k
      simp [t𝒱, Hom.resLE_comp_resLE, show c.π.app k.left ≫ t.app k.left = a ≫ f from
        congr(($ha).app k.left)])
    obtain ⟨i'', fi''i', fi'', hi''⟩ := IsCofiltered.wideCospan fun j ↦ (k j).hom
    refine ⟨i'', fi''i' ≫ fi'i, fun j ↦
      ⟨Scheme.homOfLE _ ?_ ≫ D.map (fi'' _) ∣_ _ ≫ ak j ≫ Opens.ι _, ?_, ?_⟩⟩
    · simp only [← Hom.comp_preimage, ← Functor.map_comp, 𝒱', reassoc_of% hi'']; rfl
    · have : ak j ≫ Opens.ι _ ≫ f = Opens.ι _ ≫ t.app (k j).left := by
        simpa [t𝒱] using congr($(hk' j) ≫ Opens.ι _)
      simp [this]
    · have e : c.π.app i'' ⁻¹ᵁ D.map (fi''i' ≫ fi'i) ⁻¹ᵁ 𝒱 j ≤ c.π.app i' ⁻¹ᵁ 𝒱' j := by
        simp only [← Hom.comp_preimage, Cone.w, 𝒱']; rfl
      simpa [← AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict,
        Scheme.Hom.resLE_comp_resLE_assoc] using congr(Scheme.homOfLE _ e ≫ $(hk j) ≫ Opens.ι _)
  choose k fki ak hak hak' using this
  -- We may then find an `l` for each `j₁` and `j₂` such that the map `Dⱼ₁ₗ ⁻¹ 𝒱ⱼ₁ ⟶ X` and
  -- `Dⱼ₂ₗ ⁻¹ 𝒱ⱼ₂ ⟶ X` agrees on the intersection in `Dₗ`.
  -- And again by finiteness we may choose a global `l`.
  obtain ⟨l, flk, hl⟩ : ∃ (l : I) (flk : l ⟶ k), ∀ j₁ j₂, Scheme.homOfLE _ inf_le_left ≫
      D.map flk ∣_ _ ≫ ak j₁ = Scheme.homOfLE _ inf_le_right ≫ D.map flk ∣_ _ ≫ ak j₂ := by
    let 𝒱' := (D.map fki ⁻¹ᵁ 𝒱 ·)
    have (j₁ j₂ : s) : ∃ (l : I) (flk : l ⟶ k), Scheme.homOfLE _ inf_le_left ≫ D.map flk ∣_ _ ≫
        ak j₁ = Scheme.homOfLE _ inf_le_right ≫ D.map flk ∣_ _ ≫ ak j₂ := by
      have _ (x) : CompactSpace ↥((opensDiagram D k (𝒱' j₁ ⊓ 𝒱' j₂)).obj x) :=
        isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ (𝒱' j₁ ⊓ 𝒱' j₂).isOpen
          (((h𝒱𝒰 _).1.preimage _).isCompact.inter_of_isOpen ((h𝒱𝒰 _).1.preimage _).isCompact
            (D.map fki ⁻¹ᵁ 𝒱 j₁).2 (D.map fki ⁻¹ᵁ 𝒱 j₂).2))
      obtain ⟨⟨l, ⟨⟨⟩⟩, flk⟩, ⟨flk', ⟨⟨⟨⟩⟩⟩, h⟩, e⟩ :=
        Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType _
          (opensDiagramι .. ≫ (Over.forget k).whiskerLeft t) f _
          (isLimitOpensCone D c hc k (𝒱' j₁ ⊓ 𝒱' j₂)) (i := .mk (𝟙 k))
          (Scheme.homOfLE _ (by simp [𝒱']) ≫ ak j₁) (Scheme.homOfLE _ (by simp [𝒱']) ≫ ak j₂)
          (by simp [hak]) (by simp [hak]) (by simp; simp [Hom.resLE, hak'])
      obtain rfl : flk = flk' := by simpa using h.symm
      refine ⟨l, flk, by simpa [← Scheme.Hom.resLE_eq_morphismRestrict] using e⟩
    choose l flk hflk using this
    obtain ⟨l', fl'k, fl'l, hl'⟩ := IsCofiltered.wideCospan (I := s × s) fun x ↦ flk x.1 x.2
    refine ⟨l', fl'k, fun j₁ j₂ ↦ ?_⟩
    have H : (D.map fl'k ≫ D.map fki) ⁻¹ᵁ (𝒱 j₁ ⊓ 𝒱 j₂) ≤
        (D.map (fl'l (j₁, j₂)) ≫ D.map (flk j₁ j₂) ≫ D.map fki) ⁻¹ᵁ (𝒱 j₁ ⊓ 𝒱 j₂) := by
      simp only [← Functor.map_comp, reassoc_of% hl']; rfl
    simpa [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE_assoc,
      ← Functor.map_comp, hl'] using congr((D.map (fl'l (j₁, j₂))).resLE _ _ H ≫ $(hflk j₁ j₂))
  -- We may glue the morphisms into `Dₗ ⟶ X` and verify that it indeed satisfies the hypothesis.
  let h𝒲 := (h𝒱.comap (D.map fki).base.hom).comap (D.map flk).base.hom
  let 𝒲 := Scheme.openCoverOfIsOpenCover _ (D.map flk ⁻¹ᵁ D.map fki ⁻¹ᵁ 𝒱 ·) h𝒲
  let F := 𝒲.glueMorphisms (fun j ↦ D.map flk ∣_ D.map fki ⁻¹ᵁ 𝒱 j ≫ ak j) (fun j₁ j₂ ↦ by
      rw [← cancel_epi (isPullback_opens_inf _ _).isoPullback.hom]
      simpa [𝒲] using hl j₁ j₂)
  have hF (j : s) : (D.map flk ⁻¹ᵁ D.map fki ⁻¹ᵁ 𝒱 j).ι ≫ F = D.map flk ∣_ _ ≫ ak j :=
    Scheme.Cover.ι_glueMorphisms ..
  refine ⟨l, F, ?_, ?_⟩
  · refine Cover.hom_ext (𝒲.pullback₁ (c.π.app l)) _ _ fun j ↦ ?_
    rw [← cancel_epi (isPullback_morphismRestrict _ _).flip.isoPullback.hom]
    dsimp [𝒲]
    simp only [pullback.condition_assoc, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_fst_assoc, hF]
    have h : c.π.app l ⁻¹ᵁ D.map flk ⁻¹ᵁ D.map fki ⁻¹ᵁ 𝒱 j ≤ c.π.app k ⁻¹ᵁ D.map fki ⁻¹ᵁ 𝒱 j := by
      simp only [← Hom.comp_preimage, c.w_assoc, c.w]; rfl
    simpa [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE_assoc] using
      congr(Scheme.homOfLE _ h ≫ $(hak' j))
  · refine 𝒲.hom_ext _ _ fun j ↦ ?_
    simp [F, Cover.ι_glueMorphisms_assoc, hak]; rfl

end LocallyOfFinitePresentation

end AlgebraicGeometry
