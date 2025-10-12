/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.CategoryTheory.Monad.Limits

/-!

# Inverse limits of schemes with affine transition maps

In this file, we develop API for inverse limits of schemes with affine transition maps,
following EGA IV 8 and https://stacks.math.columbia.edu/tag/01YT.

-/

universe uI u

open CategoryTheory Limits

namespace AlgebraicGeometry

-- We refrain from considering diagrams in the over category since inverse limits in the over
-- category is isomorphic to limits in `Scheme`. Instead we use `D ⟶ (Functor.const I).obj S` to
-- say that the diagram is over the base scheme `S`.
variable {I : Type u} [Category.{u} I] {S X : Scheme.{u}} (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S) (f : X ⟶ S) (c : Cone D) (hc : IsLimit c)

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
    exact Nonempty.map e.inv.base inferInstance
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
        exact Function.isEmpty F.base
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
      apply (config := { allowSynthFailures := true }) PrimeSpectrum.instNonemptyOfNontrivial
      have (i' : _) : Nontrivial ((F ⋙ Scheme.Γ.rightOp).leftOp.obj i') := by
        apply (config := { allowSynthFailures := true }) Scheme.component_nontrivial
        simp
      exact CommRingCat.FilteredColimits.nontrivial
        (isColimitCoconeLeftOpOfCone _ (limit.isLimit (F ⋙ Scheme.Γ.rightOp)))
    let α : F ⟶ Over.forget _ ⋙ D := Functor.whiskerRight
      (Functor.whiskerLeft (Over.post D) (Over.mapPullbackAdj (𝒰.f j)).counit) (Over.forget _)
    exact this.map (((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc).lift
        ((Cones.postcompose α).obj c'.1)).base

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
    (hmapsTo : ∀ {i i' : I} (f : i ⟶ i'), Set.MapsTo (D.map f).base (Z i) (Z i')) :
    ∃ (s : c.pt), ∀ i, (c.π.app i).base s ∈ Z i := by
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
  { lift s := IsClosedImmersion.lift (subschemeι _) (hc.lift ((Cones.postcompose ι).obj s)) (by
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
      Set.MapsTo (D.map hi'i).base (Z i' (hi'i ≫ hij)) (Z i hij)) :
    ∃ (s : c.pt), ∀ i hij, (c.π.app i).base s ∈ Z i hij := by
  have {i₁ i₂ : Over j} (f : i₁ ⟶ i₂) : IsAffineHom ((Over.forget j ⋙ D).map f) := by
    dsimp; infer_instance
  simpa [Over.forall_iff] using exists_mem_of_isClosed_of_nonempty (Over.forget j ⋙ D) _
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget j) c).symm hc)
    (fun i ↦ Z i.left i.hom) (fun _ ↦ hZc _ _)  (fun _ ↦ hZne _ _)  (fun _ ↦ hZcpt _ _)
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

/-- Given a diagram `{ Dᵢ }` of schemes and a open `U ⊆ Dᵢ`,
this is the diagram of `{ Dⱼᵢ⁻¹ U }_{j ≤ i}`. -/
@[simps] noncomputable
def opensDiagram (i : I) (U : (D.obj i).Opens) : Over i ⥤ Scheme where
  obj j := D.map j.hom ⁻¹ᵁ U
  map {j k} f := (D.map f.left).resLE _ _ (by rw [← Scheme.preimage_comp, ← D.map_comp, Over.w f])

/-- The map `Dⱼᵢ⁻¹ U ⟶ Dᵢ` from the restricted diagram to the original diagram. -/
@[simps] noncomputable
def opensDiagramι (i : I) (U : (D.obj i).Opens) : opensDiagram D i U ⟶ Over.forget _ ⋙ D where
  app j := Scheme.Opens.ι _

instance (i : I) (U : (D.obj i).Opens) (j : Over i) :
    IsOpenImmersion ((opensDiagramι D i U).app j) := by
  delta opensDiagramι; infer_instance

/-- Given a diagram `{ Dᵢ }` of schemes and a open `U ⊆ Dᵢ`,
the preimage of `U ⊆ Dᵢ` under the map `lim Dᵢ ⟶ Dᵢ` is the limit of `{ Dⱼᵢ⁻¹ U }_{j ≤ i}`.
This is the underlying cone, and it is limiting as witnessed by `isLimitOpensCone` below. -/
@[simps] noncomputable
def opensCone (i : I) (U : (D.obj i).Opens) : Cone (opensDiagram D i U) where
  pt := c.π.app i ⁻¹ᵁ U
  π.app j := (c.π.app j.left).resLE _ _ (by rw [← Scheme.preimage_comp, c.w]; rfl)

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

/-- Given a diagram `{ Dᵢ }_{i ∈ I}` of schemes and a open `U ⊆ Dᵢ`,
the preimage of `U ⊆ Dᵢ` under the map `lim Dᵢ ⟶ Dᵢ` is the limit of `{ Dⱼᵢ⁻¹ U }_{j ≤ i}`. -/
noncomputable
def isLimitOpensCone [IsCofiltered I] (i : I) (U : (D.obj i).Opens) :
    IsLimit (opensCone D c i U) :=
  isLimitOfIsPullbackOfIsConnected (opensDiagramι D i U) _ _
    (by exact { hom := (c.π.app i ⁻¹ᵁ U).ι })
    (fun j ↦ IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp [← Scheme.preimage_comp]))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

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
  · simp only [Functor.id_obj, opensDiagram_obj, Functor.const_obj_obj,
      Scheme.Opens.opensRange_ι]
    rintro x ⟨⟨y, h₁ : (D.map k.hom).base y ∈ U⟩, h₂, e⟩
    obtain rfl : y = (D.map f.left).base x := congr($e)
    dsimp at h₁
    rw [← Scheme.comp_base_apply] at h₁
    rwa [← D.map_comp, Over.w f] at h₁

include hc in
@[stacks 01Z4 "(2)"]
lemma exists_map_preimage_le_map_preimage
    [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U V : (D.obj i).Opens} (hU : IsCompact (U : Set (D.obj i)))
    (H : c.π.app i ⁻¹ᵁ U ≤ c.π.app i ⁻¹ᵁ V) :
    ∃ (j : I) (fji : j ⟶ i), D.map fji ⁻¹ᵁ U ≤ D.map fji ⁻¹ᵁ V := by
  have (j : Over i) : CompactSpace ↥((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := (D.map j.hom)) _ U.2 hU)
  have H : ((c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app i) ⁻¹ᵁ V = ⊤ := by
    rw [Scheme.preimage_comp, ← top_le_iff]
    exact .trans (by simp) (Scheme.Hom.preimage_le_preimage_of_le _ H)
  obtain ⟨j, fji, hj⟩ := exists_map_eq_top _ _ (isLimitOpensCone D c hc i U) (i := .mk (𝟙 i))
    (((Scheme.isoOfEq _ (by simp)).hom ≫ U.ι) ⁻¹ᵁ V)
    (by simpa [← Scheme.preimage_comp, -Scheme.comp_coeBase])
  refine ⟨j.left, j.hom, ?_⟩
  replace hj : (D.map j.hom ⁻¹ᵁ U).ι ⁻¹ᵁ D.map fji.left ⁻¹ᵁ V = ⊤ := by
    simpa [← Scheme.preimage_comp, -Scheme.comp_coeBase] using hj
  replace hj : (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ D.map fji.left ⁻¹ᵁ V := Set.image_subset_iff.mpr hj.ge
  simpa [show fji.left = j.hom by simpa using fji.w] using hj

open Scheme.Opens in
include hc in
lemma isBasis_preimage_isAffineOpen [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : I) (V : (D.obj i).Opens) (_ : IsAffineOpen V) } := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ := (isBasis_affine_open (D.obj i))
    |>.exists_subset_of_mem_open (Set.mem_univ ((c.π.app i).base x)) isOpen_univ
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
  simp only [Functor.const_obj_obj, Functor.id_obj, Scheme.preimage_basicOpen] at this ⊢
  rw [← c.pt.basicOpen_res_eq _ (eqToHom h.symm).op, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, ← this]
  exact ⟨hxr, hrU⟩

open Scheme.Opens in
include hc in
lemma isBasis_range_preimage_isAffineOpen
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] :
    TopologicalSpace.IsTopologicalBasis (α := c.pt) <| Set.range
      fun (V : Σ' (i : I) (V : (D.obj i).Opens), IsAffineOpen V) ↦
        (c.π.app V.1 ⁻¹ᵁ V.2.1 : c.pt.Opens) := by
  refine (isBasis_preimage_isAffineOpen D c hc).of_isOpen_of_subset ?_ ?_
  · rintro _ ⟨V, rfl⟩; exact (c.π.app V.1 ⁻¹ᵁ V.2.1).2
  · rintro _ ⟨_, ⟨i, V, hV, rfl⟩, rfl⟩; exact ⟨⟨i, V, hV⟩, rfl⟩

include hc in
@[stacks 01Z4 "(1)"]
lemma exists_preimage_eq
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (U : c.pt.Opens) (hU : IsCompact (U : Set c.pt)) :
    ∃ (i : I) (V : (D.obj i).Opens), IsCompact (V : Set (D.obj i)) ∧ c.π.app i ⁻¹ᵁ V = U := by
  classical
  obtain ⟨s, hs, hU⟩ := eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open _
    (isBasis_range_preimage_isAffineOpen D c hc) _ hU U.2
  obtain ⟨i, fi⟩ := IsCofiltered.inf_objs_exists (hs.toFinset.image (·.1))
  replace fi {x} (h) := (@fi x h).some
  refine ⟨i, ⨆ (V : s), D.map (fi ((Finset.mem_image_of_mem _ (by simp)))) ⁻¹ᵁ V.1.2.1, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk]
    have : Finite s := hs
    exact isCompact_iUnion fun V ↦ (V.1.2.2.preimage _).isCompact
  · ext1
    simpa [← Set.preimage_comp, ← ContinuousMap.coe_comp,
      ← TopCat.hom_comp, ← Scheme.comp_base, c.w] using hU.symm

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
## Sections of the limit

Let `D` be a cofiltered diagram schemes with affine transition map.
Consider the canonical map `colim Γ(Dᵢ, ⊤) ⟶ Γ(lim Dᵢ, ⊤)`.

If `D` consists of quasicompact schemes, then this map is injective. More generally, we show
that if `s t : Γ(Dᵢ, U)` have equal image in `lim Dᵢ`, then they are equal at some `Γ(Dⱼ, Dⱼᵢ⁻¹U)`.
See `AlgebraicGeometry.exists_app_map_eq_map_of_isLimit`.

If `D` consists of qcqs schemes, then this map is surjective. Specifically, we show that
any `s : Γ(lim Dᵢ, ⊤)` comes from `Γ(Dᵢ, ⊤)` for some `i`.
See `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit`.

These two results imply that `PreservesLimit D Scheme.Γ.rightOp`, which is available as an instance.

-/
section sections

variable [IsCofiltered I]

include hc in
lemma exists_appTop_map_eq_zero_of_isAffine_of_isLimit
    [∀ i, IsAffine (D.obj i)]
    (i : I) (s : Γ(D.obj i, ⊤)) (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).appTop s = 0 := by
  have : ∀ i, IsAffine (D.op.obj i).unop := by dsimp; infer_instance
  obtain ⟨j, f, hj⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (Scheme.Γ ⋙ forget _) hc.op) s (0 : Γ(D.obj i, ⊤))).mp (by simpa)
  exact ⟨j.unop, f.unop, by simpa using hj⟩

include hc in
lemma exists_appTop_map_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} [CompactSpace (D.obj i)] (s : Γ(D.obj i, ⊤)) (hs : (c.π.app i).appTop s = 0) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).appTop s = 0 := by
  classical
  have (x : D.obj i) : ∃ (U : (D.obj i).Opens) (hU : IsAffineOpen U)
      (hU : x ∈ U) (j : I) (f : j ⟶ i), (D.map f).app U (s |_ U) = 0 := by
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
      (isBasis_affine_open (D.obj i)).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
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
    rw [← Scheme.preimage_comp, ← D.map_comp, h₁]
  convert congr((D.map (fk _)).appLE _ _ h₂ $(H l))
  · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
    simp [Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, - CommRingCat.hom_comp,
      Scheme.appLE_comp_appLE, -Scheme.comp_appLE, ← Functor.map_comp, h₁]
  · simp

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

include hc in
lemma exists_app_map_eq_map_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U) (s t : Γ(D.obj i, U))
    (hs : (c.π.app i).app U s = (c.π.app i).app U t) :
    ∃ (j : I) (f : j ⟶ i), (D.map f).app U s = (D.map f).app U t := by
  simpa [sub_eq_zero] using exists_app_map_eq_zero_of_isLimit _ _ hc hU (s - t)
    (by simpa [map_sub, sub_eq_zero])

include hc in
lemma exists_appTop_π_eq_of_isAffine_of_isLimit
    [∀ i, IsAffine (D.obj i)] (s : Γ(c.pt, ⊤)) :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), (c.π.app i).appTop t = s := by
  have : ∀ i, IsAffine (D.op.obj i).unop := by dsimp; infer_instance
  exact ⟨_, (Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (Scheme.Γ ⋙ forget _) hc.op) s).choose_spec⟩

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
      (isBasis_affine_open (D.obj i)).exists_subset_of_mem_open
        (Set.mem_univ ((c.π.app i).base x)) isOpen_univ
    have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
    obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
      (isLimitOpensCone D c hc i U) (s |_ _)
    refine ⟨j.left, (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤, by simpa using hU.preimage (D.map _), ?_, t, ?_⟩
    · suffices (c.π.app j.1 ≫ D.map j.hom).base x ∈ U by simpa [-Cone.w] using this
      rwa [Cone.w]
    · have H : c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ (c.π.app i ⁻¹ᵁ U).ι ''ᵁ ⊤ := by
        simp [← Scheme.preimage_comp]
      convert congr(c.pt.presheaf.map (homOfLE H).op $hj)
      · convert ConcreteCategory.comp_apply _ _ _
        congr
        simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
      · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
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
      dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp only [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply,
        Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.appLE_comp_appLE,
        Cone.w]
      simp_rw [Scheme.Hom.appLE, ConcreteCategory.comp_apply, ht, TopCat.Presheaf.restrictOpen,
        TopCat.Presheaf.restrict, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
    refine ⟨k, fkj ≫ fjx, fkj ≫ fjy, ?_⟩
    have H : (D.map (fkj ≫ fjx) ⁻¹ᵁ U x ⊓ D.map (fkj ≫ fjy) ⁻¹ᵁ U y) ≤
        D.map fkj ⁻¹ᵁ ((D.map fjx ⁻¹ᵁ U x ⊓ D.map fjy ⁻¹ᵁ U y)) := by simp; rfl
    apply_fun (D.obj k).presheaf.map (homOfLE H).op at hk
    dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at hk ⊢
    simpa [sub_eq_zero, ← ConcreteCategory.comp_apply, - Scheme.comp_appLE,
      Scheme.Hom.app_eq_appLE, Scheme.appLE_comp_appLE] using hk
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
    simpa [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_coeBase])
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
      simp [Scheme.Hom.app_eq_appLE, Scheme.appLE_comp_appLE,
        - Scheme.comp_appLE, ← Functor.map_comp, hk₁]
    · dsimp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
      simp only [← ConcreteCategory.comp_apply]
      congr 2
      simp [Scheme.Hom.app_eq_appLE, Scheme.appLE_comp_appLE,
        - Scheme.comp_appLE, ← Functor.map_comp, hk₂]
  refine ⟨k', t₀, TopCat.Presheaf.section_ext c.pt.sheaf _ _ _ fun y hy ↦ c.pt.presheaf.germ_ext
    (c.π.app _ ⁻¹ᵁ U (σi y)) (hσi y) (homOfLE le_top) (homOfLE le_top) ?_⟩
  have H : c.π.app (i (σi y)) ⁻¹ᵁ U (σi y) ≤
      c.π.app k' ⁻¹ᵁ D.map (fk'k ≫ fk (hiS (hσiσ _))) ⁻¹ᵁ U (σi y) := by
    rw [← Scheme.preimage_comp, Cone.w]
  convert congr(c.pt.presheaf.map (homOfLE H).op ((c.π.app k').app _ $(ht₀ ⟨_, hσiσ y⟩))).symm
  · refine (ht (σi y)).symm.trans ?_
    dsimp [Scheme.Opens.toScheme_presheaf_obj]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    congr 2
    simp [Scheme.Hom.app_eq_appLE, Scheme.appLE_comp_appLE, -Scheme.comp_appLE]
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

section stuff

lemma Scheme.IsQuasiAffine.of_isAffineHom
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine] : X.IsQuasiAffine := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  refine .of_forall_exists_mem_basicOpen _ fun x ↦ ?_
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (IsQuasiAffine.isBasis_basicOpen
    Y).exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  refine ⟨f.appTop r, ?_⟩
  rw [← preimage_basicOpen_top]
  exact ⟨hr.preimage _, hxr⟩

open pullback in
attribute [simp] condition condition_assoc in
lemma isPullback_of_openCover
    {W X Y Z : Scheme.{u}} (fWX : W ⟶ X) (fWY : W ⟶ Y) (fXZ : X ⟶ Z) (fYZ : Y ⟶ Z)
    (𝒰 : Scheme.OpenCover.{u} X)
    (H : ∀ i, IsPullback (𝒰.pullbackHom fWX i) ((𝒰.pullback₁ fWX).f i ≫ fWY) (𝒰.f i ≫ fXZ) fYZ) :
    IsPullback fWX fWY fXZ fYZ := by
  have h : fWX ≫ fXZ = fWY ≫ fYZ :=
    Scheme.Cover.hom_ext (𝒰.pullback₁ fWX) _ _ fun i ↦ by simpa using (H i).w
  suffices IsIso (lift fWX fWY h) from .of_iso_pullback ⟨h⟩ (asIso (lift _ _ h)) (by simp) (by simp)
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    (Scheme.Pullback.openCoverOfLeft 𝒰 _ _)).mpr fun i ↦ ?_
  let f := map (𝒰.f i ≫ fXZ) fYZ fXZ fYZ (𝒰.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
  have : IsPullback (fst (𝒰.f i ≫ fXZ) fYZ) f (𝒰.f i) (fst _ _) := by
    simpa [← IsPullback.paste_vert_iff (.of_hasPullback _ _), f] using .of_hasPullback _ _
  have H' : IsPullback (fst fWX (𝒰.f i)) (lift (snd _ _) (fst _ _ ≫ fWY) (by simp [← h]))
      (lift fWX fWY h) f := by
    rw [← IsPullback.paste_vert_iff this.flip (by ext <;> simp [f])]
    simpa using .of_hasPullback _ _
  convert inferInstanceAs (IsIso (H'.isoPullback.inv ≫ (H i).isoPullback.hom))
  aesop (add simp [Iso.eq_inv_comp, Scheme.Cover.pullbackHom])

lemma CommRingCat.isPushout_of_isLocalization {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing Rₘ] [Algebra R Rₘ] [CommRing S] [CommRing Sₘ] [Algebra S Sₘ]
    (f : R →+* S) (fₘ : Rₘ →+* Sₘ) (H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp f)
    (M : Submonoid R) [IsLocalization M Rₘ] [IsLocalization (M.map f) Sₘ] :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R Rₘ))
      (CommRingCat.ofHom (algebraMap S Sₘ)) (CommRingCat.ofHom fₘ) := by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)

@[simps]
def Scheme.openCoverBasicOpenTop (X : Scheme) [X.IsQuasiAffine] :
    X.OpenCover where
  I₀ := Σ' (r : Γ(X, ⊤)), IsAffineOpen (X.basicOpen r)
  X r := X.basicOpen r.1
  f r := (X.basicOpen r.1).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
      (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨r, hr⟩, (X.basicOpen r).opensRange_ι.ge hxr⟩

@[reassoc (attr := simp)]
lemma IsAffineOpen.fromSpec_toSpecΓ {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ X.toSpecΓ = Spec.map (X.presheaf.map (homOfLE le_top).op) := by
  rw [fromSpec, Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_map_top, isoSpec_inv_toSpecΓ_assoc]

@[reassoc (attr := simp)]
lemma Scheme.Opens.toSpecΓ_naturality {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    (f ⁻¹ᵁ U).toSpecΓ ≫ Spec.map (f.app U) = f ∣_ U ≫ U.toSpecΓ := by
  simp only [toSpecΓ, topIso, Functor.op_obj, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    eqToHom_op, Hom.app_eq_appLE, Category.assoc, ← Spec.map_comp, Hom.appLE_map,
    toSpecΓ_naturality_assoc, TopologicalSpace.Opens.map_top, morphismRestrict_appLE, Hom.map_appLE]

lemma isPullback_toSpecΓ_toSpecΓ {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine] :
    IsPullback f X.toSpecΓ Y.toSpecΓ (Spec.map f.appTop) := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.IsQuasiAffine.of_isAffineHom f
  have (r : Γ(Y, ⊤)) :
      IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
        (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge) := by
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (f.appTop r)
    refine CommRingCat.isPushout_of_isLocalization f.appTop.hom (f.appLE (Y.basicOpen r)
      (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge).hom ?_ (.powers r)
    change CommRingCat.Hom.hom (Y.presheaf.map _ ≫ f.appLE _ _ _) =
      CommRingCat.Hom.hom (f.appTop ≫ X.presheaf.map _)
    rw [f.map_appLE, Scheme.Hom.appLE]
  refine isPullback_of_openCover _ _ _ _ Y.openCoverBasicOpenTop fun r ↦ ?_
  let e : pullback f (Y.basicOpen r.fst).ι ≅ Spec Γ(X, X.basicOpen (f.appTop r.1)) :=
    pullbackRestrictIsoRestrict _ _ ≪≫ X.isoOfEq (Scheme.preimage_basicOpen_top f r.1) ≪≫
    IsAffineOpen.isoSpec (by rw [← Scheme.preimage_basicOpen_top]; exact r.2.preimage f)
  refine .of_iso ((this r.1).op.map Scheme.Spec) e.symm r.2.isoSpec.symm (.refl _) (.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    dsimp [e, Scheme.Cover.pullbackHom, IsAffineOpen.isoSpec_hom, Scheme.Hom.appLE]
    simp only [homOfLE_leOfHom, Spec.map_comp, Category.assoc,
      Scheme.Opens.toSpecΓ_SpecMap_map_assoc, Scheme.Opens.toSpecΓ_naturality]
    simp_rw [← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp
  · simp only [Iso.symm_hom, Iso.eq_inv_comp]
    simp [e, IsAffineOpen.isoSpec_hom]

lemma preimage_opensRange_toSpecΓ
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] [X.IsQuasiAffine] [Y.IsQuasiAffine] :
    Spec.map f.appTop ⁻¹ᵁ Y.toSpecΓ.opensRange = X.toSpecΓ.opensRange := by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_toSpecΓ f) ⊤).symm

@[simp]
lemma Scheme.Hom.opensRange_eq_top {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : f.opensRange = ⊤ :=
  SetLike.coe_injective (Set.range_eq_univ.mpr f.surjective)

end stuff

section IsAffine

include hc in
@[stacks 01Z5]
lemma Scheme.exists_isQuasiAffine_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    [IsQuasiAffine c.pt] :
    ∃ i, IsQuasiAffine (D.obj i) := by
  classical
  have (x : c.pt) : ∃ (i : I) (f : Γ(D.obj i, ⊤)),
      IsAffineOpen (Scheme.basicOpen _ f) ∧ (c.π.app i).base x ∈ (Scheme.basicOpen _ f) := by
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (isBasis_affine_open (D.obj i)).exists_subset_of_mem_open
      (Set.mem_univ ((c.π.app i).base x)) isOpen_univ
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, hrU⟩ :=
      (IsQuasiAffine.isBasis_basicOpen c.pt).exists_subset_of_mem_open hxU (c.π.app i ⁻¹ᵁ U).isOpen
    obtain ⟨j, r, rfl⟩ := exists_appTop_π_eq_of_isLimit D c hc r
    obtain ⟨k, fki, fkj, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨l, flk, hl⟩ := exists_map_preimage_le_map_preimage D c hc (isCompact_basicOpen _
      isCompact_univ ((D.map fkj).appTop r)) (V := D.map fki ⁻¹ᵁ U) (by
        rwa [← preimage_basicOpen_top, ← preimage_comp, ← preimage_comp,
          c.w, c.w, preimage_basicOpen_top])
    refine ⟨l, (D.map (flk ≫ fkj)).appTop r, ?_, ?_⟩
    · convert (hU.preimage (D.map (flk ≫ fki))).basicOpen
        ((D.obj _).presheaf.map (homOfLE le_top).op ((D.map (flk ≫ fkj)).appTop r)) using 1
      rwa [Scheme.basicOpen_res, eq_comm, inf_eq_right, Functor.map_comp,
        elementwise_of% Scheme.comp_appTop, ← Scheme.preimage_basicOpen_top, Functor.map_comp,
        Scheme.preimage_comp]
    · change x ∈ c.π.app l ⁻¹ᵁ (D.obj l).basicOpen _
      rwa [Scheme.preimage_basicOpen_top, ← elementwise_of% Scheme.comp_appTop, Cone.w]
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

include hc in
@[stacks 01Z5]
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
    ((preimage_opensRange_toSpecΓ (X := c.pt) (c.π.app i)).trans (by simp))
  have := IsQuasiAffine.of_isAffineHom (D.map fij)
  exact ⟨j, ⟨isIso_of_isOpenImmersion_of_opensRange_eq_top _
    ((preimage_opensRange_toSpecΓ (D.map fij)).symm.trans hj)⟩⟩

include hc in
@[stacks 01Z4 "(1)"]
lemma exists_isAffineOpen_preimage_eq
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    (U : c.pt.Opens) (hU : IsAffineOpen U) :
    ∃ (i : I) (V : (D.obj i).Opens), IsAffineOpen V ∧ c.π.app i ⁻¹ᵁ V = U := by
  classical
  obtain ⟨i, U, hU', rfl⟩ := exists_preimage_eq D c hc U hU.isCompact
  have (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU')
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ U.2 hU')
  have := Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i U)

open TopologicalSpace in
include hc in
@[stacks 01Z5]
lemma Scheme.exists_isOpenCover_and_isAffine [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    {J : Type*} (U : J → c.pt.Opens) (hU : IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    ∃ (i : I) (s : Finset J) (V : s → (D.obj i).Opens),
      IsOpenCover V ∧ ∀ j, IsAffineOpen (V j) ∧ U j = c.π.app i ⁻¹ᵁ (V j) := by

  sorry

end IsAffine

/-!

# Cofiltered Limits and Schemes of Finite Type

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
    have inst : IsAffine ((Cones.postcompose (asIso e).hom).obj c).pt := by
      dsimp; infer_instance
    have := this (D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) ((Cones.postcompose (asIso e).hom).obj c)
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

omit [LocallyOfFiniteType f] in
lemma exists_index : ∃ (i' : I) (hii' : i' ⟶ A.i),
    ((D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)).base ⁻¹'
      ((Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X : Set <|
        ↑(pullback f f))ᶜ)) = ∅ := by
  let W := Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X
  by_contra! h
  let Z (i' : I) (hii' : i' ⟶ A.i) :=
    (D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)).base ⁻¹' Wᶜ
  have hZ (i') (hii' : i' ⟶ A.i) : IsClosed (Z i' hii') :=
    (W.isOpen.isClosed_compl).preimage <| Scheme.Hom.continuous _
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' D A.c A.hc Z hZ h
    (fun _ _ ↦ (hZ _ _).isCompact) (fun i i' hii' hij ↦ by simp [Z, Set.MapsTo])
  refine hs A.i (𝟙 A.i) (Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange _ _ _ ?_)
  use (A.c.π.app A.i ≫ A.a).base s
  have H : A.c.π.app A.i ≫ A.a ≫ pullback.diagonal f =
      A.c.π.app A.i ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb) := by ext <;> simp [hab]
  simp [← Scheme.comp_base_apply, - Scheme.comp_coeBase, H]

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

omit [LocallyOfFiniteType f] in
lemma range_g_subset :
    Set.range A.g.base ⊆ Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X := by
  simpa [ExistsHomHomCompEqCompAux.hii', g] using A.exists_index.choose_spec.choose_spec

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

variable [∀ i, IsAffineHom (c.π.app i)] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

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
  classical
  wlog h : i = j
  · let o := IsCofiltered.min i j
    have := this D t f c hc (D.map (IsCofiltered.minToLeft i j) ≫ a)
      (by simp [← ha]) (D.map (IsCofiltered.minToRight i j) ≫ b)
      (by simp [← hb]) (by simpa) rfl
    obtain ⟨k, hik, hjk, heq⟩ := this
    use k, hik ≫ IsCofiltered.minToLeft i j, hjk ≫ IsCofiltered.minToRight i j
    simpa using heq
  subst h
  let A : ExistsHomHomCompEqCompAux D t f :=
    { c := c, hc := hc, i := i, a := a, ha := ha, b := b, hb := hb, hab := hab
      𝒰S := S.affineCover, 𝒰X i := Scheme.affineCover _ }
  let 𝒰 := Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X
  let W := Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X
  choose k hki' heq using A.exists_eq
  let 𝒰Df := A.𝒰D.finiteSubcover
  rcases isEmpty_or_nonempty (D.obj A.i') with h | h
  · exact ⟨A.i', A.hii', A.hii', isInitialOfIsEmpty.hom_ext _ _⟩
  let O : Finset I := {A.i'} ∪ Finset.univ.image (fun i : 𝒰Df.I₀ ↦ k <| A.𝒰D.idx i.1)
  let o := Nonempty.some (inferInstanceAs <| Nonempty 𝒰Df.I₀)
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
  refine ⟨l, hl1 ho ≫ hki' _ ≫ A.hii', hl1 ho ≫ hki' _ ≫ A.hii', ?_⟩
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

end LocallyOfFiniteType

section LocallyOfFinitePresentation

end LocallyOfFinitePresentation

end AlgebraicGeometry
