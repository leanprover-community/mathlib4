/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Filtered.Final
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
    have (i' : _) : IsAffine (𝒰.obj i') := inferInstanceAs (IsAffine (Spec _))
    obtain ⟨j, H⟩ :
        ∃ j : 𝒰.J, ∀ {i'} (f : i' ⟶ i), Nonempty ((𝒰.pullbackCover (D.map f)).obj j) := by
      simp_rw [← not_isEmpty_iff]
      by_contra! H
      choose i' f hf using H
      let g (j) := IsCofiltered.infTo (insert i (Finset.univ.image i'))
        (Finset.univ.image fun j : 𝒰.J ↦ ⟨_, _, by simp, by simp, f j⟩) (X := j)
      have (j : 𝒰.J) : IsEmpty ((𝒰.pullbackCover (D.map (g i (by simp)))).obj j) := by
        let F : (𝒰.pullbackCover (D.map (g i (by simp)))).obj j ⟶
            (𝒰.pullbackCover (D.map (f j))).obj j :=
          pullback.map _ _ _ _ (D.map (g _ (by simp))) (𝟙 _) (𝟙 _) (by
            rw [← D.map_comp, IsCofiltered.infTo_commutes]
            · simp [g]
            · simp
            · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) (by simp)
        exact Function.isEmpty F.base
      obtain ⟨x, -⟩ :=
        (𝒰.pullbackCover (D.map (g i (by simp)))).covers (Nonempty.some inferInstance)
      exact (this _).elim x
    let F := Over.post D ⋙ Over.pullback (𝒰.map j) ⋙ Over.forget _
    have (i' : _) : IsAffine (F.obj i') :=
      have : IsAffineHom (pullback.snd (D.map i'.hom) (𝒰.map j)) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      isAffine_of_isAffineHom (pullback.snd (D.map i'.hom) (𝒰.map j))
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
      (Functor.whiskerLeft (Over.post D) (Over.mapPullbackAdj (𝒰.map j)).counit) (Over.forget _)
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

section

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
  · let e : D ⟶ D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := whiskerLeft D ΓSpec.adjunction.unit
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
      t = whiskerRight (NatTrans.rightOp t') Scheme.Spec ≫ e.hom :=
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
  [h𝒰S : ∀ i, IsAffine (𝒰S.obj i)]
  /-- (Implementation) A family of open covers refining `𝒰S`. See the section docstring. -/
  𝒰X (i : (Scheme.Cover.pullbackCover 𝒰S f).J) : Scheme.OpenCover.{u} ((𝒰S.pullbackCover f).obj i)
  [h𝒰X : ∀ i j, IsAffine ((𝒰X i).obj j)]

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
  Scheme.Cover.mkOfCovers (Σ i : A.𝒰S.J, (A.𝒰X i).J) _
    (fun i ↦ ((Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackCover A.g).map ⟨i.1, i.2, i.2⟩)
    (fun x ↦ by simpa [← Set.mem_range, Scheme.Pullback.range_fst,
        Scheme.Pullback.diagonalCoverDiagonalRange] using A.range_g_subset ⟨x, rfl⟩)

/-- (Implementation) An affine open cover refining `𝒰D₀`. See the section docstring. -/
noncomputable def 𝒰D : Scheme.OpenCover.{u} (D.obj A.i') :=
  A.𝒰D₀.bind fun _ ↦ Scheme.affineCover _

attribute [-simp] cast_eq eq_mpr_eq_cast

/-- (Implementation) The diagram restricted to `Over i'`. See the section docstring. -/
def D' (j : A.𝒰D.J) : Over A.i' ⥤ Scheme :=
  Over.post D ⋙ Over.pullback (A.𝒰D.map j) ⋙ Over.forget _

/-- (Implementation) The limit cone restricted to `Over i'`. See the section docstring. -/
def c' (j : A.𝒰D.J) : Cone (A.D' j) :=
  (Over.pullback (A.𝒰D.map j) ⋙ Over.forget _).mapCone ((Over.conePost _ _).obj A.c)

attribute [local instance] IsCofiltered.isConnected

/-- (Implementation)
The limit cone restricted to `Over i'` is still a limit because the diagram is cofiltered.
See the section docstring. -/
def hc' (j : A.𝒰D.J) : IsLimit (A.c' j) :=
  isLimitOfPreserves (Over.pullback (A.𝒰D.map j) ⋙ Over.forget _) (Over.isLimitConePost _ A.hc)

variable [∀ i, IsAffineHom (A.c.π.app i)]

lemma exists_eq (j : A.𝒰D.J) : ∃ (k : I) (hki' : k ⟶ A.i'),
    (A.𝒰D.pullbackCover (D.map hki')).map j ≫ D.map (hki' ≫ A.hii') ≫ A.a =
      (A.𝒰D.pullbackCover (D.map hki')).map j ≫ D.map (hki' ≫ A.hii') ≫ A.b := by
  have : IsAffine (A.𝒰D.obj j) := by dsimp [𝒰D]; infer_instance
  have (i) : IsAffine ((Over.post D ⋙ Over.pullback (A.𝒰D.map j) ⋙ Over.forget _).obj i) := by
    dsimp; infer_instance
  have : IsAffine ((Over.pullback (A.𝒰D.map j) ⋙ Over.forget (A.𝒰D.obj j)).mapCone
      ((Over.conePost D A.i').obj A.c)).pt := by
    dsimp; infer_instance
  have : LocallyOfFiniteType ((A.𝒰X j.fst.fst).map j.fst.snd ≫ A.𝒰S.pullbackHom f j.fst.fst) := by
    dsimp [Scheme.Cover.pullbackHom]; infer_instance
  have H₁ := congr($(pullback.condition (f := A.g) (g := (Scheme.Pullback.diagonalCover f
    A.𝒰S A.𝒰X).map ⟨j.1.1, (j.1.2, j.1.2)⟩)) ≫ pullback.fst _ _)
  have H₂ := congr($(pullback.condition (f := A.g) (g := (Scheme.Pullback.diagonalCover f
    A.𝒰S A.𝒰X).map ⟨j.1.1, (j.1.2, j.1.2)⟩)) ≫ pullback.snd _ _)
  simp only [Scheme.Pullback.openCoverOfBase_J, Scheme.Pullback.openCoverOfBase_obj,
    Scheme.Cover.pullbackCover_obj, Scheme.Pullback.openCoverOfLeftRight_J, g, Category.assoc,
    limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Scheme.Pullback.diagonalCover_map,
    Scheme.Cover.pullbackCover_map, Scheme.Cover.pullbackHom] at H₁ H₂
  obtain ⟨k, hik, hjk, H⟩ := Scheme.exists_hom_hom_comp_eq_comp_of_isAffine_of_locallyOfFiniteType
    (Over.post D ⋙ Over.pullback (A.𝒰D.map j) ⋙ Over.forget _)
    (whiskerLeft (Over.post D ⋙ Over.pullback (A.𝒰D.map j)) (Comma.natTrans _ _) ≫
      (Functor.const _).map ((A.𝒰D₀.obj j.1).affineCover.map j.2 ≫
      (Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackHom _ _ ≫
      pullback.fst _ _ ≫
      (A.𝒰X j.fst.fst).map j.fst.snd ≫ Scheme.Cover.pullbackHom A.𝒰S f j.fst.fst))
    (((A.𝒰X j.1.1).map j.1.2 ≫ A.𝒰S.pullbackHom f j.1.1))
    ((Over.pullback (A.𝒰D.map j) ⋙ Over.forget _).mapCone ((Over.conePost _ _).obj A.c))
    (by
      refine isLimitOfPreserves (Over.pullback (A.𝒰D.map j) ⋙ Over.forget _) ?_
      apply isLimitOfReflects (Over.forget (D.obj A.i'))
      exact (Functor.Initial.isLimitWhiskerEquiv (Over.forget A.i') A.c).symm A.hc)
    (i := Over.mk (𝟙 _))
    (pullback.snd _ _ ≫ (A.𝒰D₀.obj j.1).affineCover.map j.2 ≫
      (Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackHom _ _ ≫
      pullback.fst _ _)
    (by simp)
    (j := Over.mk (𝟙 _))
    (pullback.snd _ _ ≫ (A.𝒰D₀.obj j.1).affineCover.map j.2 ≫
      (Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackHom _ _ ≫
      pullback.snd _ _)
    (by simp [pullback.condition])
    (by
      rw [← cancel_mono ((A.𝒰X j.1.1).map j.1.2), ← cancel_mono (pullback.fst f (A.𝒰S.map j.1.1))]
      have H₃ := congr(pullback.fst (A.c.π.app A.i') (A.𝒰D.map j) ≫ $(A.hab))
      simp only [pullback.condition_assoc, 𝒰D, ← A.c.w A.hii', Category.assoc] at H₃
      simpa [Scheme.Cover.pullbackHom, g, ← H₁, ← H₂, -Cone.w, -Cone.w_assoc] using H₃)
  refine ⟨k.left, k.hom, ?_⟩
  simpa [← cancel_mono ((A.𝒰X j.1.1).map j.1.2), ← cancel_mono (pullback.fst f (A.𝒰S.map j.1.1)),
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
  let O : Finset I := {A.i'} ∪ Finset.univ.image (fun i : 𝒰Df.J ↦ k <| A.𝒰D.f i.1)
  let o := Nonempty.some (inferInstanceAs <| Nonempty 𝒰Df.J)
  have ho : k (A.𝒰D.f o.1) ∈ O := by
    simp [O]
  obtain ⟨l, hl1, hl2⟩ := IsCofiltered.inf_exists O
    (Finset.univ.image (fun i : 𝒰Df.J ↦
      ⟨k <| A.𝒰D.f i.1, A.i', by simp [O], by simp [O], hki' <| A.𝒰D.f i.1⟩))
  have (w v : 𝒰Df.J) :
      hl1 (by simp [O]) ≫ hki' (A.𝒰D.f w.1) = hl1 (by simp [O]) ≫ hki' (A.𝒰D.f v.1) := by
    trans hl1 (show A.i' ∈ O by simp [O])
    · exact hl2 _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact .symm <| hl2 _ _ (Finset.mem_image_of_mem _ (by simp))
  refine ⟨l, hl1 ho ≫ hki' _ ≫ A.hii', hl1 ho ≫ hki' _ ≫ A.hii', ?_⟩
  apply (𝒰Df.pullbackCover (D.map <| hl1 ho ≫ hki' _)).hom_ext
  intro u
  let F : pullback (D.map (hl1 ho ≫ hki' (A.𝒰D.f o.1))) (𝒰Df.map u) ⟶
      pullback (D.map (hki' <| A.𝒰D.f u.1)) (A.𝒰D.map <| A.𝒰D.f u.1) :=
    pullback.map _ _ _ _ (D.map <| hl1 (by simp [O]))
      (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← D.map_comp, this]) rfl
  have hF : F ≫ pullback.fst (D.map (hki' _)) (A.𝒰D.map _) =
      pullback.fst _ _ ≫ D.map (hl1 (by simp [O])) := by simp [F]
  simp only [Scheme.Cover.pullbackCover_obj, Scheme.Cover.pullbackCover_map, Functor.map_comp,
    Category.assoc, Set.top_eq_univ] at heq ⊢
  simp_rw [← D.map_comp_assoc, reassoc_of% this o u, D.map_comp_assoc]
  rw [← reassoc_of% hF, ← reassoc_of% hF, heq]

end

end AlgebraicGeometry
