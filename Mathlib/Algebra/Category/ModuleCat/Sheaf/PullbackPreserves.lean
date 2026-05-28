/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Over

-/

@[expose]
public section

universe u v₁ u₁ v₂ u₂ w

open CategoryTheory Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Over

instance post_preservesTerminal {X : C} (F : C ⥤ D) :
    PreservesLimit (Functor.empty.{0} _) (Over.post (X := X) F) :=
  preservesTerminal_of_iso _ <|
    (Over.post F).mapIso (terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal) ≪≫
      Over.isoMk (g := Over.mk (𝟙 (F.obj X))) (Iso.refl _) (by simp) ≪≫
      Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal

end CategoryTheory.Over

namespace CategoryTheory.GrothendieckTopology.CoversTop

protected lemma map
    {J : GrothendieckTopology C}
    {I : Type*} {X : I → C} (h : J.CoversTop X)
    (F : C ⥤ D) (K : GrothendieckTopology D) [F.Final]
    (hF : CoverPreserving J K F) :
    K.CoversTop (fun i ↦ F.obj (X i)) := by
  intro Y
  obtain ⟨Z, f, _⟩ := StructuredArrow.mk_surjective (Classical.arbitrary (StructuredArrow Y F))
  refine K.superset_covering ?_ (K.pullback_stable f ((hF.cover_preserve (h Z))))
  rintro Y' g ⟨T, k, l, ⟨i, ⟨m⟩⟩, hk⟩
  exact ⟨i, ⟨l ≫ F.map m⟩⟩

end CategoryTheory.GrothendieckTopology.CoversTop

namespace CategoryTheory

open GrothendieckTopology

lemma coverPreserving_of_preservesOneHypercovers
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [Functor.PreservesOneHypercovers.{w} F J K] [IsGeneratedByOneHypercovers.{w} J] :
    CoverPreserving J K F where
  cover_preserve {U S} hS := by
    obtain ⟨E, _, hES⟩ := (⊤ : OneHypercoverFamily.{w} J).exists_oneHypercover S hS
    refine K.superset_covering ?_ (OneHypercover.IsPreservedBy.mem₀ (E := E))
    simpa [PreOneHypercover.map, PreZeroHypercover.sieve₀_map] using
      (Sieve.functorPushforward_monotone F U hES)

end CategoryTheory

namespace SheafOfModules

variable [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.PreservesOneHypercovers F J K] [Limits.PreservesLimitsOfShape (Discrete WalkingPair) F]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (M : SheafOfModules.{u} S)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) (X : C)

abbrev StructureHomOver :
    S.over X ⟶ ((Over.post F).sheafPushforwardContinuous _ _ _).obj (R.over (F.obj X)) :=
  (J.overPullback RingCat X).map φ

attribute [local simp] prodComparison_natural in
set_option backward.isDefEq.respectTransparency false in
abbrev Over.starCompPostNatIso : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X) :=
  NatIso.ofComponents (fun Y => Over.isoMk (asIso (prodComparison F X Y)))

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def pushforwardPushforwardOverNatIso : pushforward (pushforwardOver (F.obj X)) ⋙ pushforward φ ≅
    pushforward (StructureHomOver φ X) ⋙ pushforward (pushforwardOver X) := by
  haveI := F.isContinuous_comp (Over.star (F.obj X)) J K (K.over _)
  haveI := (Over.star X).isContinuous_comp (Over.post F) J (J.over X) (K.over _)
  refine pushforwardComp φ (pushforwardOver (F.obj X)) ≪≫ pushforwardCongr ?_ ≪≫
    (pushforwardNatIso _ (Over.starCompPostNatIso X).symm).symm ≪≫
    (pushforwardComp (pushforwardOver X) (StructureHomOver φ X)).symm
  ext : 3
  simp [pushforwardOver]
  congr
  simp [← Functor.map_comp, ← op_comp, prodComparison_snd]

variable [(pushforward.{u} φ).IsRightAdjoint] [(pushforward (StructureHomOver φ X)).IsRightAdjoint]

@[simps!]
def pullbackRestrict : pushforward.{u} (𝟙 (S.over X)) ⋙ pullback (StructureHomOver φ X) ≅
    pullback φ ⋙ pushforward.{u} (𝟙 (R.over (F.obj X))) :=
  ((overPushforwardOverAdj X).comp (pullbackPushforwardAdjunction _)).leftAdjointUniq
    (((pullbackPushforwardAdjunction φ).comp (overPushforwardOverAdj (F.obj X))).ofNatIsoRight
      (pushforwardPushforwardOverNatIso φ X))

abbrev overPullbackIso : (pullback (StructureHomOver φ X)).obj (M.over X) ≅
    ((pullback φ).obj M).over (F.obj X) := (pullbackRestrict φ X).app M

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (K.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (pushforward.{u} (StructureHomOver φ X)).IsRightAdjoint]
  [F.Final]

variable {M} in
protected def QuasicoherentData.pullback (q : M.QuasicoherentData) :
    ((pullback φ).obj M).QuasicoherentData where
  I := q.I
  X i := F.obj (q.X i)
  coversTop := q.coversTop.map _ K coverPreserving_of_preservesOneHypercovers
  presentation i := ((q.presentation i).map _ (asIso (pullbackObjUnitToUnit _)).symm).ofIsIso
    (M.overPullbackIso φ (q.X i)).hom

variable {M} in
protected theorem IsQuasicoherent.pullback [q : M.IsQuasicoherent] :
    ((pullback φ).obj M).IsQuasicoherent :=
  (q.nonempty_quasicoherentData.some.pullback φ).isQuasicoherent

end SheafOfModules

instance {X Y : TopCat} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f).PreservesOneHypercovers
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
  intro U E
  constructor
  · simpa [PreOneHypercover.map, PreZeroHypercover.sieve₀_map] using
      (coverPreserving_opens_map f).cover_preserve E.mem₀
  · intro i₁ i₂ W p₁ p₂ _ x hx
    obtain ⟨V, _, hq, hxV⟩ := E.mem₁ i₁ i₂ (W := E.X i₁ ⊓ E.X i₂)
      (homOfLE inf_le_left) (homOfLE inf_le_right) (Subsingleton.elim _ _) (f x)
      ⟨p₁.le hx, p₂.le hx⟩
    obtain ⟨j, h, -, -⟩ := hq
    exact ⟨(TopologicalSpace.Opens.map f).obj V ⊓ W, homOfLE inf_le_right,
      ⟨j, homOfLE fun y hy ↦ h.le hy.1, Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
      ⟨hxV, hx⟩⟩
