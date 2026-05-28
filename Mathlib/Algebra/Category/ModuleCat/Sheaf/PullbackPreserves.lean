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

namespace CategoryTheory.Functor

theorem final_of_isTerminal_obj_isTerminal {C : Type u₁} [Category.{v₁} C] [HasTerminal C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {T : C} (hT : IsTerminal T)
    (hF : IsTerminal (F.obj T)) : F.Final :=
  have : (fromPUnit.{0} T).Final := final_fromPUnit_of_isTerminal hT
  have : (fromPUnit.{0} (F.obj T)).Final := final_fromPUnit_of_isTerminal hF
  have : ((fromPUnit.{0} T) ⋙ F).Final := final_of_natIso (F := fromPUnit.{0} (F.obj T))
    (NatIso.ofComponents (fun _ => Iso.refl _))
  final_of_final_comp (fromPUnit.{0} T) F

instance {C : Type u₁} [Category.{v₁} C] [HasTerminal C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) [PreservesLimit (Functor.empty.{0} C) F] : F.Final :=
  final_of_isTerminal_obj_isTerminal F terminalIsTerminal
    (terminalIsTerminal.isTerminalObj F (⊤_ C))

end CategoryTheory.Functor

namespace CategoryTheory.Over

instance post_preservesTerminal {T : Type u₁} [Category.{v₁} T] {D : Type u₂} [Category.{v₂} D]
    {X : T} (F : T ⥤ D) : PreservesLimit (Functor.empty.{0} _) (Over.post (X := X) F) :=
  preservesTerminal_of_iso _ <|
    (Over.post F).mapIso (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := X))) ≪≫
      Over.isoMk (g := Over.mk (𝟙 (F.obj X))) (Iso.refl _) (by simp) ≪≫
      Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal

end CategoryTheory.Over

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {D : Type u₂} [Category.{v₂} D]
  [HasBinaryProducts D]
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
@[simps!]
def Over.starCompPostNatIso : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X) :=
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

abbrev overPullbackIso :
    (pullback (StructureHomOver φ X)).obj (M.over X) ≅
    ((pullback φ).obj M).over (F.obj X) := (pullbackRestrict φ X).app M

#check M.overPullbackIso φ X

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (K.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (pushforward.{u} (StructureHomOver φ X)).IsRightAdjoint]
  [F.Final]

#check QuasicoherentData.{u} M

set_option backward.isDefEq.respectTransparency false in
omit [HasBinaryProducts C] [HasBinaryProducts D]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (K.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
variable (J K F) in
theorem coversTop_map {I : Type w} {X : I → C} (h : J.CoversTop X) :
    K.CoversTop (fun i => F.obj (X i)) := by
  intro Y
  let X₀ := Functor.Final.lift F Y
  let f : Y ⟶ F.obj X₀ := Functor.Final.homToLift F Y
  let S : J.Cover X₀ := h.cover X₀
  let E : J.OneHypercover X₀ := S.oneHypercover
  have hE : (E.toPreOneHypercover.map F).sieve₀ ∈ K (F.obj X₀) :=
    GrothendieckTopology.OneHypercover.IsPreservedBy.mem₀ (E := E) (F := F) (K := K)
  have hFX₀ : Sieve.ofObjects (fun i => F.obj (X i)) (F.obj X₀) ∈ K (F.obj X₀) := by
    refine K.superset_covering ?_ hE
    change (E.toPreOneHypercover.toPreZeroHypercover.map F).sieve₀ ≤
      Sieve.ofObjects (fun i => F.obj (X i)) (F.obj X₀)
    rw [PreZeroHypercover.sieve₀_map]
    simpa [S, E, Function.comp_def] using
      (Sieve.functorPushforward_ofObjects_le (F := F) X X₀)
  simpa [f] using K.pullback_stable f hFX₀

variable {M} in
def QuasicoherentData.pullback (q : M.QuasicoherentData) :
    ((pullback φ).obj M).QuasicoherentData where
  I := q.I
  X i := F.obj (q.X i)
  coversTop := coversTop_map J K _ q.coversTop
  presentation i := ((q.presentation i).map _ (asIso (pullbackObjUnitToUnit _)).symm).ofIsIso
    (M.overPullbackIso φ (q.X i)).hom

variable {M} in
theorem IsQuasicoherent.pullback [q : M.IsQuasicoherent] : ((pullback φ).obj M).IsQuasicoherent :=
  (q.nonempty_quasicoherentData.some.pullback φ).isQuasicoherent

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

instance {X Y : TopCat} (f : X ⟶ Y) : PreservesFiniteProducts (TopologicalSpace.Opens.map f) := by
  haveI : PreservesLimit (Functor.empty.{0} (TopologicalSpace.Opens Y))
      (TopologicalSpace.Opens.map f) := by
    apply preservesTerminal_of_iso
    apply eqToIso
    ext x
    constructor
    · intro _
      exact leOfHom (terminalIsTerminal.from (⊤ : TopologicalSpace.Opens X)) trivial
    · intro _
      exact leOfHom (terminalIsTerminal.from (⊤ : TopologicalSpace.Opens Y)) trivial
  haveI : PreservesLimitsOfShape (Discrete PEmpty.{1}) (TopologicalSpace.Opens.map f) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  haveI : ∀ U V : TopologicalSpace.Opens Y,
      IsIso (prodComparison (TopologicalSpace.Opens.map f) U V) := by
    intro U V
    let h : (TopologicalSpace.Opens.map f).obj (U ⨯ V) =
        ((TopologicalSpace.Opens.map f).obj U ⨯ (TopologicalSpace.Opens.map f).obj V) := by
      ext x
      simp
    rw [Subsingleton.elim (prodComparison (TopologicalSpace.Opens.map f) U V) (eqToHom h)]
    infer_instance
  haveI : PreservesLimitsOfShape (Discrete WalkingPair) (TopologicalSpace.Opens.map f) :=
    preservesBinaryProducts_of_isIso_prodComparison (TopologicalSpace.Opens.map f)
  exact Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal (TopologicalSpace.Opens.map f)

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

variable {X Y : Scheme} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)

#synth HasLimits X.Opens

instance [M.IsQuasicoherent] : ((pullback f).obj M).IsQuasicoherent :=
  SheafOfModules.IsQuasicoherent.pullback _

#check M.overPullbackIso f.toRingCatSheafHom U

variable (q : M.QuasicoherentData)

#check q.pullback f.toRingCatSheafHom

end AlgebraicGeometry.Scheme.Modules
