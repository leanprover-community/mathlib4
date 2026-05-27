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

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {D : Type u₂} [Category.{v₂} D]
  [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (M : SheafOfModules.{u} S)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [(pushforward.{u} φ).IsRightAdjoint] [Functor.PreservesOneHypercovers F J K]
  [Limits.PreservesFiniteProducts F]

variable (X : C)

set_option backward.isDefEq.respectTransparency false in
abbrev StructureHomOver :
    S.over X ⟶ ((Over.post F).sheafPushforwardContinuous _ _ _).obj (R.over (F.obj X)) :=
  (J.overPullback RingCat X).map φ

variable [(pushforward (StructureHomOver φ X)).IsRightAdjoint]

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
  refine (pushforwardComp (pushforwardOver X) (StructureHomOver φ X) ≪≫
    pushforwardNatIso _ (Over.starCompPostNatIso X).symm ≪≫ pushforwardCongr ?_ ≪≫
    (pushforwardComp φ (pushforwardOver (F.obj X))).symm).symm
  ext : 3
  simp [pushforwardOver]
  congr
  simp [IsIso.comp_inv_eq, ← Functor.map_comp, ← op_comp, prodComparison_snd]

@[simps!]
def pullbackRestrict : pushforward.{u} (𝟙 (S.over X)) ⋙ pullback (StructureHomOver φ X) ≅
    pullback φ ⋙ pushforward.{u} (𝟙 (R.over (F.obj X))) :=
  ((overPushforwardOverAdj X).comp (pullbackPushforwardAdjunction _)).leftAdjointUniq
    (((pullbackPushforwardAdjunction φ).comp (overPushforwardOverAdj (F.obj X))).ofNatIsoRight
      (pushforwardPushforwardOverNatIso φ X))

abbrev overPullback :
    (pullback (StructureHomOver φ X)).obj (M.over X) ≅
    ((pullback φ).obj M).over (F.obj X) := (pullbackRestrict φ X).app M

#check M.overPullback φ X

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

#check M.overPullback f.toRingCatSheafHom U

end AlgebraicGeometry.Scheme.Modules
