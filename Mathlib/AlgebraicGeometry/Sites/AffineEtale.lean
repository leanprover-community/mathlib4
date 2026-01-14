/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

@[expose] public section

/-!
# Affine étale site
-/

universe u

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

section

/-- Construct an object of affine `P`-schemes over `S` by giving a morphism `Spec R ⟶ S`. -/
@[simps! hom left]
def affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ S) (hf : P f) :
    P.CostructuredArrow ⊤ Scheme.Spec S :=
  .mk ⊤ f hf

/-- The `Spec` functor from affine `P`-schemes over `S` to `P`-schemes over `S` is dense
if `P` is local at the source. -/
instance isCoverDense_toOver_Spec (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense
      (smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage P) U.left :=
      U.left.affineCover.changeProp
      (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    refine ⟨𝒰, ⟨fun i ↦ inferInstance, fun i ↦ ⟨rfl⟩⟩, ?_, ?_⟩
    · intro i
      exact P.comp_mem _ _ (𝒰.map_prop i) U.prop
    · rintro X f ⟨i⟩
      rw [Sieve.coverByImage]
      refine ⟨⟨affineOverMk (𝒰.f i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop), ?_, ?_, ?_⟩⟩
      · exact CostructuredArrow.homMk (𝟙 _) ⟨⟩ rfl
      · exact Over.homMk (𝒰.f i) (by simp) trivial
      · ext
        simp

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape ?_ ?_ ?_ _
  · intro D _
    exact Sigma.cocone _
  · intro D
    exact coproductIsCoproduct' _
  · intro D _ X s h
    exact IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) :=
      IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete _ _
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

end

/-- The small affine étale site: The category of affine schemes étale over `S`, whose objects are
commutative rings `R` with an étale structure morphism `Spec R ⟶ S`. -/
def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @IsEtale.{u} ⊤ Scheme.Spec.{u} S

namespace AffineEtale

/-- Construct an object of the small affine étale site. -/
@[simps!]
protected def mk {R : CommRingCat.{u}} (f : Spec R ⟶ S) [IsEtale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

instance : Category S.AffineEtale :=
  inferInstanceAs <| Category (MorphismProperty.CostructuredArrow _ _ _ _)

/-- The `Spec` functor from the small affine étale site of `S` to the small étale site of `S`. -/
@[simps! obj_left obj_hom map_left]
protected noncomputable def Spec (S : Scheme.{u}) : S.AffineEtale ⥤ S.Etale :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

instance : (AffineEtale.Spec S).Faithful :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

instance : (AffineEtale.Spec S).Full :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

instance : (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (smallGrothendieckTopology _)

instance : HasPullbacks S.AffineEtale :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.CostructuredArrow _ _ _ _)

variable (S) in
/-- The topology on the small affine étale site is the topology induced by `Spec` from
the small étale site. -/
def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology (smallEtaleTopology S)

/-- The category of sheafs on the small affine étale site is equivalent to the category of
sheafs on the small étale site. -/
noncomputable def sheafEquiv (A : Type*) [Category A]
    [∀ (X : S.Etaleᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow X (AffineEtale.Spec S).op) A] :
    Sheaf (AffineEtale.topology S) A ≌ Sheaf (smallEtaleTopology S) A :=
  (AffineEtale.Spec S).sheafInducedTopologyEquivOfIsCoverDense _ _

end AlgebraicGeometry.Scheme.AffineEtale
