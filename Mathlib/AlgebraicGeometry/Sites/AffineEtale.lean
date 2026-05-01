/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Sites.Affine
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Affine étale site

In this file we define the small affine étale site of a scheme `S`. The underlying
category is the category of commutative rings `R` equipped with an étale structure
morphism `Spec R ⟶ S`. We show that this category is essentially small,
that it is a dense subsite of the small étale site, and that it is `1`-hypercover
dense, which allows to show that if `S : Scheme.{u}`, then we can sheafify
étale presheaves with values in `Type u`, `AddCommGrpCat.{u}`, etc.

## Main results

- `AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv`: The category of sheaves on the
  small affine étale site is equivalent to the category of schemes on the small étale site.
- `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`: The category of
  sheaves on the étale site with values in a Grothendieck abelian category is Grothendieck abelian.
-/

@[expose] public section

universe u v u'

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The small affine étale site: The category of affine schemes étale over `S`, whose objects are
commutative rings `R` with an étale structure morphism `Spec R ⟶ S`. -/
def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S

namespace AffineEtale

/-- Construct an object of the small affine étale site. -/
@[simps!]
protected noncomputable def mk {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

noncomputable instance : Category S.AffineEtale :=
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
noncomputable def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology S.smallEtaleTopology

instance : Functor.IsDenseSubsite (topology S) S.smallEtaleTopology (AffineEtale.Spec S) := by
  dsimp [topology]
  infer_instance

instance : Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
    (topology S) S.smallEtaleTopology :=
  isOneHypercoverDense_toOver_Spec _

instance : EssentiallySmall.{u} S.AffineEtale :=
  essentiallySmall_costructuredArrow_Spec _ fun _ _ _ _ ↦ inferInstance

end AffineEtale

section

variable {A : Type u'} [Category.{u} A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

instance : HasSheafify (AffineEtale.topology S) A :=
    hasSheafifyEssentiallySmallSite.{u} _ _

instance : ((AffineEtale.Spec S).sheafPushforwardContinuous A
    (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

instance : HasSheafify S.smallEtaleTopology A :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)

instance :
    ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

instance : (AffineEtale.topology S).WEqualsLocallyBijective A :=
  .ofEssentiallySmall (AffineEtale.topology S)

instance : S.smallEtaleTopology.WEqualsLocallyBijective A :=
  .transport  _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.topology S) _
      (AffineEtale.Spec S))

variable (S A)

/-- The category of sheaves on the small affine étale site is equivalent to the category of
sheaves on the small étale site. -/
@[simps! inverse]
noncomputable def AffineEtale.sheafEquiv :
    Sheaf (AffineEtale.topology S) A ≌ Sheaf S.smallEtaleTopology A :=
  ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (topology S) S.smallEtaleTopology).asEquivalence.symm

-- Making this an instance would create timeouts
lemma isGrothendieckAbelian_sheaf_affineEtaleTopology [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf (AffineEtale.topology S) A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

-- Making this an instance would create timeouts
lemma isGrothendieckAbelian_sheaf_smallEtaleTopology [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology A) :=
  have := isGrothendieckAbelian_sheaf_affineEtaleTopology S A
  IsGrothendieckAbelian.of_equivalence (AffineEtale.sheafEquiv S A)

instance (R : Type u) [Ring R] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :=
  isGrothendieckAbelian_sheaf_smallEtaleTopology _ _

end

end AlgebraicGeometry.Scheme
