/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHausLike P`,
which may be useful due to their definitional properties.

So far, we have the following:
- Explicit pullbacks, defined in the "usual" way as a subset of the product.
- Explicit finite coproducts, defined as a disjoint union.

-/

namespace CompHausLike

universe u w

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

section Pullbacks

variable {P : TopCat.{u} → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B)

variable (hP : P (TopCat.of { xy : X × Y | f xy.fst = g xy.snd }))

/--
The pullback of two morphisms `f,g` in `CompHaus`, constructed explicitly as the set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
def pullback : CompHausLike P :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.continuous.comp continuous_fst)
      (g.continuous.comp continuous_snd)).isCompact
  CompHausLike.of P set hP

/--
The projection from the pullback to the first component.
-/
def pullback.fst : pullback f g hP ⟶ X where
  toFun := fun ⟨⟨x,_⟩,_⟩ => x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/--
The projection from the pullback to the second component.
-/
def pullback.snd : pullback f g hP ⟶ Y where
  toFun := fun ⟨⟨_,y⟩,_⟩ => y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

@[reassoc]
lemma pullback.condition : pullback.fst f g hP ≫ f = pullback.snd f g hP ≫ g := by
  ext ⟨_,h⟩; exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g hP where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g hP a b w ≫ pullback.fst f g hP = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g hP a b w ≫ pullback.snd f g hP = b := rfl

lemma pullback.hom_ext {Z : CompHausLike P} (a b : Z ⟶ pullback f g hP)
    (hfst : a ≫ pullback.fst f g hP = b ≫ pullback.fst f g hP)
    (hsnd : a ≫ pullback.snd f g hP = b ≫ pullback.snd f g hP) : a = b := by
  ext z
  apply_fun (fun q => q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/--
The pullback cone whose cone point is the explicit pullback.
-/
@[simps! pt π]
def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g hP) (pullback.snd f g hP) (pullback.condition f g hP)

/--
The explicit pullback cone is a limit cone.
-/
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g hP) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g hP s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ _ (hm .left) (hm .right))

theorem hasPullback : HasLimit (cospan f g) where
  exists_limit := ⟨⟨pullback.cone f g hP, pullback.isLimit f g hP⟩⟩

/-- The functor to `TopCat` creates pullbacks if they exist. -/
noncomputable def createsPullback : CreatesLimit (cospan f g) (compHausLikeToTop P) := by
  refine createsLimitOfFullyFaithfulOfIso (pullback f g hP)
    (((TopCat.pullbackConeIsLimit f g).conePointUniqueUpToIso
        (limit.isLimit _)) ≪≫ Limits.lim.mapIso (?_ ≪≫ (diagramIsoCospan _).symm))
  exact Iso.refl _

/-- The functor to `TopCat` preserves pullbacks. -/
noncomputable def preservesPullback : PreservesLimit (cospan f g) (compHausLikeToTop P) :=
  letI := createsPullback f g hP
  preservesLimitOfCreatesLimitAndHasLimit _ _

/-- The functor to another `CompHausLike` preserves pullbacks. -/
noncomputable def preservesPullback' {P' : TopCat → Prop}
    (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    PreservesLimit (cospan f g) (toCompHausLike h) := by
  have hh := preservesPullback f g hP
  change PreservesLimit _ (toCompHausLike h ⋙ compHausLikeToTop P') at hh
  exact preservesLimitOfReflectsOfPreserves (toCompHausLike h) (compHausLikeToTop P')

theorem hasPullbacks (hP : ∀ ⦃X Y B : CompHausLike P⦄ (f : X ⟶ B) (g : Y ⟶ B),
    P (TopCat.of { xy : X × Y | f xy.fst = g xy.snd })) :
    HasPullbacks (CompHausLike P) where
  has_limit F :=
    have : HasLimit (cospan (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr)) :=
      hasPullback _ _ (hP _ _)
    hasLimitOfIso (diagramIsoCospan F).symm

end Pullbacks

section FiniteCoproducts

variable {P : TopCat.{max u w} → Prop} {α : Type w} [Finite α] (X : α → CompHausLike P)
  (hP : P (TopCat.of (Σ (a : α), (X a).toTop)))

/--
The coproduct of a finite family of objects in `CompHaus`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : CompHausLike P := CompHausLike.of P (Σ (a : α), X a) hP

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X hP where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X hP ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X hP a ≫ finiteCoproduct.desc X hP e = e a := rfl

lemma finiteCoproduct.hom_ext {B : CompHausLike P} (f g : finiteCoproduct X hP ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X hP a ≫ f = finiteCoproduct.ι X hP a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
abbrev finiteCoproduct.cofan : Limits.Cofan X :=
  Cofan.mk (finiteCoproduct X hP) (finiteCoproduct.ι X hP)

/-- The explicit finite coproduct cocone is a colimit cocone. -/
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cofan X hP) :=
  mkCofanColimit _
    (fun s ↦ desc _ _ fun a ↦ s.inj a)
    (fun _ _ ↦ ι_desc _ _ _ _)
    fun _ _ hm ↦ finiteCoproduct.hom_ext _ _ _ _ fun a ↦
      (DFunLike.ext _ _ fun t ↦ congrFun (congrArg DFunLike.coe (hm a)) t)

lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X hP a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X hP) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X hP a r := ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {B : CompHausLike P} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X _ π (finiteCoproduct.ι X hP a x) = π a x := by
  intro x
  change (ι X hP a ≫ desc X _ π) _ = _
  simp only [ι_desc]
-- `elementwise` should work here, but doesn't

theorem has_coproduct : HasCoproduct X where
  exists_colimit := ⟨finiteCoproduct.cofan X hP, finiteCoproduct.isColimit X hP⟩

variable {P : TopCat.{u} → Prop}

theorem has_finite_coproducts
    (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike P),
      P (TopCat.of (Σ (a : α), (X a).toTop))) :
    HasFiniteCoproducts (CompHausLike P) where
  out _ := { has_colimit := (by
    intro F
    have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) := has_coproduct _ (hP _)
    exact hasColimitOfIso Discrete.natIsoFunctor) }

/-- The inclusion maps into the explicit finite coproduct are open embeddings. -/
lemma finiteCoproduct.openEmbedding_ι (a : α) :
    OpenEmbedding (finiteCoproduct.ι X hP a) :=
  openEmbedding_sigmaMk (σ := fun a => (X a))

/-- The inclusion maps into the abstract finite coproduct are open embeddings. -/
lemma Sigma.openEmbedding_ι (a : α) :
    haveI := has_coproduct X hP
    OpenEmbedding (Sigma.ι X a) := by
  haveI := has_coproduct X hP
  refine' OpenEmbedding.of_comp _ (homeoOfIso
    ((colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit X hP))).openEmbedding _
  convert finiteCoproduct.openEmbedding_ι X hP a
  ext x
  change (Sigma.ι X a ≫ _) x = _
  simp

/-- The functor to `TopCat` preserves finite coproducts if they exist. -/
def preservesFiniteCoproducts
    (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike P),
      P (TopCat.of (Σ (a : α), (X a).toTop))) :
    PreservesFiniteCoproducts (compHausLikeToTop P) := by
  refine ⟨fun J hJ ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) (compHausLikeToTop P) from
    preservesColimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
  apply preservesColimitOfPreservesColimitCocone (CompHausLike.finiteCoproduct.isColimit _ _)
  · exact TopCat.sigmaCofanIsColimit _
  · exact hP _

/-- The functor to another `CompHausLike` preserves finite coproducts if they exist. -/
noncomputable def preservesFiniteCoproducts' (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike P),
      P (TopCat.of (Σ (a : α), (X a).toTop)))
      {P' : TopCat.{u} → Prop} (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    PreservesFiniteCoproducts (toCompHausLike h) := by
  have hh := preservesFiniteCoproducts hP
  change PreservesFiniteCoproducts (toCompHausLike h ⋙ compHausLikeToTop P') at hh
  exact preservesFiniteCoproductsOfReflectsOfPreserves (toCompHausLike h) (compHausLikeToTop P')

variable {P : TopCat.{u} → Prop}

theorem hasPullbacksOfInclusions
    (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike.{u} P),
      P (TopCat.of.{u} (Σ (a : α), (X a).toTop)))
    (hP' : ∀ ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
      (_ : OpenEmbedding g), P (TopCat.of.{u} { xy : X × Y | f xy.fst = g xy.snd })) :
    haveI := has_finite_coproducts.{u} hP
    HasPullbacksOfInclusions (CompHausLike P) :=
  haveI := has_finite_coproducts.{u} hP
  { hasPullbackInl := by
      intro _ _ _ f
      haveI := has_finite_coproducts.{u} hP
      apply (config := { allowSynthFailures := true }) hasPullback_symmetry
      apply hasPullback
      apply hP'
      apply Sigma.openEmbedding_ι
      exact hP _ }

/-- The functor to `TopCat` creates pullbacks of inclusions if they exist. -/
noncomputable def preservesPullbacksOfInclusions
    (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike.{u} P),
      P (TopCat.of.{u} (Σ (a : α), (X a).toTop)))
    (hP' : ∀ ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
      (_ : OpenEmbedding g), P (TopCat.of.{u} { xy : X × Y | f xy.fst = g xy.snd })) :
    have := has_finite_coproducts.{u} hP
    PreservesPullbacksOfInclusions (compHausLikeToTop P) :=
  haveI := has_finite_coproducts.{u} hP
  { preservesPullbackInl := by
      intros X Y Z f
      apply (config := { allowSynthFailures := true }) preservesPullbackSymmetry
      apply preservesPullback
      apply hP'
      apply Sigma.openEmbedding_ι
      exact hP _  }

theorem finitaryExtensive
    (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike P), P (TopCat.of (Σ (a : α), X a)))
    (hP' : ∀ ⦃X Y B : CompHausLike P⦄ (f : X ⟶ B) (g : Y ⟶ B) (_ : OpenEmbedding g),
      P (TopCat.of { xy : X × Y | f xy.fst = g xy.snd })) :
      FinitaryExtensive (CompHausLike P) :=
  have := has_finite_coproducts.{u} hP
  letI := preservesFiniteCoproducts.{u} hP
  have := hasPullbacksOfInclusions hP hP'
  letI := preservesPullbacksOfInclusions hP hP'
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

end FiniteCoproducts

section Terminal

variable {P : TopCat.{u} → Prop}

/-- A one-element space is terminal in `CompHaus` -/
def isTerminalPUnit (h : P (TopCat.of PUnit.{u+1})) :
    IsTerminal (CompHausLike.of P PUnit.{u + 1} h) :=
  haveI : ∀ X, Unique (X ⟶ CompHausLike.of P PUnit.{u + 1} h) := fun _ ↦
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun _ ↦ rfl⟩
  Limits.IsTerminal.ofUnique _

end Terminal

end CompHausLike
