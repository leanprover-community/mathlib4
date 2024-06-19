/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHaus`,
which may be useful due to their definitional properties.

So far, we have the following:
- Explicit pullbacks, defined in the "usual" way as a subset of the product.
- Explicit finite coproducts, defined as a disjoint union.

-/

namespace CompHaus

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

universe u w

open CategoryTheory Limits

section Pullbacks

variable {X Y B : CompHaus.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/--
The pullback of two morphisms `f,g` in `CompHaus`, constructed explicitly as the set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
def pullback : CompHaus.{u} :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.continuous.comp continuous_fst)
      (g.continuous.comp continuous_snd)).isCompact
  CompHaus.of set

/--
The projection from the pullback to the first component.
-/
def pullback.fst : pullback f g ⟶ X where
  toFun := fun ⟨⟨x,_⟩,_⟩ => x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/--
The projection from the pullback to the second component.
-/
def pullback.snd : pullback f g ⟶ Y where
  toFun := fun ⟨⟨_,y⟩,_⟩ => y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

@[reassoc]
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_,h⟩; exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

lemma pullback.hom_ext {Z : CompHaus.{u}} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
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
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/--
The explicit pullback cone is a limit cone.
-/
@[simps! lift]
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => pullback.lift f g s.fst s.snd s.condition)
    (fun _ => pullback.lift_fst _ _ _ _ _)
    (fun _ => pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

section Isos

/-- The isomorphism from the explicit pullback to the abstract pullback. -/
noncomputable
def pullbackIsoPullback : CompHaus.pullback f g ≅ Limits.pullback f g :=
  Limits.IsLimit.conePointUniqueUpToIso (pullback.isLimit f g) (Limits.limit.isLimit _)

/-- The homeomorphism from the explicit pullback to the abstract pullback. -/
noncomputable
def pullbackHomeoPullback : (CompHaus.pullback f g).toTop ≃ₜ (Limits.pullback f g).toTop :=
  CompHaus.homeoOfIso (pullbackIsoPullback f g)

theorem pullback_fst_eq :
    CompHaus.pullback.fst f g = (pullbackIsoPullback f g).hom ≫ Limits.pullback.fst := by
  dsimp [pullbackIsoPullback]
  simp only [Limits.limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt, pullback.cone_π]

theorem pullback_snd_eq :
    CompHaus.pullback.snd f g = (pullbackIsoPullback f g).hom ≫ Limits.pullback.snd := by
  dsimp [pullbackIsoPullback]
  simp only [Limits.limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt, pullback.cone_π]

end Isos

end Pullbacks

section FiniteCoproducts

variable {α : Type w} [Finite α] (X : α → CompHaus)

/--
The coproduct of a finite family of objects in `CompHaus`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : CompHaus := CompHaus.of <| Σ (a : α), X a

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : CompHaus} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : CompHaus} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : CompHaus} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
abbrev finiteCoproduct.cofan : Limits.Cofan X :=
  Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)

/-- The explicit finite coproduct cocone is a colimit cocone. -/
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cofan X) :=
  mkCofanColimit _
    (fun s ↦ desc _ fun a ↦ s.inj a)
    (fun _ _ ↦ ι_desc _ _ _)
    fun _ _ hm ↦ finiteCoproduct.hom_ext _ _ _ fun a ↦
      (DFunLike.ext _ _ fun t ↦ congrFun (congrArg DFunLike.coe (hm a)) t)

section Iso

/-- The isomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductIsoCoproduct : finiteCoproduct X ≅ ∐ X :=
  Limits.IsColimit.coconePointUniqueUpToIso (finiteCoproduct.isColimit X)
    (Limits.colimit.isColimit _)

theorem Sigma.ι_comp_toFiniteCoproduct (a : α) :
    (Limits.Sigma.ι X a) ≫ (coproductIsoCoproduct X).inv = finiteCoproduct.ι X a := by
  simp [coproductIsoCoproduct]

/-- The homeomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductHomeoCoproduct : finiteCoproduct X ≃ₜ (∐ X : _) :=
  CompHaus.homeoOfIso (coproductIsoCoproduct X)

end Iso

lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {B : CompHaus} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  intro x
  change (ι X a ≫ desc X π) _ = _
  simp only [ι_desc]
-- `elementwise` should work here, but doesn't

instance : PreservesFiniteCoproducts compHausToTop := by
  refine ⟨fun J hJ ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) compHausToTop from
    preservesColimitOfIsoDiagram _ Discrete.natIsoFunctor.symm
  apply preservesColimitOfPreservesColimitCocone (CompHaus.finiteCoproduct.isColimit _)
  exact TopCat.sigmaCofanIsColimit _

instance : FinitaryExtensive CompHaus :=
  finitaryExtensive_of_preserves_and_reflects compHausToTop

end FiniteCoproducts

section Terminal

/-- A one-element space is terminal in `CompHaus` -/
def isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ CompHaus.of PUnit.{u + 1}) := fun _ ↦
    ⟨⟨⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun _ ↦ rfl⟩
  Limits.IsTerminal.ofUnique _

/-- The isomorphism from an arbitrary terminal object of `CompHaus` to a one-element space. -/
noncomputable def terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit :=
  terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

end Terminal

end CompHaus
