/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHaus`,
which may be useful due to their definitional properties.

So far, we have the following:
- Explicit pullbacks, defined in the "usual" way as a subset of the product.
- Explicit finite coproducts, defined as a disjoint union.

-/

namespace CompHaus

universe u

open CategoryTheory

section Pullbacks

variable {X Y B : CompHaus.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/--
The pullback of two morphisms `f,g` in `CompHaus`, constructed explicitly as the set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
def Pullback : CompHaus.{u} :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set := by
    rw [← isCompact_iff_compactSpace]
    apply IsClosed.isCompact
    exact isClosed_eq (f.continuous.comp continuous_fst) (g.continuous.comp continuous_snd)
  CompHaus.of set

/--
The projection from the pullback to the first component.
-/
def Pullback.fst : Pullback f g ⟶ X where
  toFun := fun ⟨⟨x,_⟩,_⟩ => x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/--
The projection from the pullback to the second component.
-/
def Pullback.snd : Pullback f g ⟶ Y where
  toFun := fun ⟨⟨_,y⟩,_⟩ => y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

@[reassoc]
lemma Pullback.condition : Pullback.fst f g ≫ f = Pullback.snd f g ≫ g := by
  ext ⟨_,h⟩ ; exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def Pullback.lift {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ Pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w ; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma Pullback.lift_fst {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
  Pullback.lift f g a b w ≫ Pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma Pullback.lift_snd {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
  Pullback.lift f g a b w ≫ Pullback.snd f g = b := rfl

lemma Pullback.hom_ext {Z : CompHaus.{u}} (a b : Z ⟶ Pullback f g)
    (hfst : a ≫ Pullback.fst f g = b ≫ Pullback.fst f g)
    (hsnd : a ≫ Pullback.snd f g = b ≫ Pullback.snd f g) : a = b := by
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
def Pullback.cone : Limits.PullbackCone f g:=
  Limits.PullbackCone.mk (Pullback.fst f g) (Pullback.snd f g) (Pullback.condition f g)

/--
The explicit pullback cone is a limit cone.
-/
@[simps! lift]
def Pullback.isLimit : Limits.IsLimit (Pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s => Pullback.lift f g s.fst s.snd s.condition)
    (fun _ => Pullback.lift_fst _ _ _ _ _)
    (fun _ => Pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm => Pullback.hom_ext _ _ _ _ (hm .left) (hm .right))

end Pullbacks

section FiniteCoproducts

variable {α : Type} [Fintype α] (X : α → CompHaus.{u})

/--
The coproduct of a finite family of objects in `CompHaus`, constructed as the disjoint
union with its usual topology.
-/
def FiniteCoproduct : CompHaus := CompHaus.of <| Σ (a : α), X a

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
def FiniteCoproduct.incl (a : α) : X a ⟶ FiniteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def FiniteCoproduct.desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) :
    FiniteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a ; exact (e a).continuous

@[reassoc (attr := simp)]
lemma FiniteCoproduct.incl_desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  FiniteCoproduct.incl X a ≫ FiniteCoproduct.desc X e = e a := rfl

lemma FiniteCoproduct.hom_ext {B : CompHaus.{u}} (f g : FiniteCoproduct X ⟶ B)
    (h : ∀ a : α, FiniteCoproduct.incl X a ≫ f = FiniteCoproduct.incl X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/--
The coproduct cocone associated to the explicit finite coproduct.
-/
@[simps]
def FiniteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := FiniteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => FiniteCoproduct.incl X a

/--
The explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def FiniteCoproduct.isColimit : Limits.IsColimit (FiniteCoproduct.cocone X) where
  desc := fun s => FiniteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => FiniteCoproduct.incl_desc _ _ _
  uniq := fun s m hm => FiniteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

end FiniteCoproducts

end CompHaus
