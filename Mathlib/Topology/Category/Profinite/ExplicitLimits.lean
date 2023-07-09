/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks

/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHaus`,
which may be useful due to their definitional properties.

So far, we have the following:
- Explicit pullbacks, defined in the "usual" way as a subset of the product.
- Explicit finite coproducts, defined as a disjoint union.

-/

namespace Profinite

universe u

open CategoryTheory

section Pullbacks

variable {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/--
The pullback of two morphisms `f,g` in `Profinite`, constructed explicitly as the set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
def pullback : Profinite.{u} :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
  isCompact_iff_compactSpace.mp (isClosed_eq (f.continuous.comp continuous_fst)
    (g.continuous.comp continuous_snd)).isCompact
  Profinite.of set

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
def pullback.lift {Z : Profinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_prod_mk]
    exact ⟨a.continuous, b.continuous⟩

@[reassoc (attr := simp)]
lemma pullback.lift_fst {Z : Profinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
  pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
lemma pullback.lift_snd {Z : Profinite.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
  pullback.lift f g a b w ≫ pullback.snd f g = b := rfl

lemma pullback.hom_ext {Z : Profinite.{u}} (a b : Z ⟶ pullback f g)
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

noncomputable
def FromExplicitIso : Profinite.pullback f g ≅ Limits.pullback f g :=
Limits.IsLimit.conePointUniqueUpToIso (pullback.isLimit f g) (Limits.limit.isLimit _)

theorem explicit_fst_eq :
    Profinite.pullback.fst f g = (FromExplicitIso f g).hom ≫ Limits.pullback.fst := by
  dsimp [FromExplicitIso]
  simp only [Limits.limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt, pullback.cone_π]

theorem explicit_snd_eq :
    Profinite.pullback.snd f g = (FromExplicitIso f g).hom ≫ Limits.pullback.snd := by
  dsimp [FromExplicitIso]
  simp only [Limits.limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt, pullback.cone_π]

end Isos

end Pullbacks

section FiniteCoproducts

variable {α : Type} [Fintype α] (X : α → Profinite.{u})

/--
The coproduct of a finite family of objects in `Profinite`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : Profinite := Profinite.of <| Σ (a : α), X a

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
def finiteCoproduct.desc {B : Profinite.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : Profinite.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : Profinite.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/--
The coproduct cocone associated to the explicit finite coproduct.
-/
@[simps]
def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

section Iso

noncomputable
def FromFiniteCoproductIso : finiteCoproduct X ≅ ∐ X :=
Limits.IsColimit.coconePointUniqueUpToIso (finiteCoproduct.isColimit X) (Limits.colimit.isColimit _)

@[simp]
theorem Sigma.ι_comp_toFiniteCoproduct (a : α) :
    finiteCoproduct.ι X a = (Limits.Sigma.ι X a) ≫ (FromFiniteCoproductIso X).inv := by
  dsimp [FromFiniteCoproductIso]
  simp only [Limits.colimit.comp_coconePointUniqueUpToIso_inv, finiteCoproduct.cocone_pt,
    finiteCoproduct.cocone_ι, Discrete.natTrans_app]

@[simp]
theorem finiteCoproduct.ι_comp_fromFiniteCoproduct (a : α) :
    (finiteCoproduct.ι X a) ≫ (FromFiniteCoproductIso X).hom = Limits.Sigma.ι X a := by
  simp only [Sigma.ι_comp_toFiniteCoproduct, Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable
def ToFiniteCoproductHomeo : finiteCoproduct X ≃ₜ (∐ X : _) :=
Profinite.homeoOfIso (FromFiniteCoproductIso X)

end Iso

lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {B : Profinite} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  intro x
  change (ι X a ≫ desc X π) _ = _
  simp only [ι_desc]

end FiniteCoproducts

end Profinite
