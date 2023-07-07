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
def pullback : CompHaus.{u} :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set := by
    rw [← isCompact_iff_compactSpace]
    apply IsClosed.isCompact
    exact isClosed_eq (f.continuous.comp continuous_fst) (g.continuous.comp continuous_snd)
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

noncomputable
def ToExplicit : Limits.pullback f g ⟶ CompHaus.pullback f g :=
  pullback.lift f g Limits.pullback.fst Limits.pullback.snd Limits.pullback.condition

noncomputable
def FromExplicit : CompHaus.pullback f g ⟶ Limits.pullback f g :=
  Limits.pullback.lift (pullback.fst _ _) (pullback.snd _ _) (pullback.condition f g)

@[simp]
theorem toExplicit_comp_fromExplicit_eq_id :
    (ToExplicit f g ≫ FromExplicit f g) = 𝟙 _ := by
  refine' Limits.pullback.hom_ext (k := (ToExplicit f g ≫ FromExplicit f g)) _ _
  · simp [ToExplicit, FromExplicit]
  · rw [Category.id_comp, Category.assoc, FromExplicit, Limits.pullback.lift_snd,
      ToExplicit, pullback.lift_snd]

@[simp]
theorem fromExplicit_comp_toExplicit_eq_id :
    (FromExplicit f g ≫ ToExplicit f g) = 𝟙 _ :=
  pullback.hom_ext f g _ _ (by simp [ToExplicit, FromExplicit]) (by simp [ToExplicit, FromExplicit])

@[simps]
noncomputable
def FromExplicitIso : CompHaus.pullback f g ≅ Limits.pullback f g where
  hom := FromExplicit f g
  inv := ToExplicit f g
  hom_inv_id := fromExplicit_comp_toExplicit_eq_id f g
  inv_hom_id := toExplicit_comp_fromExplicit_eq_id f g

end Isos

section Compatibility

theorem explicit_fst_eq :
    CompHaus.pullback.fst f g = FromExplicit f g ≫ Limits.pullback.fst := by
  dsimp [FromExplicit]
  simp only [Limits.limit.lift_π, Limits.PullbackCone.mk_pt, Limits.PullbackCone.mk_π_app]

theorem explicit_snd_eq :
    CompHaus.pullback.snd f i = FromExplicit f i ≫ Limits.pullback.snd := by
  dsimp [FromExplicit]
  simp only [Limits.limit.lift_π, Limits.PullbackCone.mk_pt, Limits.PullbackCone.mk_π_app]

end Compatibility

end Pullbacks

section FiniteCoproducts

variable {α : Type} [Fintype α] (X : α → CompHaus.{u})

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
def finiteCoproduct.desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : CompHaus.{u}} (f g : finiteCoproduct X ⟶ B)
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
def ToFiniteCoproduct : ∐ X ⟶ finiteCoproduct X :=
  Limits.Sigma.desc <| fun a => finiteCoproduct.ι X a ≫ (𝟙 _)

noncomputable
def FromFiniteCoproduct : finiteCoproduct X ⟶ ∐ X :=
  finiteCoproduct.desc X <| fun a => (Limits.Sigma.ι X a)

@[simp]
theorem toFiniteCoproduct_comp_fromFiniteCoproduct_eq_id :
    (ToFiniteCoproduct X ≫ FromFiniteCoproduct X) = 𝟙 _ := by
  ext
  simp [ToFiniteCoproduct, FromFiniteCoproduct]

@[simp]
theorem fromFiniteCoproduct_comp_toFiniteCoproduct_eq_id :
    (FromFiniteCoproduct X ≫ ToFiniteCoproduct X) = 𝟙 _ := by
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  simp [ToFiniteCoproduct, FromFiniteCoproduct]

@[simps]
noncomputable
def FromFiniteCoproductIso : finiteCoproduct X ≅ ∐ X where
  hom := FromFiniteCoproduct X
  inv := ToFiniteCoproduct X
  hom_inv_id := fromFiniteCoproduct_comp_toFiniteCoproduct_eq_id X
  inv_hom_id := toFiniteCoproduct_comp_fromFiniteCoproduct_eq_id X

@[simps]
noncomputable
def ToFiniteCoproductIso : ∐ X ≅ finiteCoproduct X where
  hom := ToFiniteCoproduct X
  inv := FromFiniteCoproduct X
  hom_inv_id := toFiniteCoproduct_comp_fromFiniteCoproduct_eq_id X
  inv_hom_id := fromFiniteCoproduct_comp_toFiniteCoproduct_eq_id X

theorem isIso_toFiniteCoproduct :
    IsIso (ToFiniteCoproduct X) :=
  ⟨FromFiniteCoproduct X, by simp, by simp⟩

theorem isIso_fromFiniteCoproduct :
    IsIso (FromFiniteCoproduct X) :=
  ⟨ToFiniteCoproduct X, by simp, by simp⟩

@[simp]
theorem Sigma.ι_comp_toFiniteCoproduct (a : α) :
    (Limits.Sigma.ι X a) ≫ ToFiniteCoproduct X = finiteCoproduct.ι X a := by
  simp [ToFiniteCoproduct]

@[simp]
theorem finiteCoproduct.ι_comp_fromFiniteCoproduct (a : α) :
    (finiteCoproduct.ι X a) ≫ FromFiniteCoproduct X = Limits.Sigma.ι X a := by
  simp [FromFiniteCoproduct]

@[simps] noncomputable
def ToFiniteCoproductHomeo : (∐ X : _) ≃ₜ finiteCoproduct X where
  toFun := ToFiniteCoproduct X
  invFun := FromFiniteCoproduct X
  left_inv := fun x => by
    change (ToFiniteCoproduct X ≫ FromFiniteCoproduct X) x = x
    simp only [toFiniteCoproduct_comp_fromFiniteCoproduct_eq_id, id_apply]
  right_inv := fun x => by
    change (FromFiniteCoproduct X ≫ ToFiniteCoproduct X) x = x
    simp only [fromFiniteCoproduct_comp_toFiniteCoproduct_eq_id, id_apply]
  continuous_toFun := (ToFiniteCoproduct X).continuous_toFun
  continuous_invFun := (FromFiniteCoproduct X).continuous_toFun

theorem ToFiniteCoproduct.OpenEmbedding : OpenEmbedding (ToFiniteCoproductHomeo X) :=
  Homeomorph.openEmbedding (ToFiniteCoproductHomeo X)

end Iso

lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := by
  exact ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {B : CompHaus} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  intro x
  change (ι X a ≫ desc X π) _ = _
  simp only [ι_desc]

end FiniteCoproducts

end CompHaus
