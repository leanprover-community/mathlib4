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
  -- ⊢ ↑(fst f g ≫ f) { val := val✝, property := h } = ↑(snd f g ≫ g) { val := val✝ …
             -- 🎉 no goals

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : CompHaus.{u}} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g where
  toFun := fun z => ⟨⟨a z, b z⟩, by apply_fun (fun q => q z) at w; exact w⟩
                                    -- ⊢ (↑a z, ↑b z) ∈ {xy | ↑f xy.fst = ↑g xy.snd}
                                                                   -- 🎉 no goals
  continuous_toFun := by
    apply Continuous.subtype_mk
    -- ⊢ Continuous fun x => (↑a x, ↑b x)
    rw [continuous_prod_mk]
    -- ⊢ (Continuous fun x => ↑a x) ∧ Continuous fun x => ↑b x
    exact ⟨a.continuous, b.continuous⟩
    -- 🎉 no goals

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
  -- ⊢ ↑a z = ↑b z
  apply_fun (fun q => q z) at hfst hsnd
  -- ⊢ ↑a z = ↑b z
  apply Subtype.ext
  -- ⊢ ↑(↑a z) = ↑(↑b z)
  apply Prod.ext
  -- ⊢ (↑(↑a z)).fst = (↑(↑b z)).fst
  · exact hfst
    -- 🎉 no goals
  · exact hsnd
    -- 🎉 no goals

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
  -- ⊢ pullback.fst f g = (Limits.IsLimit.conePointUniqueUpToIso (pullback.isLimit  …
  simp only [Limits.limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt, pullback.cone_π]
  -- 🎉 no goals

theorem pullback_snd_eq :
    CompHaus.pullback.snd f g = (pullbackIsoPullback f g).hom ≫ Limits.pullback.snd := by
  dsimp [pullbackIsoPullback]
  -- ⊢ pullback.snd f g = (Limits.IsLimit.conePointUniqueUpToIso (pullback.isLimit  …
  simp only [Limits.limit.conePointUniqueUpToIso_hom_comp, pullback.cone_pt, pullback.cone_π]
  -- 🎉 no goals

end Isos

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
    -- ⊢ ∀ (i : α),
    intro a; exact (e a).continuous
    -- ⊢ Continuous fun a_1 =>
             -- 🎉 no goals

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : CompHaus.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : CompHaus.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  -- ⊢ ↑f { fst := a, snd := x } = ↑g { fst := a, snd := x }
  specialize h a
  -- ⊢ ↑f { fst := a, snd := x } = ↑g { fst := a, snd := x }
  apply_fun (fun q => q x) at h
  -- ⊢ ↑f { fst := a, snd := x } = ↑g { fst := a, snd := x }
  exact h
  -- 🎉 no goals

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
    -- ⊢ ι (fun a => X a) a ≫ m = ι (fun a => X a) a ≫ (fun s => desc (fun a => X a)  …
    ext t
    -- ⊢ ↑(ι (fun a => X a) a ≫ m) t = ↑(ι (fun a => X a) a ≫ (fun s => desc (fun a = …
    apply_fun (fun q => q t) at hm
    -- ⊢ ↑(ι (fun a => X a) a ≫ m) t = ↑(ι (fun a => X a) a ≫ (fun s => desc (fun a = …
    exact hm
    -- 🎉 no goals

section Iso

/-- The isomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductIsoCoproduct : finiteCoproduct X ≅ ∐ X :=
Limits.IsColimit.coconePointUniqueUpToIso (finiteCoproduct.isColimit X) (Limits.colimit.isColimit _)

theorem Sigma.ι_comp_toFiniteCoproduct (a : α) :
    (Limits.Sigma.ι X a) ≫ (coproductIsoCoproduct X).inv = finiteCoproduct.ι X a := by
  dsimp [coproductIsoCoproduct]
  -- ⊢ Limits.Sigma.ι X a ≫ (Limits.IsColimit.coconePointUniqueUpToIso (finiteCopro …
  simp only [Limits.colimit.comp_coconePointUniqueUpToIso_inv, finiteCoproduct.cocone_pt,
    finiteCoproduct.cocone_ι, Discrete.natTrans_app]

/-- The homeomorphism from the explicit finite coproducts to the abstract coproduct. -/
noncomputable
def coproductHomeoCoproduct : finiteCoproduct X ≃ₜ (∐ X : _) :=
CompHaus.homeoOfIso (coproductIsoCoproduct X)

end Iso

lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  -- ⊢ x = y
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2
  -- 🎉 no goals

lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {B : CompHaus} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  intro x
  -- ⊢ ↑(desc X π) (↑(ι X a) x) = ↑(π a) x
  change (ι X a ≫ desc X π) _ = _
  -- ⊢ ↑(ι X a ≫ desc X π) x = ↑(π a) x
  simp only [ι_desc]
  -- 🎉 no goals
-- `elementwise` should work here, but doesn't

end FiniteCoproducts

end CompHaus
