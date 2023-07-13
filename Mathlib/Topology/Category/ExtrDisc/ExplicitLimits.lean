/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Category.ExtrDisc.Basic
/-!
# Explicit (co)limits in Extremally disconnected sets

This file describes some explicit (co)limits in `ExtrDisc`

## Overview

We define explicit finite coproducts in `ExtrDisc` as sigma types (disjoint unions).

TODO: Define pullbacks of open embeddings.

-/

open CategoryTheory

namespace ExtrDisc

/-!
This section defines the finite Coproduct of a finite family
of profinite spaces `X : α → ExtrDisc.{u}`

Notes: The content is mainly copied from
`Mathlib/Topology/Category/CompHaus/ExplicitLimits.lean`
-/
section FiniteCoproducts

open Limits

variable {α : Type} [Fintype α] {B : ExtrDisc.{u}}
  (X : α → ExtrDisc.{u})

/--
The coproduct of a finite family of objects in `ExtrDisc`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : ExtrDisc := ExtrDisc.of <| Σ (a : α), X a

/-- The inclusion of one of the factors into the explicit finite coproduct. -/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : ExtrDisc.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
@[simps]
def finiteCoproduct.cocone (F : Discrete α ⥤ ExtrDisc) :
    Cocone F where
  pt := finiteCoproduct F.obj
  ι := Discrete.natTrans fun a => finiteCoproduct.ι F.obj a

/-- The explicit finite coproduct cocone is a colimit cocone. -/
@[simps]
def finiteCoproduct.isColimit (F : Discrete α ⥤ ExtrDisc) :
    IsColimit (finiteCoproduct.cocone F) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app a
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm a
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

/-- The category of extremally disconnected spaces has finite coproducts.
-/
instance hasFiniteCoproducts : HasFiniteCoproducts ExtrDisc.{u} where
  out _ := {
    has_colimit := fun F => {
      exists_colimit := ⟨{
        cocone := finiteCoproduct.cocone F
        isColimit := finiteCoproduct.isColimit F }⟩ } }

/--
A coproduct cocone associated to the explicit finite coproduct with cone point `finiteCoproduct X`.
-/
@[simps]
def finiteCoproduct.explicitCocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The more explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit' : Limits.IsColimit (finiteCoproduct.explicitCocone X) where
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
Limits.IsColimit.coconePointUniqueUpToIso
  (finiteCoproduct.isColimit' X) (Limits.colimit.isColimit _)

theorem Sigma.ι_comp_toFiniteCoproduct (a : α) :
    finiteCoproduct.ι X a = (Limits.Sigma.ι X a) ≫ (FromFiniteCoproductIso X).inv := by
  dsimp [FromFiniteCoproductIso]
  simp only [colimit.comp_coconePointUniqueUpToIso_inv, finiteCoproduct.explicitCocone_pt,
    finiteCoproduct.explicitCocone_ι, Discrete.natTrans_app]

end Iso

end FiniteCoproducts

end ExtrDisc
