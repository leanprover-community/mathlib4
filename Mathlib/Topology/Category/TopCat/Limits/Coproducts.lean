/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.Topology.Category.TopCat.Limits.Basic

open CategoryTheory

namespace TopCat

universe v u

variable {α : Type v} (X : α → TopCatMax.{u, v})

def coproduct : TopCatMax.{u, v} where
  α := (a : α) × (X a)

def coproduct.desc {W : TopCatMax.{u, v}} (π : (a : α) → X a ⟶ W) :
    coproduct X ⟶ W where
  toFun := fun ⟨a,x⟩ => π a x
  continuous_toFun := by
    apply continuous_sigma
    intro a
    exact (π a).continuous

def coproduct.ι (a : α) : X a ⟶ coproduct X where
  toFun := (⟨a,·⟩)
  continuous_toFun := by apply continuous_sigmaMk (i := a)

@[reassoc (attr := simp)]
lemma coproduct.ι_desc {W : TopCatMax.{u, v}} (π : (a : α) → X a ⟶ W) (a : α) :
    coproduct.ι X a ≫ coproduct.desc X π = π a :=
  rfl

lemma coproduct.hom_ext {W : TopCatMax.{u, v}} (f g : coproduct X ⟶ W)
  (h : ∀ a : α, coproduct.ι X a ≫ f = coproduct.ι X a ≫ g) :
    f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun e => e x) at h
  exact h

end TopCat
