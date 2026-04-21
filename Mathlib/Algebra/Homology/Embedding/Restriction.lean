/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Additive

/-!
# The restriction functor of an embedding of complex shapes

Given `c` and `c'` complex shapes on two types, and `e : c.Embedding c'`
(satisfying `[e.IsRelIff]`), we define the restriction functor
`e.restrictionFunctor C : HomologicalComplex C c' ⥤ HomologicalComplex C c`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

/-- Given `K : HomologicalComplex C c'` and `e : c.Embedding c'` (satisfying `[e.IsRelIff]`),
this is the homological complex in `HomologicalComplex C c` obtained by restriction. -/
@[simps]
def restriction : HomologicalComplex C c where
  X i := K.X (e.f i)
  d _ _ := K.d _ _
  shape i j hij := K.shape _ _ (by simpa only [← e.rel_iff] using hij)

/-- The isomorphism `(K.restriction e).X i ≅ K.X i'` when `e.f i = i'`. -/
def restrictionXIso {i : ι} {i' : ι'} (h : e.f i = i') :
    (K.restriction e).X i ≅ K.X i' :=
  eqToIso (h ▸ rfl)

@[reassoc]
lemma restriction_d_eq {i j : ι} {i' j' : ι'} (hi : e.f i = i') (hj : e.f j = j') :
    (K.restriction e).d i j = (K.restrictionXIso e hi).hom ≫ K.d i' j' ≫
      (K.restrictionXIso e hj).inv := by
  subst hi hj
  simp [restrictionXIso]

variable {K L}

/-- The morphism `K.restriction e ⟶ L.restriction e` induced by a morphism `φ : K ⟶ L`. -/
@[simps]
def restrictionMap : K.restriction e ⟶ L.restriction e where
  f i := φ.f (e.f i)

@[reassoc]
lemma restrictionMap_f' {i : ι} {i' : ι'} (hi : e.f i = i') :
    (restrictionMap φ e).f i = (K.restrictionXIso e hi).hom ≫
      φ.f i' ≫ (L.restrictionXIso e hi).inv := by
  subst hi
  simp [restrictionXIso]

variable (K)

@[simp]
lemma restrictionMap_id : restrictionMap (𝟙 K) e = 𝟙 _ := rfl

@[simp, reassoc]
lemma restrictionMap_comp :
    restrictionMap (φ ≫ φ') e = restrictionMap φ e ≫ restrictionMap φ' e := rfl

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') (C : Type*) [Category* C] [HasZeroObject C] [e.IsRelIff]

/-- Given `e : ComplexShape.Embedding c c'`, this is the restriction
functor `HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
def restrictionFunctor [HasZeroMorphisms C] :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.restriction e
  map φ := HomologicalComplex.restrictionMap φ e

instance [HasZeroMorphisms C] : (e.restrictionFunctor C).PreservesZeroMorphisms where

instance [Preadditive C] : (e.restrictionFunctor C).Additive where

end ComplexShape.Embedding
