/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Product of convex spaces

This file defines the cartesian product of convex spaces.
-/

open Convexity Finsupp Set

public noncomputable section

variable {I R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

namespace Prod
variable {X Y : Type*} [ConvexSpace R X] [ConvexSpace R Y]

instance : ConvexSpace R (X × Y) := .mk
  (fun w ↦ (w.iConvexComb fst, w.iConvexComb snd))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
lemma fst_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.fst = w.iConvexComb fst := rfl

@[simp]
lemma snd_sConvexComb (w : StdSimplex R (X × Y)) : w.sConvexComb.snd = w.iConvexComb snd := rfl

@[fun_prop]
lemma isAffineMap_fst : IsAffineMap R (fst : X × Y → X) where map_sConvexComb := fst_sConvexComb

@[fun_prop]
lemma isAffineMap_snd : IsAffineMap R (snd : X × Y → Y) where map_sConvexComb := snd_sConvexComb

@[simp]
lemma fst_iConvexComb (w : StdSimplex R I) (f : I → X × Y) :
    (w.iConvexComb f).fst = w.iConvexComb (fun i ↦ (f i).fst) :=
  isAffineMap_fst.map_iConvexComb ..

@[simp]
lemma snd_iConvexComb (w : StdSimplex R I) (f : I → X × Y) :
    (w.iConvexComb f).snd = w.iConvexComb (fun i ↦ (f i).snd) :=
  isAffineMap_snd.map_iConvexComb ..

@[simp]
lemma fst_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).fst = convexCombPair a b ha hb hab x.fst y.fst :=
  isAffineMap_fst.map_convexCombPair ..

@[simp]
lemma snd_convexCombPair (a b : R) (ha hb hab) (x y : X × Y) :
    (convexCombPair a b ha hb hab x y).snd = convexCombPair a b ha hb hab x.snd y.snd :=
  isAffineMap_snd.map_convexCombPair ..

end Prod

namespace Pi
variable {ι : Type*} {X : ι → Type*} [∀ i, ConvexSpace R (X i)] {i : ι}

instance : ConvexSpace R (∀ i, X i) := .mk
  (fun w i ↦ w.iConvexComb (· i))
  (by simp)
  (by simp [iConvexComb_assoc])

@[simp]
lemma sConvexComb_apply (w : StdSimplex R (∀ i, X i)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
lemma isAffineMap_eval : IsAffineMap R (· i : (∀ i, X i) → X i) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ∀ i, X i) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ∀ i, X i) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

end Pi

namespace Finsupp
variable {ι : Type*} {X : Type*} [Zero X] [ConvexSpace R X] {i : ι}

instance : ConvexSpace R (ι →₀ X) := .mk
  (fun w ↦ by
    classical
    refine .onFinset (w.weights.support.biUnion Finsupp.support) (fun i ↦ w.iConvexComb (· i)) ?_
    rintro i hi
    contrapose! hi
    simp_all)
  (by simp)
  (fun w ↦ by ext; simp [iConvexComb_assoc])

@[simp]
lemma sConvexComb_apply (w : StdSimplex R (ι →₀ X)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
lemma isAffineMap_eval : IsAffineMap R (· i : (ι →₀ X) → X) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ι →₀ X) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

@[simp]
lemma convexCombPair_apply (a b : R) (ha hb hab) (f g : ι →₀ X) (i : ι) :
    convexCombPair a b ha hb hab f g i = convexCombPair a b ha hb hab (f i) (g i) :=
  isAffineMap_eval.map_convexCombPair ..

end Finsupp
