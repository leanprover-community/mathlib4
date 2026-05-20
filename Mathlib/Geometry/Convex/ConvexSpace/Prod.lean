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
  (by simp [Function.comp_def, iConvexComb_assoc])

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

end Prod

namespace Pi
variable {ι : Type*} {X : ι → Type*} [∀ i, ConvexSpace R (X i)] {i : ι}

instance : ConvexSpace R (∀ i, X i) := .mk
  (fun w i ↦ w.iConvexComb (· i))
  (by simp)
  (by simp [Function.comp_def, iConvexComb_assoc])

@[simp]
lemma sConvexComb_apply (w : StdSimplex R (∀ i, X i)) (i : ι) :
    w.sConvexComb i = w.iConvexComb (· i) := rfl

@[fun_prop]
lemma isAffineMap_eval : IsAffineMap R (· i : (∀ i, X i) → X i) where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex R I) (f : I → ∀ i, X i) (i : ι) :
    w.iConvexComb f i = w.iConvexComb (fun j ↦ f j i) := isAffineMap_eval.map_iConvexComb ..

end Pi
