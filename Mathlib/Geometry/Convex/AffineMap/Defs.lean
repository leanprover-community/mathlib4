/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap

/-!
# The convex space of affine maps

This file shows that affine maps between two convex spaces `X` and `Y` themselves form a convex
space under pointwise convex combinations.
-/

@[expose] public section

namespace Convexity
variable {R S X Y Z I : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Semiring S]
  [PartialOrder S] [IsStrictOrderedRing S] [ConvexSpace R X] [ConvexSpace R Y] [ConvexSpace S Y]
  [ConvexSpace R Z] [ConvexSpace S Z] [IsConvexCombComm S R Y]

/-- A pointwise `S`-convex combination of `R`-affine maps is `R`-affine.

This requires the `R`-convex space and `S`-convex space structures on the codomain to commute, as it
essentially swaps around two combinations. -/
@[fun_prop]
protected lemma IsAffineMap.iConvexComb {f : I → X → Y} (hf : ∀ i, IsAffineMap R (f i))
    (w : StdSimplex S I) : IsAffineMap R fun x ↦ w.iConvexComb (f · x) where
  map_sConvexComb s := by
    have hfs (i : I) : f i s.sConvexComb = s.iConvexComb (f i) := (hf i).map_sConvexComb s
    simp only [hfs, sConvexComb_map]
    exact iConvexComb_comm ..

namespace ConvexSpace.AffineMap

noncomputable instance instConvexSpace : ConvexSpace S (ConvexSpace.AffineMap R X Y) := .mk
  (sConvexComb := fun w ↦ ⟨fun x ↦ w.iConvexComb (· x), by fun_prop⟩)
  (single := fun f ↦ by ext; simp)
  (assoc := fun W ↦ by ext; simp [iConvexComb_assoc])

@[simp]
lemma sConvexComb_apply (w : StdSimplex S (ConvexSpace.AffineMap R X Y)) (x : X) :
    w.sConvexComb x = w.iConvexComb (· x) := rfl

/-- Evaluation at a point is affine in the affine map. -/
@[fun_prop]
lemma isAffineMap_eval (x : X) : IsAffineMap S fun f : ConvexSpace.AffineMap R X Y ↦ f x where
  map_sConvexComb _ := sConvexComb_apply ..

@[simp]
lemma iConvexComb_apply (w : StdSimplex S I) (f : I → ConvexSpace.AffineMap R X Y) (x : X) :
    w.iConvexComb f x = w.iConvexComb fun i ↦ f i x := (isAffineMap_eval x).map_iConvexComb ..

@[simp]
lemma convexCombPair_apply (a b : S) (ha hb hab) (f g : ConvexSpace.AffineMap R X Y) (x : X) :
    convexCombPair a b ha hb hab f g x = convexCombPair a b ha hb hab (f x) (g x) :=
  (isAffineMap_eval x).map_convexCombPair ..

@[fun_prop]
lemma isAffineMap_const_comp [IsConvexCombComm S R Z] (g : ConvexSpace.AffineMap R Y Z)
    (hg : IsAffineMap S g) :
    IsAffineMap S (g.comp : ConvexSpace.AffineMap R X Y → ConvexSpace.AffineMap R X Z) where
  map_sConvexComb w := by ext x; simpa using hg.map_iConvexComb w (· x)

omit [ConvexSpace S Y] [IsConvexCombComm S R Y] in
@[fun_prop]
lemma isAffineMap_comp_const [IsConvexCombComm S R Z] (f : ConvexSpace.AffineMap R X Y) :
    IsAffineMap S fun g : ConvexSpace.AffineMap R Y Z ↦ g.comp f where
  map_sConvexComb w := by ext x; simp

end ConvexSpace.AffineMap
end Convexity
