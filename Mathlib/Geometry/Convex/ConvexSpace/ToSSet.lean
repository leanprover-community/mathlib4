/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMapCone

/-!
# The simplicial set of affine simplices in a convex space

Let `Y` be a `R`-convex space. In this file, we introduce the simplicial
set `toSSet R Y` whose `n`-simplices are affine maps from
the standard `n`-dimensional simplex to `Y`. (When `R := ℝ` and `Y` has
a suitable topology, this identifies to a subcomplex of the singular
simplicial set of the topological space `Y`.)

For `y : Y`, we define a cone operation
`toSSet.cone : ((toSSet R Y).chainComplex M).X n ⟶ ((toSSet R Y).chainComplex M).X (n + 1)`
on the simplicial chains of `toSSet R Y` with coefficients in `M`,
as a linear extension of the cone of affine maps `AffineMap.cone`.
This cone operation is part of a homotopy which explains that the chain complex
of `toSSet R Y` is acyclic in nonzero degrees. The proof uses the technical notion
of extra degeneracy which also allows to show the stronger result that the
simplicial set `toSSet R Y` is contractible.

This construction shall be used in the construction of the subdivision operator
on the singular homology complex of topological spaces, which shall be used in the
proof of the excision theorem (TODO @joelriou).

-/

@[expose] public noncomputable section

universe w u

open CategoryTheory Limits

namespace Convexity.ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

variable (R) in
/-- Given a convex space `Y`, this is the simplicial set whose `n`-simplices are
affine maps from the `n`-dimensional standard simplex to `Y`. -/
@[simps -isSimp]
abbrev toSSet (Y : Type w) [ConvexSpace R Y] : SSet.{max u w} where
  obj n := ConvexSpace.AffineMap R (StdSimplex R (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)

variable {Y Z} in
/-- The morphism `toSSet R Y ⟶ toSSet R Z` of simplicial sets of
affine simplices that is induced by an affine map `φ` from `Y` to `Z`:
on simplices, it is induced by the postcomposition with `φ`. -/
@[simps]
def AffineMap.toSSetMap
    {Y Z : Type w} [ConvexSpace R Y] [ConvexSpace R Z]
    (φ : ConvexSpace.AffineMap R Y Z) :
    toSSet R Y ⟶ toSSet R Z where
  app n := ↾fun g ↦ φ.comp g

section

variable {Y : Type w} [ConvexSpace R Y]

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply

example (y₀ y₁ y₂ y₃ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁, y₂, y₃]) =
      StdSimplex.affineMapMk ![y₀, y₂, y₃] := by
  ext i; fin_cases i <;> simp [Fin.succAbove]

/-- The zeroth face of the cone of a simplex `s` is `s`. -/
@[simp]
lemma toSSet.δ_zero (y : Y) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    (toSSet R Y).δ 0 (s.cone y) = s := by
  aesop

/-- In the simplicial set `toSSet R Y`, the `i`th face of a simplex `[y₀, ..., yₙ₊₁]`
(considered as an affine map from the standard simplex to `Y`) is obtained by
dropping the `i`th vertex. -/
lemma toSSet.δ_affineMapMk {n : ℕ} (s : Fin (n + 2) → Y) (i : Fin (n + 2)) :
    (toSSet R Y).δ i (StdSimplex.affineMapMk s) = StdSimplex.affineMapMk (s ∘ i.succAbove) := by
  aesop

end

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply
  SimplicialObject.σ_def SimplexCategory.σ_apply in
/-- Given a convex space `Y` (over a semiring `R`) and `y : Y`, this is an extra degeneracy
for the augmented simplicial set attached to `ConvexSpace.toSSet R Y`.
In degree `0`, it is given by `[y]`, and otherwise it sends
a `n`-simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, where affine maps
from the standard `n`-simplex to `Y` are identified to tuples `[y₀, ..., yₙ]` corresponding
by the images of the vertices. (Note that this data implies that the simplicial set
`ConvexSpace.toSSet R Y` is contractible, see the example below.) -/
@[simps]
def toSSet.extraDegeneracy {Y : Type w} [ConvexSpace R Y] (y : Y) :
    (toSSet R Y).toAugmented.ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾fun f ↦ f.cone y
  s₀_comp_δ₁ := by ext _ i; fin_cases i; simp
  s_comp_δ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_δ₀ n := by ext; simp

example {Y : Type w} [ConvexSpace R Y] (y : Y) :
    SimplicialObject.Homotopy (SSet.const (AffineMap.const y)) (𝟙 (toSSet R Y)) :=
  (toSSet.extraDegeneracy y).homotopy

variable {Y Z : Type w} [ConvexSpace R Y] [ConvexSpace R Z]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{max u w} C]

/-- Given a convex space `Y`, `y : Y` and `n : ℕ`, this is the morphism from
affine `n`-chains (with coefficients in `M`) to affine `n + 1`-chains which
sends a simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, i.e. it is induced by
`ConvexSpace.AffineMap.cone`. -/
def toSSet.cone (y : Y) (M : C) (n : ℕ) :
    ((toSSet R Y).chainComplex M).X n ⟶ ((toSSet R Y).chainComplex M).X (n + 1) :=
  ((extraDegeneracy y).map (sigmaConst.obj M)).s n

/-- On `n`-chains, the morphism of chain complexes `toSSet.cone (R := R) y M n`
sends the simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, i.e. it is induced by
`ConvexSpace.AffineMap.cone`. -/
@[reassoc (attr := simp)]
lemma toSSet.ι_cone
    (y : Y) (M : C) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ toSSet.cone (R := R) y M n =
      SSet.ιChainComplex _ (s.cone y) := by
  simp [cone, SimplicialObject.Augmented.ExtraDegeneracy.map, SSet.ιChainComplex]

/-- Given a convex space `Y` and `y : Y`, the family of morphisms
`toSSet.cone y M n` form a homotopy between the identity of the chain
complex of `toSSet R Y` and a morphism which is zero in positive degrees. -/
@[simp]
lemma toSSet.d_comp_cone_add_cone_comp_d (y : Y) (M : C) {n : ℕ} :
    ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n +
    toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) = 𝟙 _ := by
  have := Preadditive.hasZeroObject_of_hasCoproduct C
  have := (((extraDegeneracy (R := R) y).map
    (sigmaConst.obj M)).homotopyEquiv.homotopyHomInvId.symm.comm (n + 1)).symm
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_succ_chainComplex] at this
  simpa [-AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv] using! this

@[inherit_doc d_comp_cone_add_cone_comp_d]
lemma toSSet.d_comp_cone_eq_sub (y : Y) (M : C) {n : ℕ} :
    ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n =
    𝟙 _ - toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) := by
  rw [← d_comp_cone_add_cone_comp_d y]
  abel

@[inherit_doc d_comp_cone_add_cone_comp_d]
lemma toSSet.cone_comp_d_eq_sub (y : Y) (M : C) {n : ℕ} :
    toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) =
    𝟙 _ - ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n := by
  rw [← d_comp_cone_add_cone_comp_d y]
  abel

@[reassoc]
lemma AffineMap.cone_naturality
    (φ : ConvexSpace.AffineMap R Y Z) (y : Y) (M : C) (n : ℕ) :
    (SSet.chainComplexMap φ.toSSetMap M).f n ≫ toSSet.cone (φ y) M n =
    toSSet.cone y M n ≫ (SSet.chainComplexMap φ.toSSetMap M).f (n + 1) := by
  ext x
  simp [AffineMap.cone_comp]

end Convexity.ConvexSpace
