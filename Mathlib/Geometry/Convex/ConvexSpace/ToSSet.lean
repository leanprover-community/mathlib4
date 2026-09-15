/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMapCone

/-!
# The simplicial set of affine simplices in a convex space

Let `Y` be a `R`-convex space. In this file, we introduce the simplicial
set `toSSet R Y` whose `n`-simplices are affine maps from
the standard `n`-dimensional simplex to `Y`. (When `R := ℝ` and `Y` has
a suitable topology, this identifies to a subcomplex of the singular
simplicial set of the topological space `Y`.)
When `Y` is nonempty, we show that `toSSet R Y` is contractible: for any `y : Y`,
we provide an extradegeneracy for the augmented simplicial set given
by `toSSet R Y` and `y`. The definition of this extradegeneracy involves
the cone of affine maps `AffineMap.cone`. We use this extradegeneracy
in order to define a cone operation
`toSSet.cone : ((toSSet R Y).chainComplex M).X n ⟶ ((toSSet R Y).chainComplex M).X (n + 1)`
on simplicial chains of `toSSet R Y` with coefficients in `M`.

-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace Convexity.ConvexSpace

variable {R : Type u} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

variable (R) in
/-- Given a convex space `Y`, this is the simplicial set whose `n`-simplices are
affine maps from the `n`-dimensional standard simplex to `Y`. -/
@[simps -isSimp]
noncomputable abbrev toSSet (Y : Type w) [ConvexSpace R Y] : SSet.{max u w} where
  obj n := ConvexSpace.AffineMap R (StdSimplex R (Fin (n.unop.len + 1))) Y
  map f := ↾fun g ↦ g.comp (StdSimplex.affineMap f.unop)

variable {Y Z} in
/-- The morphism `toSSet R Y ⟶ toSSet R Z` of simplicial sets of
affine simplices that is induced by an affine map from `Y` to `Z`. -/
@[simps]
noncomputable def AffineMap.toSSetMap
    {Y Z : Type w} [ConvexSpace R Y] [ConvexSpace R Z]
    (φ : ConvexSpace.AffineMap R Y Z) :
    toSSet R Y ⟶ toSSet R Z where
  app n := ↾fun g ↦ φ.comp g

section

variable {Y : Type w} [ConvexSpace R Y]

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply

@[simp]
lemma toSSet.δ_zero_affineMapMk₂ (y₀ y₁ : Y) :
    (toSSet R Y).δ 0 (StdSimplex.affineMapMk ![y₀, y₁]) =
      StdSimplex.affineMapMk ![y₁] := by
  ext i; fin_cases i; simp

@[simp high]
lemma toSSet.δ_one_affineMapMk₂ (y₀ y₁ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁]) =
      StdSimplex.affineMapMk ![y₀] := by
  ext i; fin_cases i; simp

@[simp]
lemma toSSet.δ_zero_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 0 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₁, y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma toSSet.δ_one_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 1 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₀, y₂] := by
  ext i; fin_cases i <;> simp

@[simp]
lemma toSSet.δ_two_affineMapMk₃ (y₀ y₁ y₂ : Y) :
    (toSSet R Y).δ 2 (StdSimplex.affineMapMk ![y₀, y₁, y₂]) =
      StdSimplex.affineMapMk ![y₀, y₁] := by
  ext i; fin_cases i <;> simp [Fin.succAbove]

@[simp]
lemma toSSet.δ_zero (y : Y) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    (toSSet R Y).δ 0 (s.cone y) = s := by
  ext
  simp [SimplicialObject.δ_def, SimplexCategory.δ_apply,
    AffineMap.cone_def, StdSimplex.affineMapMk_apply]

lemma toSSet.δ_affineMapMk {n : ℕ} (s : Fin (n + 2) → Y)
    (i : Fin (n + 2)) :
    (toSSet R Y).δ i (StdSimplex.affineMapMk s) = StdSimplex.affineMapMk (s ∘ i.succAbove) := by
  aesop

end

variable (R) in
/-- Given a convex space `Y`, this is the augmented simplicial set
whose `n`-simplices are affine maps from the `n`-dimensional standard simplex to `Y`. -/
noncomputable abbrev toSSetAugmented (Y : Type w) [ConvexSpace R Y] :
    SSet.Augmented where
  left := toSSet R Y
  right := PUnit
  hom.app _ := ↾fun _ ↦ .unit

attribute [local simp] SimplicialObject.δ_def SimplexCategory.δ_apply
  SimplicialObject.σ_def SimplexCategory.σ_apply in
variable {Y} in
/-- Given a convex space `Y` (over a semiring `R`) and `y : Y`, this is an extra degeneracy
for `ConvexSpace.toSSetAugmented R Y`. In degree `0`, it is given by `[y]`, and otherwise
it sends a `n`-simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`, where affine maps
from the standard `n`-simplex to `Y` are identified to tuples `[y₀, ..., yₙ]` given
by the images of the vertices. -/
@[simps]
noncomputable def toSSet.extraDegeneracy {Y : Type w} [ConvexSpace R Y] (y : Y) :
    (toSSetAugmented R Y).ExtraDegeneracy where
  s' := ↾fun _ ↦ .const y
  s n := ↾fun f ↦ f.cone y
  s₀_comp_δ₁ := by ext _ i; fin_cases i; simp
  s_comp_δ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_σ _ _ := by ext _ j; obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ <;> simp
  s_comp_δ₀ n := by ext; simp

variable {Y Z : Type w} [ConvexSpace R Y] [ConvexSpace R Z]
  {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{max u w} C]

/-- Given a convex space `Y`, `y : Y` and `n : ℕ`, this is the morphism from
affine `n`-chains (with coefficients in `M`) to affine `n + 1`-chains which
sends a simplex `[y₀, ..., yₙ]` to `[y, y₀, ..., yₙ]`. -/
noncomputable def toSSet.cone (y : Y) (M : C) (n : ℕ) :
    ((toSSet R Y).chainComplex M).X n ⟶
      ((toSSet R Y).chainComplex M).X (n + 1) :=
  ((extraDegeneracy y).map (sigmaConst.obj M)).s n

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

lemma toSSet.d_comp_cone_eq_sub (y : Y) (M : C) {n : ℕ} :
    ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n =
    𝟙 _ - toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) := by
  rw [← d_comp_cone_add_cone_comp_d y]
  abel

lemma toSSet.cone_comp_d_eq_sub (y : Y) (M : C) {n : ℕ} :
    toSSet.cone y M (n + 1) ≫ ((toSSet R Y).chainComplex M).d (n + 2) (n + 1) =
    𝟙 _ - ((toSSet R Y).chainComplex M).d (n + 1) n ≫ toSSet.cone y M n := by
  rw [← d_comp_cone_add_cone_comp_d y]
  abel

@[reassoc (attr := simp)]
lemma toSSet.ι_cone
    (y : Y) (M : C) {n : ℕ} (s : ConvexSpace.AffineMap R (StdSimplex R (Fin (n + 1))) Y) :
    SSet.ιChainComplex _ s ≫ toSSet.cone (R := R) y M n =
      SSet.ιChainComplex _ (s.cone y) := by
  simp [cone, SimplicialObject.Augmented.ExtraDegeneracy.map, SSet.ιChainComplex]

@[reassoc]
lemma AffineMap.cone_naturality
    (φ : ConvexSpace.AffineMap R Y Z) (y : Y) (M : C) (n : ℕ) :
    (SSet.chainComplexMap φ.toSSetMap M).f n ≫ toSSet.cone (φ y) M n =
    toSSet.cone y M n ≫ (SSet.chainComplexMap φ.toSSetMap M).f (n + 1) := by
  ext x
  simp [AffineMap.cone_comp]

end Convexity.ConvexSpace
