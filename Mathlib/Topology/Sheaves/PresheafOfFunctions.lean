/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Category.TopCommRingCat
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheafToTypes X T`, where `T : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheafToType X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheafToTop X T`, where `T : TopCat`,
  is the presheaf of continuous functions into a topological space `T`
* `presheafToTopCommRing X R`, where `R : TopCommRingCat`
  is the presheaf valued in `CommRing` of functions functions into a topological ring `R`
* as an example of the previous construction,
  `presheafToTopCommRing X (TopCommRingCat.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/


universe v u

open CategoryTheory

open TopologicalSpace

open Opposite

namespace TopCat

variable (X : TopCat.{v})

/-- The presheaf of dependently typed functions on `X`, with fibres given by a type family `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToTypes (T : X → Type v) : X.Presheaf (Type v) where
  obj U := ∀ x : U.unop, T x
  map {U V} i g := fun x : V.unop => g (i.unop x)
  map_id U := by
    ext g
    rfl
  map_comp {U V W} i j := rfl

@[simp]
theorem presheafToTypes_obj {T : X → Type v} {U : (Opens X)ᵒᵖ} :
    (presheafToTypes X T).obj U = ∀ x : U.unop, T x :=
  rfl

@[simp]
theorem presheafToTypes_map {T : X → Type v} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToTypes X T).map i f = fun x => f (i.unop x) :=
  rfl

-- We don't just define this in terms of `presheafToTypes`,
-- as it's helpful later to see (at a syntactic level) that `(presheafToType X T).obj U`
-- is a non-dependent function.
-- We don't use `@[simps]` to generate the projection lemmas here,
-- as it turns out to be useful to have `presheafToType_map`
-- written as an equality of functions (rather than being applied to some argument).
/-- The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToType (T : Type v) : X.Presheaf (Type v) where
  obj U := U.unop → T
  map {U V} i g := g ∘ i.unop
  map_id U := by
    ext g
    rfl
  map_comp {U V W} i j := rfl

@[simp]
theorem presheafToType_obj {T : Type v} {U : (Opens X)ᵒᵖ} :
    (presheafToType X T).obj U = (U.unop → T) :=
  rfl

@[simp]
theorem presheafToType_map {T : Type v} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToType X T).map i f = f ∘ i.unop :=
  rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space
`T`. -/
def presheafToTop (T : TopCat.{v}) : X.Presheaf (Type v) :=
  (Opens.toTopCat X).op ⋙ yoneda.obj T

@[simp]
theorem presheafToTop_obj (T : TopCat.{v}) (U : (Opens X)ᵒᵖ) :
    (presheafToTop X T).obj U = ((Opens.toTopCat X).obj (unop U) ⟶ T) :=
  rfl

-- TODO upgrade the result to TopCommRing?
/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
def continuousFunctions (X : TopCat.{v}ᵒᵖ) (R : TopCommRingCat.{v}) : CommRingCat.{v} :=
  -- Porting note: Lean did not see through that `X.unop ⟶ R` is just continuous functions
  -- hence forms a ring
  @CommRingCat.of (X.unop ⟶ (forget₂ TopCommRingCat TopCat).obj R) <|
  show CommRing (ContinuousMap _ _) by infer_instance

namespace continuousFunctions

/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X Y : TopCatᵒᵖ} (f : X ⟶ Y) (R : TopCommRingCat) :
    continuousFunctions X R ⟶ continuousFunctions Y R where
  toFun g := f.unop ≫ g
  map_one' := rfl
  map_zero' := rfl
  map_add' := by aesop_cat
  map_mul' := by aesop_cat

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S) :
    continuousFunctions X R ⟶ continuousFunctions X S where
  toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
  -- Porting note: `ext` tactic does not work, since Lean can't see through `R ⟶ S` is just
  -- continuous ring homomorphism
  map_one' := ContinuousMap.ext fun _ => φ.1.map_one
  map_zero' := ContinuousMap.ext fun _ => φ.1.map_zero
  map_add' := fun _ _ => ContinuousMap.ext fun _ => φ.1.map_add _ _
  map_mul' := fun _ _ => ContinuousMap.ext fun _ => φ.1.map_mul _ _

end continuousFunctions

/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : TopCat` to `R : TopCommRingCat` form a commutative ring, functorial in both `X` and
`R`. -/
def commRingYoneda : TopCommRingCat.{u} ⥤ TopCat.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  obj R :=
    { obj := fun X => continuousFunctions X R
      map := fun {X Y} f => continuousFunctions.pullback f R
      map_id := fun X => by
        ext
        rfl
      map_comp := fun {X Y Z} f g => rfl }
  map {R S} φ :=
    { app := fun X => continuousFunctions.map X φ
      naturality := fun X Y f => rfl }
  map_id X := by
    ext
    rfl
  map_comp {X Y Z} f g := rfl

/-- The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex valued functions of `X` as
```
presheafToTopCommRing X (TopCommRingCat.of ℂ)
```
(this requires `import Topology.Instances.Complex`).
-/
def presheafToTopCommRing (T : TopCommRingCat.{v}) : X.Presheaf CommRingCat.{v} :=
  (Opens.toTopCat X).op ⋙ commRingYoneda.obj T

end TopCat
