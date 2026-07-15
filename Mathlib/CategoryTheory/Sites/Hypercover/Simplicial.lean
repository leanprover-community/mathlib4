/-
Copyright (c) 2026 Robin Carlier, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Semi
public import Mathlib.CategoryTheory.Functor.Bracket
public import Mathlib.CategoryTheory.MorphismProperty.LocalEpi
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# Hypercovers

In this file we define hypercovers as semi-simplicial objects satisfying a
covering condition.
-/

@[expose] public section

open CategoryTheory Limits SimplicialObject
  Simplicial

universe w v u

variable {C : Type*} [Category* C] (X : SemiSimplicialObject C) (K : SemiSSet.{w})

namespace CategoryTheory

instance [K.Nonsingular] [HasLimitsOfShape K.Nᵒᵈ C] : X.HasBracket K :=
  sorry

instance [K.Nonsingular] [HasFiniteLimits C] [K.Finite] : X.HasBracket K :=
  have := Fintype.ofFinite K.N
  inferInstance

/--
A semi-simplicial object in a category `C` with finite limits is a `P`-hypercover
if the natural map `X[Δⁿ] ⟶ X[∂Δⁿ]` satisfies `P`.

To obtain the usual notion of a hypercover on a site `C` with topology `J`, we
take a semi-simplicial object `H` in `FormalCoproduct C` and ask
for the induced semi-simplical object in `Cᵒᵖ ⥤ Type _` to be a `P`-hypercover, where
`P` is the class of "covering morphisms" (which SGA calls "morphisme couvrant"):
A morphism of presheafs `K ⟶ L` is covering if it becomes an epimorphism after
sheafification (see `CategoryTheory.ObjectProperty.localEpi`).

The `1`-truncation of a hypercover in the above sense induces a `1`-hypercover
(TODO).
-/
structure MorphismProperty.IsHypercover [HasFiniteLimits C] (P : MorphismProperty C) : Prop where
  prop_bracketMap (n : ℕ) : P (X.bracketMap <| (∂Δ[n]ₛ : (Δ[n]ₛ : SemiSSet.{0}).Subcomplex).ι)

/-- The `1`-truncation of a semi-simplical object in `FormalCoproduct.{w} (Over S)`
induces a pre-`1`-hypercover of `S`. -/
@[simps]
def SemiSimplicialObject.preOneHypercover {S : C}
    (H : SemiSimplicialObject (FormalCoproduct.{w} (Over S))) : PreOneHypercover.{w} S where
  I₀ := (H _⦋0⦌ₛ).I
  X i := ((H _⦋0⦌ₛ).obj i).left
  f i := ((H _⦋0⦌ₛ).obj i).hom
  I₁ i j := { x : (H _⦋1⦌ₛ).I // (H.δ 0).f x = i ∧ (H.δ 1).f x = j }
  Y _ _ k := ((H _⦋1⦌ₛ).obj k).left
  p₁ i j k := ((H.δ 0).φ k.1).left ≫ ((H _⦋0⦌ₛ).objIsoOfEq k.2.1).hom.left
  p₂ i j k := ((H.δ 1).φ k.1).left ≫ ((H _⦋0⦌ₛ).objIsoOfEq k.2.2).hom.left
  w := by simp

variable (J : GrothendieckTopology C)

variable {A : Type*} [Category* A]

/-- Covering morphisms in the sense of SGA. -/
def GrothendieckTopology.couvrant : MorphismProperty (Cᵒᵖ ⥤ A) :=
  ObjectProperty.localEpi (Presheaf.IsSheaf J)

/-- The `1`-truncation of a hypercover induces a `1`-hypercover. -/
def GrothendieckTopology.OneHypercover.ofIsHypercover {S : C}
    (H : SemiSimplicialObject (FormalCoproduct.{w} (Over S)))
    (h : (J.over S).couvrant.IsHypercover <| H ⋙ FormalCoproduct.uliftYoneda) :
    J.OneHypercover S where
  __ := H.preOneHypercover
  mem₀ := sorry
  mem₁ := sorry

end CategoryTheory
