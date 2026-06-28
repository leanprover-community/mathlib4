/-
Copyright (c) 2026 Robin Carlier, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Christian Merten
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Semi
public import Mathlib.CategoryTheory.Functor.Bracket

@[expose] public section

/-!
# Hypercovers

In this file we define hypercovers as semi-simplicial objects satisfying a
covering condition.
-/

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

end CategoryTheory
