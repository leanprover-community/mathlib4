/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.ObjectProperty.Opposite

/-!
# Object properties transported along morphisms

In this file we define the predicates `InheritedFromSource` and `InheritedFromTarget`
for an object property `P` along a morphism property `Q`.
`P` is inherited from the source (resp. target) along `Q` if for every morphism
`f : X ⟶ Y` with `Q f`, `P X` implies `P Y` (resp. `P Y` implies `P X`).
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]

namespace ObjectProperty

variable (P P' : ObjectProperty C) (Q Q' : MorphismProperty C)

/-- A property of objects `P` is inherited from the source of morphisms satisfying `Q` if
whenever `P` holds for `X` and `f : X ⟶ Y` is a `Q`-morphism, then `P` holds for `Y`. -/
class InheritedFromSource (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_source {X Y : C} (f : X ⟶ Y) (hf : Q f) : P X → P Y

/-- A property of objects `P` is inherited from the target of morphisms satisfying `Q` if
whenever `P` holds for `Y` and `f : X ⟶ Y` is a `Q`-morphism, then `P` holds for `X`. -/
class InheritedFromTarget (P : ObjectProperty C) (Q : MorphismProperty C) : Prop where
  of_hom_of_target {X Y : C} (f : X ⟶ Y) (hf : Q f) : P Y → P X

export InheritedFromSource (of_hom_of_source)
export InheritedFromTarget (of_hom_of_target)

namespace InheritedFromSource

instance [P.IsClosedUnderIsomorphisms] :
    P.InheritedFromSource (MorphismProperty.isomorphisms C) where
  of_hom_of_source f (_ : IsIso f) h := P.prop_of_iso (asIso f) h

instance op [P.InheritedFromSource Q] : P.op.InheritedFromTarget Q.op where
  of_hom_of_target f hf h := P.of_hom_of_source f.unop hf h

instance [P.InheritedFromSource Q] [P'.InheritedFromSource Q] :
    (P ⊓ P').InheritedFromSource Q where
  of_hom_of_source f hf h := ⟨P.of_hom_of_source f hf h.1, P'.of_hom_of_source f hf h.2⟩

lemma of_le (hQ : Q ≤ Q') [P.InheritedFromSource Q'] : P.InheritedFromSource Q where
  of_hom_of_source f hf h := P.of_hom_of_source f (hQ _ hf) h

end InheritedFromSource

namespace InheritedFromTarget

instance [P.IsClosedUnderIsomorphisms] :
    P.InheritedFromTarget (MorphismProperty.isomorphisms C) where
  of_hom_of_target f (_ : IsIso f) h := P.prop_of_iso (asIso f).symm h

instance op [P.InheritedFromTarget Q] : P.op.InheritedFromSource Q.op where
  of_hom_of_source f hf h := P.of_hom_of_target f.unop hf h

instance [P.InheritedFromTarget Q] [P'.InheritedFromTarget Q] :
    (P ⊓ P').InheritedFromTarget Q where
  of_hom_of_target f hf h := ⟨P.of_hom_of_target f hf h.1, P'.of_hom_of_target f hf h.2⟩

lemma of_le (hQ : Q ≤ Q') [P.InheritedFromTarget Q'] : P.InheritedFromTarget Q where
  of_hom_of_target f hf h := P.of_hom_of_target f (hQ _ hf) h

end InheritedFromTarget

lemma IsClosedUnderIsomorphisms.of_inheritedFromSource [P.InheritedFromSource Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_source e.hom (Q.of_isIso e.hom) h

lemma IsClosedUnderIsomorphisms.of_inheritedFromTarget [P.InheritedFromTarget Q] [Q.RespectsIso]
    [Q.ContainsIdentities] : P.IsClosedUnderIsomorphisms where
  of_iso e h := P.of_hom_of_target e.inv (Q.of_isIso e.inv) h

end ObjectProperty

end CategoryTheory
