/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Properties of objects that are stable under finite products

We introduce typeclasses `IsClosedUnderBinaryProducts` and
`IsClosedUnderFiniteProducts` expressing that `P : ObjectProperty C`
is closed under binary products or finite products.
We introduce a constructor for `P.IsClosedUnderFiniteProducts`
assuming `P.IsClosedUnderBinaryProducts`,
`P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)` and that `C`
has finite products.

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

/-- The typeclass saying that `P : ObjectProperty C` is stable under binary products. -/
abbrev IsClosedUnderBinaryProducts :=
    P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)

lemma prop_prod [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨯ Y) :=
  P.prop_limit _ (by rintro ⟨_ | _⟩ <;> assumption)

lemma prop_of_isTerminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsTerminal X) :
    P X :=
  P.prop_of_isLimit hX (by rintro ⟨⟨⟩⟩)

lemma IsClosedUnderBinaryProducts.closedUnderIsomorphisms [HasTerminal C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsLimit (BinaryFan.mk (terminal.from Y) e.inv) :=
      BinaryFan.IsLimit.mk _ (fun _ f ↦ f ≫ e.hom) (by cat_disch) (by simp) (by cat_disch)
    apply P.prop_of_isLimit h
    rintro (_ | _)
    · exact P.prop_of_isTerminal _ terminalIsTerminal
    · exact hX

/-- The typeclass saying that `P : ObjectProperty C` is stable under finite products. -/
class IsClosedUnderFiniteProducts : Prop where
  isClosedUnderLimitsOfShape (J : Type) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) := by infer_instance

instance [P.IsClosedUnderFiniteProducts] (J : Type*) [Finite J] :
    P.IsClosedUnderLimitsOfShape (Discrete J) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderLimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteProducts.isClosedUnderLimitsOfShape _
  exact IsClosedUnderLimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cones.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsLimit.conePointUniqueUpToIso hX (IsZero.isTerminal hZ)))

variable {P} in
lemma IsClosedUnderFiniteProducts.mk' [HasFiniteProducts C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderFiniteProducts := by
  have := IsClosedUnderBinaryProducts.closedUnderIsomorphisms P
  have := hasFiniteProducts_of_has_binary_and_terminal (C := P.FullSubcategory)
  have := PreservesFiniteProducts.of_preserves_binary_and_terminal P.ι
  exact ⟨fun J _ ↦ P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _⟩

end CategoryTheory.ObjectProperty
