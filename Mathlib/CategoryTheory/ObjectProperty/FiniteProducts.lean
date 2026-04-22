/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsClosure
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

lemma prop_of_isLimit_binaryFan [P.IsClosedUnderBinaryProducts] {X Y : C} {B : BinaryFan X Y}
    (hB : IsLimit B) (hX : P X) (hY : P Y) :
    P B.pt :=
  P.prop_of_isLimit hB (by rintro ⟨_ | _⟩ <;> assumption)

lemma prop_prod [P.IsClosedUnderBinaryProducts] (X Y : C) [HasBinaryProduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨯ Y) :=
  P.prop_of_isLimit_binaryFan (limit.isLimit _) hX hY

lemma prop_of_isTerminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsTerminal X) :
    P X :=
  P.prop_of_isLimit hX (by rintro ⟨⟨⟩⟩)

lemma prop_terminal [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] :
    P (⊤_ C) :=
  P.prop_of_isTerminal _ terminalIsTerminal

-- see Note [lower instance priority]
instance (priority := 100) [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [HasTerminal C] :
    P.Nonempty :=
  nonempty_of_prop P.prop_terminal

lemma IsClosedUnderBinaryProducts.closedUnderIsomorphisms [HasTerminal C]
    [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsLimit (BinaryFan.mk (terminal.from Y) e.inv) :=
      BinaryFan.IsLimit.mk _ (fun _ f ↦ f ≫ e.hom) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isLimit_binaryFan h P.prop_terminal hX

/-- All objects that are binary products of objects in `P`. -/
abbrev binaryProductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.limitClosure (Discrete WalkingPair)

lemma binaryProductsClosure_le_iff [HasTerminal C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryProducts] [Q.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryProductsClosure ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ (P.le_limitsClosure _).trans h, fun h ↦ ?_⟩
  letI : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryProducts.closedUnderIsomorphisms Q
  exact limitsClosure_le h

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

instance [HasFiniteProducts C] [P.IsClosedUnderFiniteProducts] :
    HasFiniteProducts P.FullSubcategory where
  out _ := inferInstance

lemma prop_of_isLimit_fan [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J → C}
    {F : Fan f} (hF : IsLimit F) (h : ∀ j, P (f j)) :
    P F.pt :=
  P.prop_of_isLimit hF (by intro ⟨j⟩; exact h j)

lemma prop_product [P.IsClosedUnderFiniteProducts] {J : Type*} [Finite J] {f : J → C}
    [HasProduct f] (h : ∀ j, P (f j)) :
    P (∏ᶜ f) :=
  P.prop_of_isLimit_fan (limit.isLimit (Discrete.functor f)) h

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsTerminal X :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
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

/-- The typeclass saying that `P : ObjectProperty C` is stable under binary coproducts. -/
abbrev IsClosedUnderBinaryCoproducts :=
  P.IsClosedUnderColimitsOfShape (Discrete WalkingPair)

lemma prop_of_isColimit_binaryCofan [P.IsClosedUnderBinaryCoproducts] {X Y : C}
    {B : BinaryCofan X Y} (hB : IsColimit B) (hX : P X) (hY : P Y) :
    P B.pt :=
  P.prop_of_isColimit hB (by rintro ⟨_ | _⟩ <;> assumption)

lemma prop_coprod [P.IsClosedUnderBinaryCoproducts] (X Y : C) [HasBinaryCoproduct X Y]
    (hX : P X) (hY : P Y) :
    P (X ⨿ Y) :=
  P.prop_of_isColimit_binaryCofan (colimit.isColimit (Limits.pair X Y)) hX hY

lemma prop_of_isInitial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
    (X : C) (hX : IsInitial X) :
    P X :=
  P.prop_of_isColimit hX (by rintro ⟨⟨⟩⟩)

lemma prop_initial [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] :
    P (⊥_ C) :=
  P.prop_of_isInitial _ initialIsInitial

-- see Note [lower instance priority]
instance (priority := 100) [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [HasInitial C] :
    P.Nonempty :=
  nonempty_of_prop P.prop_initial

set_option backward.defeqAttrib.useBackward true in
lemma IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms [HasInitial C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] [P.IsClosedUnderBinaryCoproducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let h : IsColimit (BinaryCofan.mk (initial.to Y) e.hom) :=
      BinaryCofan.IsColimit.mk _ (fun _ f ↦ e.inv ≫ f) (by cat_disch) (by simp) (by cat_disch)
    exact P.prop_of_isColimit_binaryCofan h P.prop_initial hX

/-- All objects that are binary coproducts of objects in `P`. -/
abbrev binaryCoproductsClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.colimitClosure (Discrete WalkingPair)

lemma binaryCoproductsClosure_le_iff [HasInitial C] {P Q : ObjectProperty C}
    [Q.IsClosedUnderBinaryCoproducts] [Q.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)] :
    P.binaryCoproductsClosure ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ (P.le_colimitsClosure _).trans h, fun h ↦ ?_⟩
  letI : Q.IsClosedUnderIsomorphisms := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms Q
  exact colimitsClosure_le h

/-- The typeclass saying that `P : ObjectProperty C` is stable under finite coproducts. -/
class IsClosedUnderFiniteCoproducts : Prop where
  isClosedUnderColimitsOfShape (J : Type) [Finite J] :
    P.IsClosedUnderColimitsOfShape (Discrete J) := by infer_instance

instance [P.IsClosedUnderFiniteCoproducts] (J : Type*) [Finite J] :
    P.IsClosedUnderColimitsOfShape (Discrete J) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have : P.IsClosedUnderColimitsOfShape (Discrete (Fin n)) :=
    IsClosedUnderFiniteCoproducts.isClosedUnderColimitsOfShape _
  exact IsClosedUnderColimitsOfShape.of_equivalence (Discrete.equivalence e.symm)

instance [HasFiniteCoproducts C] [P.IsClosedUnderFiniteCoproducts] :
    HasFiniteCoproducts P.FullSubcategory where
  out _ := inferInstance

lemma prop_of_isColimit_cofan [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J → C}
    {F : Cofan f} (hF : IsColimit F) (h : ∀ j, P (f j)) :
    P F.pt :=
  P.prop_of_isColimit hF (by intro ⟨j⟩; exact h j)

lemma prop_coproduct [P.IsClosedUnderFiniteCoproducts] {J : Type*} [Finite J] {f : J → C}
    [HasCoproduct f] (h : ∀ j, P (f j)) :
    P (∐ f) :=
  P.prop_of_isColimit_cofan (colimit.isColimit (Discrete.functor f)) h

instance [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty) where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    obtain ⟨Z, hZ, hZ₂⟩ := P.exists_prop_of_containsZero
    have hX : IsInitial X :=
      (IsColimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isColimit
    exact P.prop_of_isZero (IsZero.of_iso hZ
      (IsColimit.coconePointUniqueUpToIso hX (IsZero.isInitial hZ)))

variable {P} in
lemma IsClosedUnderFiniteCoproducts.mk' [HasFiniteCoproducts C]
    [P.IsClosedUnderColimitsOfShape (Discrete.{0} PEmpty)]
    [P.IsClosedUnderBinaryCoproducts] :
    P.IsClosedUnderFiniteCoproducts := by
  have := IsClosedUnderBinaryCoproducts.closedUnderIsomorphisms P
  have := hasFiniteCoproducts_of_has_binary_and_initial (C := P.FullSubcategory)
  have := PreservesFiniteCoproducts.of_preserves_binary_and_initial P.ι
  exact ⟨fun J _ ↦ P.isClosedUnderColimitsOfShape_of_preservesColimitsOfShape_ι _⟩

end CategoryTheory.ObjectProperty
