/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

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
  suffices ∀ (J : Type) [Finite J], P.IsClosedUnderLimitsOfShape (Discrete J) from ⟨this⟩
  intro J _
  induction J using Finite.induction_empty_option with
  | of_equiv e =>
    exact IsClosedUnderLimitsOfShape.of_equivalence (Discrete.equivalence e)
  | h_empty => infer_instance
  | h_option =>
    constructor
    rintro X ⟨p⟩
    have hc : IsLimit
        (BinaryFan.mk (Pi.lift (fun j ↦ p.π.app (.mk (some j)))) (p.π.app (.mk none))) :=
      BinaryFan.IsLimit.mk _
        (fun f₁ f₂ ↦ p.isLimit.lift (Cone.mk _ (Discrete.natTrans (fun ⟨j⟩ ↦ by
          induction j with
          | some j => exact f₁ ≫ Pi.π _ j
          | none => exact f₂))))
        (fun _ _ ↦ by dsimp; ext; simp [p.isLimit.fac])
        (fun _ _ ↦ by simp [p.isLimit.fac])
        (fun f₁ f₂ l hl₁ hl₂ ↦ by
          refine p.isLimit.hom_ext (fun ⟨j⟩ ↦ ?_)
          induction j with
          | some j => simp [p.isLimit.fac, ← hl₁]
          | none => simpa [p.isLimit.fac])
    refine P.prop_of_isLimit hc ?_
    rintro ⟨_ | _⟩
    · exact P.prop_limit _ (fun _ ↦ p.prop_diag_obj _)
    · exact p.prop_diag_obj _

end CategoryTheory.ObjectProperty
