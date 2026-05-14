/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
public import Mathlib.CategoryTheory.GuitartExact.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.GuitartExact.Opposite
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Guitart exact squares and quotient categories

Consider a commutative square of categories given by a natural isomorphism
`e : T ⋙ R ≅ L ⋙ B`:
```
      T
 C₀ ----> H₀
 |        |
L|        |R
 v        v
 C  ----> H
      B
```

If both `T` and `B` are full and `T` is essentially surjective, we show
that the `2`-square above is Guitart exact if, whenever two morphisms
`f₀` and `f₁` in `L.obj X₀ ⟶ Y` (for `X₀ : C₀` and `Y : C`) become equal
after applying `B`, there exists a precylinder object `P` of `X₀`
such that `T.map P.i₀ = T.map i₁` and there exists a left homotopy
between `f₀` and `f₁` for `P.map L`. The dual result is also obtained.

This result shall be applied in the situation where `C₀` is a suitable
full subcategory of a category `C` of homological complexes, and `H₀` and `H`
are the corresponding homotopy categories (TODO @joelriou).

-/

public section

namespace CategoryTheory.TwoSquare.GuitartExact

open HomotopicalAlgebra Opposite

variable {C₀ C H₀ H : Type*} [Category* C₀] [Category* C] [Category* H₀] [Category* H]
  {T : C₀ ⥤ H₀} {L : C₀ ⥤ C} {R : H₀ ⥤ H} {B : C ⥤ H}
  [T.EssSurj] [T.Full] [B.Full]

set_option backward.isDefEq.respectTransparency false in
lemma quotient_of_nonempty_leftHomotopy (e : T ⋙ R ≅ L ⋙ B)
    (he : ∀ ⦃X₀ : C₀⦄ ⦃Y : C⦄ (f₀ f₁ : L.obj X₀ ⟶ Y) (_ : B.map f₀ = B.map f₁),
      ∃ (P : Precylinder X₀), T.map P.i₀ = T.map P.i₁ ∧
        Nonempty ((P.map L).LeftHomotopy f₀ f₁)) :
    GuitartExact e.hom := by
  rw [guitartExact_iff_isConnected_downwards]
  intro Y₀ X g
  let X₀ := T.objPreimage Y₀
  let e₀ : T.obj X₀ ≅ Y₀ := T.objObjPreimageIso Y₀
  let S := { f : L.obj X₀ ⟶ X // B.map f = e.inv.app X₀ ≫ R.map e₀.hom ≫ g }
  let Z (s : S) : CostructuredArrowDownwards e.hom g :=
    CostructuredArrowDownwards.mk _ _ X₀ e₀.inv s.val (by simp [s.property])
  have : Nonempty (CostructuredArrowDownwards e.hom g) := by
    obtain ⟨f, hf⟩ := B.map_surjective (e.inv.app _ ≫ R.map e₀.hom ≫ g)
    exact ⟨Z ⟨f, hf⟩⟩
  refine zigzag_isConnected (fun A₀ A₁ ↦ ?_)
  have H (A : CostructuredArrowDownwards e.hom g) : ∃ s, Nonempty (Z s ⟶ A) := by
    obtain ⟨a, ha⟩ := T.map_surjective (e₀.hom ≫ A.left.hom)
    refine ⟨⟨L.map a ≫ A.hom.right, ?_⟩,
      ⟨CostructuredArrow.homMk (StructuredArrow.homMk a ?_)⟩⟩
    · simp [← dsimp% NatIso.naturality_1 e a, ha, dsimp% A.hom.w]
    · cat_disch
  obtain ⟨s₀, ⟨f₀⟩⟩ := H A₀
  obtain ⟨s₁, ⟨f₁⟩⟩ := H A₁
  obtain ⟨P, hP, ⟨h⟩⟩ := he s₀.val s₁.val (by simp [s₀.property, s₁.property])
  let Z' : CostructuredArrowDownwards e.hom g :=
    CostructuredArrowDownwards.mk _ _ P.I (e₀.inv ≫ T.map P.i₀) h.h (by
      simp [R.map_comp, ← B.map_comp, dsimp% h.h₀, s₀.property,
        dsimp% e.hom.naturality_assoc P.i₀])
  calc
    Zigzag A₀ (Z s₀) := .of_inv f₀
    Zigzag (Z s₀) Z' := .of_hom <|
      CostructuredArrow.homMk (StructuredArrow.homMk P.i₀) (by simp [Z, Z', dsimp% h.h₀])
    Zigzag Z' (Z s₁) := .of_inv <|
      CostructuredArrow.homMk (StructuredArrow.homMk P.i₁) (by simp [Z, Z', dsimp% h.h₁])
    Zigzag (Z s₁) A₁ := .of_hom f₁

lemma quotient_of_nonempty_rightHomotopy (e : T ⋙ R ≅ L ⋙ B)
    (he : ∀ ⦃X : C⦄ ⦃Y₀ : C₀⦄ (f₀ f₁ : X ⟶ L.obj Y₀) (_ : B.map f₀ = B.map f₁),
      ∃ (P : PrepathObject Y₀), T.map P.p₀ = T.map P.p₁ ∧
        Nonempty ((P.map L).RightHomotopy f₀ f₁)) :
    GuitartExact e.inv := by
  rw [← guitartExact_op_iff]
  let e' : T.op ⋙ R.op ≅ L.op ⋙ B.op := NatIso.op e.symm
  refine quotient_of_nonempty_leftHomotopy e' (fun X₀ Y f₀ f₁ h ↦ ?_)
  obtain ⟨P, hP, ⟨h⟩⟩ := he f₀.unop f₁.unop (Quiver.Hom.op_inj h)
  exact ⟨P.op, Quiver.Hom.unop_inj hP, ⟨h.op⟩⟩

end CategoryTheory.TwoSquare.GuitartExact
