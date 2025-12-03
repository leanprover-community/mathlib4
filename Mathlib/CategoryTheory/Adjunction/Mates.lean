/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Emily Riehl, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.HomCongr

/-!
# Mate of natural transformations

This file establishes the bijection between the 2-cells

```
         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂
```

where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`. The corresponding natural transformations are called mates.

This bijection includes a number of interesting cases as specializations. For instance, in the
special case where `G,H` are identity functors then the bijection preserves and reflects
isomorphisms (i.e. we have bijections `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, and if either side is an iso then the
other side is as well). This demonstrates that adjoints to a given functor are unique up to
isomorphism (since if `L₁ ≅ L₂` then we deduce `R₁ ≅ R₂`).

Another example arises from considering the square representing that a functor `H` preserves
products, in particular the morphism `HA ⨯ H- ⟶ H(A ⨯ -)`. Then provided `(A ⨯ -)` and `HA ⨯ -`
have left adjoints (for instance if the relevant categories are Cartesian closed), the transferred
natural transformation is the exponential comparison morphism: `H(A ^ -) ⟶ HA ^ H-`.
Furthermore if `H` has a left adjoint `L`, this morphism is an isomorphism iff its mate
`L(HA ⨯ -) ⟶ A ⨯ L-` is an isomorphism, see
https://ncatlab.org/nlab/show/Frobenius+reciprocity#InCategoryTheory.
This also relates to Grothendieck's yoga of six operations, though this is not spelled out in
mathlib: https://ncatlab.org/nlab/show/six+operations.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉
namespace CategoryTheory

open Category Functor Adjunction NatTrans TwoSquare

section mateEquiv

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
variable {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Suppose we have a square of functors (where the top and bottom are adjunctions `L₁ ⊣ R₁`
and `L₂ ⊣ R₂` respectively).

```
      C ↔ D
    G ↓   ↓ H
      E ↔ F
```

Then we have a bijection between natural transformations `G ⋙ L₂ ⟶ L₁ ⋙ H` and
`R₁ ⋙ G ⟶ H ⋙ R₂`. This can be seen as a bijection of the 2-cells:

```
         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂
```

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/
@[simps]
def mateEquiv : TwoSquare G L₁ L₂ H ≃ TwoSquare R₁ H G R₂ where
  toFun α := .mk _ _ _ _ <|
    (rightUnitor _).inv ≫
    whiskerLeft (R₁ ⋙ G) adj₂.unit ≫
    (associator _ _ _).hom ≫ whiskerLeft _ (associator _ _ _).inv ≫
    whiskerLeft R₁ (whiskerRight α.natTrans R₂) ≫
    whiskerLeft _ (associator _ _ _).hom ≫ (associator _ _ _).inv ≫
    whiskerRight adj₁.counit (H ⋙ R₂) ≫
    (leftUnitor _).hom
  invFun β := .mk _ _ _ _ <|
    (leftUnitor _).inv ≫
    whiskerRight adj₁.unit (G ⋙ L₂) ≫
    (associator _ _ _).inv ≫ whiskerRight (associator _ _ _).hom _ ≫
    whiskerRight (whiskerLeft L₁ β.natTrans) L₂ ≫
    whiskerRight (associator _ _ _).inv _ ≫ (associator _ _ _).hom ≫
    whiskerLeft (L₁ ⋙ H) adj₂.counit ≫
    (rightUnitor _).hom
  left_inv α := by
    ext
    simp only [comp_obj, whiskerLeft_comp, whiskerLeft_twice, assoc, Iso.hom_inv_id_assoc,
      whiskerRight_comp, comp_app, id_obj, leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, associator_inv_app, associator_hom_app, map_id, Functor.whiskerLeft_app,
      rightUnitor_inv_app, leftUnitor_hom_app, rightUnitor_hom_app, comp_id, id_comp,
      counit_naturality, counit_naturality_assoc, left_triangle_components_assoc]
    rw [← assoc, ← Functor.comp_map, α.natTrans.naturality, Functor.comp_map, assoc, ← H.map_comp,
      left_triangle_components, map_id]
    simp only [comp_obj, comp_id]
  right_inv β := by
    ext
    simp only [comp_obj, whiskerRight_comp, whiskerRight_twice, assoc, Iso.inv_hom_id_assoc,
      whiskerLeft_comp, comp_app, id_obj, rightUnitor_inv_app, Functor.whiskerLeft_app,
      associator_hom_app, associator_inv_app, Functor.whiskerRight_app, leftUnitor_inv_app, map_id,
      Functor.comp_map, rightUnitor_hom_app, leftUnitor_hom_app, comp_id, id_comp,
      unit_naturality_assoc, right_triangle_components_assoc]
    rw [← assoc, ← Functor.comp_map, assoc, ← β.natTrans.naturality, ← assoc, Functor.comp_map,
      ← G.map_comp, right_triangle_components, map_id, id_comp]

/-- A component of a transposed version of the mates correspondence. -/
theorem mateEquiv_counit (α : TwoSquare G L₁ L₂ H) (d : D) :
    L₂.map ((mateEquiv adj₁ adj₂ α).app _) ≫ adj₂.counit.app _ =
      α.app _ ≫ H.map (adj₁.counit.app d) := by simp

/-- A component of a transposed version of the inverse mates correspondence. -/
theorem mateEquiv_counit_symm (α : TwoSquare R₁ H G R₂) (d : D) :
    L₂.map (α.app _) ≫ adj₂.counit.app _ =
      ((mateEquiv adj₁ adj₂).symm α).app _ ≫ H.map (adj₁.counit.app d) := by
  conv_lhs => rw [← (mateEquiv adj₁ adj₂).right_inv α]
  exact (mateEquiv_counit adj₁ adj₂ ((mateEquiv adj₁ adj₂).symm α) d)

/- A component of a transposed version of the mates correspondence. -/
theorem unit_mateEquiv (α : TwoSquare G L₁ L₂ H) (c : C) :
    G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).app _ =
      adj₂.unit.app _ ≫ R₂.map (α.app _) := by
  simp only [id_obj, comp_obj, mateEquiv, Equiv.coe_fn_mk, comp_app, rightUnitor_inv_app,
    Functor.whiskerLeft_app, associator_hom_app, associator_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, leftUnitor_hom_app, comp_id, id_comp]
  rw [← adj₂.unit_naturality_assoc]
  slice_lhs 2 3 =>
    rw [← R₂.map_comp, ← Functor.comp_map G L₂, α.naturality]
  rw [R₂.map_comp]
  slice_lhs 3 4 =>
    rw [← R₂.map_comp, Functor.comp_map L₁ H, ← H.map_comp, left_triangle_components]
  simp only [comp_obj, map_id, comp_id]

/-- A component of a transposed version of the inverse mates correspondence. -/
theorem unit_mateEquiv_symm (α : TwoSquare R₁ H G R₂) (c : C) :
    G.map (adj₁.unit.app c) ≫ α.app _ =
      adj₂.unit.app _ ≫ R₂.map (((mateEquiv adj₁ adj₂).symm α).app _) := by
  conv_lhs => rw [← (mateEquiv adj₁ adj₂).right_inv α]
  exact (unit_mateEquiv adj₁ adj₂ ((mateEquiv adj₁ adj₂).symm α) c)

end mateEquiv

section mateEquivVComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- The mates equivalence commutes with vertical composition. -/
theorem mateEquiv_vcomp (α : TwoSquare G₁ L₁ L₂ H₁) (β : TwoSquare G₂ L₂ L₃ H₂) :
    (mateEquiv adj₁ adj₃) (α ≫ₕ β) = (mateEquiv adj₁ adj₂ α) ≫ᵥ (mateEquiv adj₂ adj₃ β) := by
  unfold hComp vComp mateEquiv
  ext b
  simp only [comp_obj, Equiv.coe_fn_mk, whiskerRight_comp, whiskerRight_twice, assoc,
    whiskerLeft_comp, comp_app, id_obj, rightUnitor_inv_app, Functor.whiskerLeft_app,
    associator_hom_app, associator_inv_app, Functor.whiskerRight_app, map_id, Functor.comp_map,
    leftUnitor_hom_app, comp_id, id_comp, whiskerLeft_twice, Iso.hom_inv_id_assoc]
  slice_rhs 1 4 => rw [← assoc, ← assoc, ← unit_naturality (adj₃)]
  rw [L₃.map_comp, R₃.map_comp]
  slice_rhs 2 4 =>
    rw [← R₃.map_comp, ← R₃.map_comp, ← assoc, ← L₃.map_comp, ← G₂.map_comp, ← G₂.map_comp]
    rw [← Functor.comp_map G₂ L₃, β.naturality]
  rw [(L₂ ⋙ H₂).map_comp, R₃.map_comp, R₃.map_comp]
  slice_rhs 4 5 =>
    rw [← R₃.map_comp, Functor.comp_map L₂ _, ← Functor.comp_map _ L₂, ← H₂.map_comp]
    rw [adj₂.counit.naturality]
  simp only [comp_obj, Functor.comp_map, map_comp, id_obj, Functor.id_map, assoc]
  slice_rhs 4 5 =>
    rw [← R₃.map_comp, ← H₂.map_comp, ← Functor.comp_map _ L₂, adj₂.counit.naturality]
  simp only [comp_obj, id_obj, Functor.id_map, map_comp, assoc]
  slice_rhs 3 4 =>
    rw [← R₃.map_comp, ← H₂.map_comp, left_triangle_components]
  simp only [map_id, id_comp]

end mateEquivVComp

section mateEquivHComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
variable {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)

/-- The mates equivalence commutes with horizontal composition of squares. -/
theorem mateEquiv_hcomp (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄)) (α ≫ᵥ β) =
      (mateEquiv adj₃ adj₄ β) ≫ₕ (mateEquiv adj₁ adj₂ α) := by
  unfold vComp hComp mateEquiv Adjunction.comp
  ext c
  simp only [comp_obj, whiskerRight_comp, assoc, mk'_unit, whiskerLeft_comp, mk'_counit,
    whiskerRight_twice, Iso.inv_hom_id_assoc, Equiv.coe_fn_mk, comp_app, id_obj,
    rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, map_id,
    associator_inv_app, associator_hom_app, Functor.comp_map, rightUnitor_hom_app,
    leftUnitor_hom_app, comp_id, id_comp, whiskerLeft_twice, Iso.hom_inv_id_assoc]
  slice_rhs 2 4 =>
    rw [← R₂.map_comp, ← R₂.map_comp, ← assoc, ← unit_naturality (adj₄)]
  rw [R₂.map_comp, L₄.map_comp, R₄.map_comp, R₂.map_comp]
  slice_rhs 4 5 =>
    rw [← R₂.map_comp, ← R₄.map_comp, ← Functor.comp_map _ L₄, β.naturality]
  simp only [comp_obj, Functor.comp_map, map_comp, assoc]

end mateEquivHComp

section mateEquivSquareComp

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {D : Type u₄} {E : Type u₅} {F : Type u₆}
variable {X : Type u₇} {Y : Type u₈} {Z : Type u₉}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
variable [Category.{v₇} X] [Category.{v₈} Y] [Category.{v₉} Z]
variable {G₁ : A ⥤ D} {H₁ : B ⥤ E} {K₁ : C ⥤ F} {G₂ : D ⥤ X} {H₂ : E ⥤ Y} {K₂ : F ⥤ Z}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B} {L₃ : D ⥤ E} {R₃ : E ⥤ D}
variable {L₄ : E ⥤ F} {R₄ : F ⥤ E} {L₅ : X ⥤ Y} {R₅ : Y ⥤ X} {L₆ : Y ⥤ Z} {R₆ : Z ⥤ Y}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
variable (adj₄ : L₄ ⊣ R₄) (adj₅ : L₅ ⊣ R₅) (adj₆ : L₆ ⊣ R₆)

/-- The mates equivalence commutes with composition of squares of squares. These results form the
basis for an isomorphism of double categories to be proven later.
-/
theorem mateEquiv_square (α : TwoSquare G₁ L₁ L₃ H₁) (β : TwoSquare H₁ L₂ L₄ K₁)
    (γ : TwoSquare G₂ L₃ L₅ H₂) (δ : TwoSquare H₂ L₄ L₆ K₂) :
    (mateEquiv (adj₁.comp adj₂) (adj₅.comp adj₆)) ((α ≫ᵥ β) ≫ₕ (γ ≫ᵥ δ)) =
      ((mateEquiv adj₂ adj₄ β) ≫ₕ (mateEquiv adj₁ adj₃ α))
         ≫ᵥ ((mateEquiv adj₄ adj₆ δ) ≫ₕ (mateEquiv adj₃ adj₅ γ)) := by
  have vcomp :=
    mateEquiv_vcomp (adj₁.comp adj₂) (adj₃.comp adj₄) (adj₅.comp adj₆) (α ≫ᵥ β) (γ ≫ᵥ δ)
  simp only [mateEquiv_hcomp] at vcomp
  assumption

end mateEquivSquareComp

section conjugateEquiv

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- Given two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` both between categories `C`, `D`, there is a
bijection between natural transformations `L₂ ⟶ L₁` and natural transformations `R₁ ⟶ R₂`. This is
defined as a special case of `mateEquiv`, where the two "vertical" functors are identity, modulo
composition with the unitors. Corresponding natural transformations are called `conjugateEquiv`.
TODO: Generalise to when the two vertical functors are equivalences rather than being exactly `𝟭`.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a transformation is an iso
iff its image under the bijection is an iso, see e.g. `CategoryTheory.conjugateIsoEquiv`.
This is in contrast to the general case `mateEquiv` which does not in general have this property.
-/
@[simps!]
def conjugateEquiv : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
  calc
    (L₂ ⟶ L₁) ≃ (𝟭 C ⋙ L₂ ⟶ L₁ ⋙ 𝟭 D) := (Iso.homCongr L₂.leftUnitor L₁.rightUnitor).symm
    _ ≃ TwoSquare _ _ _ _ := (TwoSquare.equivNatTrans _ _ _ _).symm
    _ ≃ _ := mateEquiv adj₁ adj₂
    _ ≃ (R₁ ⋙ 𝟭 C ⟶ 𝟭 D ⋙ R₂) := TwoSquare.equivNatTrans _ _ _ _
    _ ≃ (R₁ ⟶ R₂) := R₁.rightUnitor.homCongr R₂.leftUnitor

/-- A component of a transposed form of the conjugation definition. -/
theorem conjugateEquiv_counit (α : L₂ ⟶ L₁) (d : D) :
    L₂.map ((conjugateEquiv adj₁ adj₂ α).app _) ≫ adj₂.counit.app d =
      α.app _ ≫ adj₁.counit.app d := by
  simp

/-- A component of a transposed form of the inverse conjugation definition. -/
theorem conjugateEquiv_counit_symm (α : R₁ ⟶ R₂) (d : D) :
    L₂.map (α.app _) ≫ adj₂.counit.app d =
      ((conjugateEquiv adj₁ adj₂).symm α).app _ ≫ adj₁.counit.app d := by
    conv_lhs => rw [← (conjugateEquiv adj₁ adj₂).right_inv α]
    exact (conjugateEquiv_counit adj₁ adj₂ ((conjugateEquiv adj₁ adj₂).symm α) d)

/-- A component of a transposed form of the conjugation definition. -/
theorem unit_conjugateEquiv (α : L₂ ⟶ L₁) (c : C) :
    adj₁.unit.app _ ≫ (conjugateEquiv adj₁ adj₂ α).app _ =
      adj₂.unit.app c ≫ R₂.map (α.app _) := by
  dsimp [conjugateEquiv]
  rw [id_comp, comp_id]
  have := unit_mateEquiv adj₁ adj₂ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) c
  dsimp at this
  rw [this]
  simp

/-- A component of a transposed form of the inverse conjugation definition. -/
theorem unit_conjugateEquiv_symm (α : R₁ ⟶ R₂) (c : C) :
    adj₁.unit.app _ ≫ α.app _ =
      adj₂.unit.app c ≫ R₂.map (((conjugateEquiv adj₁ adj₂).symm α).app _) := by
    conv_lhs => rw [← (conjugateEquiv adj₁ adj₂).right_inv α]
    exact (unit_conjugateEquiv adj₁ adj₂ ((conjugateEquiv adj₁ adj₂).symm α) c)

@[simp]
theorem conjugateEquiv_id : conjugateEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _ := by
  ext
  simp

@[simp]
theorem conjugateEquiv_symm_id : (conjugateEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by
  rw [Equiv.symm_apply_eq]
  simp only [conjugateEquiv_id]

theorem conjugateEquiv_adjunction_id {L R : C ⥤ C} (adj : L ⊣ R) (α : 𝟭 C ⟶ L) (c : C) :
    (conjugateEquiv adj Adjunction.id α).app c = α.app (R.obj c) ≫ adj.counit.app c := by
  simp [conjugateEquiv, mateEquiv, Adjunction.id]

theorem conjugateEquiv_adjunction_id_symm {L R : C ⥤ C} (adj : L ⊣ R) (α : R ⟶ 𝟭 C) (c : C) :
    ((conjugateEquiv adj Adjunction.id).symm α).app c = adj.unit.app c ≫ α.app (L.obj c) := by
  simp [conjugateEquiv, mateEquiv, Adjunction.id]

end conjugateEquiv

section ConjugateComposition
variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ L₃ : C ⥤ D} {R₁ R₂ R₃ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

@[reassoc (attr := simp)]
theorem conjugateEquiv_comp (α : L₂ ⟶ L₁) (β : L₃ ⟶ L₂) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β =
      conjugateEquiv adj₁ adj₃ (β ≫ α) := by
  ext d
  dsimp [conjugateEquiv, mateEquiv]
  have vcomp := mateEquiv_vcomp adj₁ adj₂ adj₃
    (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv)
    (L₃.leftUnitor.hom ≫ β ≫ L₂.rightUnitor.inv)
  have vcompd := congr_app vcomp d
  simp only [comp_obj, id_obj, mateEquiv_apply, comp_app, rightUnitor_inv_app,
    Functor.whiskerLeft_app, associator_hom_app, associator_inv_app, Functor.whiskerRight_app,
    hComp_app, leftUnitor_hom_app, comp_id, id_comp, Functor.id_map, map_comp, Functor.comp_map,
    assoc, whiskerRight_comp, whiskerLeft_comp, vComp_app, map_id] at vcompd ⊢
  rw [vcompd]

@[reassoc (attr := simp)]
theorem conjugateEquiv_symm_comp (α : R₁ ⟶ R₂) (β : R₂ ⟶ R₃) :
    (conjugateEquiv adj₂ adj₃).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α =
      (conjugateEquiv adj₁ adj₃).symm (α ≫ β) := by
  rw [Equiv.eq_symm_apply, ← conjugateEquiv_comp _ adj₂]
  simp only [Equiv.apply_symm_apply]

theorem conjugateEquiv_comm {α : L₂ ⟶ L₁} {β : L₁ ⟶ L₂} (βα : β ≫ α = 𝟙 _) :
    conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₁ β = 𝟙 _ := by
  rw [conjugateEquiv_comp, βα, conjugateEquiv_id]

theorem conjugateEquiv_symm_comm {α : R₁ ⟶ R₂} {β : R₂ ⟶ R₁} (αβ : α ≫ β = 𝟙 _) :
    (conjugateEquiv adj₂ adj₁).symm β ≫ (conjugateEquiv adj₁ adj₂).symm α = 𝟙 _ := by
  rw [conjugateEquiv_symm_comp, αβ, conjugateEquiv_symm_id]

end ConjugateComposition

section ConjugateIsomorphism

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- If `α` is an isomorphism between left adjoints, then its conjugate transformation is an
isomorphism. The converse is given in `conjugateEquiv_of_iso`.
-/
instance conjugateEquiv_iso (α : L₂ ⟶ L₁) [IsIso α] :
    IsIso (conjugateEquiv adj₁ adj₂ α) :=
  ⟨⟨conjugateEquiv adj₂ adj₁ (inv α),
      ⟨conjugateEquiv_comm _ _ (by simp), conjugateEquiv_comm _ _ (by simp)⟩⟩⟩

/-- If `α` is an isomorphism between right adjoints, then its conjugate transformation is an
isomorphism. The converse is given in `conjugateEquiv_symm_of_iso`.
-/
instance conjugateEquiv_symm_iso (α : R₁ ⟶ R₂) [IsIso α] :
    IsIso ((conjugateEquiv adj₁ adj₂).symm α) :=
  ⟨⟨(conjugateEquiv adj₂ adj₁).symm (inv α),
      ⟨conjugateEquiv_symm_comm _ _ (by simp), conjugateEquiv_symm_comm _ _ (by simp)⟩⟩⟩

/-- If `α` is a natural transformation between left adjoints whose conjugate natural transformation
is an isomorphism, then `α` is an isomorphism. The converse is given in `Conjugate_iso`.
-/
theorem conjugateEquiv_of_iso (α : L₂ ⟶ L₁) [IsIso (conjugateEquiv adj₁ adj₂ α)] :
    IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂).symm (conjugateEquiv adj₁ adj₂ α))
    by simpa using this
  infer_instance

/--
If `α` is a natural transformation between right adjoints whose conjugate natural transformation is
an isomorphism, then `α` is an isomorphism. The converse is given in `conjugateEquiv_symm_iso`.
-/
theorem conjugateEquiv_symm_of_iso (α : R₁ ⟶ R₂)
    [IsIso ((conjugateEquiv adj₁ adj₂).symm α)] : IsIso α := by
  suffices IsIso ((conjugateEquiv adj₁ adj₂) ((conjugateEquiv adj₁ adj₂).symm α))
    by simpa using this
  infer_instance

/-- Thus conjugation defines an equivalence between natural isomorphisms. -/
@[simps]
def conjugateIsoEquiv : (L₂ ≅ L₁) ≃ (R₁ ≅ R₂) where
  toFun α := {
    hom := conjugateEquiv adj₁ adj₂ α.hom
    inv := conjugateEquiv adj₂ adj₁ α.inv
  }
  invFun β := {
    hom := (conjugateEquiv adj₁ adj₂).symm β.hom
    inv := (conjugateEquiv adj₂ adj₁).symm β.inv
  }
  left_inv := by cat_disch
  right_inv := by cat_disch

end ConjugateIsomorphism

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

section IteratedmateEquiv

variable {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
variable {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)

/-- When all four functors in a square are left adjoints, the mates operation can be iterated:

```
         L₁                  R₁                  R₁
      C --→ D             C ←-- D             C ←-- D
   F₁ ↓  ↗  ↓  F₂      F₁ ↓  ↘  ↓ F₂       U₁ ↑  ↙  ↑ U₂
      E --→ F             E ←-- F             E ←-- F
         L₂                  R₂                  R₂
```

In this case the iterated mate equals the conjugate of the original transformation and is thus an
isomorphism if and only if the original transformation is. This explains why some Beck-Chevalley
natural transformations are natural isomorphisms.
-/
theorem iterated_mateEquiv_conjugateEquiv (α : TwoSquare F₁ L₁ L₂ F₂) :
    (mateEquiv adj₄ adj₃ (mateEquiv adj₁ adj₂ α)).natTrans =
      conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂) α := by
  ext d
  unfold conjugateEquiv mateEquiv Adjunction.comp
  simp

theorem iterated_mateEquiv_conjugateEquiv_symm (α : TwoSquare U₂ R₂ R₁ U₁) :
    (mateEquiv adj₁ adj₂).symm ((mateEquiv adj₄ adj₃).symm α) =
      (conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)).symm.trans
        (equivNatTrans _ _ _ _).symm α := by
  ext
  simp

end IteratedmateEquiv

variable {G : A ⥤ C} {H : B ⥤ D}

/-- The mates equivalence commutes with this composition, essentially by `mateEquiv_vcomp`. -/
theorem mateEquiv_conjugateEquiv_vcomp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (α : TwoSquare G L₁ L₂ H) (β : L₃ ⟶ L₂) :
    (mateEquiv adj₁ adj₃) (α.whiskerRight β) =
      (mateEquiv adj₁ adj₂ α).whiskerBottom (conjugateEquiv adj₂ adj₃ β) := by
  ext b
  have vcomp := mateEquiv_vcomp adj₁ adj₂ adj₃ α (L₃.leftUnitor.hom ≫ β ≫ L₂.rightUnitor.inv)
  unfold vComp hComp at vcomp
  unfold TwoSquare.whiskerRight TwoSquare.whiskerBottom conjugateEquiv
  have vcompb := congr_app vcomp b
  simp only [comp_obj, id_obj, whiskerLeft_comp, assoc, mateEquiv_apply, whiskerLeft_twice,
    Iso.hom_inv_id_assoc, whiskerRight_comp, comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, associator_hom_app, map_id, associator_inv_app, leftUnitor_hom_app,
    rightUnitor_inv_app, Functor.id_map, Functor.comp_map, id_comp, whiskerRight_twice,
    comp_id] at vcompb
  simpa [mateEquiv]

/-- The mates equivalence commutes with this composition, essentially by `mateEquiv_vcomp`. -/
theorem conjugateEquiv_mateEquiv_vcomp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : A ⥤ B} {R₂ : B ⥤ A}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (α : L₂ ⟶ L₁) (β : TwoSquare G L₂ L₃ H) :
    (mateEquiv adj₁ adj₃) (β.whiskerLeft α) =
      (mateEquiv adj₂ adj₃ β).whiskerTop (conjugateEquiv adj₁ adj₂ α) := by
  ext b
  have vcomp := mateEquiv_vcomp adj₁ adj₂ adj₃ (L₂.leftUnitor.hom ≫ α ≫ L₁.rightUnitor.inv) β
  unfold vComp hComp at vcomp
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerTop conjugateEquiv
  have vcompb := congr_app vcomp b
  simp only [comp_obj, id_obj, whiskerRight_comp, assoc, mateEquiv_apply, whiskerLeft_comp,
    whiskerLeft_twice, comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    associator_hom_app, map_id, associator_inv_app, leftUnitor_hom_app, rightUnitor_inv_app,
    Functor.comp_map, Functor.id_map, id_comp, whiskerRight_twice, Iso.inv_hom_id_assoc,
    comp_id] at vcompb
  simpa [mateEquiv]

lemma conjugateEquiv_associator_hom
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)
      (associator _ _ _).hom = (associator _ _ _).hom := by
  ext X
  simp only [comp_obj, conjugateEquiv_apply_app, Adjunction.comp_unit_app, id_obj,
    Functor.comp_map, Category.assoc, ← map_comp, associator_hom_app, map_id,
    Adjunction.comp_counit_app, Category.id_comp]
  simp

lemma conjugateEquiv_leftUnitor_hom
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateEquiv adj (id.comp adj) (leftUnitor L).hom =
      (rightUnitor R).inv := by
  cat_disch

lemma conjugateEquiv_rightUnitor_hom
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateEquiv adj (adj.comp id) (rightUnitor L).hom =
      (leftUnitor R).inv := by
  cat_disch

lemma conjugateEquiv_whiskerLeft
    {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : L₂ ⟶ L₁) :
    conjugateEquiv (adj.comp adj₁) (adj.comp adj₂) (whiskerLeft L τ) =
      whiskerRight (conjugateEquiv adj₁ adj₂ τ) R := by
  ext X
  have h₁ := congr_map (R₂ ⋙ R) (τ.naturality (adj.counit.app (R₁.obj X)))
  have h₂ := congr_map R (adj₂.unit_naturality (adj.counit.app (R₁.obj X)))
  simp only [comp_obj, id_obj, Functor.map_comp] at h₁ h₂
  simp [← reassoc_of% h₁, reassoc_of% h₂]

lemma conjugateEquiv_whiskerRight
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (τ : L₂ ⟶ L₁) :
    conjugateEquiv (adj₁.comp adj) (adj₂.comp adj) (whiskerRight τ L) =
      whiskerLeft R (conjugateEquiv adj₁ adj₂ τ) := by
  ext X
  simp only [comp_obj, conjugateEquiv_apply_app, comp_unit_app, id_obj, Functor.whiskerRight_app,
    Functor.comp_map, comp_counit_app, ← map_comp, assoc, Functor.whiskerLeft_app]
  simp

end CategoryTheory
