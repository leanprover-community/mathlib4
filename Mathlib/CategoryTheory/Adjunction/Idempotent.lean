/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Data.List.TFAE

import Mathlib.Tactic.TFAE

/-!
# Fixed points of an adjunction and idempotent adjunctions

Let `adj : L ⊣ R` be an adjunction between `C` and `D`, with unit `η` and counit `ε`.

* `Adjunction.fixedLeft adj` is the full subcategory of `C` of objects `X` at which `η` is an
  isomorphism, and `Adjunction.fixedRight adj` the full subcategory of `D` of objects `Y` at
  which `ε` is an isomorphism. They are closed under isomorphisms.
* `Adjunction.fixedEquiv adj`: `L` and `R` restrict to an equivalence between them, whose unit
  and counit are those of the adjunction. This holds for any adjunction.
* `Adjunction.idempotent_tfae`: the four conditions `ηR`, `Rε`, `εL` and `Lη` invertible are
  equivalent. An adjunction satisfying them is called *idempotent*.
* For an idempotent adjunction, `fixedLeft adj` is reflective in `C`, with reflector `L ⋙ R`
  (`Adjunction.fixedLeftReflective`), and `fixedRight adj` is coreflective in `D`, with
  coreflector `R ⋙ L` (`Adjunction.fixedRightCoreflective`).

## References

* [F. Borceux, *Handbook of categorical algebra 1*][borceux-vol1], Proposition 3.4.1
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- If `f ≫ g = 𝟙 X`, then `f` is an isomorphism if and only if `g` is. -/
private lemma isIso_iff_of_comp_eq_id {E : Type*} [Category* E] {X Y : E} {f : X ⟶ Y}
    {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) : IsIso f ↔ IsIso g :=
  ⟨fun _ ↦ isIso_of_hom_comp_eq_id f h, fun _ ↦ isIso_of_comp_hom_eq_id g h⟩

section Idempotent

/-- For an adjunction `L ⊣ R` with unit `η` and counit `ε`, the four conditions `ηR`, `Rε`,
`εL` and `Lη` invertible are equivalent. An adjunction satisfying them is *idempotent*. -/
theorem idempotent_tfae :
    List.TFAE [∀ Y, IsIso (adj.unit.app (R.obj Y)), ∀ Y, IsIso (R.map (adj.counit.app Y)),
      ∀ X, IsIso (adj.counit.app (L.obj X)), ∀ X, IsIso (L.map (adj.unit.app X))] := by
  tfae_have 1 ↔ 2 := forall_congr' fun Y =>
    isIso_iff_of_comp_eq_id (adj.right_triangle_components Y)
  tfae_have 3 ↔ 4 := forall_congr' fun X =>
    (isIso_iff_of_comp_eq_id (adj.left_triangle_components X)).symm
  tfae_have 1 → 3 := by
    intro h X
    have : IsIso (R.map (adj.counit.app (L.obj X))) :=
      (isIso_iff_of_comp_eq_id (adj.right_triangle_components (L.obj X))).1 (h _)
    -- `RLη_X = η_{RLX}`: both are sections of the isomorphism `Rε_{LX}`.
    have key : R.map (L.map (adj.unit.app X)) = adj.unit.app (R.obj (L.obj X)) := by
      rw [← cancel_mono (R.map (adj.counit.app (L.obj X))), ← Functor.map_comp]
      simp
    refine ⟨L.map (adj.unit.app X), ?_, adj.left_triangle_components X⟩
    have nat := adj.counit.naturality (L.map (adj.unit.app X))
    dsimp at nat
    rw [← nat, key]
    simp
  tfae_have 3 → 1 := by
    intro h Y
    have : IsIso (L.map (adj.unit.app (R.obj Y))) :=
      (isIso_iff_of_comp_eq_id (adj.left_triangle_components (R.obj Y))).2 (h _)
    -- `LRε_Y = ε_{LRY}`: both are retractions of the isomorphism `Lη_{RY}`.
    have key : L.map (R.map (adj.counit.app Y)) = adj.counit.app (L.obj (R.obj Y)) := by
      rw [← cancel_epi (L.map (adj.unit.app (R.obj Y))), ← Functor.map_comp]
      simp
    refine ⟨R.map (adj.counit.app Y), adj.right_triangle_components Y, ?_⟩
    have nat := adj.unit.naturality (R.map (adj.counit.app Y))
    dsimp at nat
    rw [nat, key]
    simp
  tfae_finish

/-- In an idempotent adjunction, `RLη_X = η_{RLX}`. -/
theorem map_map_unit_app_of_idempotent (h : ∀ Y, IsIso (adj.unit.app (R.obj Y))) (X : C) :
    R.map (L.map (adj.unit.app X)) = adj.unit.app (R.obj (L.obj X)) := by
  have h' : ∀ Y, IsIso (R.map (adj.counit.app Y)) := (adj.idempotent_tfae.out 1 2).1 h
  have := h' (L.obj X)
  rw [← cancel_mono (R.map (adj.counit.app (L.obj X))), ← Functor.map_comp]
  simp

/-- In an idempotent adjunction, `LRε_Y = ε_{LRY}`. -/
theorem map_map_counit_app_of_idempotent (h : ∀ X, IsIso (adj.counit.app (L.obj X))) (Y : D) :
    L.map (R.map (adj.counit.app Y)) = adj.counit.app (L.obj (R.obj Y)) := by
  have h' : ∀ X, IsIso (L.map (adj.unit.app X)) := (adj.idempotent_tfae.out 3 4).1 h
  have := h' (R.obj Y)
  rw [← cancel_epi (L.map (adj.unit.app (R.obj Y))), ← Functor.map_comp]
  simp

end Idempotent

section Fixed

/-- The objects of `C` at which the unit of `L ⊣ R` is an isomorphism. -/
def fixedLeft : ObjectProperty C := fun X => IsIso (adj.unit.app X)

/-- The objects of `D` at which the counit of `L ⊣ R` is an isomorphism. -/
def fixedRight : ObjectProperty D := fun Y => IsIso (adj.counit.app Y)

variable {adj} in
lemma fixedLeft_iff {X : C} : adj.fixedLeft X ↔ IsIso (adj.unit.app X) := Iff.rfl

variable {adj} in
lemma fixedRight_iff {Y : D} : adj.fixedRight Y ↔ IsIso (adj.counit.app Y) := Iff.rfl

variable {adj} in
lemma fixedRight_obj {X : C} (h : adj.fixedLeft X) : adj.fixedRight (L.obj X) :=
  have : IsIso (adj.unit.app X) := h
  (isIso_iff_of_comp_eq_id (adj.left_triangle_components X)).1 inferInstance

variable {adj} in
lemma fixedLeft_obj {Y : D} (h : adj.fixedRight Y) : adj.fixedLeft (R.obj Y) :=
  have : IsIso (adj.counit.app Y) := h
  (isIso_iff_of_comp_eq_id (adj.right_triangle_components Y)).2 inferInstance

instance : adj.fixedLeft.IsClosedUnderIsomorphisms where
  of_iso {X X'} e (h : IsIso (adj.unit.app X)) := by
    rw [fixedLeft_iff, show adj.unit.app X' = e.inv ≫ adj.unit.app X ≫ R.map (L.map e.hom) by simp]
    infer_instance

instance : adj.fixedRight.IsClosedUnderIsomorphisms where
  of_iso {Y Y'} e (h : IsIso (adj.counit.app Y)) := by
    rw [fixedRight_iff,
      show adj.counit.app Y' = L.map (R.map e.inv) ≫ adj.counit.app Y ≫ e.hom by simp]
    infer_instance

/-- The unit of `L ⊣ R` at a fixed object of `C`, as an isomorphism. -/
noncomputable def fixedLeftUnitIso (X : adj.fixedLeft.FullSubcategory) :
    X.obj ≅ R.obj (L.obj X.obj) :=
  @asIso _ _ _ _ (adj.unit.app X.obj) X.2

@[simp]
lemma fixedLeftUnitIso_hom (X : adj.fixedLeft.FullSubcategory) :
    (adj.fixedLeftUnitIso X).hom = adj.unit.app X.obj :=
  rfl

/-- The counit of `L ⊣ R` at a fixed object of `D`, as an isomorphism. -/
noncomputable def fixedRightCounitIso (Y : adj.fixedRight.FullSubcategory) :
    L.obj (R.obj Y.obj) ≅ Y.obj :=
  @asIso _ _ _ _ (adj.counit.app Y.obj) Y.2

@[simp]
lemma fixedRightCounitIso_hom (Y : adj.fixedRight.FullSubcategory) :
    (adj.fixedRightCounitIso Y).hom = adj.counit.app Y.obj :=
  rfl

/-- An object of `D` is fixed if and only if it is isomorphic to `L.obj X` for some fixed `X`. -/
lemma fixedRight_iff_exists {Y : D} :
    adj.fixedRight Y ↔ ∃ X, adj.fixedLeft X ∧ Nonempty (L.obj X ≅ Y) := by
  refine ⟨fun (h : IsIso _) => ⟨R.obj Y, fixedLeft_obj h, ⟨asIso (adj.counit.app Y)⟩⟩, ?_⟩
  rintro ⟨X, hX, ⟨e⟩⟩
  exact adj.fixedRight.prop_of_iso e (fixedRight_obj hX)

/-- An object of `C` is fixed if and only if it is isomorphic to `R.obj Y` for some fixed `Y`. -/
lemma fixedLeft_iff_exists {X : C} :
    adj.fixedLeft X ↔ ∃ Y, adj.fixedRight Y ∧ Nonempty (R.obj Y ≅ X) := by
  refine ⟨fun (h : IsIso _) => ⟨L.obj X, fixedRight_obj h, ⟨(asIso (adj.unit.app X)).symm⟩⟩, ?_⟩
  rintro ⟨Y, hY, ⟨e⟩⟩
  exact adj.fixedLeft.prop_of_iso e (fixedLeft_obj hY)

/-- The restriction of `L` to the fixed objects. -/
@[simps!]
def fixedLeftToFixedRight : adj.fixedLeft.FullSubcategory ⥤ adj.fixedRight.FullSubcategory :=
  adj.fixedRight.lift (adj.fixedLeft.ι ⋙ L) fun X => fixedRight_obj X.2

/-- The restriction of `R` to the fixed objects. -/
@[simps!]
def fixedRightToFixedLeft : adj.fixedRight.FullSubcategory ⥤ adj.fixedLeft.FullSubcategory :=
  adj.fixedLeft.lift (adj.fixedRight.ι ⋙ R) fun Y => fixedLeft_obj Y.2

/-- Any adjunction `L ⊣ R` restricts to an equivalence between the objects at which the unit is
an isomorphism and the objects at which the counit is an isomorphism. -/
@[simps]
noncomputable def fixedEquiv : adj.fixedLeft.FullSubcategory ≌ adj.fixedRight.FullSubcategory where
  functor := adj.fixedLeftToFixedRight
  inverse := adj.fixedRightToFixedLeft
  unitIso := NatIso.ofComponents
    (fun X => adj.fixedLeft.isoMk (adj.fixedLeftUnitIso X))
    (fun f => ObjectProperty.hom_ext _ (adj.unit.naturality f.hom))
  counitIso := NatIso.ofComponents
    (fun Y => adj.fixedRight.isoMk (adj.fixedRightCounitIso Y))
    (fun f => ObjectProperty.hom_ext _ (adj.counit.naturality f.hom))
  functor_unitIso_comp X := ObjectProperty.hom_ext _ (adj.left_triangle_components X.obj)

end Fixed

section Reflective

/-- The reflector onto the fixed objects of an idempotent adjunction: `L ⋙ R`, corestricted. -/
@[simps!]
def fixedLeftReflector (h : ∀ X, adj.fixedRight (L.obj X)) : C ⥤ adj.fixedLeft.FullSubcategory :=
  adj.fixedLeft.lift (L ⋙ R) fun X => fixedLeft_obj (h X)

/-- For an idempotent adjunction `L ⊣ R`, the inclusion of the objects of `C` at which the unit
is an isomorphism has the left adjoint `L ⋙ R`. -/
@[simps]
noncomputable def fixedLeftAdjunction (h : ∀ X, adj.fixedRight (L.obj X)) :
    adj.fixedLeftReflector h ⊣ adj.fixedLeft.ι where
  unit := { app X := adj.unit.app X, naturality _ _ f := adj.unit.naturality f }
  counit :=
    { app X := adj.fixedLeft.homMk (adj.fixedLeftUnitIso X).inv
      naturality X Y f := ObjectProperty.hom_ext _ (by
        change R.map (L.map f.hom) ≫ (adj.fixedLeftUnitIso Y).inv =
          (adj.fixedLeftUnitIso X).inv ≫ f.hom
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (adj.unit.naturality f.hom).symm) }
  left_triangle_components X := ObjectProperty.hom_ext _ (by
    have h' : ∀ Y, IsIso (adj.unit.app (R.obj Y)) := (adj.idempotent_tfae.out 3 1).1 h
    change R.map (L.map (adj.unit.app X)) ≫
      (adj.fixedLeftUnitIso ((adj.fixedLeftReflector h).obj X)).inv = 𝟙 _
    rw [map_map_unit_app_of_idempotent adj h' X]
    exact (adj.fixedLeftUnitIso ((adj.fixedLeftReflector h).obj X)).hom_inv_id)
  right_triangle_components X := (adj.fixedLeftUnitIso X).hom_inv_id

/-- For an idempotent adjunction `L ⊣ R`, the objects of `C` at which the unit is an isomorphism
form a reflective subcategory. -/
noncomputable abbrev fixedLeftReflective (h : ∀ X, adj.fixedRight (L.obj X)) :
    Reflective adj.fixedLeft.ι where
  L := adj.fixedLeftReflector h
  adj := adj.fixedLeftAdjunction h

/-- The coreflector onto the fixed objects of an idempotent adjunction: `R ⋙ L`, corestricted. -/
@[simps!]
def fixedRightCoreflector (h : ∀ Y, adj.fixedLeft (R.obj Y)) :
    D ⥤ adj.fixedRight.FullSubcategory :=
  adj.fixedRight.lift (R ⋙ L) fun Y => fixedRight_obj (h Y)

/-- For an idempotent adjunction `L ⊣ R`, the inclusion of the objects of `D` at which the
counit is an isomorphism has the right adjoint `R ⋙ L`. -/
@[simps]
noncomputable def fixedRightAdjunction (h : ∀ Y, adj.fixedLeft (R.obj Y)) :
    adj.fixedRight.ι ⊣ adj.fixedRightCoreflector h where
  unit :=
    { app Y := adj.fixedRight.homMk (adj.fixedRightCounitIso Y).inv
      naturality X Y f := ObjectProperty.hom_ext _ (by
        change f.hom ≫ (adj.fixedRightCounitIso Y).inv =
          (adj.fixedRightCounitIso X).inv ≫ L.map (R.map f.hom)
        rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
        exact (adj.counit.naturality f.hom).symm) }
  counit := { app Y := adj.counit.app Y, naturality _ _ f := adj.counit.naturality f }
  left_triangle_components Y := (adj.fixedRightCounitIso Y).inv_hom_id
  right_triangle_components Y := ObjectProperty.hom_ext _ (by
    have h' : ∀ X, IsIso (adj.counit.app (L.obj X)) := (adj.idempotent_tfae.out 1 3).1 h
    refine (Iso.inv_comp_eq
      (adj.fixedRightCounitIso ((adj.fixedRightCoreflector h).obj Y))).2 ?_
    exact (map_map_counit_app_of_idempotent adj h' Y).trans (Category.comp_id _).symm)

/-- For an idempotent adjunction `L ⊣ R`, the objects of `D` at which the counit is an
isomorphism form a coreflective subcategory. -/
noncomputable abbrev fixedRightCoreflective (h : ∀ Y, adj.fixedLeft (R.obj Y)) :
    Coreflective adj.fixedRight.ι where
  R := adj.fixedRightCoreflector h
  adj := adj.fixedRightAdjunction h

end Reflective

end CategoryTheory.Adjunction
