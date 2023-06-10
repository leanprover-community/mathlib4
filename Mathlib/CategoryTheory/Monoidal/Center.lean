/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.center
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathlib.CategoryTheory.Monoidal.Coherence

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `center C` is braided monoidal,
and provide the monoidal functor `center.forget` from `center C` back to `C`.

## Future work

Verifying the various axioms here is done by tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial;
   I'm unsure if the monoidal coherence theorem is even usable in dependent type theory).
3. Automating these proofs using `rewrite_search` or some relative.

-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
@[nolint has_nonempty_instance]
structure HalfBraiding (X : C) where
  β : ∀ U, X ⊗ U ≅ U ⊗ X
  monoidal' :
    ∀ U U',
      (β (U ⊗ U')).Hom =
        (α_ _ _ _).inv ≫
          ((β U).Hom ⊗ 𝟙 U') ≫ (α_ _ _ _).Hom ≫ (𝟙 U ⊗ (β U').Hom) ≫ (α_ _ _ _).inv := by
    obviously
  naturality' : ∀ {U U'} (f : U ⟶ U'), (𝟙 X ⊗ f) ≫ (β U').Hom = (β U).Hom ≫ (f ⊗ 𝟙 X) := by
    obviously
#align category_theory.half_braiding CategoryTheory.HalfBraiding

restate_axiom half_braiding.monoidal'

attribute [reassoc, simp] half_braiding.monoidal

-- the reassoc lemma is redundant as a simp lemma
restate_axiom half_braiding.naturality'

attribute [simp, reassoc] half_braiding.naturality

variable (C)

/-- The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
@[nolint has_nonempty_instance]
def Center :=
  Σ X : C, HalfBraiding X
#align category_theory.center CategoryTheory.Center

namespace Center

variable {C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism in the Drinfeld center of `C`. -/
@[ext, nolint has_nonempty_instance]
structure Hom (X Y : Center C) where
  f : X.1 ⟶ Y.1
  comm' : ∀ U, (f ⊗ 𝟙 U) ≫ (Y.2.β U).Hom = (X.2.β U).Hom ≫ (𝟙 U ⊗ f) := by obviously
#align category_theory.center.hom CategoryTheory.Center.Hom

restate_axiom hom.comm'

attribute [simp, reassoc] hom.comm

instance : Category (Center C) where
  Hom := Hom
  id X := { f := 𝟙 X.1 }
  comp X Y Z f g := { f := f.f ≫ g.f }

@[simp]
theorem id_f (X : Center C) : Hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl
#align category_theory.center.id_f CategoryTheory.Center.id_f

@[simp]
theorem comp_f {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl
#align category_theory.center.comp_f CategoryTheory.Center.comp_f

@[ext]
theorem ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g := by cases f; cases g; congr;
  exact w
#align category_theory.center.ext CategoryTheory.Center.ext

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def isoMk {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  Hom := f
  inv :=
    ⟨inv f.f, fun U => by simp [← cancel_epi (f.f ⊗ 𝟙 U), ← comp_tensor_id_assoc, ← id_tensor_comp]⟩
#align category_theory.center.iso_mk CategoryTheory.Center.isoMk

instance isIso_of_f_isIso {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : IsIso f := by
  change is_iso (iso_mk f).Hom
  infer_instance
#align category_theory.center.is_iso_of_f_is_iso CategoryTheory.Center.isIso_of_f_isIso

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensorObj (X Y : Center C) : Center C :=
  ⟨X.1 ⊗ Y.1,
    { β := fun U =>
        α_ _ _ _ ≪≫
          (Iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm ≪≫ (X.2.β U ⊗ Iso.refl Y.1) ≪≫ α_ _ _ _
      monoidal' := fun U U' => by
        dsimp
        simp only [comp_tensor_id, id_tensor_comp, category.assoc, half_braiding.monoidal]
        -- On the RHS, we'd like to commute `((X.snd.β U).hom ⊗ 𝟙 Y.fst) ⊗ 𝟙 U'`
        -- and `𝟙 U ⊗ 𝟙 X.fst ⊗ (Y.snd.β U').hom` past each other,
        -- but there are some associators we need to get out of the way first.
        slice_rhs 6 8 => rw [pentagon]
        slice_rhs 5 6 => rw [associator_naturality]
        slice_rhs 7 8 => rw [← associator_naturality]
        slice_rhs 6 7 =>
          rw [tensor_id, tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id, ←
            tensor_id, ← tensor_id]
        -- Now insert associators as needed to make the four half-braidings look identical
        slice_rhs 10 10 => rw [associator_inv_conjugation]
        slice_rhs 7 7 => rw [associator_inv_conjugation]
        slice_rhs 6 6 => rw [associator_conjugation]
        slice_rhs 3 3 => rw [associator_conjugation]
        -- Finish with an application of the coherence theorem.
        coherence
      naturality' := fun U U' f => by
        dsimp
        rw [category.assoc, category.assoc, category.assoc, category.assoc,
          id_tensor_associator_naturality_assoc, ← id_tensor_comp_assoc, half_braiding.naturality,
          id_tensor_comp_assoc, associator_inv_naturality_assoc, ← comp_tensor_id_assoc,
          half_braiding.naturality, comp_tensor_id_assoc, associator_naturality, ← tensor_id] }⟩
#align category_theory.center.tensor_obj CategoryTheory.Center.tensorObj

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensorHom {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f ⊗ g.f
  comm' U := by
    dsimp
    rw [category.assoc, category.assoc, category.assoc, category.assoc, associator_naturality_assoc,
      ← tensor_id_comp_id_tensor, category.assoc, ← id_tensor_comp_assoc, g.comm,
      id_tensor_comp_assoc, tensor_id_comp_id_tensor_assoc, ← id_tensor_comp_tensor_id,
      category.assoc, associator_inv_naturality_assoc, id_tensor_associator_inv_naturality_assoc,
      tensor_id, id_tensor_comp_tensor_id_assoc, ← tensor_id_comp_id_tensor g.f, category.assoc, ←
      comp_tensor_id_assoc, f.comm, comp_tensor_id_assoc, id_tensor_associator_naturality,
      associator_naturality_assoc, ← id_tensor_comp, tensor_id_comp_id_tensor]
#align category_theory.center.tensor_hom CategoryTheory.Center.tensorHom

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
@[simps]
def tensorUnit : Center C :=
  ⟨𝟙_ C,
    { β := fun U => λ_ U ≪≫ (ρ_ U).symm
      monoidal' := fun U U' => by simp
      naturality' := fun U U' f => by
        dsimp
        rw [left_unitor_naturality_assoc, right_unitor_inv_naturality, category.assoc] }⟩
#align category_theory.center.tensor_unit CategoryTheory.Center.tensorUnit

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def associator (X Y Z : Center C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk
    ⟨(α_ X.1 Y.1 Z.1).Hom, fun U => by
      dsimp
      simp only [comp_tensor_id, id_tensor_comp, ← tensor_id, associator_conjugation]
      coherence⟩
#align category_theory.center.associator CategoryTheory.Center.associator

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def leftUnitor (X : Center C) : tensorObj tensorUnit X ≅ X :=
  isoMk
    ⟨(λ_ X.1).Hom, fun U => by
      dsimp
      simp only [category.comp_id, category.assoc, tensor_inv_hom_id, comp_tensor_id,
        tensor_id_comp_id_tensor, triangle_assoc_comp_right_inv]
      rw [← left_unitor_tensor, left_unitor_naturality, left_unitor_tensor'_assoc]⟩
#align category_theory.center.left_unitor CategoryTheory.Center.leftUnitor

/-- Auxiliary definition for the `monoidal_category` instance on `center C`. -/
def rightUnitor (X : Center C) : tensorObj X tensorUnit ≅ X :=
  isoMk
    ⟨(ρ_ X.1).Hom, fun U => by
      dsimp
      simp only [tensor_id_comp_id_tensor_assoc, triangle_assoc, id_tensor_comp, category.assoc]
      rw [← tensor_id_comp_id_tensor_assoc (ρ_ U).inv, cancel_epi, ← right_unitor_tensor_inv_assoc,
        ← right_unitor_inv_naturality_assoc]
      simp⟩
#align category_theory.center.right_unitor CategoryTheory.Center.rightUnitor

section

attribute [local simp] associator_naturality left_unitor_naturality right_unitor_naturality pentagon

attribute [local simp] center.associator center.left_unitor center.right_unitor

instance : MonoidalCategory (Center C) where
  tensorObj X Y := tensorObj X Y
  tensorHom X₁ Y₁ X₂ Y₂ f g := tensorHom f g
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_fst (X Y : Center C) : (X ⊗ Y).1 = X.1 ⊗ Y.1 :=
  rfl
#align category_theory.center.tensor_fst CategoryTheory.Center.tensor_fst

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_β (X Y : Center C) (U : C) :
    (X ⊗ Y).2.β U =
      α_ _ _ _ ≪≫
        (Iso.refl X.1 ⊗ Y.2.β U) ≪≫ (α_ _ _ _).symm ≪≫ (X.2.β U ⊗ Iso.refl Y.1) ≪≫ α_ _ _ _ :=
  rfl
#align category_theory.center.tensor_β CategoryTheory.Center.tensor_β

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem tensor_f {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ g).f = f.f ⊗ g.f :=
  rfl
#align category_theory.center.tensor_f CategoryTheory.Center.tensor_f

@[simp]
theorem tensorUnit_β (U : C) : (𝟙_ (Center C)).2.β U = λ_ U ≪≫ (ρ_ U).symm :=
  rfl
#align category_theory.center.tensor_unit_β CategoryTheory.Center.tensorUnit_β

@[simp]
theorem associator_hom_f (X Y Z : Center C) : Hom.f (α_ X Y Z).Hom = (α_ X.1 Y.1 Z.1).Hom :=
  rfl
#align category_theory.center.associator_hom_f CategoryTheory.Center.associator_hom_f

@[simp]
theorem associator_inv_f (X Y Z : Center C) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv := by ext;
  rw [← associator_hom_f, ← comp_f, iso.hom_inv_id]; rfl
#align category_theory.center.associator_inv_f CategoryTheory.Center.associator_inv_f

@[simp]
theorem leftUnitor_hom_f (X : Center C) : Hom.f (λ_ X).Hom = (λ_ X.1).Hom :=
  rfl
#align category_theory.center.left_unitor_hom_f CategoryTheory.Center.leftUnitor_hom_f

@[simp]
theorem leftUnitor_inv_f (X : Center C) : Hom.f (λ_ X).inv = (λ_ X.1).inv := by ext;
  rw [← left_unitor_hom_f, ← comp_f, iso.hom_inv_id]; rfl
#align category_theory.center.left_unitor_inv_f CategoryTheory.Center.leftUnitor_inv_f

@[simp]
theorem rightUnitor_hom_f (X : Center C) : Hom.f (ρ_ X).Hom = (ρ_ X.1).Hom :=
  rfl
#align category_theory.center.right_unitor_hom_f CategoryTheory.Center.rightUnitor_hom_f

@[simp]
theorem rightUnitor_inv_f (X : Center C) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv := by ext;
  rw [← right_unitor_hom_f, ← comp_f, iso.hom_inv_id]; rfl
#align category_theory.center.right_unitor_inv_f CategoryTheory.Center.rightUnitor_inv_f

end

section

variable (C)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
@[simps]
def forget : MonoidalFunctor (Center C) C where
  obj X := X.1
  map X Y f := f.f
  ε := 𝟙 (𝟙_ C)
  μ X Y := 𝟙 (X.1 ⊗ Y.1)
#align category_theory.center.forget CategoryTheory.Center.forget

instance : ReflectsIsomorphisms (forget C).toFunctor
    where reflects A B f i := by dsimp at i ; skip; change is_iso (iso_mk f).Hom; infer_instance

end

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Auxiliary definition for the `braided_category` instance on `center C`. -/
@[simps]
def braiding (X Y : Center C) : X ⊗ Y ≅ Y ⊗ X :=
  isoMk
    ⟨(X.2.β Y.1).Hom, fun U => by
      dsimp
      simp only [category.assoc]
      rw [← is_iso.inv_comp_eq, is_iso.iso.inv_hom, ← half_braiding.monoidal_assoc, ←
        half_braiding.naturality_assoc, half_braiding.monoidal]
      simp⟩
#align category_theory.center.braiding CategoryTheory.Center.braiding

instance braidedCategoryCenter : BraidedCategory (Center C) where
  braiding := braiding
  braiding_naturality' X Y X' Y' f g := by
    ext
    dsimp
    rw [← tensor_id_comp_id_tensor, category.assoc, half_braiding.naturality, f.comm_assoc,
      id_tensor_comp_tensor_id]
#align category_theory.center.braided_category_center CategoryTheory.Center.braidedCategoryCenter

-- `obviously` handles the hexagon axioms
section

variable [BraidedCategory C]

open BraidedCategory

/-- Auxiliary construction for `of_braided`. -/
@[simps]
def ofBraidedObj (X : C) : Center C :=
  ⟨X, {
      β := fun Y => β_ X Y
      monoidal' := fun U U' => by
        rw [iso.eq_inv_comp, ← category.assoc, ← category.assoc, iso.eq_comp_inv, category.assoc,
          category.assoc]
        exact hexagon_forward X U U' }⟩
#align category_theory.center.of_braided_obj CategoryTheory.Center.ofBraidedObj

variable (C)

/-- The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
@[simps]
def ofBraided : MonoidalFunctor C (Center C) where
  obj := ofBraidedObj
  map X X' f :=
    { f
      comm' := fun U => braiding_naturality _ _ }
  ε :=
    { f := 𝟙 _
      comm' := fun U => by
        dsimp
        rw [tensor_id, category.id_comp, tensor_id, category.comp_id, ← braiding_right_unitor,
          category.assoc, iso.hom_inv_id, category.comp_id] }
  μ X Y :=
    { f := 𝟙 _
      comm' := fun U => by
        dsimp
        rw [tensor_id, tensor_id, category.id_comp, category.comp_id, ← iso.inv_comp_eq, ←
          category.assoc, ← category.assoc, ← iso.comp_inv_eq, category.assoc, hexagon_reverse,
          category.assoc] }
#align category_theory.center.of_braided CategoryTheory.Center.ofBraided

end

end Center

end CategoryTheory

