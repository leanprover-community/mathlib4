/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Functor.ReflectsIso

#align_import category_theory.monoidal.center from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# Half braidings and the Drinfeld center of a monoidal category

We define `Center C` to be pairs `⟨X, b⟩`, where `X : C` and `b` is a half-braiding on `X`.

We show that `Center C` is braided monoidal,
and provide the monoidal functor `Center.forget` from `Center C` back to `C`.

## Implementation notes

Verifying the various axioms directly requires tedious rewriting.
Using the `slice` tactic may make the proofs marginally more readable.

More exciting, however, would be to make possible one of the following options:
1. Integration with homotopy.io / globular to give "picture proofs".
2. The monoidal coherence theorem, so we can ignore associators
   (after which most of these proofs are trivial).
3. Automating these proofs using `rewrite_search` or some relative.

In this file, we take the second approach using the monoidal composition `⊗≫` and the
`coherence` tactic.
-/


open CategoryTheory

open CategoryTheory.MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
-- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
structure HalfBraiding (X : C) where
  β : ∀ U, X ⊗ U ≅ U ⊗ X
  monoidal : ∀ U U', (β (U ⊗ U')).hom =
      (α_ _ _ _).inv ≫
        ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv := by
    aesop_cat
  naturality : ∀ {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X) := by
    aesop_cat
#align category_theory.half_braiding CategoryTheory.HalfBraiding

attribute [reassoc, simp] HalfBraiding.monoidal -- the reassoc lemma is redundant as a simp lemma

attribute [simp, reassoc] HalfBraiding.naturality

variable (C)

/-- The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
-- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
def Center :=
  Σ X : C, HalfBraiding X -- Why is this defined as a sigma type instead of a structure?
#align category_theory.center CategoryTheory.Center

namespace Center

variable {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext] -- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
structure Hom (X Y : Center C) where
  f : X.1 ⟶ Y.1
  comm : ∀ U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f) := by aesop_cat
#align category_theory.center.hom CategoryTheory.Center.Hom

attribute [reassoc (attr := simp)] Hom.comm

instance : Category (Center C) where
  Hom := Hom
  id X := { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[ext]
theorem ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g := by
  cases f; cases g; congr
#align category_theory.center.ext CategoryTheory.Center.ext

@[simp]
theorem id_f (X : Center C) : Hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl
#align category_theory.center.id_f CategoryTheory.Center.id_f

@[simp]
theorem comp_f {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl
#align category_theory.center.comp_f CategoryTheory.Center.comp_f

/-- Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def isoMk {X Y : Center C} (f : X.1 ≅ Y.1)
    (H : ∀ U, (f.hom ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f.hom)) :
    X ≅ Y where
  hom := ⟨f.hom, H⟩
  inv := ⟨f.inv,
    fun U => by erw [(whiskerRightIso f U).inv_comp_eq, ← Category.assoc, H,
      Category.assoc, (whiskerLeftIso U f).hom_inv_id, Category.comp_id]⟩
#align category_theory.center.iso_mk CategoryTheory.Center.isoMk

instance isIso_of_f_isIso {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : IsIso f := by
  obtain ⟨g, h1, h2⟩ := ‹IsIso f.f›
  exact inferInstanceAs (IsIso (isoMk ⟨f.f, g, h1, h2⟩ f.comm).hom)
#align category_theory.center.is_iso_of_f_is_iso CategoryTheory.Center.isIso_of_f_isIso

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
def tensorObj (X Y : Center C) : Center C :=
  ⟨X.1 ⊗ Y.1,
    { β := fun U =>
        α_ _ _ _ ≪≫
          (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
            (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _
      monoidal := fun U U' => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        simp only [HalfBraiding.monoidal]
        -- We'd like to commute `X.1 ◁ U ◁ (HalfBraiding.β Y.2 U').hom`
        -- and `((HalfBraiding.β X.2 U).hom ▷ U' ▷ Y.1)` past each other.
        -- We do this with the help of the monoidal composition `⊗≫` and the `coherence` tactic.
        calc
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom ▷ U' ⊗≫
              (_ ◁ (HalfBraiding.β Y.2 U').hom ≫
                (HalfBraiding.β X.2 U).hom ▷ _) ⊗≫
                  U ◁ (HalfBraiding.β X.2 U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by coherence
          _ = _ := by rw [whisker_exchange]; coherence
      naturality := fun {U U'} f => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        calc
          _ = 𝟙 _ ⊗≫
            (X.1 ◁ (Y.1 ◁ f ≫ (HalfBraiding.β Y.2 U').hom)) ⊗≫
              (HalfBraiding.β X.2 U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by coherence
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom ⊗≫
              (X.1 ◁ f ≫ (HalfBraiding.β X.2 U').hom) ▷ Y.1 ⊗≫ 𝟙 _ := by
            rw [HalfBraiding.naturality]; coherence
          _ = _ := by rw [HalfBraiding.naturality]; coherence }⟩
#align category_theory.center.tensor_obj CategoryTheory.Center.tensorObj

@[reassoc]
theorem whiskerLeft_comm (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C) :
    (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2.β U).hom =
      ((tensorObj X Y₁).2.β U).hom ≫ U ◁ X.1 ◁ f.f := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (f.f ▷ U ≫ (HalfBraiding.β Y₂.snd U).hom) ⊗≫
        (HalfBraiding.β X.snd U).hom ▷ Y₂.fst ⊗≫ 𝟙 _ := by coherence
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (HalfBraiding.β Y₁.snd U).hom ⊗≫
        ((X.fst ⊗ U) ◁ f.f ≫ (HalfBraiding.β X.snd U).hom ▷ Y₂.fst) ⊗≫ 𝟙 _ := by
      rw [f.comm]; coherence
    _ = _ := by rw [whisker_exchange]; coherence

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def whiskerLeft (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  f := X.1 ◁ f.f
  comm U := whiskerLeft_comm X f U

@[reassoc]
theorem whiskerRight_comm {X₁ X₂: Center C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C) :
    f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2.β U).hom =
      ((tensorObj X₁ Y).2.β U).hom ≫ U ◁ f.f ▷ Y.1 := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      (f.f ▷ (Y.fst ⊗ U) ≫ X₂.fst ◁ (HalfBraiding.β Y.snd U).hom) ⊗≫
        (HalfBraiding.β X₂.snd U).hom ▷ Y.fst ⊗≫ 𝟙 _ := by coherence
    _ = 𝟙 _ ⊗≫
      X₁.fst ◁ (HalfBraiding.β Y.snd U).hom ⊗≫
        (f.f ▷ U ≫ (HalfBraiding.β X₂.snd U).hom) ▷ Y.fst ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; coherence
    _ = _ := by rw [f.comm]; coherence

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def whiskerRight {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  f := f.f ▷ Y.1
  comm U := whiskerRight_comm f Y U

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
def tensorHom {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f ⊗ g.f
  comm U := by
    rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm, whiskerRight_comm_assoc,
      MonoidalCategory.whiskerLeft_comp]
#align category_theory.center.tensor_hom CategoryTheory.Center.tensorHom

section

attribute [local simp] id_tensorHom tensorHom_id

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
def tensorUnit : Center C :=
  ⟨𝟙_ C, { β := fun U => λ_ U ≪≫ (ρ_ U).symm }⟩
#align category_theory.center.tensor_unit CategoryTheory.Center.tensorUnit

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def associator (X Y Z : Center C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk (α_ X.1 Y.1 Z.1) (by simp)
#align category_theory.center.associator CategoryTheory.Center.associator

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def leftUnitor (X : Center C) : tensorObj tensorUnit X ≅ X :=
  isoMk (λ_ X.1) (by simp)
#align category_theory.center.left_unitor CategoryTheory.Center.leftUnitor

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def rightUnitor (X : Center C) : tensorObj X tensorUnit ≅ X :=
  isoMk (ρ_ X.1) (by simp)
#align category_theory.center.right_unitor CategoryTheory.Center.rightUnitor

end

section

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

attribute [local simp] Center.associator Center.leftUnitor Center.rightUnitor

attribute [local simp] Center.whiskerLeft Center.whiskerRight Center.tensorHom

instance : MonoidalCategory (Center C) where
  tensorObj X Y := tensorObj X Y
  tensorHom f g := tensorHom f g
  tensorHom_def := by intros; ext; simp [tensorHom_def]
  whiskerLeft X _ _ f := whiskerLeft X f
  whiskerRight f Y := whiskerRight f Y
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

@[simp]
theorem tensor_fst (X Y : Center C) : (X ⊗ Y).1 = X.1 ⊗ Y.1 :=
  rfl
#align category_theory.center.tensor_fst CategoryTheory.Center.tensor_fst

@[simp]
theorem tensor_β (X Y : Center C) (U : C) :
    (X ⊗ Y).2.β U =
      α_ _ _ _ ≪≫
        (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
          (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _ :=
  rfl
#align category_theory.center.tensor_β CategoryTheory.Center.tensor_β

@[simp]
theorem whiskerLeft_f (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) : (X ◁ f).f = X.1 ◁ f.f :=
  rfl

@[simp]
theorem whiskerRight_f {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) : (f ▷ Y).f = f.f ▷ Y.1 :=
  rfl

@[simp]
theorem tensor_f {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ g).f = f.f ⊗ g.f :=
  rfl
#align category_theory.center.tensor_f CategoryTheory.Center.tensor_f

@[simp]
theorem tensorUnit_β (U : C) : (𝟙_ (Center C)).2.β U = λ_ U ≪≫ (ρ_ U).symm :=
  rfl
#align category_theory.center.tensor_unit_β CategoryTheory.Center.tensorUnit_β

@[simp]
theorem associator_hom_f (X Y Z : Center C) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
  rfl
#align category_theory.center.associator_hom_f CategoryTheory.Center.associator_hom_f

@[simp]
theorem associator_inv_f (X Y Z : Center C) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv := by
  apply Iso.inv_ext' -- Porting note: Originally `ext`
  rw [← associator_hom_f, ← comp_f, Iso.hom_inv_id]; rfl
#align category_theory.center.associator_inv_f CategoryTheory.Center.associator_inv_f

@[simp]
theorem leftUnitor_hom_f (X : Center C) : Hom.f (λ_ X).hom = (λ_ X.1).hom :=
  rfl
#align category_theory.center.left_unitor_hom_f CategoryTheory.Center.leftUnitor_hom_f

@[simp]
theorem leftUnitor_inv_f (X : Center C) : Hom.f (λ_ X).inv = (λ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note: Originally `ext`
  rw [← leftUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl
#align category_theory.center.left_unitor_inv_f CategoryTheory.Center.leftUnitor_inv_f

@[simp]
theorem rightUnitor_hom_f (X : Center C) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
  rfl
#align category_theory.center.right_unitor_hom_f CategoryTheory.Center.rightUnitor_hom_f

@[simp]
theorem rightUnitor_inv_f (X : Center C) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note: Originally `ext`
  rw [← rightUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl
#align category_theory.center.right_unitor_inv_f CategoryTheory.Center.rightUnitor_inv_f

end

section

variable (C)

/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
def forget : MonoidalFunctor (Center C) C :=
  .mk' (.mk ⟨(fun X => X.1), (fun f => f.f)⟩) (Iso.refl _) (fun _ _ => Iso.refl _)
#align category_theory.center.forget CategoryTheory.Center.forget

variable {C}

@[simp] lemma forget_obj (X : Center C) : (forget C).obj X = X.1 := rfl
@[simp] lemma forget_map {X Y} (f : X ⟶ Y) : (forget C).map f = f.f := rfl
@[simp]
lemma forget_μIso (X Y : Center C) : (forget C).μIso X Y = Iso.refl _ := rfl

variable (C)

@[simp] lemma forget_εIso : (forget C).εIso = Iso.refl _ := rfl

instance : ReflectsIsomorphisms (forget C).toFunctor where
  reflects f i := by
    obtain ⟨g, h1, h2⟩ := i
    exact inferInstanceAs (IsIso (isoMk ⟨f.f, g, h1, h2⟩ f.comm).hom)

end

/-- Auxiliary definition for the `BraidedCategory` instance on `Center C`. -/
@[simps!]
def braiding (X Y : Center C) : X ⊗ Y ≅ Y ⊗ X :=
  isoMk (X.2.β Y.1) fun U => by
    dsimp
    simp only [Category.assoc]
    rw [← IsIso.inv_comp_eq, IsIso.Iso.inv_hom, ← HalfBraiding.monoidal_assoc,
      ← HalfBraiding.naturality_assoc, HalfBraiding.monoidal]
    simp
#align category_theory.center.braiding CategoryTheory.Center.braiding

instance braidedCategoryCenter : BraidedCategory (Center C) where
  braiding := braiding
#align category_theory.center.braided_category_center CategoryTheory.Center.braidedCategoryCenter

-- `aesop_cat` handles the hexagon axioms
section

variable [BraidedCategory C]

open BraidedCategory

/-- Auxiliary construction for `ofBraided`. -/
@[simps]
def ofBraidedObj (X : C) : Center C :=
  ⟨X, { β := fun Y => β_ X Y}⟩
#align category_theory.center.of_braided_obj CategoryTheory.Center.ofBraidedObj

variable (C)

/-- The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
def ofBraided : BraidedFunctor C (Center C) :=
  .mk' <| .mk' (.mk ⟨ofBraidedObj, (fun f => ⟨f, braiding_naturality_left f⟩)⟩)
    (isoMk (Iso.refl _) (by aesop_cat))
    (fun _ _ => isoMk (Iso.refl _) (by aesop_cat))
#align category_theory.center.of_braided CategoryTheory.Center.ofBraided

variable {C}

@[simp]
lemma ofBraided_obj (X : C) : (ofBraided C).obj X = ofBraidedObj X := rfl
@[simp]
lemma ofBraided_map_f {X Y} (f : X ⟶ Y) : ((ofBraided C).map f).f = f := rfl

@[simp]
lemma ofBraided_μIso_hom_f (X Y : C) :
    ((ofBraided C).μIso X Y).hom.f = 𝟙 _ := rfl

variable (C)

@[simp] lemma ofBraided_εIso_hom_f : (ofBraided C).εIso.hom.f = 𝟙 _ := rfl

end

end Center

end CategoryTheory
