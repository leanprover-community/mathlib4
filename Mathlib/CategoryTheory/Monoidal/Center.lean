/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

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

@[expose] public section


universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- A half-braiding on `X : C` is a family of isomorphisms `X ⊗ U ≅ U ⊗ X`,
monoidally natural in `U : C`.

Thinking of `C` as a 2-category with a single `0`-morphism, these are the same as natural
transformations (in the pseudo- sense) of the identity 2-functor on `C`, which send the unique
`0`-morphism to `X`.
-/
structure HalfBraiding (X : C) where
  /-- The family of isomorphisms `X ⊗ U ≅ U ⊗ X` -/
  β : ∀ U, X ⊗ U ≅ U ⊗ X
  monoidal : ∀ U U', (β (U ⊗ U')).hom =
      (α_ _ _ _).inv ≫
        ((β U).hom ▷ U') ≫ (α_ _ _ _).hom ≫ (U ◁ (β U').hom) ≫ (α_ _ _ _).inv := by
    cat_disch
  naturality : ∀ {U U'} (f : U ⟶ U'), (X ◁ f) ≫ (β U').hom = (β U).hom ≫ (f ▷ X) := by
    cat_disch

attribute [reassoc, simp] HalfBraiding.monoidal -- the reassoc lemma is redundant as a simp lemma

attribute [simp, reassoc] HalfBraiding.naturality

variable (C)

/-- The Drinfeld center of a monoidal category `C` has as objects pairs `⟨X, b⟩`, where `X : C`
and `b` is a half-braiding on `X`.
-/
def Center :=
  Σ X : C, HalfBraiding X

namespace Center

variable {C}

/-- A morphism in the Drinfeld center of `C`. -/
@[ext]
structure Hom (X Y : Center C) where
  /-- The underlying morphism between the first components of the objects involved -/
  f : X.1 ⟶ Y.1
  comm : ∀ U, (f ▷ U) ≫ (Y.2.β U).hom = (X.2.β U).hom ≫ (U ◁ f) := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

instance : Quiver (Center C) where
  Hom := Hom

@[ext]
theorem ext {X Y : Center C} (f g : X ⟶ Y) (w : f.f = g.f) : f = g := by
  cases f; cases g; congr

instance : Category (Center C) where
  id X := { f := 𝟙 X.1 }
  comp f g := { f := f.f ≫ g.f }

@[simp]
theorem id_f (X : Center C) : Hom.f (𝟙 X) = 𝟙 X.1 :=
  rfl

@[simp]
theorem comp_f {X Y Z : Center C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- Construct an isomorphism in the Drinfeld center from
a morphism whose underlying morphism is an isomorphism.
-/
@[simps]
def isoMk {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : X ≅ Y where
  hom := f
  inv := ⟨inv f.f,
    fun U => by simp [← cancel_epi (f.f ▷ U), ← comp_whiskerRight_assoc,
      ← MonoidalCategory.whiskerLeft_comp] ⟩

instance isIso_of_f_isIso {X Y : Center C} (f : X ⟶ Y) [IsIso f.f] : IsIso f := by
  change IsIso (isoMk f).hom
  infer_instance

set_option backward.defeqAttrib.useBackward true in
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
                  U ◁ (HalfBraiding.β X.2 U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by monoidal
          _ = _ := by rw [whisker_exchange]; monoidal
      naturality := fun {U U'} f => by
        dsimp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, whiskerRightIso_hom]
        calc
          _ = 𝟙 _ ⊗≫
            (X.1 ◁ (Y.1 ◁ f ≫ (HalfBraiding.β Y.2 U').hom)) ⊗≫
              (HalfBraiding.β X.2 U').hom ▷ Y.1 ⊗≫ 𝟙 _ := by monoidal
          _ = 𝟙 _ ⊗≫
            X.1 ◁ (HalfBraiding.β Y.2 U).hom ⊗≫
              (X.1 ◁ f ≫ (HalfBraiding.β X.2 U').hom) ▷ Y.1 ⊗≫ 𝟙 _ := by
            rw [HalfBraiding.naturality]; monoidal
          _ = _ := by rw [HalfBraiding.naturality]; monoidal }⟩

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem whiskerLeft_comm (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) (U : C) :
    (X.1 ◁ f.f) ▷ U ≫ ((tensorObj X Y₂).2.β U).hom =
      ((tensorObj X Y₁).2.β U).hom ≫ U ◁ X.1 ◁ f.f := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (f.f ▷ U ≫ (HalfBraiding.β Y₂.snd U).hom) ⊗≫
        (HalfBraiding.β X.snd U).hom ▷ Y₂.fst ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫
      X.fst ◁ (HalfBraiding.β Y₁.snd U).hom ⊗≫
        ((X.fst ⊗ U) ◁ f.f ≫ (HalfBraiding.β X.snd U).hom ▷ Y₂.fst) ⊗≫ 𝟙 _ := by
      rw [f.comm]; monoidal
    _ = _ := by rw [whisker_exchange]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def whiskerLeft (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) :
    tensorObj X Y₁ ⟶ tensorObj X Y₂ where
  f := X.1 ◁ f.f
  comm U := whiskerLeft_comm X f U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in -- Needed below.
@[reassoc]
theorem whiskerRight_comm {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) (U : C) :
    f.f ▷ Y.1 ▷ U ≫ ((tensorObj X₂ Y).2.β U).hom =
      ((tensorObj X₁ Y).2.β U).hom ≫ U ◁ f.f ▷ Y.1 := by
  dsimp only [tensorObj_fst, tensorObj_snd_β, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, whiskerRightIso_hom]
  calc
    _ = 𝟙 _ ⊗≫
      (f.f ▷ (Y.fst ⊗ U) ≫ X₂.fst ◁ (HalfBraiding.β Y.snd U).hom) ⊗≫
        (HalfBraiding.β X₂.snd U).hom ▷ Y.fst ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫
      X₁.fst ◁ (HalfBraiding.β Y.snd U).hom ⊗≫
        (f.f ▷ U ≫ (HalfBraiding.β X₂.snd U).hom) ▷ Y.fst ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by rw [f.comm]; monoidal

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def whiskerRight {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) :
    tensorObj X₁ Y ⟶ tensorObj X₂ Y where
  f := f.f ▷ Y.1
  comm U := whiskerRight_comm f Y U

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
def tensorHom {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ where
  f := f.f ⊗ₘ g.f
  comm U := by
    rw [tensorHom_def, comp_whiskerRight_assoc, whiskerLeft_comm, whiskerRight_comm_assoc,
      MonoidalCategory.whiskerLeft_comp]

section

/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
@[simps]
def tensorUnit : Center C :=
  ⟨𝟙_ C, { β := fun U => λ_ U ≪≫ (ρ_ U).symm }⟩

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def associator (X Y Z : Center C) : tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) :=
  isoMk ⟨(α_ X.1 Y.1 Z.1).hom, fun U => by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def leftUnitor (X : Center C) : tensorObj tensorUnit X ≅ X :=
  isoMk ⟨(λ_ X.1).hom, fun U => by simp⟩

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `MonoidalCategory` instance on `Center C`. -/
def rightUnitor (X : Center C) : tensorObj X tensorUnit ≅ X :=
  isoMk ⟨(ρ_ X.1).hom, fun U => by simp⟩

end

section

attribute [local simp] associator_naturality leftUnitor_naturality rightUnitor_naturality pentagon

attribute [local simp] Center.associator Center.leftUnitor Center.rightUnitor

attribute [local simp] Center.whiskerLeft Center.whiskerRight Center.tensorHom

set_option backward.defeqAttrib.useBackward true in
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

@[simp]
theorem tensor_β (X Y : Center C) (U : C) :
    (X ⊗ Y).2.β U =
      α_ _ _ _ ≪≫
        (whiskerLeftIso X.1 (Y.2.β U)) ≪≫ (α_ _ _ _).symm ≪≫
          (whiskerRightIso (X.2.β U) Y.1) ≪≫ α_ _ _ _ :=
  rfl

@[simp]
theorem whiskerLeft_f (X : Center C) {Y₁ Y₂ : Center C} (f : Y₁ ⟶ Y₂) : (X ◁ f).f = X.1 ◁ f.f :=
  rfl

@[simp]
theorem whiskerRight_f {X₁ X₂ : Center C} (f : X₁ ⟶ X₂) (Y : Center C) : (f ▷ Y).f = f.f ▷ Y.1 :=
  rfl

@[simp]
theorem tensor_f {X₁ Y₁ X₂ Y₂ : Center C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : (f ⊗ₘ g).f = f.f ⊗ₘ g.f :=
  rfl

@[simp]
theorem tensorUnit_β (U : C) : (𝟙_ (Center C)).2.β U = λ_ U ≪≫ (ρ_ U).symm :=
  rfl

@[simp]
theorem associator_hom_f (X Y Z : Center C) : Hom.f (α_ X Y Z).hom = (α_ X.1 Y.1 Z.1).hom :=
  rfl

@[simp]
theorem associator_inv_f (X Y Z : Center C) : Hom.f (α_ X Y Z).inv = (α_ X.1 Y.1 Z.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← associator_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

@[simp]
theorem leftUnitor_hom_f (X : Center C) : Hom.f (λ_ X).hom = (λ_ X.1).hom :=
  rfl

@[simp]
theorem leftUnitor_inv_f (X : Center C) : Hom.f (λ_ X).inv = (λ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← leftUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

@[simp]
theorem rightUnitor_hom_f (X : Center C) : Hom.f (ρ_ X).hom = (ρ_ X.1).hom :=
  rfl

@[simp]
theorem rightUnitor_inv_f (X : Center C) : Hom.f (ρ_ X).inv = (ρ_ X.1).inv := by
  apply Iso.inv_ext' -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Originally `ext`
  rw [← rightUnitor_hom_f, ← comp_f, Iso.hom_inv_id]; rfl

end

section

variable (C)

/-- The forgetful monoidal functor from the Drinfeld center to the original category. -/
@[simps]
def forget : Center C ⥤ C where
  obj X := X.1
  map f := f.f

set_option backward.isDefEq.respectTransparency false in
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

@[simp] lemma forget_ε : ε (forget C) = 𝟙 _ := rfl
@[simp] lemma forget_η : η (forget C) = 𝟙 _ := rfl

variable {C}

@[simp] lemma forget_μ (X Y : Center C) : μ (forget C) X Y = 𝟙 _ := rfl
@[simp] lemma forget_δ (X Y : Center C) : δ (forget C) X Y = 𝟙 _ := rfl

set_option backward.defeqAttrib.useBackward true in
instance : (forget C).ReflectsIsomorphisms where
  reflects f i := by dsimp at i; change IsIso (isoMk f).hom; infer_instance

end

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for the `BraidedCategory` instance on `Center C`. -/
@[simps!]
def braiding (X Y : Center C) : X ⊗ Y ≅ Y ⊗ X :=
  isoMk
    ⟨(X.2.β Y.1).hom, fun U => by
      dsimp
      simp only [Category.assoc]
      rw [← IsIso.inv_comp_eq, IsIso.Iso.inv_hom, ← HalfBraiding.monoidal_assoc,
        ← HalfBraiding.naturality_assoc, HalfBraiding.monoidal]
      simp⟩

instance braidedCategoryCenter : BraidedCategory (Center C) where
  braiding := braiding

-- `cat_disch` handles the hexagon axioms
section

variable [BraidedCategory C]

open BraidedCategory

/-- Auxiliary construction for `ofBraided`. -/
@[simps]
def ofBraidedObj (X : C) : Center C :=
  ⟨X, { β := fun Y => β_ X Y}⟩

variable (C)

/-- The functor lifting a braided category to its center, using the braiding as the half-braiding.
-/
@[simps]
def ofBraided : C ⥤ Center C where
  obj := ofBraidedObj
  map f :=
    { f
      comm := fun U => braiding_naturality_left f U }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (ofBraided C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso :=
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } }
      μIso := fun _ _ ↦
        { hom := { f := 𝟙 _ }
          inv := { f := 𝟙 _ } } }

@[simp] lemma ofBraided_ε_f : (ε (ofBraided C)).f = 𝟙 _ := rfl
@[simp] lemma ofBraided_η_f : (η (ofBraided C)).f = 𝟙 _ := rfl

variable {C}

@[simp] lemma ofBraided_μ_f (X Y : C) : (μ (ofBraided C) X Y).f = 𝟙 _ := rfl
@[simp] lemma ofBraided_δ_f (X Y : C) : (δ (ofBraided C) X Y).f = 𝟙 _ := rfl

end

end Center

end CategoryTheory
