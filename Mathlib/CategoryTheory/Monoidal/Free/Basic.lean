/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Functor

#align_import category_theory.monoidal.free.basic from "leanprover-community/mathlib"@"14b69e9f3c16630440a2cbd46f1ddad0d561dee7"

/-!
# The free monoidal category over a type

Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.

In this file, we construct the free monoidal category and prove that it is a monoidal category. If
`D` is a monoidal category, we construct the functor `FreeMonoidalCategory C ⥤ D` associated to
a function `C → D`.

The free monoidal category has two important properties: it is a groupoid and it is thin. The former
is obvious from the construction, and the latter is what is commonly known as the monoidal coherence
theorem. Both of these properties are proved in the file `Coherence.lean`.

-/


universe v' u u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u}

section

variable (C)

/--
Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.
-/
inductive FreeMonoidalCategory : Type u
  | of : C → FreeMonoidalCategory
  | Unit : FreeMonoidalCategory
  | tensor : FreeMonoidalCategory → FreeMonoidalCategory → FreeMonoidalCategory
  deriving Inhabited
#align category_theory.free_monoidal_category CategoryTheory.FreeMonoidalCategory

end

local notation "F" => FreeMonoidalCategory

namespace FreeMonoidalCategory

attribute [nolint simpNF] Unit.sizeOf_spec tensor.injEq tensor.sizeOf_spec

/-- Formal compositions and tensor products of identities, unitors and associators. The morphisms
    of the free monoidal category are obtained as a quotient of these formal morphisms by the
    relations defining a monoidal category. -/
-- porting note: unsupported linter
-- @[nolint has_nonempty_instance]
inductive Hom : F C → F C → Type u
  | id (X) : Hom X X
  | α_hom (X Y Z : F C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : F C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (Unit.tensor X) X
  | l_inv (X) : Hom X (Unit.tensor X)
  | ρ_hom (X : F C) : Hom (X.tensor Unit) X
  | ρ_inv (X : F C) : Hom X (X.tensor Unit)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : F C) {Y Z : F C} (f : Hom Y Z) :
      Hom (X.tensor Y) (X.tensor Z)
  | whiskerRight {X Y : F C} (f : Hom X Y) (Z : F C) : Hom (X.tensor Z) (Y.tensor Z)
#align category_theory.free_monoidal_category.hom CategoryTheory.FreeMonoidalCategory.Hom

local infixr:10 " ⟶ᵐ " => Hom

/-- The morphisms of the free monoidal category satisfy 21 relations ensuring that the resulting
    category is in fact a category and that it is monoidal. -/
inductive HomEquiv : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f : X ⟶ᵐ Y) : HomEquiv f f
  | symm {X Y} (f g : X ⟶ᵐ Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶ᵐ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whisker_left (X) {Y Z} (f f' : Y ⟶ᵐ Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whisker_right {Y Z} (f f' : Y ⟶ᵐ Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | comp_id {X Y} (f : X ⟶ᵐ Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | whisker_left_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | whisker_left_comp (W) {X Y Z} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
      HomEquiv ((f.comp g).whiskerLeft W) ((f.whiskerLeft W).comp (g.whiskerLeft W))
  | id_whisker_left {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv (f.whiskerLeft Unit) ((Hom.l_hom X).comp <| f.comp (Hom.l_inv Y))
  | tensor_whisker_left (X Y) {Z Z'} (f : Z ⟶ᵐ Z') :
     HomEquiv (f.whiskerLeft (X.tensor Y))
      ((Hom.α_hom X Y Z).comp <| ((f.whiskerLeft Y).whiskerLeft X).comp <| Hom.α_inv X Y Z')
  | id_whisker_right (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | comp_whisker_right {X Y Z} (W) (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
      HomEquiv ((f.comp g).whiskerRight W) ((f.whiskerRight W).comp <| g.whiskerRight W)
  | whisker_right_id {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv (f.whiskerRight Unit) ((Hom.ρ_hom X).comp <| f.comp <| Hom.ρ_inv Y)
  | whisker_right_tensor {X X'} (f : X ⟶ᵐ X') (Y Z) :
      HomEquiv (f.whiskerRight <| Y.tensor Z)
        ((Hom.α_inv X Y Z).comp <| ((f.whiskerRight Y).whiskerRight Z).comp <| Hom.α_hom X' Y Z)
  | whisker_assoc (X) {Y Y'} (f : Y ⟶ᵐ Y') (Z) :
      HomEquiv ((f.whiskerLeft X).whiskerRight Z)
        ((Hom.α_hom X Y Z).comp <| ((f.whiskerRight Z).whiskerLeft X).comp <| Hom.α_inv X Y' Z)
  | whisker_exchange {W X Y Z} (f : W ⟶ᵐ X) (g : Y ⟶ᵐ Z) :
      HomEquiv ((g.whiskerLeft W).comp <| f.whiskerRight Z)
        ((f.whiskerRight Y).comp <| g.whiskerLeft X)
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X Unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)
set_option linter.uppercaseLean3 false
#align category_theory.free_monoidal_category.HomEquiv CategoryTheory.FreeMonoidalCategory.HomEquiv

/-- We say that two formal morphisms in the free monoidal category are equivalent if they become
    equal if we apply the relations that are true in a monoidal category. Note that we will prove
    that there is only one equivalence class -- this is the monoidal coherence theorem. -/
def setoidHom (X Y : F C) : Setoid (X ⟶ᵐ Y) :=
  ⟨HomEquiv,
    ⟨fun f => HomEquiv.refl f, @fun f g => HomEquiv.symm f g, @fun _ _ _ hfg hgh =>
      HomEquiv.trans hfg hgh⟩⟩
#align category_theory.free_monoidal_category.setoid_hom CategoryTheory.FreeMonoidalCategory.setoidHom

attribute [instance] setoidHom

section

open FreeMonoidalCategory.HomEquiv

instance categoryFreeMonoidalCategory : Category.{u} (F C) where
  Hom X Y := Quotient (FreeMonoidalCategory.setoidHom X Y)
  id X := ⟦FreeMonoidalCategory.Hom.id _⟧
  comp := @fun X Y Z f g =>
    Quotient.map₂ Hom.comp
      (by
        intro f f' hf g g' hg
        exact comp hf hg)
      f g
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)
#align category_theory.free_monoidal_category.category_free_monoidal_category CategoryTheory.FreeMonoidalCategory.categoryFreeMonoidalCategory

instance : MonoidalCategory (F C) where
  tensorObj X Y := FreeMonoidalCategory.tensor X Y
  whiskerLeft := fun X _ _ f => Quotient.map (Hom.whiskerLeft X) (HomEquiv.whisker_left X) f
  whiskerRight := fun f Y =>
    Quotient.map (fun f' => Hom.whiskerRight f' Y) (fun _ _ h => HomEquiv.whisker_right _ _ _ h) f
  tensorUnit' := FreeMonoidalCategory.Unit
  associator X Y Z :=
    ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧, Quotient.sound α_hom_inv, Quotient.sound α_inv_hom⟩
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  whisker_exchange := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    apply HomEquiv.whisker_exchange
  whiskerLeft_id := fun X Y ↦ Quotient.sound (HomEquiv.whisker_left_id X Y)
  whiskerLeft_comp := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩
    apply Quotient.sound
    apply HomEquiv.whisker_left_comp
  id_whiskerLeft := by
    rintro X Y ⟨f⟩
    apply Quotient.sound
    apply HomEquiv.id_whisker_left
  tensor_whiskerLeft := by
    rintro X Y Z Z' ⟨f⟩
    apply Quotient.sound
    apply HomEquiv.tensor_whisker_left
  id_whiskerRight := by
    intro X Y
    apply Quotient.sound
    apply HomEquiv.id_whisker_right
  comp_whiskerRight := by
    rintro W X Y ⟨f⟩ ⟨g⟩ Z
    apply Quotient.sound
    apply HomEquiv.comp_whisker_right
  whiskerRight_id := by
    rintro X Y ⟨f⟩
    apply Quotient.sound
    apply HomEquiv.whisker_right_id
  whiskerRight_tensor := by
    rintro X X' ⟨f⟩ Y Z
    apply Quotient.sound
    apply HomEquiv.whisker_right_tensor
  whisker_assoc := by
    rintro X Y Y' ⟨f⟩ Z
    apply Quotient.sound
    apply HomEquiv.whisker_assoc
  pentagon W X Y Z := Quotient.sound pentagon
  triangle X Y := Quotient.sound triangle

@[simp]
theorem mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl
#align category_theory.free_monoidal_category.mk_comp CategoryTheory.FreeMonoidalCategory.mk_comp

#noalign category_theory.free_monoidal_category.mk_tensor

@[simp]
theorem mk_whiskerLeft (X : F C) {Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂) :
    ⟦f.whiskerLeft X⟧ = MonoidalCategory.whiskerLeft (C := F C) (X := X) (f := ⟦f⟧) :=
  rfl

@[simp]
theorem mk_whiskerRight {X₁ X₂ : F C} (f : X₁ ⟶ᵐ X₂) (Y : F C) :
    ⟦f.whiskerRight Y⟧ = MonoidalCategory.whiskerRight (C := F C) (f := ⟦f⟧) (Y := Y) :=
  rfl

@[simp]
theorem mk_id {X : F C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl
#align category_theory.free_monoidal_category.mk_id CategoryTheory.FreeMonoidalCategory.mk_id

@[simp]
theorem mk_α_hom {X Y Z : F C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl
#align category_theory.free_monoidal_category.mk_α_hom CategoryTheory.FreeMonoidalCategory.mk_α_hom

@[simp]
theorem mk_α_inv {X Y Z : F C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl
#align category_theory.free_monoidal_category.mk_α_inv CategoryTheory.FreeMonoidalCategory.mk_α_inv

@[simp]
theorem mk_ρ_hom {X : F C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl
#align category_theory.free_monoidal_category.mk_ρ_hom CategoryTheory.FreeMonoidalCategory.mk_ρ_hom

@[simp]
theorem mk_ρ_inv {X : F C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl
#align category_theory.free_monoidal_category.mk_ρ_inv CategoryTheory.FreeMonoidalCategory.mk_ρ_inv

@[simp]
theorem mk_l_hom {X : F C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl
#align category_theory.free_monoidal_category.mk_l_hom CategoryTheory.FreeMonoidalCategory.mk_l_hom

@[simp]
theorem mk_l_inv {X : F C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl
#align category_theory.free_monoidal_category.mk_l_inv CategoryTheory.FreeMonoidalCategory.mk_l_inv

@[simp]
theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
  rfl
#align category_theory.free_monoidal_category.tensor_eq_tensor CategoryTheory.FreeMonoidalCategory.tensor_eq_tensor

@[simp]
theorem unit_eq_unit : FreeMonoidalCategory.Unit = 𝟙_ (F C) :=
  rfl
#align category_theory.free_monoidal_category.unit_eq_unit CategoryTheory.FreeMonoidalCategory.unit_eq_unit

section Functor

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (f : C → D)

/-- Auxiliary definition for `free_monoidal_category.project`. -/
def projectObj : F C → D
  | FreeMonoidalCategory.of X => f X
  | FreeMonoidalCategory.Unit => 𝟙_ D
  | FreeMonoidalCategory.tensor X Y => projectObj X ⊗ projectObj Y
#align category_theory.free_monoidal_category.project_obj CategoryTheory.FreeMonoidalCategory.projectObj

section


open Hom

/-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
-- Porting note: here `@[simp]` generates a panic in
-- _private.Lean.Meta.Match.MatchEqs.0.Lean.Meta.Match.SimpH.substRHS
def projectMapAux : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (projectObj f X ⟶ projectObj f Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (λ_ _).hom
  | _, _, l_inv _ => (λ_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => projectObj f X ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ projectObj f X
#align category_theory.free_monoidal_category.project_map_aux CategoryTheory.FreeMonoidalCategory.projectMapAux

-- Porting note: this declaration generates the same panic.
/-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
def projectMap (X Y : F C) : (X ⟶ Y) → (projectObj f X ⟶ projectObj f Y) :=
  Quotient.lift (projectMapAux f) <| by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whisker_left _ _ _ _ h => dsimp only [projectMapAux]; rw [h]
    | whisker_right _ _ _ _ h => dsimp only [projectMapAux]; rw [h]
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | pentagon =>
        dsimp only [projectMapAux]
        exact MonoidalCategory.pentagon _ _ _ _
    | triangle =>
        dsimp only [projectMapAux]
        exact MonoidalCategory.triangle _ _
    | whisker_exchange =>
        dsimp only [projectMapAux, projectObj]; simp [MonoidalCategory.whisker_exchange]
    | _ =>
        dsimp only [projectMapAux, projectObj]; simp
#align category_theory.free_monoidal_category.project_map CategoryTheory.FreeMonoidalCategory.projectMap

end

/-- If `D` is a monoidal category and we have a function `C → D`, then we have a functor from the
    free monoidal category over `C` to the category `D`. -/
def project : MonoidalFunctor (F C) D where
  obj := projectObj f
  map := projectMap f _ _
  -- Porting note: `map_comp` and `μ_natural` were proved in mathlib3 by tidy, using induction.
  -- We probably don't expect `aesop_cat` to handle this yet, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- In any case I don't understand why we need to specify `using Quotient.recOn`.
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl
  ε := 𝟙 _
  μ X Y := 𝟙 _
  μ_natural_left := fun f _ => by
    induction' f using Quotient.recOn
    · dsimp
      simp
      rfl
    · rfl
  μ_natural_right := fun _ f => by
    induction' f using Quotient.recOn
    · dsimp
      simp
      rfl
    · rfl
#align category_theory.free_monoidal_category.project CategoryTheory.FreeMonoidalCategory.project

end Functor

end

end FreeMonoidalCategory

end CategoryTheory
