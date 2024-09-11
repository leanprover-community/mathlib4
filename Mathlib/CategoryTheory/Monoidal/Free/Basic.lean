/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Monoidal.Functor

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
  | unit : FreeMonoidalCategory
  | tensor : FreeMonoidalCategory → FreeMonoidalCategory → FreeMonoidalCategory
  deriving Inhabited

end

local notation "F" => FreeMonoidalCategory

namespace FreeMonoidalCategory

attribute [nolint simpNF] unit.sizeOf_spec tensor.injEq tensor.sizeOf_spec

/-- Formal compositions and tensor products of identities, unitors and associators. The morphisms
    of the free monoidal category are obtained as a quotient of these formal morphisms by the
    relations defining a monoidal category. -/
-- Porting note(#5171): linter not ported yet
-- @[nolint has_nonempty_instance]
inductive Hom : F C → F C → Type u
  | id (X) : Hom X X
  | α_hom (X Y Z : F C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : F C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (unit.tensor X) X
  | l_inv (X) : Hom X (unit.tensor X)
  | ρ_hom (X : F C) : Hom (X.tensor unit) X
  | ρ_inv (X : F C) : Hom X (X.tensor unit)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : F C) {Y₁ Y₂} (f : Hom Y₁ Y₂) : Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : F C) : Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

local infixr:10 " ⟶ᵐ " => Hom

/-- The morphisms of the free monoidal category satisfy 21 relations ensuring that the resulting
    category is in fact a category and that it is monoidal. -/
inductive HomEquiv : ∀ {X Y : F C}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f : X ⟶ᵐ Y) : HomEquiv f f
  | symm {X Y} (f g : X ⟶ᵐ Y) : HomEquiv f g → HomEquiv g f
  | trans {X Y} {f g h : X ⟶ᵐ Y} : HomEquiv f g → HomEquiv g h → HomEquiv f h
  | comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶ᵐ Z) :
      HomEquiv f f' → HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶ᵐ Z) (X) :
      HomEquiv f f' → HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' → HomEquiv g g' → HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶ᵐ Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | tensor_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁)
      (g₂ : Y₂ ⟶ᵐ Z₂) :
    HomEquiv ((f₁.comp g₁).tensor (f₂.comp g₂)) ((f₁.tensor f₂).comp (g₁.tensor g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)

/-- We say that two formal morphisms in the free monoidal category are equivalent if they become
    equal if we apply the relations that are true in a monoidal category. Note that we will prove
    that there is only one equivalence class -- this is the monoidal coherence theorem. -/
def setoidHom (X Y : F C) : Setoid (X ⟶ᵐ Y) :=
  ⟨HomEquiv,
    ⟨fun f => HomEquiv.refl f, @fun f g => HomEquiv.symm f g, @fun _ _ _ hfg hgh =>
      HomEquiv.trans hfg hgh⟩⟩

attribute [instance] setoidHom

section

open FreeMonoidalCategory.HomEquiv

instance categoryFreeMonoidalCategory : Category.{u} (F C) where
  Hom X Y := Quotient (FreeMonoidalCategory.setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg ↦ HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)

instance : MonoidalCategory (F C) where
  tensorObj X Y := FreeMonoidalCategory.tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg ↦ HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f ↦ Hom.whiskerLeft X f) (fun f f' ↦ .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f ↦ Hom.whiskerRight f Y) (fun f f' ↦ .whiskerRight f f' Y) f
  tensorHom_def := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩
    exact Quotient.sound (tensorHom_def _ _)
  tensor_id X Y := Quot.sound tensor_id
  tensor_comp := @fun X₁ Y₁ Z₁ X₂ Y₂ Z₂ => by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensor_comp _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X Y)
  tensorUnit := FreeMonoidalCategory.unit
  associator X Y Z :=
    ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧, Quotient.sound α_hom_inv, Quotient.sound α_inv_hom⟩
  associator_naturality := @fun X₁ X₂ X₃ Y₁ Y₂ Y₃ => by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality := @fun X Y => by
    rintro ⟨f⟩
    exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality := @fun X Y => by
    rintro ⟨f⟩
    exact Quotient.sound (ρ_naturality _)
  pentagon W X Y Z := Quotient.sound pentagon
  triangle X Y := Quotient.sound triangle

@[simp]
theorem mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

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

@[simp]
theorem mk_α_hom {X Y Z : F C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
theorem mk_α_inv {X Y Z : F C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
theorem mk_ρ_hom {X : F C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
theorem mk_ρ_inv {X : F C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
theorem mk_l_hom {X : F C} : ⟦Hom.l_hom X⟧ = (λ_ X).hom :=
  rfl

@[simp]
theorem mk_l_inv {X : F C} : ⟦Hom.l_inv X⟧ = (λ_ X).inv :=
  rfl

@[simp]
theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X ⊗ Y :=
  rfl

@[simp]
theorem unit_eq_unit : FreeMonoidalCategory.unit = 𝟙_ (F C) :=
  rfl

/-- The abbreviation for `⟦f⟧`. -/
/- This is useful since the notation `⟦f⟧` often behaves like an element of the quotient set,
but not like a morphism. This is why we need weird `@CategoryStruct.comp (F C) ...` in the
statement in `mk_comp` above. -/
abbrev homMk {X Y : F C} (f : X ⟶ᵐ Y) : X ⟶ Y := ⟦f⟧

theorem Hom.inductionOn {motive : {X Y : F C} → (X ⟶ Y) → Prop} {X Y : F C} (t : X ⟶ Y)
    (id : (X : F C) → motive (𝟙 X))
    (α_hom : (X Y Z : F C) → motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : F C) → motive (α_ X Y Z).inv)
    (l_hom : (X : F C) → motive (λ_ X).hom)
    (l_inv : (X : F C) → motive (λ_ X).inv)
    (ρ_hom : (X : F C) → motive (ρ_ X).hom)
    (ρ_inv : (X : F C) → motive (ρ_ X).inv)
    (comp : {X Y Z : F C} → (f : X ⟶ Y) → (g : Y ⟶ Z) → motive f → motive g → motive (f ≫ g))
    (whiskerLeft : (X : F C) → {Y Z : F C} → (f : Y ⟶ Z) → motive f → motive (X ◁ f))
    (whiskerRight : {X Y : F C} → (f : X ⟶ Y) → (Z : F C) → motive f → motive (f ▷ Z)) :
    motive t := by
  apply Quotient.inductionOn
  intro f
  induction f with
  | id X => exact id X
  | α_hom X Y Z => exact α_hom X Y Z
  | α_inv X Y Z => exact α_inv X Y Z
  | l_hom X => exact l_hom X
  | l_inv X => exact l_inv X
  | ρ_hom X => exact ρ_hom X
  | ρ_inv X => exact ρ_inv X
  | comp f g hf hg => exact comp _ _ (hf ⟦f⟧) (hg ⟦g⟧)
  | whiskerLeft X f hf => exact whiskerLeft X _ (hf ⟦f⟧)
  | whiskerRight f X hf => exact whiskerRight _ X (hf ⟦f⟧)
  | @tensor W X Y Z f g hf hg =>
      have : homMk f ⊗ homMk g = homMk f ▷ X ≫ Y ◁ homMk g :=
        Quotient.sound (HomEquiv.tensorHom_def f g)
      change motive (homMk f ⊗ homMk g)
      rw [this]
      exact comp _ _ (whiskerRight _ _ (hf ⟦f⟧)) (whiskerLeft _ _ (hg ⟦g⟧))

section Functor

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (f : C → D)

/-- Auxiliary definition for `free_monoidal_category.project`. -/
def projectObj : F C → D
  | FreeMonoidalCategory.of X => f X
  | FreeMonoidalCategory.unit => 𝟙_ D
  | FreeMonoidalCategory.tensor X Y => projectObj X ⊗ projectObj Y

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
  | _, _, Hom.tensor f g => projectMapAux f ⊗ projectMapAux g

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
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [projectMapAux]; rw [hfg, hfg']
    | tensorHom_def _ _ =>
        dsimp only [projectMapAux, projectObj]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    | tensor_id => dsimp only [projectMapAux]; rw [MonoidalCategory.tensor_id]; rfl
    | tensor_comp => dsimp only [projectMapAux]; rw [MonoidalCategory.tensor_comp]
    | whiskerLeft_id =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.whiskerLeft_id]
    | id_whiskerRight =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.id_whiskerRight]
    | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.rightUnitor_naturality]
    | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.leftUnitor_naturality]
    | pentagon =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.pentagon]
    | triangle =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.triangle]

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
      simp only [Category.comp_id, Category.id_comp]
      rw [← tensorHom_id, ← tensorHom_id]
      rfl
    · rfl
  μ_natural_right := fun _ f => by
    induction' f using Quotient.recOn
    · dsimp
      simp only [Category.comp_id, Category.id_comp]
      rw [← id_tensorHom, ← id_tensorHom]
      rfl
    · rfl

end Functor

end

end FreeMonoidalCategory

end CategoryTheory
