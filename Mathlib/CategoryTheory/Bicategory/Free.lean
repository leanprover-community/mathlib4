/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Functor

#align_import category_theory.bicategory.free from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# Free bicategories

We define the free bicategory over a quiver. In this bicategory, the 1-morphisms are freely
generated by the arrows in the quiver, and the 2-morphisms are freely generated by the formal
identities, the formal unitors, and the formal associators modulo the relation derived from the
axioms of a bicategory.

## Main definitions

* `FreeBicategory B`: the free bicategory over a quiver `B`.
* `FreeBicategory.lift F`: the pseudofunctor from `FreeBicategory B` to `C` associated with a
  prefunctor `F` from `B` to `C`.
-/


universe w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace CategoryTheory

open Category Bicategory

open Bicategory

/-- Free bicategory over a quiver. Its objects are the same as those in the underlying quiver. -/
def FreeBicategory (B : Type u) :=
  B
#align category_theory.free_bicategory CategoryTheory.FreeBicategory

instance (B : Type u) : ∀ [Inhabited B], Inhabited (FreeBicategory B) := by
  intro h
  exact id h

namespace FreeBicategory

section

variable {B : Type u} [Quiver.{v + 1} B]

/-- 1-morphisms in the free bicategory. -/
inductive Hom : B → B → Type max u v
  | of {a b : B} (f : a ⟶ b) : Hom a b
  | id (a : B) : Hom a a
  | comp {a b c : B} (f : Hom a b) (g : Hom b c) : Hom a c
#align category_theory.free_bicategory.hom CategoryTheory.FreeBicategory.Hom

instance (a b : B) [Inhabited (a ⟶ b)] : Inhabited (Hom a b) :=
  ⟨Hom.of default⟩

instance quiver : Quiver.{max u v + 1} (FreeBicategory B) where
  Hom := fun a b : B => Hom a b

instance categoryStruct : CategoryStruct.{max u v} (FreeBicategory B) where
  id   := fun a : B => Hom.id a
  comp := @fun _ _ _ => Hom.comp

/-- Representatives of 2-morphisms in the free bicategory. -/
-- Porting note: no such linter
-- @[nolint has_nonempty_instance]
inductive Hom₂ : ∀ {a b : FreeBicategory B}, (a ⟶ b) → (a ⟶ b) → Type max u v
  | id {a b} (f : a ⟶ b) : Hom₂ f f
  | vcomp {a b} {f g h : a ⟶ b} (η : Hom₂ f g) (θ : Hom₂ g h) : Hom₂ f h
  | whisker_left {a b c} (f : a ⟶ b) {g h : b ⟶ c} (η : Hom₂ g h) :
      Hom₂ (f ≫ g) (f ≫ h)-- `η` cannot be earlier than `h` since it is a recursive argument.
  | whisker_right {a b c} {f g : a ⟶ b} (h : b ⟶ c) (η : Hom₂ f g) : Hom₂ (f.comp h) (g.comp h)
  | associator {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      Hom₂ ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | associator_inv {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
      Hom₂ (f ≫ (g ≫ h)) ((f ≫ g) ≫ h)
  | right_unitor {a b} (f : a ⟶ b) : Hom₂ (f ≫ (𝟙 b)) f
  | right_unitor_inv {a b} (f : a ⟶ b) : Hom₂ f (f ≫ (𝟙 b))
  | left_unitor {a b} (f : a ⟶ b) : Hom₂ ((𝟙 a) ≫ f) f
  | left_unitor_inv {a b} (f : a ⟶ b) : Hom₂ f ((𝟙 a) ≫ f)
#align category_theory.free_bicategory.hom₂ CategoryTheory.FreeBicategory.Hom₂

section

-- Porting note: commenting out redundant binder annotation update
-- variable {B}

-- mathport name: vcomp
-- The following notations are only used in the definition of `Rel` to simplify the notation.
local infixr:0 " ≫ " => Hom₂.vcomp

-- mathport name: id
local notation "𝟙" => Hom₂.id

-- mathport name: whisker_left
local notation f " ◁ " η => Hom₂.whisker_left f η

-- mathport name: whisker_right
local notation η " ▷ " h => Hom₂.whisker_right h η

-- mathport name: associator
local notation "α_" => Hom₂.associator

-- mathport name: left_unitor
local notation "λ_" => Hom₂.left_unitor

-- mathport name: right_unitor
local notation "ρ_" => Hom₂.right_unitor

-- mathport name: associator_inv
local notation "α⁻¹_" => Hom₂.associator_inv

-- mathport name: left_unitor_inv
local notation "λ⁻¹_" => Hom₂.left_unitor_inv

-- mathport name: right_unitor_inv
local notation "ρ⁻¹_" => Hom₂.right_unitor_inv

/-- Relations between 2-morphisms in the free bicategory. -/
inductive Rel : ∀ {a b : FreeBicategory B} {f g : a ⟶ b}, Hom₂ f g → Hom₂ f g → Prop
  | vcomp_right {a b} {f g h : Hom a b} (η : Hom₂ f g) (θ₁ θ₂ : Hom₂ g h) :
      Rel θ₁ θ₂ → Rel (η ≫ θ₁) (η ≫ θ₂)
  | vcomp_left {a b} {f g h : Hom a b} (η₁ η₂ : Hom₂ f g) (θ : Hom₂ g h) :
      Rel η₁ η₂ → Rel (η₁ ≫ θ) (η₂ ≫ θ)
  | id_comp {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (𝟙 f ≫ η) η
  | comp_id {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (η ≫ 𝟙 g) η
  | assoc {a b} {f g h i : Hom a b} (η : Hom₂ f g) (θ : Hom₂ g h) (ι : Hom₂ h i) :
      Rel ((η ≫ θ) ≫ ι) (η ≫ θ ≫ ι)
  | whisker_left {a b c} (f : Hom a b) (g h : Hom b c) (η η' : Hom₂ g h) :
      Rel η η' → Rel (f ◁ η) (f ◁ η')
  | whisker_left_id {a b c} (f : Hom a b) (g : Hom b c) : Rel (f ◁ 𝟙 g) (𝟙 (f.comp g))
  | whisker_left_comp {a b c} (f : Hom a b) {g h i : Hom b c} (η : Hom₂ g h) (θ : Hom₂ h i) :
      Rel (f ◁ η ≫ θ) ((f ◁ η) ≫ f ◁ θ)
  | id_whisker_left {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (Hom.id a ◁ η) (λ_ f ≫ η ≫ λ⁻¹_ g)
  | comp_whisker_left {a b c d} (f : Hom a b) (g : Hom b c) {h h' : Hom c d} (η : Hom₂ h h') :
     Rel (f.comp g ◁ η) (α_ f g h ≫ (f ◁ g ◁ η) ≫ α⁻¹_ f g h')
  | whisker_right {a b c} (f g : Hom a b) (h : Hom b c) (η η' : Hom₂ f g) :
      Rel η η' → Rel (η ▷ h) (η' ▷ h)
  | id_whisker_right {a b c} (f : Hom a b) (g : Hom b c) : Rel (𝟙 f ▷ g) (𝟙 (f.comp g))
  | comp_whisker_right {a b c} {f g h : Hom a b} (i : Hom b c) (η : Hom₂ f g) (θ : Hom₂ g h) :
      Rel ((η ≫ θ) ▷ i) ((η ▷ i) ≫ θ ▷ i)
  | whisker_right_id {a b} {f g : Hom a b} (η : Hom₂ f g) : Rel (η ▷ Hom.id b) (ρ_ f ≫ η ≫ ρ⁻¹_ g)
  | whisker_right_comp {a b c d} {f f' : Hom a b} (g : Hom b c) (h : Hom c d) (η : Hom₂ f f') :
      Rel (η ▷ g.comp h) (α⁻¹_ f g h ≫ ((η ▷ g) ▷ h) ≫ α_ f' g h)
  | whisker_assoc {a b c d} (f : Hom a b) {g g' : Hom b c} (η : Hom₂ g g') (h : Hom c d) :
      Rel ((f ◁ η) ▷ h) (α_ f g h ≫ (f ◁ η ▷ h) ≫ α⁻¹_ f g' h)
  | whisker_exchange {a b c} {f g : Hom a b} {h i : Hom b c} (η : Hom₂ f g) (θ : Hom₂ h i) :
      Rel ((f ◁ θ) ≫ η ▷ i) ((η ▷ h) ≫ g ◁ θ)
  | associator_hom_inv {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
      Rel (α_ f g h ≫ α⁻¹_ f g h) (𝟙 ((f.comp g).comp h))
  | associator_inv_hom {a b c d} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
      Rel (α⁻¹_ f g h ≫ α_ f g h) (𝟙 (f.comp (g.comp h)))
  | left_unitor_hom_inv {a b} (f : Hom a b) : Rel (λ_ f ≫ λ⁻¹_ f) (𝟙 ((Hom.id a).comp f))
  | left_unitor_inv_hom {a b} (f : Hom a b) : Rel (λ⁻¹_ f ≫ λ_ f) (𝟙 f)
  | right_unitor_hom_inv {a b} (f : Hom a b) : Rel (ρ_ f ≫ ρ⁻¹_ f) (𝟙 (f.comp (Hom.id b)))
  | right_unitor_inv_hom {a b} (f : Hom a b) : Rel (ρ⁻¹_ f ≫ ρ_ f) (𝟙 f)
  | pentagon {a b c d e} (f : Hom a b) (g : Hom b c) (h : Hom c d) (i : Hom d e) :
      Rel ((α_ f g h ▷ i) ≫ α_ f (g.comp h) i ≫ f ◁ α_ g h i)
        (α_ (f.comp g) h i ≫ α_ f g (h.comp i))
  | triangle {a b c} (f : Hom a b) (g : Hom b c) : Rel (α_ f (Hom.id b) g ≫ f ◁ λ_ g) (ρ_ f ▷ g)
#align category_theory.free_bicategory.rel CategoryTheory.FreeBicategory.Rel

end

-- Porting note: commenting out redundant binder annotation update
-- variable {B}

instance homCategory (a b : FreeBicategory B) : Category (a ⟶ b) where
  Hom f g := Quot (@Rel _ _ a b f g)
  id f := Quot.mk Rel (Hom₂.id f)
  comp := @fun f g h => Quot.map₂ Hom₂.vcomp Rel.vcomp_right Rel.vcomp_left
  id_comp := by
    rintro f g ⟨η⟩
    exact Quot.sound (Rel.id_comp η)
  comp_id := by
    rintro f g ⟨η⟩
    exact Quot.sound (Rel.comp_id η)
  assoc := by
    rintro f g h i ⟨η⟩ ⟨θ⟩ ⟨ι⟩
    exact Quot.sound (Rel.assoc η θ ι)
#align category_theory.free_bicategory.hom_category CategoryTheory.FreeBicategory.homCategory

/-- Bicategory structure on the free bicategory. -/
instance bicategory : Bicategory (FreeBicategory B) where
  homCategory := @fun (a b : B) => FreeBicategory.homCategory a b
  whiskerLeft := @fun a b c f g h η => Quot.map (Hom₂.whisker_left f) (Rel.whisker_left f g h) η
  whiskerLeft_id := @fun a b c f g => Quot.sound (Rel.whisker_left_id f g)
  associator := @fun a b c d f g h =>
    { hom := Quot.mk Rel (Hom₂.associator f g h)
      inv := Quot.mk Rel (Hom₂.associator_inv f g h)
      hom_inv_id := Quot.sound (Rel.associator_hom_inv f g h)
      inv_hom_id := Quot.sound (Rel.associator_inv_hom f g h) }
  leftUnitor := @fun a b f =>
    { hom := Quot.mk Rel (Hom₂.left_unitor f)
      inv := Quot.mk Rel (Hom₂.left_unitor_inv f)
      hom_inv_id := Quot.sound (Rel.left_unitor_hom_inv f)
      inv_hom_id := Quot.sound (Rel.left_unitor_inv_hom f) }
  rightUnitor := @fun a b f =>
    { hom := Quot.mk Rel (Hom₂.right_unitor f)
      inv := Quot.mk Rel (Hom₂.right_unitor_inv f)
      hom_inv_id := Quot.sound (Rel.right_unitor_hom_inv f)
      inv_hom_id := Quot.sound (Rel.right_unitor_inv_hom f) }
  whiskerLeft_comp := by
    rintro a b c f g h i ⟨η⟩ ⟨θ⟩
    exact Quot.sound (Rel.whisker_left_comp f η θ)
  id_whiskerLeft := by
    rintro a b f g ⟨η⟩
    exact Quot.sound (Rel.id_whisker_left η)
  comp_whiskerLeft := by
    rintro a b c d f g h h' ⟨η⟩
    exact Quot.sound (Rel.comp_whisker_left f g η)
  whiskerRight := @fun a b c f g η h => Quot.map (Hom₂.whisker_right h) (Rel.whisker_right f g h) η
  id_whiskerRight := @fun a b c f g => Quot.sound (Rel.id_whisker_right f g)
  comp_whiskerRight := by
    rintro a b c f g h ⟨η⟩ ⟨θ⟩ i
    exact Quot.sound (Rel.comp_whisker_right i η θ)
  whiskerRight_id := by
    rintro a b f g ⟨η⟩
    exact Quot.sound (Rel.whisker_right_id η)
  whiskerRight_comp := by
    rintro a b c d f f' ⟨η⟩ g h
    exact Quot.sound (Rel.whisker_right_comp g h η)
  whisker_assoc := by
    rintro a b c d f g g' ⟨η⟩ h
    exact Quot.sound (Rel.whisker_assoc f η h)
  whisker_exchange := by
    rintro a b c f g h i ⟨η⟩ ⟨θ⟩
    exact Quot.sound (Rel.whisker_exchange η θ)
  pentagon := @fun a b c d e f g h i => Quot.sound (Rel.pentagon f g h i)
  triangle := @fun a b c f g => Quot.sound (Rel.triangle f g)
#align category_theory.free_bicategory.bicategory CategoryTheory.FreeBicategory.bicategory

variable {a b c d : FreeBicategory B}

abbrev Hom₂.mk {f g : a ⟶ b} (η : Hom₂ f g) : f ⟶ g :=
  Quot.mk Rel η

@[simp]
theorem mk_vcomp {f g h : a ⟶ b} (η : Hom₂ f g) (θ : Hom₂ g h) :
    (η.vcomp θ).mk = (η.mk ≫ θ.mk : f ⟶ h) :=
  rfl
#align category_theory.free_bicategory.mk_vcomp CategoryTheory.FreeBicategory.mk_vcomp

@[simp]
theorem mk_whisker_left (f : a ⟶ b) {g h : b ⟶ c} (η : Hom₂ g h) :
    (Hom₂.whisker_left f η).mk = (f ◁ η.mk : f ≫ g ⟶ f ≫ h) :=
  rfl
#align category_theory.free_bicategory.mk_whisker_left CategoryTheory.FreeBicategory.mk_whisker_left

@[simp]
theorem mk_whisker_right {f g : a ⟶ b} (η : Hom₂ f g) (h : b ⟶ c) :
    (Hom₂.whisker_right h η).mk = (η.mk ▷ h : f ≫ h ⟶ g ≫ h) :=
  rfl
#align category_theory.free_bicategory.mk_whisker_right CategoryTheory.FreeBicategory.mk_whisker_right

variable (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)

-- Porting note: I can not get this to typecheck, and I don't understand why.
-- theorem id_def : Hom.id a = 𝟙 a :=
--   rfl
-- #align category_theory.free_bicategory.id_def CategoryTheory.FreeBicategory.id_def
#noalign category_theory.free_bicategory.id_def

theorem comp_def : Hom.comp f g = f ≫ g :=
  rfl
#align category_theory.free_bicategory.comp_def CategoryTheory.FreeBicategory.comp_def

@[simp]
theorem mk_id : Quot.mk _ (Hom₂.id f) = 𝟙 f :=
  rfl
#align category_theory.free_bicategory.mk_id CategoryTheory.FreeBicategory.mk_id

@[simp]
theorem mk_associator_hom : Quot.mk _ (Hom₂.associator f g h) = (α_ f g h).hom :=
  rfl
#align category_theory.free_bicategory.mk_associator_hom CategoryTheory.FreeBicategory.mk_associator_hom

@[simp]
theorem mk_associator_inv : Quot.mk _ (Hom₂.associator_inv f g h) = (α_ f g h).inv :=
  rfl
#align category_theory.free_bicategory.mk_associator_inv CategoryTheory.FreeBicategory.mk_associator_inv

@[simp]
theorem mk_left_unitor_hom : Quot.mk _ (Hom₂.left_unitor f) = (λ_ f).hom :=
  rfl
#align category_theory.free_bicategory.mk_left_unitor_hom CategoryTheory.FreeBicategory.mk_left_unitor_hom

@[simp]
theorem mk_left_unitor_inv : Quot.mk _ (Hom₂.left_unitor_inv f) = (λ_ f).inv :=
  rfl
#align category_theory.free_bicategory.mk_left_unitor_inv CategoryTheory.FreeBicategory.mk_left_unitor_inv

@[simp]
theorem mk_right_unitor_hom : Quot.mk _ (Hom₂.right_unitor f) = (ρ_ f).hom :=
  rfl
#align category_theory.free_bicategory.mk_right_unitor_hom CategoryTheory.FreeBicategory.mk_right_unitor_hom

@[simp]
theorem mk_right_unitor_inv : Quot.mk _ (Hom₂.right_unitor_inv f) = (ρ_ f).inv :=
  rfl
#align category_theory.free_bicategory.mk_right_unitor_inv CategoryTheory.FreeBicategory.mk_right_unitor_inv

/-- Canonical prefunctor from `B` to `free_bicategory B`. -/
@[simps]
def of : Prefunctor B (FreeBicategory B) where
  obj := id
  map := @fun _ _ => Hom.of
#align category_theory.free_bicategory.of CategoryTheory.FreeBicategory.of

end

section

variable {B : Type u₁} [Quiver.{v₁ + 1} B] {C : Type u₂} [CategoryStruct.{v₂} C]
variable (F : Prefunctor B C)

/-- Auxiliary definition for `lift`. -/
@[simp]
def liftHom : ∀ {a b : FreeBicategory B}, (a ⟶ b) → (F.obj a ⟶ F.obj b)
  | _, _, Hom.of f => F.map f
  | _, _, Hom.id a => 𝟙 (F.obj a)
  | _, _, Hom.comp f g => liftHom f ≫ liftHom g
#align category_theory.free_bicategory.lift_hom CategoryTheory.FreeBicategory.liftHom

@[simp]
theorem liftHom_id (a : FreeBicategory B) : liftHom F (𝟙 a) = 𝟙 (F.obj a) :=
  rfl
#align category_theory.free_bicategory.lift_hom_id CategoryTheory.FreeBicategory.liftHom_id

@[simp]
theorem liftHom_comp {a b c : FreeBicategory B} (f : a ⟶ b) (g : b ⟶ c) :
    liftHom F (f ≫ g) = liftHom F f ≫ liftHom F g :=
  rfl
#align category_theory.free_bicategory.lift_hom_comp CategoryTheory.FreeBicategory.liftHom_comp

end

section

variable {B : Type u₁} [Quiver.{v₁ + 1} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable (F : Prefunctor B C)

/-- Auxiliary definition for `lift`. -/
-- @[simp] -- Porting note: adding `@[simp]` causes a PANIC.
def liftHom₂ : ∀ {a b : FreeBicategory B} {f g : a ⟶ b}, Hom₂ f g → (liftHom F f ⟶ liftHom F g)
  | _, _, _, _, Hom₂.id _ => 𝟙 _
  | _, _, _, _, Hom₂.associator _ _ _ => (α_ _ _ _).hom
  | _, _, _, _, Hom₂.associator_inv _ _ _ => (α_ _ _ _).inv
  | _, _, _, _, Hom₂.left_unitor _ => (λ_ _).hom
  | _, _, _, _, Hom₂.left_unitor_inv _ => (λ_ _).inv
  | _, _, _, _, Hom₂.right_unitor _ => (ρ_ _).hom
  | _, _, _, _, Hom₂.right_unitor_inv _ => (ρ_ _).inv
  | _, _, _, _, Hom₂.vcomp η θ => liftHom₂ η ≫ liftHom₂ θ
  | _, _, _, _, Hom₂.whisker_left f η => liftHom F f ◁ liftHom₂ η
  | _, _, _, _, Hom₂.whisker_right h η => liftHom₂ η ▷ liftHom F h
#align category_theory.free_bicategory.lift_hom₂ CategoryTheory.FreeBicategory.liftHom₂

attribute [local simp] whisker_exchange

theorem liftHom₂_congr {a b : FreeBicategory B} {f g : a ⟶ b} {η θ : Hom₂ f g} (H : Rel η θ) :
    liftHom₂ F η = liftHom₂ F θ := by induction H <;> (dsimp [liftHom₂]; aesop_cat)
#align category_theory.free_bicategory.lift_hom₂_congr CategoryTheory.FreeBicategory.liftHom₂_congr

/-- A prefunctor from a quiver `B` to a bicategory `C` can be lifted to a pseudofunctor from
`free_bicategory B` to `C`.
-/
@[simps]
def lift : Pseudofunctor (FreeBicategory B) C where
  obj := F.obj
  map := liftHom F
  mapId a := Iso.refl _
  mapComp f g := Iso.refl _
  map₂ := Quot.lift (liftHom₂ F) fun η θ H => liftHom₂_congr F H
  -- Porting note: We'd really prefer not to be doing this by hand.
  -- in mathlib3 `tidy` did these inductions for us.
  map₂_comp := by
    intros a b f g h η θ
    apply Quot.rec _ _ η
    · intro η
      apply Quot.rec _ _ θ
      · intro θ; rfl
      · intros; rfl
    · intros; rfl
  -- Porting note: still borked from here. The infoview doesn't update properly for me.
  map₂_whisker_left := by
    intro a b c f g h η
    apply Quot.rec _ _ η
    · intros; aesop_cat
    · intros; rfl
  map₂_whisker_right := by intro _ _ _ _ _ η h; dsimp; apply Quot.rec _ _ η <;> aesop_cat
#align category_theory.free_bicategory.lift CategoryTheory.FreeBicategory.lift

end

end FreeBicategory

end CategoryTheory
