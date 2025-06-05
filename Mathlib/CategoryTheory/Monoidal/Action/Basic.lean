/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.Trifunctor

/-!

# Left actions from a monoidal category on a category

Given a monoidal category `C`, and a category `D`, we define a left action of
`C` on `D` as the data of an object `c ⊙ d` of `D` for every
`c : C` and `d : D`, as well as the data required to turn `- ⊙ -` into
a bifunctor, along with structure natural isomorphisms
`(- ⊗ -) ⊙ - ≅ - ⊙ - ⊙ -` and `𝟙_ C ⊙ - ≅ -`, subject to coherence conditions.


## References
* [Janelidze, G, and Kelly, G.M., *A note on actions of a monoidal category*][JanelidzeKelly2001]

## TODOs/Projects
* Equivalence between actions of `C` on `D` and pseudofunctors from the
  classifying bicategory of `C` to `Cat`.
* Functors that respects left actions.
* Actions as monoidal functors C ⥤ (D ⥤ D).
* Action of `(C ⥤ C)` on `C`.
* Modules in `D` over a monoid object in `C`. Equivalence with `Mod_` when
  `D` is `C`.
* Given a monad `M` on `C`, equivalence between `Algebra M`, and modules in `C`
  on `M.toMon : Mon_ (C ⥤ C)`.
* Canonical action of `Type u` on `u`-small cocomplete categories via the
  copower.

-/

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category C] [Category D]
/-- A class that carries the non-Prop data required to define a left action of a
monoidal category `C` on a category `D`, to set up notations. -/
class MonoidalLeftActionStruct [MonoidalCategoryStruct C] where
  /-- The left action on objects. This is denoted `c ⊙ d`. -/
  actionObj : C → D → D
  /-- The left action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.map f).obj d`. This is denoted `f ⊵ d` -/
  actionHomLeft {c c' : C} (f : c ⟶ c') (d : D) :
    actionObj c d ⟶ actionObj c' d
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.obj c).map f`. This is denoted `c ⊴ f`. -/
  actionHomRight (c : C) {d d' : D} (f : d ⟶ d') :
    actionObj c d ⟶ actionObj c d'
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    actionObj c d ⟶ actionObj c' d' := actionHomLeft f d ≫ actionHomRight c' g
  /-- The structural isomorphism `(c ⊗ c') ⊙ d ≅ c ⊙ (c' ⊙ d)`. -/
  actionAssocIso (c c' : C) (d : D) :
    actionObj (c ⊗ c') d ≅ actionObj c (actionObj c' d)
  /-- The structural isomorphism between `𝟙_ C ⊙ d` and `d`. -/
  actionUnitIso (d : D) : actionObj (𝟙_ C) d ≅ d

namespace MonoidalLeftAction

export MonoidalLeftActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`.
so that `c ⊗ c' ⊙ d` means `(c ⊗ c') ⊙ d`. -/
scoped infixr:70 " ⊙ " => MonoidalLeftActionStruct.actionObj

scoped infixr:81 " ⊵ " => MonoidalLeftActionStruct.actionHomLeft

scoped infixr:81 " ⊴ " => MonoidalLeftActionStruct.actionHomRight

scoped infixr:70 " ⊙ " => MonoidalLeftActionStruct.actionHom

scoped notation "σ_ " => MonoidalLeftActionStruct.actionAssocIso

scoped notation "υ_ " => MonoidalLeftActionStruct.actionUnitIso

end MonoidalLeftAction

open scoped MonoidalLeftAction in

/-- A `MonoidalLeftAction C D` is is the data of:
- For every object `c : C` and `d : D`, an object `c ⊙ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ⊵ d : c ⊙ d ⟶ c' ⊙ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ⊴ f : c ⊙ d ⟶ c ⊙ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ⊙ f' : c ⊙ d ⟶ c' ⊙ d'`.
- A structure isomorphism `σ_ c c' d : c ⊗ c' ⊙ d ≅ c ⊙ c' ⊙ d`.
- A structure isomorphism `υ_ d : (𝟙_ C) ⊙ d ≅ d`.
Furthermore, we require identities that turn `- ⊙ -` into a bifunctor,
ensure naturality of `σ_` and `υ_`, and ensure compatibilies with
the associator and unitor isomorphisms in `C`. -/
class MonoidalLeftAction [MonoidalCategory C] extends MonoidalLeftActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
      f ⊙ g = f ⊵ d ≫ c' ⊴ g := by
    aesop_cat

  actionHomRight_id (c : C) (d : D) : c ⊴ 𝟙 d = 𝟙 (c ⊙ d) := by aesop_cat
  id_actionHomLeft (c : C) (d : D) : 𝟙 c ⊵ d = 𝟙 (c ⊙ d) := by aesop_cat

  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'')
      (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
      (f₁ ≫ f₂) ⊙ (g₁ ≫ g₂) = (f₁ ⊙ g₁) ≫ (f₂ ⊙ g₂) := by
    aesop_cat

  actionAssocIso_naturality
      {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
      ((f ⊗ g) ⊙ h) ≫ (σ_ c₂ c₄ d₂).hom = (σ_ c₁ c₃ d₁).hom ≫ (f ⊙ g ⊙ h) := by
    aesop_cat

  actionUnitIso_naturality {d d' : D} (f : d ⟶ d') :
      (υ_ d).hom ≫ f = (𝟙_ C) ⊴ f ≫ (υ_ d').hom := by
    aesop_cat

  whiskerLeft_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
      (c ◁ f) ⊵ d = (σ_ _ _ _).hom ≫ c ⊴ (f ⊵ d) ≫ (σ_ _ _ _).inv := by
    aesop_cat

  whiskerRight_actionHomLeft {c c' : C} (c'' : C) (f : c ⟶ c') (d : D) :
      (f ▷ c'') ⊵ d = (σ_ c c'' d).hom ≫
        f ⊵ (c'' ⊙ d : D) ≫ (σ_ c' c'' d).inv := by
    aesop_cat

  associator_actionHom (c₁ c₂ c₃ : C) (d : D) :
      (α_ c₁ c₂ c₃).hom ⊵ d ≫ (σ_ c₁ (c₂ ⊗ c₃) d).hom ≫
        c₁ ⊴ (σ_ c₂ c₃ d).hom =
      (σ_ (c₁ ⊗ c₂ : C) c₃ d).hom ≫ (σ_ c₁ c₂ (c₃ ⊙ d)).hom := by
    aesop_cat

  leftUnitor_actionHom (c : C) (d : D) :
      (λ_ c).hom ⊵ d = (σ_ _ _ _).hom ≫ (υ_ _).hom := by
    aesop_cat

  rightUnitor_actionHom (c : C) (d : D) :
      (ρ_ c).hom ⊵ d = (σ_ _ _ _).hom ≫ c ⊴ (υ_ _).hom := by
    aesop_cat

attribute [reassoc] MonoidalLeftAction.actionHom_def
attribute [reassoc, simp] MonoidalLeftAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalLeftAction.actionHomRight_id
attribute [simp, reassoc] MonoidalLeftAction.actionHom_comp
attribute [reassoc] MonoidalLeftAction.actionAssocIso_naturality
attribute [reassoc] MonoidalLeftAction.actionUnitIso_naturality
attribute [reassoc (attr := simp)] MonoidalLeftAction.associator_actionHom
attribute [reassoc (attr := simp)] MonoidalLeftAction.leftUnitor_actionHom
attribute [reassoc (attr := simp)] MonoidalLeftAction.rightUnitor_actionHom

/-- A monoidal category acts on itself through the tensor product. -/
instance [MonoidalCategory C] : MonoidalLeftAction C C where
  actionObj x y := x ⊗ y
  actionHom f g := f ⊗ g
  actionUnitIso x := λ_ x
  actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

namespace MonoidalLeftAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalLeftAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCateogry`.

@[simp]
lemma id_actionHom (c : C) {d d' : D} (f : d ⟶ d') :
    (𝟙 c) ⊙ f = c ⊴ f := by
  simp [actionHom_def]

@[simp]
lemma actionHom_id {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊙ (𝟙 d) = f ⊵ d := by
  simp [actionHom_def]

@[reassoc, simp]
theorem actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ (f ≫ g) = w ⊴ f ≫ w ⊴ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    (𝟙_ C) ⊴ f = (υ_ x).hom ≫ f ≫ (υ_ y).inv := by
  rw [← Category.assoc, actionUnitIso_naturality]
  simp

@[reassoc, simp]
theorem tensor_actionHomRight (x y : C) {z z' : D} (f : z ⟶ z') :
    ((x ⊗ y) ⊴ f) = (σ_ x y z).hom ≫ x ⊴ y ⊴ f ≫ (σ_ x y z').inv := by
  simp only [← id_actionHom, ← actionHom_id]
  rw [← Category.assoc, ← actionAssocIso_naturality]
  simp

@[reassoc, simp]
theorem comp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) :
    (f ≫ g) ⊵ z = f ⊵ z ≫ g ⊵ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
theorem actionHomLeft_action {x x' : C} (f : x ⟶ x') (y : C) (z : D) :
    f ⊵ (y ⊙ z) = (σ_ x y z).inv ≫ (f ▷ y) ⊵ z ≫ (σ_ x' y z).hom := by
  simp only [← id_actionHom, ← tensorHom_id, ← actionHom_id]
  rw [actionAssocIso_naturality]
  simp [actionHom_id]

@[reassoc, simp]
theorem action_assoc (x : C) {y y' : C} (f : y ⟶ y') (z : D) :
    (x ◁ f) ⊵ z = (σ_ x y z).hom ≫ x ⊴ f ⊵ z ≫ (σ_ x y' z).inv := by
  simp only [← id_actionHom, ← tensorHom_id, ← actionHom_id]
  rw [← Category.assoc, ← actionAssocIso_naturality]
  simp

@[reassoc]
theorem action_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ g ≫ f ⊵ z = f ⊵ y ≫ x ⊴ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
theorem actionHom_def' {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ g = x₁ ⊴ g ≫ f ⊵ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc (attr := simp)]
theorem actionHomRight_hom_inv (x : C) {y z : D} (f : y ≅ z) :
    (x ⊴ f.hom ≫ x ⊴ f.inv) = 𝟙 (x ⊙ y : D) := by
  rw [← actionHomRight_comp, Iso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem hom_inv_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.hom ⊵ z ≫ f.inv ⊵ z = 𝟙 (x ⊙ z) := by
  rw [← comp_actionHomLeft, Iso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_inv_hom (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ f.inv ≫ x ⊴ f.hom = 𝟙 (x ⊙ z) := by
  rw [← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem inv_hom_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.inv ⊵ z ≫ f.hom ⊵ z = 𝟙 (y ⊙ z) := by
  rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ f ≫ x ⊴ inv f = 𝟙 (x ⊙ y) := by
  rw [← actionHomRight_comp, IsIso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    f ⊵ z ≫ inv f ⊵ z = 𝟙 (x ⊙ z) := by
  rw [← comp_actionHomLeft, IsIso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_inv_hom' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ inv f ≫ x ⊴ f = 𝟙 (x ⊙ z) := by
  rw [← actionHomRight_comp, IsIso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem inv_hom_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv f ⊵ z ≫ f ⊵ z = 𝟙 (y ⊙ z) := by
  rw [← comp_actionHomLeft, IsIso.inv_hom_id, id_actionHomLeft]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := x ⊙ y
      map f := x ⊴ f }
  map f :=
    { app y := f ⊵ y
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ c ⊙ d` as a functor. -/
@[simps!]
abbrev actionLeft (c : C) : D ⥤ D := curriedAction C D|>.obj c

variable {D} in
/-- Bundle `c ↦ c ⊙ d` as a functor. -/
@[simps!]
abbrev actionRight (d : D) : C ⥤ D := curriedAction C D|>.flip.obj d

/-- Bundle `σ_ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
def actionAssocNatIso :
    (Functor.postcompose₂.obj (curriedAction C D)|>.obj
      (curriedTensor C)) ≅
    bifunctorComp₂₃Functor|>.obj (curriedAction C D)|>.obj
      (curriedAction C D) :=
  NatIso.ofComponents fun _ ↦
    NatIso.ofComponents fun _ ↦
     NatIso.ofComponents fun _ ↦ σ_ _ _ _

/-- Bundle `υ_ _` as an isomorphism of functors. -/
@[simps!]
def actionUnitNatIso :
    actionLeft D (𝟙_ C) ≅ 𝟭 D :=
  NatIso.ofComponents (fun _ ↦ υ_ _)

end

end MonoidalLeftAction

end CategoryTheory.MonoidalCategory
