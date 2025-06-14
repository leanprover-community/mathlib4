/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.Trifunctor

/-!

# Actions from a monoidal category on a category

Given a monoidal category `C`, and a category `D`, we define a left action of
`C` on `D` as the data of an object `c ⊙ₗ d` of `D` for every
`c : C` and `d : D`, as well as the data required to turn `- ⊙ₗ -` into
a bifunctor, along with structure natural isomorphisms
`(- ⊗ -) ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -` and `𝟙_ C ⊙ₗ - ≅ -`, subject to coherence conditions.

We also define right actions, for these, the notation for the action of `c`
on `d` is `d ᵣ⊙ c`, and the structure isomorphisms are of the form
`- ᵣ⊙ (- ⊗ -) ≅ (- ᵣ⊙ -) ᵣ⊙ -` and `- ⊙ₗ 𝟙_ C ≅ -`.


## References
* [Janelidze, G, and Kelly, G.M., *A note on actions of a monoidal category*][JanelidzeKelly2001]

## TODOs/Projects
* Equivalence between actions of `C` on `D` and pseudofunctors from the
  classifying bicategory of `C` to `Cat`.
* Functors that respects left/right actions.
* Left actions of `C` as right `Cᴹᵒᵖ`-actions, and vice-versa.
* Left/Right Modules in `D` over a monoid object in `C`.
  Equivalence with `Mod_` when `D` is `C`. Bimodules objects.
* Given a monad `M` on `C`, equivalence between `Algebra M`, and modules in `C`
  on `M.toMon : Mon_ (C ⥤ C)`.
* Canonical left action of `Type u` on `u`-small cocomplete categories via the
  copower.

-/

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category C] [Category D]
/-- A class that carries the non-Prop data required to define a left action of a
monoidal category `C` on a category `D`, to set up notations. -/
class MonoidalLeftActionStruct [MonoidalCategoryStruct C] where
  /-- The left action on objects. This is denoted `c ⊙ₗ d`. -/
  actionObj : C → D → D
  /-- The left action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.map f).obj d`. This is denoted `f ⊵ₗ d` -/
  actionHomLeft {c c' : C} (f : c ⟶ c') (d : D) :
    actionObj c d ⟶ actionObj c' d
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.obj c).map f`. This is denoted `c ⊴ₗ f`. -/
  actionHomRight (c : C) {d d' : D} (f : d ⟶ d') :
    actionObj c d ⟶ actionObj c d'
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    actionObj c d ⟶ actionObj c' d' := actionHomLeft f d ≫ actionHomRight c' g
  /-- The structural isomorphism `(c ⊗ c') ⊙ₗ d ≅ c ⊙ₗ (c' ⊙ₗ d)`. -/
  actionAssocIso (c c' : C) (d : D) :
    actionObj (c ⊗ c') d ≅ actionObj c (actionObj c' d)
  /-- The structural isomorphism between `𝟙_ C ⊙ₗ d` and `d`. -/
  actionUnitIso (d : D) : actionObj (𝟙_ C) d ≅ d

namespace MonoidalLeftAction

export MonoidalLeftActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`. -/
scoped infixr:70 " ⊙ₗ " => MonoidalLeftActionStruct.actionObj

/-- Notation for `actionHomLeft`, the action of `C` on morphisms in `D`. -/
scoped infixr:81 " ⊵ₗ " => MonoidalLeftActionStruct.actionHomLeft

/-- Notation for `actionHomRight`, the action of morphism in `C` on `D`. -/
scoped infixr:81 " ⊴ₗ " => MonoidalLeftActionStruct.actionHomRight

/-- Notation for `actionHom`, the bifunctorial action of morphisms in `C` and
`D` on `- ⊙ₗ -`. -/
scoped infixr:70 " ⊙ₗ " => MonoidalLeftActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ⊗ - ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -`. -/
scoped notation "σ_ₗ " => MonoidalLeftActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`. -/
scoped notation "υ_ₗ " => MonoidalLeftActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`,
allowing one to specify the acting category. -/
scoped notation "υ_ₗ["J"]" => MonoidalLeftActionStruct.actionUnitIso (C := J)

end MonoidalLeftAction

open scoped MonoidalLeftAction in

/-- A `MonoidalLeftAction C D` is is the data of:
- For every object `c : C` and `d : D`, an object `c ⊙ₗ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ⊵ₗ d : c ⊙ₗ d ⟶ c' ⊙ₗ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ⊴ₗ f : c ⊙ₗ d ⟶ c ⊙ₗ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ⊙ₗ f' : c ⊙ₗ d ⟶ c' ⊙ₗ d'`.
- A structure isomorphism `σ_ₗ c c' d : c ⊗ c' ⊙ₗ d ≅ c ⊙ₗ c' ⊙ₗ d`.
- A structure isomorphism `υ_ₗ d : (𝟙_ C) ⊙ₗ d ≅ d`.
Furthermore, we require identities that turn `- ⊙ₗ -` into a bifunctor,
ensure naturality of `σ_ₗ` and `υ_ₗ`, and ensure compatibilies with
the associator and unitor isomorphisms in `C`. -/
class MonoidalLeftAction [MonoidalCategory C] extends
    MonoidalLeftActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
      f ⊙ₗ g = f ⊵ₗ d ≫ c' ⊴ₗ g := by
    aesop_cat

  actionHomRight_id (c : C) (d : D) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d) := by aesop_cat
  id_actionHomLeft (c : C) (d : D) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d) := by aesop_cat

  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'')
      (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
      (f₁ ≫ f₂) ⊙ₗ (g₁ ≫ g₂) = (f₁ ⊙ₗ g₁) ≫ (f₂ ⊙ₗ g₂) := by
    aesop_cat

  actionAssocIso_naturality
      {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
      ((f ⊗ g) ⊙ₗ h) ≫ (σ_ₗ c₂ c₄ d₂).hom =
        (σ_ₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗ g ⊙ₗ h) := by
    aesop_cat

  actionUnitIso_naturality {d d' : D} (f : d ⟶ d') :
      (υ_ₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (υ_ₗ d').hom := by
    aesop_cat

  whiskerLeft_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
      (c ◁ f) ⊵ₗ d = (σ_ₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (σ_ₗ _ _ _).inv := by
    aesop_cat

  whiskerRight_actionHomLeft {c c' : C} (c'' : C) (f : c ⟶ c') (d : D) :
      (f ▷ c'') ⊵ₗ d = (σ_ₗ c c'' d).hom ≫
        f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (σ_ₗ c' c'' d).inv := by
    aesop_cat

  associator_actionHom (c₁ c₂ c₃ : C) (d : D) :
      (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (σ_ₗ c₁ (c₂ ⊗ c₃) d).hom ≫
        c₁ ⊴ₗ (σ_ₗ c₂ c₃ d).hom =
      (σ_ₗ (c₁ ⊗ c₂ : C) c₃ d).hom ≫ (σ_ₗ c₁ c₂ (c₃ ⊙ₗ d)).hom := by
    aesop_cat

  leftUnitor_actionHom (c : C) (d : D) :
      (λ_ c).hom ⊵ₗ d = (σ_ₗ _ _ _).hom ≫ (υ_ₗ _).hom := by
    aesop_cat

  rightUnitor_actionHom (c : C) (d : D) :
      (ρ_ c).hom ⊵ₗ d = (σ_ₗ _ _ _).hom ≫ c ⊴ₗ (υ_ₗ _).hom := by
    aesop_cat

attribute [reassoc] MonoidalLeftAction.actionHom_def
attribute [reassoc, simp] MonoidalLeftAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalLeftAction.actionHomRight_id
attribute [reassoc, simp] MonoidalLeftAction.whiskerLeft_actionHomLeft
attribute [simp, reassoc] MonoidalLeftAction.actionHom_comp
attribute [reassoc] MonoidalLeftAction.actionAssocIso_naturality
attribute [reassoc] MonoidalLeftAction.actionUnitIso_naturality
attribute [reassoc (attr := simp)] MonoidalLeftAction.associator_actionHom
attribute [simp, reassoc] MonoidalLeftAction.leftUnitor_actionHom
attribute [simp, reassoc] MonoidalLeftAction.rightUnitor_actionHom

/--
A monoidal category acts on itself on the left through the tensor product.
-/
@[simps!]
instance selfLeftAction [MonoidalCategory C] : MonoidalLeftAction C C where
  actionObj x y := x ⊗ y
  actionHom f g := f ⊗ g
  actionUnitIso x := λ_ x
  actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

@[deprecated (since := "2025-06-13")] alias selfAction := selfLeftAction

namespace MonoidalLeftAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalLeftAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCateogry`.

@[simp]
lemma id_actionHom (c : C) {d d' : D} (f : d ⟶ d') :
    (𝟙 c) ⊙ₗ f = c ⊴ₗ f := by
  simp [actionHom_def]

@[simp]
lemma actionHom_id {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊙ₗ (𝟙 d) = f ⊵ₗ d := by
  simp [actionHom_def]

@[reassoc, simp]
theorem actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ₗ (f ≫ g) = w ⊴ₗ f ≫ w ⊴ₗ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    (𝟙_ C) ⊴ₗ f = (υ_ₗ x).hom ≫ f ≫ (υ_ₗ y).inv := by
  rw [← Category.assoc, actionUnitIso_naturality]
  simp

@[reassoc, simp]
theorem tensor_actionHomRight (x y : C) {z z' : D} (f : z ⟶ z') :
    (x ⊗ y) ⊴ₗ f = (σ_ₗ x y z).hom ≫ x ⊴ₗ y ⊴ₗ f ≫ (σ_ₗ x y z').inv := by
  simp only [← id_actionHom, ← actionHom_id]
  rw [← Category.assoc, ← actionAssocIso_naturality]
  simp

@[reassoc, simp]
theorem comp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) :
    (f ≫ g) ⊵ₗ z = f ⊵ₗ z ≫ g ⊵ₗ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
theorem actionHomLeft_action {x x' : C} (f : x ⟶ x') (y : C) (z : D) :
    f ⊵ₗ (y ⊙ₗ z) = (σ_ₗ x y z).inv ≫ (f ▷ y) ⊵ₗ z ≫ (σ_ₗ x' y z).hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
theorem action_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ₗ g ≫ f ⊵ₗ z = f ⊵ₗ y ≫ x ⊴ₗ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
theorem actionHom_def' {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ₗ g = x₁ ⊴ₗ g ≫ f ⊵ₗ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc (attr := simp)]
theorem actionHomRight_hom_inv (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ₗ f.hom ≫ x ⊴ₗ f.inv = 𝟙 (x ⊙ₗ y : D) := by
  rw [← actionHomRight_comp, Iso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem hom_inv_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.hom ⊵ₗ z ≫ f.inv ⊵ₗ z = 𝟙 (x ⊙ₗ z) := by
  rw [← comp_actionHomLeft, Iso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_inv_hom (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ₗ f.inv ≫ x ⊴ₗ f.hom = 𝟙 (x ⊙ₗ z) := by
  rw [← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem inv_hom_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.inv ⊵ₗ z ≫ f.hom ⊵ₗ z = 𝟙 (y ⊙ₗ z) := by
  rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ₗ f ≫ x ⊴ₗ inv f = 𝟙 (x ⊙ₗ y) := by
  rw [← actionHomRight_comp, IsIso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    f ⊵ₗ z ≫ inv f ⊵ₗ z = 𝟙 (x ⊙ₗ z) := by
  rw [← comp_actionHomLeft, IsIso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_inv_hom' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ₗ inv f ≫ x ⊴ₗ f = 𝟙 (x ⊙ₗ z) := by
  rw [← actionHomRight_comp, IsIso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem inv_hom_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv f ⊵ₗ z ≫ f ⊵ₗ z = 𝟙 (y ⊙ₗ z) := by
  rw [← comp_actionHomLeft, IsIso.inv_hom_id, id_actionHomLeft]

instance isIso_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    IsIso (x ⊴ₗ f) :=
  ⟨x ⊴ₗ inv f, by simp⟩

instance isIso_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    IsIso (f ⊵ₗ z) :=
  ⟨inv f ⊵ₗ z, by simp⟩

instance isIso_actionHom {x y : C} {x' y' : D}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    IsIso (f ⊙ₗ g) :=
  ⟨(inv f) ⊙ₗ (inv g), by simp [← actionHom_comp]⟩

@[simp]
lemma inv_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv (f ⊵ₗ z) = inv f ⊵ₗ z :=
  IsIso.inv_eq_of_hom_inv_id <| hom_inv_actionHomLeft' f z

@[simp]
lemma inv_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    inv (x ⊴ₗ f) = x ⊴ₗ inv f :=
  IsIso.inv_eq_of_hom_inv_id <| actionHomRight_hom_inv' x f

@[simp]
lemma inv_actionHom {x y : C} {x' y' : D}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    inv (f ⊙ₗ g) = (inv f) ⊙ₗ (inv g) :=
  IsIso.inv_eq_of_hom_inv_id <| by simp [← actionHom_comp]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := x ⊙ₗ y
      map f := x ⊴ₗ f }
  map f :=
    { app y := f ⊵ₗ y
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ c ⊙ₗ d` as a functor. -/
@[simps!]
abbrev actionLeft (c : C) : D ⥤ D := curriedAction C D|>.obj c

variable {D} in
/-- Bundle `c ↦ c ⊙ₗ d` as a functor. -/
@[simps!]
abbrev actionRight (d : D) : C ⥤ D := curriedAction C D|>.flip.obj d

/-- Bundle `σ_ₗ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
def actionAssocNatIso :
    (Functor.postcompose₂.obj (curriedAction C D)|>.obj
      (curriedTensor C)) ≅
    bifunctorComp₂₃Functor|>.obj (curriedAction C D)|>.obj
      (curriedAction C D) :=
  NatIso.ofComponents fun _ ↦
    NatIso.ofComponents fun _ ↦
     NatIso.ofComponents fun _ ↦ σ_ₗ _ _ _

/-- Bundle `υ_ₗ _` as an isomorphism of functors. -/
@[simps!]
def actionUnitNatIso : actionLeft D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (υ_ₗ ·)

end

end MonoidalLeftAction

/-- A class that carries the non-Prop data required to define a right action of
a monoidal category `C` on a category `D`, to set up notations. -/
class MonoidalRightActionStruct [MonoidalCategoryStruct C] where
  /-- The right action on objects. This is denoted `d ᵣ⊙ c`. -/
  actionObj : D → C → D
  /-- The right action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.map f).obj d`. This is denoted `d ᵣ⊴ f` -/
  actionHomRight (d : D) {c c' : C} (f : c ⟶ c') :
    actionObj d c ⟶ actionObj d c'
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.obj c).map f`. This is denoted `f ᵣ⊵ c`. -/
  actionHomLeft {d d' : D} (f : d ⟶ d') (c : C):
    actionObj d c ⟶ actionObj d' c
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') :
    actionObj d c ⟶ actionObj d' c' := actionHomLeft f c ≫ actionHomRight d' g
  /-- The structural isomorphism `d ᵣ⊙ (c ⊗ c') ≅ (d ᵣ⊙ c) ᵣ⊙ c'`. -/
  actionAssocIso (d : D) (c c' : C) :
    actionObj d (c ⊗ c') ≅ actionObj (actionObj d c) c'
  /-- The structural isomorphism between `d ᵣ⊙ 𝟙_ C` and `d`. -/
  actionUnitIso (d : D) : actionObj d (𝟙_ C) ≅ d

namespace MonoidalRightAction

export MonoidalRightActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`. -/
scoped infixr:70 " ᵣ⊙ " => MonoidalRightActionStruct.actionObj

/-- Notation for `actionHomLeft`, the action of `D` on morphisms in `C`. -/
scoped infixr:81 " ᵣ⊵ " => MonoidalRightActionStruct.actionHomLeft

/-- Notation for `actionHomRight`, the action of morphism in `D` on `C`. -/
scoped infixr:81 " ᵣ⊴ " => MonoidalRightActionStruct.actionHomRight

/-- Notation for `actionHom`, the bifunctorial action of morphisms in `C` and
`D` on `- ⊙ -`. -/
scoped infixr:70 " ᵣ⊙ " => MonoidalRightActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ᵣ⊙ (- ⊗ -) ≅ (- ᵣ⊙ -) ᵣ⊙ -`. -/
scoped notation "ᵣσ_ " => MonoidalRightActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `- ᵣ⊙ 𝟙_ C  ≅ -`. -/
scoped notation "ᵣυ_ " => MonoidalRightActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `- ᵣ⊙ 𝟙_ C  ≅ -`,
allowing one to specify the acting category. -/
scoped notation "ᵣυ_["J"]" => MonoidalRightActionStruct.actionUnitIso (C := J)

end MonoidalRightAction

open scoped MonoidalRightAction in

/-- A `MonoidalRightAction C D` is is the data of:
- For every object `c : C` and `d : D`, an object `c ᵣ⊙ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ᵣ⊵ d : c ᵣ⊙ d ⟶ c' ᵣ⊙ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ᵣ⊴ f : c ᵣ⊙ d ⟶ c ᵣ⊙ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ᵣ⊙ f' : c ᵣ⊙ d ⟶ c' ᵣ⊙ d'`.
- A structure isomorphism `ᵣσ_ c c' d : c ⊗ c' ᵣ⊙ d ≅ c ᵣ⊙ c' ᵣ⊙ d`.
- A structure isomorphism `ᵣυ_ d : (𝟙_ C) ᵣ⊙ d ≅ d`.
Furthermore, we require identities that turn `- ᵣ⊙ -` into a bifunctor,
ensure naturality of `ᵣσ_` and `ᵣυ_`, and ensure compatibilies with
the associator and unitor isomorphisms in `C`. -/
class MonoidalRightAction [MonoidalCategory C] extends
    MonoidalRightActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') :
      f ᵣ⊙ g = f ᵣ⊵ c ≫ d' ᵣ⊴ g := by
    aesop_cat

  actionHomRight_id (c : C) (d : D) : d ᵣ⊴ 𝟙 c = 𝟙 (d ᵣ⊙ c) := by aesop_cat
  id_actionHomLeft (c : C) (d : D) : 𝟙 d ᵣ⊵ c = 𝟙 (d ᵣ⊙ c) := by aesop_cat

  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : d ⟶ d') (f₂ : d' ⟶ d'')
      (g₁ : c ⟶ c') (g₂ : c' ⟶ c'') :
      (f₁ ≫ f₂) ᵣ⊙ (g₁ ≫ g₂) = (f₁ ᵣ⊙ g₁) ≫ (f₂ ᵣ⊙ g₂) := by
    aesop_cat

  actionAssocIso_naturality
      {d₁ d₂ : D} {c₁ c₂ c₃ c₄: C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄) :
      (f ᵣ⊙ g ⊗ h) ≫ (ᵣσ_ d₂ c₂ c₄).hom =
        (ᵣσ_ d₁ c₁ c₃).hom ≫ ((f ᵣ⊙ g) ᵣ⊙ h) := by
    aesop_cat

  actionUnitIso_naturality {d d' : D} (f : d ⟶ d') :
      (ᵣυ_ d).hom ≫ f = f ᵣ⊵ (𝟙_ C) ≫ (ᵣυ_ d').hom := by
    aesop_cat

  actionHomRight_whiskerRight {c' c'' : C} (f : c' ⟶ c'') (c : C) (d : D) :
     d ᵣ⊴ (f ▷ c) = (ᵣσ_ _ _ _).hom ≫ ((d ᵣ⊴ f) ᵣ⊵ c) ≫ (ᵣσ_ _ _ _).inv := by
    aesop_cat

  whiskerRight_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
     d ᵣ⊴ (c ◁ f) = (ᵣσ_ d c c').hom ≫ (d ᵣ⊙ c) ᵣ⊴ f ≫ (ᵣσ_ d c c'').inv := by
    aesop_cat

  actionHom_associator (c₁ c₂ c₃ : C) (d : D) :
      d ᵣ⊴ (α_ c₁ c₂ c₃).hom ≫ (ᵣσ_ d c₁ (c₂ ⊗ c₃)).hom ≫
        (ᵣσ_ (d ᵣ⊙ c₁ : D) c₂ c₃).hom =
      (ᵣσ_ d (c₁ ⊗ c₂ : C) c₃).hom ≫ (ᵣσ_ d c₁ c₂).hom ᵣ⊵ c₃ := by
    aesop_cat

  actionHom_leftUnitor (c : C) (d : D) :
      d ᵣ⊴ (λ_ c).hom = (ᵣσ_ _ _ _).hom ≫ (ᵣυ_ _).hom ᵣ⊵ c := by
    aesop_cat

  actionHom_rightUnitor (c : C) (d : D) :
      d ᵣ⊴ (ρ_ c).hom = (ᵣσ_ _ _ _).hom ≫ (ᵣυ_ _).hom := by
    aesop_cat

attribute [reassoc] MonoidalRightAction.actionHom_def
attribute [reassoc, simp] MonoidalRightAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalRightAction.actionHomRight_id
attribute [reassoc, simp] MonoidalRightAction.actionHomRight_whiskerRight
attribute [simp, reassoc] MonoidalRightAction.actionHom_comp
attribute [reassoc] MonoidalRightAction.actionAssocIso_naturality
attribute [reassoc] MonoidalRightAction.actionUnitIso_naturality
attribute [reassoc (attr := simp)] MonoidalRightAction.actionHom_associator
attribute [simp, reassoc] MonoidalRightAction.actionHom_leftUnitor
attribute [simp, reassoc] MonoidalRightAction.actionHom_rightUnitor

/-- A monoidal category acts on itself through the tensor product. -/
@[simps!]
instance selRightfAction [MonoidalCategory C] : MonoidalRightAction C C where
  actionObj x y := x ⊗ y
  actionHom f g := f ⊗ g
  actionUnitIso x := ρ_ x
  actionAssocIso x y z := α_ x y z|>.symm
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

namespace MonoidalRightAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalRightAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCateogry`.

@[simp]
lemma actionHom_id {d d' : D} (f : d ⟶ d') (c : C):
    f ᵣ⊙ (𝟙 c) = f ᵣ⊵ c := by
  simp [actionHom_def]

@[simp]
lemma id_actionHom  (d : D) {c c' : C} (f : c ⟶ c'):
    (𝟙 d) ᵣ⊙ f = d ᵣ⊴ f := by
  simp [actionHom_def]

@[reassoc, simp]
theorem actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    w ᵣ⊴ (f ≫ g) = w ᵣ⊴ f ≫ w ᵣ⊴ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    f ᵣ⊵ (𝟙_ C) = (ᵣυ_ x).hom ≫ f ≫ (ᵣυ_ y).inv := by
  rw [← Category.assoc, actionUnitIso_naturality]
  simp

@[reassoc, simp]
theorem actionHomLeft_tensor  {z z' : D} (f : z ⟶ z') (x y : C):
    (f ᵣ⊵ (x ⊗ y)) = (ᵣσ_ z x y).hom ≫ (f ᵣ⊵ x) ᵣ⊵ y ≫ (ᵣσ_ z' x y).inv := by
  simp only [← id_actionHom, ← actionHom_id]
  rw [← Category.assoc, ← actionAssocIso_naturality]
  simp

@[reassoc, simp]
theorem comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) :
    (f ≫ g) ᵣ⊵ z = f ᵣ⊵ z ≫ g ᵣ⊵ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
theorem action_actionHomRight (y : D) (z : C) {x x' : C} (f : x ⟶ x') :
    (y ᵣ⊙ z) ᵣ⊴ f = (ᵣσ_ y z x).inv ≫ y ᵣ⊴ (z ◁ f) ≫ (ᵣσ_ y z x').hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
theorem action_exchange {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z) :
    w ᵣ⊴ g ≫ f ᵣ⊵ z = f ᵣ⊵ y ≫ x ᵣ⊴ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
theorem actionHom_def' {x₁ y₁ : D} {x₂ y₂ : C} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ᵣ⊙ g = x₁ ᵣ⊴ g ≫ f ᵣ⊵ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc (attr := simp)]
theorem actionHomRight_hom_inv (x : D) {y z : C} (f : y ≅ z) :
    x ᵣ⊴ f.hom ≫ x ᵣ⊴ f.inv = 𝟙 (x ᵣ⊙ y : D) := by
  rw [← actionHomRight_comp, Iso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem hom_inv_actionHomLeft {x y : D} (f : x ≅ y) (z : C) :
    f.hom ᵣ⊵ z ≫ f.inv ᵣ⊵ z = 𝟙 (x ᵣ⊙ z) := by
  rw [← comp_actionHomLeft, Iso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_inv_hom (x : D) {y z : C} (f : y ≅ z) :
    x ᵣ⊴ f.inv ≫ x ᵣ⊴ f.hom = 𝟙 (x ᵣ⊙ z) := by
  rw [← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem inv_hom_actionHomLeft {x y : D} (f : x ≅ y) (z : C) :
    f.inv ᵣ⊵ z ≫ f.hom ᵣ⊵ z = 𝟙 (y ᵣ⊙ z) := by
  rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_hom_inv' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    x ᵣ⊴ f ≫ x ᵣ⊴ inv f = 𝟙 (x ᵣ⊙ y) := by
  rw [← actionHomRight_comp, IsIso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem hom_inv_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    f ᵣ⊵ z ≫ inv f ᵣ⊵ z = 𝟙 (x ᵣ⊙ z) := by
  rw [← comp_actionHomLeft, IsIso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
theorem actionHomRight_inv_hom' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    x ᵣ⊴ inv f ≫ x ᵣ⊴ f = 𝟙 (x ᵣ⊙ z) := by
  rw [← actionHomRight_comp, IsIso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
theorem inv_hom_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    inv f ᵣ⊵ z ≫ f ᵣ⊵ z = 𝟙 (y ᵣ⊙ z) := by
  rw [← comp_actionHomLeft, IsIso.inv_hom_id, id_actionHomLeft]

instance isIso_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    IsIso (f ᵣ⊵ z) :=
  ⟨inv f ᵣ⊵ z, by simp⟩

instance isIso_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    IsIso (x ᵣ⊴ f) :=
  ⟨x ᵣ⊴ inv f, by simp⟩

instance isIso_actionHom {x y : D} {x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    IsIso (f ᵣ⊙ g) :=
  ⟨(inv f) ᵣ⊙ (inv g), by simp [← actionHom_comp]⟩

@[simp]
lemma inv_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    inv (f ᵣ⊵ z) = inv f ᵣ⊵ z :=
  IsIso.inv_eq_of_hom_inv_id <| hom_inv_actionHomLeft' f z

@[simp]
lemma inv_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    inv (x ᵣ⊴ f) = x ᵣ⊴ inv f :=
  IsIso.inv_eq_of_hom_inv_id <| actionHomRight_hom_inv' x f

@[simp]
lemma inv_actionHom
    {x y : D} {x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    inv (f ᵣ⊙ g) = (inv f) ᵣ⊙ (inv g) :=
  IsIso.inv_eq_of_hom_inv_id <| by simp [← actionHom_comp]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := y ᵣ⊙ x
      map f := f ᵣ⊵ x }
  map f :=
    { app y := y ᵣ⊴ f
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ c ᵣ⊙ d` as a functor. -/
@[simps!]
abbrev actionRight (c : C) : D ⥤ D := curriedAction C D|>.obj c

variable {D} in
/-- Bundle `c ↦ c ᵣ⊙ d` as a functor. -/
@[simps!]
abbrev actionLeft (d : D) : C ⥤ D := curriedAction C D|>.flip.obj d

/-- Bundle `ᵣσ_ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
def actionAssocNatIso :
    (Functor.postcompose₂.obj (curriedAction C D)|>.obj
      (curriedTensor C)) ≅
    bifunctorComp₂₃Functor|>.obj (curriedAction C D)|>.obj
      (curriedAction C D)|>.flip :=
  NatIso.ofComponents fun _ ↦
    NatIso.ofComponents fun _ ↦
     NatIso.ofComponents fun _ ↦ ᵣσ_ _ _ _

/-- Bundle `ᵣυ_ _` as an isomorphism of functors. -/
@[simps!]
def actionUnitNatIso : actionRight D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (ᵣυ_ ·)

end

end MonoidalRightAction

end CategoryTheory.MonoidalCategory
