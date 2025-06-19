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
`C` on `D` as the data of an object `c ⊙ₗ d` of `D` for every
`c : C` and `d : D`, as well as the data required to turn `- ⊙ₗ -` into
a bifunctor, along with structure natural isomorphisms
`(- ⊗ -) ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -` and `𝟙_ C ⊙ₗ - ≅ -`, subject to coherence conditions.


## References
* [Janelidze, G, and Kelly, G.M., *A note on actions of a monoidal category*][JanelidzeKelly2001]

## TODOs/Projects
* Equivalence between actions of `C` on `D` and pseudofunctors from the
  classifying bicategory of `C` to `Cat`.
* Right actions
* Functors that respects left actions.
* Left actions as monoidal functors C ⥤ (D ⥤ D)ᴹᵒᵖ.
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
  /-- The left action on objects. This is denoted `c ⊙ₗ d`. -/
  actionObj : C → D → D
  /-- The left action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is (Α.map f).app d`. This is denoted `f ⊵ₗ d` -/
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
scoped infixr:70 " ⊙ₗₘ " => MonoidalLeftActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ⊗ - ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -`. -/
scoped notation "αₗ " => MonoidalLeftActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`. -/
scoped notation "λₗ " => MonoidalLeftActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`,
allowing one to specify the acting category. -/
scoped notation "λₗ["J"]" => MonoidalLeftActionStruct.actionUnitIso (C := J)

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
- A structure isomorphism `αₗ c c' d : c ⊗ c' ⊙ₗ d ≅ c ⊙ₗ c' ⊙ₗ d`.
- A structure isomorphism `λₗ d : (𝟙_ C) ⊙ₗ d ≅ d`.
Furthermore, we require identities that turn `- ⊙ₗ -` into a bifunctor,
ensure naturality of `αₗ` and `λₗ`, and ensure compatibilies with
the associator and unitor isomorphisms in `C`. -/
class MonoidalLeftAction [MonoidalCategory C] extends
    MonoidalLeftActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
      f ⊙ₗₘ g = f ⊵ₗ d ≫ c' ⊴ₗ g := by
    aesop_cat
  actionHomRight_id (c : C) (d : D) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d) := by aesop_cat
  id_actionHomLeft (c : C) (d : D) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d) := by aesop_cat
  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'')
      (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
      (f₁ ≫ f₂) ⊙ₗₘ (g₁ ≫ g₂) = (f₁ ⊙ₗₘ g₁) ≫ (f₂ ⊙ₗₘ g₂) := by
    aesop_cat
  actionAssocIso_hom_naturality
      {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
      ((f ⊗ₘ g) ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).hom =
        (αₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗₘ g ⊙ₗₘ h) := by
    aesop_cat
  actionUnitIso_hom_naturality {d d' : D} (f : d ⟶ d') :
      (λₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (λₗ d').hom := by
    aesop_cat
  whiskerLeft_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
      (c ◁ f) ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (αₗ _ _ _).inv := by
    aesop_cat
  whiskerRight_actionHomLeft {c c' : C} (c'' : C) (f : c ⟶ c') (d : D) :
      (f ▷ c'') ⊵ₗ d = (αₗ c c'' d).hom ≫
        f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (αₗ c' c'' d).inv := by
    aesop_cat
  associator_actionHom (c₁ c₂ c₃ : C) (d : D) :
      (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (αₗ c₁ (c₂ ⊗ c₃) d).hom ≫
        c₁ ⊴ₗ (αₗ c₂ c₃ d).hom =
      (αₗ (c₁ ⊗ c₂ : C) c₃ d).hom ≫ (αₗ c₁ c₂ (c₃ ⊙ₗ d)).hom := by
    aesop_cat
  leftUnitor_actionHom (c : C) (d : D) :
      (λ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ (λₗ _).hom := by
    aesop_cat
  rightUnitor_actionHom (c : C) (d : D) :
      (ρ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ (λₗ _).hom := by
    aesop_cat

attribute [reassoc] MonoidalLeftAction.actionHom_def
attribute [reassoc, simp] MonoidalLeftAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalLeftAction.actionHomRight_id
attribute [reassoc, simp] MonoidalLeftAction.whiskerLeft_actionHomLeft
attribute [simp, reassoc] MonoidalLeftAction.actionHom_comp
attribute [reassoc] MonoidalLeftAction.actionAssocIso_hom_naturality
attribute [reassoc] MonoidalLeftAction.actionUnitIso_hom_naturality
attribute [reassoc (attr := simp)] MonoidalLeftAction.associator_actionHom
attribute [simp, reassoc] MonoidalLeftAction.leftUnitor_actionHom
attribute [simp, reassoc] MonoidalLeftAction.rightUnitor_actionHom

/-- A monoidal category acts on itself through the tensor product. -/
@[simps!]
instance selfAction [MonoidalCategory C] : MonoidalLeftAction C C where
  actionObj x y := x ⊗ y
  actionHom f g := f ⊗ₘ g
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
    (𝟙 c) ⊙ₗₘ f = c ⊴ₗ f := by
  simp [actionHom_def]

@[simp]
lemma actionHom_id {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊙ₗₘ (𝟙 d) = f ⊵ₗ d := by
  simp [actionHom_def]

@[reassoc, simp]
theorem actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ₗ (f ≫ g) = w ⊴ₗ f ≫ w ⊴ₗ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    (𝟙_ C) ⊴ₗ f = (λₗ x).hom ≫ f ≫ (λₗ y).inv := by
  rw [← Category.assoc, actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]
theorem tensor_actionHomRight (x y : C) {z z' : D} (f : z ⟶ z') :
    (x ⊗ y) ⊴ₗ f = (αₗ x y z).hom ≫ x ⊴ₗ y ⊴ₗ f ≫ (αₗ x y z').inv := by
  simp only [← id_actionHom, ← actionHom_id]
  rw [← Category.assoc, ← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]
theorem comp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) :
    (f ≫ g) ⊵ₗ z = f ⊵ₗ z ≫ g ⊵ₗ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
theorem actionHomLeft_action {x x' : C} (f : x ⟶ x') (y : C) (z : D) :
    f ⊵ₗ (y ⊙ₗ z) = (αₗ x y z).inv ≫ (f ▷ y) ⊵ₗ z ≫ (αₗ x' y z).hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
theorem action_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ₗ g ≫ f ⊵ₗ z = f ⊵ₗ y ≫ x ⊴ₗ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
theorem actionHom_def' {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ₗₘ g = x₁ ⊴ₗ g ≫ f ⊵ₗ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc]
theorem actionAssocIso_inv_naturality
    {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
    (f ⊙ₗₘ g ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).inv =
    (αₗ c₁ c₃ d₁).inv ≫ ((f ⊗ₘ g) ⊙ₗₘ h) := by
  rw [Iso.comp_inv_eq, Category.assoc, Eq.comm, Iso.inv_comp_eq, actionAssocIso_hom_naturality]

@[reassoc]
theorem actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') :
      (λₗ d).inv ≫ (𝟙_ C) ⊴ₗ f = f ≫ (λₗ d').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, actionUnitIso_hom_naturality]

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
    IsIso (f ⊙ₗₘ g) :=
  ⟨(inv f) ⊙ₗₘ (inv g), by simp [← actionHom_comp]⟩

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
    inv (f ⊙ₗₘ g) = (inv f) ⊙ₗₘ (inv g) :=
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

/-- Bundle `αₗ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
def actionAssocNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) ≅
    bifunctorComp₂₃ (curriedAction C D) (curriedAction C D) :=
  NatIso.ofComponents fun _ ↦
    NatIso.ofComponents fun _ ↦
     NatIso.ofComponents fun _ ↦ αₗ _ _ _

/-- Bundle `λₗ _` as an isomorphism of functors. -/
@[simps!]
def actionUnitNatIso : actionLeft D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (λₗ ·)

end

end MonoidalLeftAction

end CategoryTheory.MonoidalCategory
