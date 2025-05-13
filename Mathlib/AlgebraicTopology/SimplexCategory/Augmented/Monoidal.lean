/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal structure on the augmented simplex category

This file defines a monoidal structure on `AugmentedSimplexCategory`.
The tensor product of objects is characterized by the fact that the initial object `star` is
also the unit, and the fact that `⦋m⦌ ⊗ ⦋n⦌ = ⦋m + n + 1⦌` for `n m : ℕ`.

Through the (not in mathlib) equivalence between `AugmentedSimplexCategory` and the category
of finite ordinals, the tensor products corresponds to ordinal sum.

As the unit of this structure is an initial object, for every `x y : AugmentedSimplexCategory`,
there are maps `AugmentedSimplexCategory.φ₁ x y : x ⟶ x ⊗ y` and
`AugmentedSimplexCategory.φ₁ x y : y ⟶ x ⊗ y`. The main API for working with the tensor product
of maps is given by  `AugmentedSimplexCategory.tensorObj_hom_ext`, which characterizes maps
`x ⊗ y ⟶ z` in terms of their composition with these two maps. We also characterize the behaviour
of the associator isomorphism with respect to these maps.

-/

namespace AugmentedSimplexCategory

attribute [local aesop safe cases (rule_sets := [CategoryTheory])] CategoryTheory.WithInitial

open CategoryTheory MonoidalCategory
open scoped Simplicial

@[simp]
lemma eqToHom_toOrderHom {x y : SimplexCategory} (h : WithInitial.of x = WithInitial.of y) :
  SimplexCategory.Hom.toOrderHom (WithInitial.down <| eqToHom h) =
    (Fin.castOrderIso
      (congrArg (fun t ↦ t + 1) (by injection h with h; rw [h]))).toOrderEmbedding.toOrderHom := by
  injection h with h
  subst h
  rfl

/-- An auxiliary definition for the tensor product of two objects in `AugmentedSimplexCategory`. -/
-- (Impl. note): This definition could easily be inlined in
-- the definition of `tensorObjOf` below, but having it type check directly as an element
-- of `SimplexCategory` avoids having to sprinkle `WithInitial.down` everywhere.
abbrev tensorObjOf (m n : SimplexCategory) : SimplexCategory := .mk (m.len + n.len + 1)

/-- The tensor product of two objects of `AugmentedSimplexCategory`. -/
def tensorObj (m n : AugmentedSimplexCategory) : AugmentedSimplexCategory :=
  match m, n with
  | .of m, .of n => .of <| tensorObjOf m n
  | .star, x => x
  | x, .star => x

/-- The action of the tensor product on maps coming from `SimplexCategory`. -/
def tensorHomOf {x₁ y₁ x₂ y₂: SimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObjOf x₁ x₂ ⟶ tensorObjOf y₁ y₂ :=
  letI f₁ : Fin ((x₁.len + 1) + (x₂.len + 1)) →o Fin ((y₁.len + 1) + (y₂.len + 1)) :=
    { toFun i :=
        Fin.addCases
          (motive := fun _ ↦ Fin <| (y₁.len + 1) + (y₂.len + 1))
          (fun i ↦ (f₁.toOrderHom i).castAdd _)
          (fun i ↦ (f₂.toOrderHom i).natAdd _)
          i
      monotone' i j h := by
        cases i using Fin.addCases <;>
        cases j using Fin.addCases <;>
        rw [Fin.le_def] at h ⊢ <;>
        simp [Fin.coe_castAdd, Fin.coe_natAdd, Fin.addCases_left,
          Fin.addCases_right] at h ⊢
        · case left.left i j => exact f₁.toOrderHom.monotone h
        · case left.right i j => omega
        · case right.left i j => omega
        · case right.right i j => exact f₂.toOrderHom.monotone h }
  (eqToHom (congrArg _ (Nat.succ_add _ _)).symm ≫ (SimplexCategory.mkHom f₁) ≫
    eqToHom (congrArg _ (Nat.succ_add _ _)) : _ ⟶ ⦋y₁.len + y₂.len + 1⦌)

/-- The action of the tensor product on maps of `AugmentedSimplexCategory`. -/
def tensorHom {x₁ y₁ x₂ y₂: AugmentedSimplexCategory} (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) :
    tensorObj x₁ x₂ ⟶ tensorObj y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of _, .of _, .of _, .of _, f₁, f₂ => tensorHomOf f₁ f₂
  | .of _, .of y₁, .star, .of y₂, f₁, _ =>
    f₁ ≫ ((SimplexCategory.mkHom <| (Fin.castAddOrderEmb (y₂.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₁.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .of y₁, .of _, .of y₂, _, f₂ =>
    f₂ ≫ ((SimplexCategory.mkHom <| (Fin.natAddOrderEmb (y₁.len + 1)).toOrderHom) ≫
      eqToHom (congrArg _ (Nat.succ_add _ _)) : ⦋y₂.len⦌ ⟶ ⦋y₁.len + y₂.len + 1⦌)
  | .star, .star, .of _, .of _, _, f₂ => f₂
  | .of _, .of _, .star, .star, f₁, _ => f₁
  | .star, _, .star, _, _, _ => WithInitial.starInitial.to _

/-- The unit for the monoidal structure on `AugmentedSimplexCategory` is the initial object. -/
abbrev tensorUnit : AugmentedSimplexCategory := WithInitial.star

/-- The associator isomorphism for the monoidal structure on `AugmentedSimplexCategory` -/
def associator (x y z : AugmentedSimplexCategory) :
    tensorObj (tensorObj x y) z ≅ tensorObj x (tensorObj y z) :=
  match x, y, z with
  | .of x, .of y, .of z =>
    eqToIso (congrArg (fun j ↦ WithInitial.of <| SimplexCategory.mk j)
      (by simp +arith))
  | .star, .star, .star => Iso.refl _
  | .star, .of _, .star => Iso.refl _
  | .star, .star, .of _ => Iso.refl _
  | .star, .of _, .of _ => Iso.refl _
  | .of _, .star, .star => Iso.refl _
  | .of _, .star, .of _ => Iso.refl _
  | .of _, .of _, .star => Iso.refl _

/-- The left unitor isomorphism for the monoidal structure in `AugmentedSimplexCategory` -/
def leftUnitor (x : AugmentedSimplexCategory) :
    tensorObj tensorUnit x ≅ x :=
  match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

/-- The right unitor isomorphism for the monoidal structure in `AugmentedSimplexCategory` -/
def rightUnitor (x : AugmentedSimplexCategory) :
    tensorObj x tensorUnit ≅ x :=
  match x with
  | .of _ => Iso.refl _
  | .star => Iso.refl _

instance : MonoidalCategoryStruct AugmentedSimplexCategory where
  tensorObj := tensorObj
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft x _ _ f := tensorHom (𝟙 x) f
  whiskerRight f x := tensorHom f (𝟙 x)

@[local simp]
lemma id_tensorHom (x : AugmentedSimplexCategory) {y₁ y₂ : AugmentedSimplexCategory}
    (f : y₁ ⟶ y₂) : 𝟙 x ⊗ f = x ◁ f :=
  rfl

@[local simp]
lemma tensorHom_id {x₁ x₂ : AugmentedSimplexCategory} (y : AugmentedSimplexCategory)
    (f : x₁ ⟶ x₂) : f ⊗ 𝟙 y = f ▷ y :=
  rfl

@[local simp]
lemma whiskerLeft_id_star {x: AugmentedSimplexCategory} : x ◁ 𝟙 WithInitial.star = 𝟙 _ := by
  cases x <;>
  rfl

@[local simp]
lemma id_star_whiskerRight {x: AugmentedSimplexCategory} : 𝟙 WithInitial.star ▷ x = 𝟙 _ := by
  cases x <;>
  rfl

/-- Thanks to `tensorUnit` being initial in `AugmentedSimplexCategory`, we get
a morhpim `Δ ⟶ Δ ⊗ Δ'` for every pair of objects `Δ, Δ'`. -/
def φ₁ (x y : AugmentedSimplexCategory) : x ⟶ x ⊗ y :=
  (ρ_ x).inv ≫ _ ◁ (WithInitial.starInitial.to y)

/-- Thanks to `tensorUnit` being initial in `AugmentedSimplexCategory`, we get
a morhpim `Δ' ⟶ Δ ⊗ Δ'` for every pair of objects `Δ, Δ'`. -/
def φ₂ (x y : AugmentedSimplexCategory) : y ⟶ x ⊗ y :=
  (λ_ y).inv ≫ (WithInitial.starInitial.to x) ▷ _

/-- Again, to ease type checking, we also provide a version of φ₁ that lives in
`SimplexCategory`. -/
abbrev φ₁' (x y : SimplexCategory) : x ⟶ tensorObjOf x y := WithInitial.down <| φ₁ (.of x) (.of y)

/-- Again, to ease type checking, we also provide a version of φ₂ that lives in
`SimplexCategory`. -/
abbrev φ₂' (x y : SimplexCategory) : y ⟶ tensorObjOf x y := WithInitial.down <| φ₂ (.of x) (.of y)

lemma φ₁'_eval (x y : SimplexCategory) (i : Fin (x.len + 1)) :
    (φ₁' x y).toOrderHom i = (i.castAdd _).cast (Nat.succ_add x.len (y.len + 1)) := by
  simp only [φ₁', WithInitial.down, φ₁, MonoidalCategoryStruct.rightUnitor, rightUnitor, tensorObj,
    Iso.refl_inv, MonoidalCategoryStruct.whiskerLeft, tensorHom, SimplexCategory.mk_len, Nat.add_eq,
    SimplexCategory.mkHom, Category.id_comp, SimplexCategory.comp_toOrderHom,
    SimplexCategory.len_mk, SimplexCategory.eqToHom_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
    Function.comp_apply, Fin.castOrderIso_apply, Fin.cast_inj]
  rfl

lemma φ₂'_eval (x y : SimplexCategory) (i : Fin (y.len + 1)) :
    (φ₂' x y).toOrderHom i = (i.natAdd _).cast (Nat.succ_add x.len (y.len + 1)) := by
  simp only [SimplexCategory.len_mk, φ₂', WithInitial.down, φ₂, MonoidalCategoryStruct.leftUnitor,
    leftUnitor, tensorObj, Iso.refl_inv, MonoidalCategoryStruct.whiskerRight, tensorHom,
    SimplexCategory.mk_len, Nat.add_eq, SimplexCategory.mkHom, Category.id_comp,
    SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Function.comp_apply, Fin.castOrderIso_apply, Fin.cast_inj]
  rfl

/-- We can characterize morphisms out of a tensor product via their precomposition with `φ₁` and
`φ₂`. -/
@[ext]
theorem tensorObj_hom_ext {x y z : AugmentedSimplexCategory} (f g : x ⊗ y ⟶ z)
    (h₁ : φ₁ _ _ ≫ f = φ₁ _ _ ≫ g)
    (h₂ : φ₂ _ _ ≫ f = φ₂ _ _ ≫ g)
    : f = g :=
  match x, y, z, f, g with
  | .of x, .of y, .of z, f, g => by
    change (tensorObjOf x y) ⟶ z at f g
    change φ₁' _ _ ≫ f = φ₁' _ _ ≫ g at h₁
    change φ₂' _ _ ≫ f = φ₂' _ _ ≫ g at h₂
    ext i
    set j : Fin ((x.len + 1) + (y.len + 1)) := i.cast (Nat.succ_add x.len (y.len + 1)).symm
    haveI : i = j.cast (Nat.succ_add x.len (y.len + 1)) := rfl
    rw [this]
    cases j using Fin.addCases (m := x.len + 1) (n := y.len + 1) with
    | left j =>
      rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁
      simpa [← φ₁'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₁ j
    | right j =>
      rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₂
      simpa [← φ₂'_eval, ConcreteCategory.hom, Fin.ext_iff] using congrFun h₂ j
  | .of x, .star, .of z, f, g => by
      simp only [φ₁, φ₂, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        whiskerLeft_id_star] at h₁
      simpa [Category.id_comp f, Category.id_comp g] using h₁
  | .star, .of y, .of z, f, g => by
      simp only [φ₁, φ₂, Category.assoc, Iso.cancel_iso_inv_left, Limits.IsInitial.to_self,
        id_star_whiskerRight] at h₂
      simpa [Category.id_comp f, Category.id_comp g] using h₂
  | .star, .star, .of z, f, g => rfl
  | .star, .star, .star, f, g => rfl

@[reassoc (attr := simp)]
lemma φ₁_comp_tensorHom {x₁ y₁ x₂ y₂: AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : φ₁ x₁ x₂ ≫ (f₁ ⊗ f₂) = f₁ ≫ φ₁ y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change φ₁' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₁ ≫ φ₁' _ _
    ext i
    simp only [SimplexCategory.len_mk, tensorHomOf, Nat.add_eq, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom,
      SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Function.comp_apply, Fin.castOrderIso_apply, Fin.coe_cast]
    haveI := φ₁'_eval x₁ x₂ i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    haveI := φ₁'_eval y₁ y₂ <| (WithInitial.down f₁).toOrderHom i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    conv_lhs =>
      arg 1
      change Fin.addCases
        (fun i ↦ Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i ↦ Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.castAdd (x₂.len + 1) i)
      rw [Fin.addCases_left]
    rfl
  | _, _, .star, _, f₁, f₂ => by aesop_cat
  | .star, _, _, _, _, _ => rfl

@[reassoc (attr := simp)]
lemma φ₂_comp_tensorHom {x₁ y₁ x₂ y₂: AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) : φ₂ x₁ x₂ ≫ (f₁ ⊗ f₂) = f₂ ≫ φ₂ y₁ y₂ :=
  match x₁, y₁, x₂, y₂, f₁, f₂ with
  | .of x₁, .of y₁, .of x₂, .of y₂, f₁, f₂ => by
    change φ₂' _ _ ≫ tensorHomOf _ _ = WithInitial.down f₂ ≫ φ₂' _ _
    ext i
    simp only [SimplexCategory.len_mk, tensorHomOf, Nat.add_eq, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.eqToHom_toOrderHom,
      SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
      OrderIso.coe_toOrderEmbedding, Function.comp_apply, Fin.castOrderIso_apply, Fin.coe_cast]
    haveI := φ₂'_eval x₁ x₂ i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    haveI := φ₂'_eval y₁ y₂ <| (WithInitial.down f₂).toOrderHom i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    conv_lhs =>
      arg 1
      rw [Fin.cast_trans, Fin.cast_natAdd_left]
      change Fin.addCases
        (fun i ↦ Fin.castAdd (y₂.len + 1) (f₁.toOrderHom i))
        (fun i ↦ Fin.natAdd (y₁.len + 1) (f₂.toOrderHom i))
        (Fin.natAdd (x₁.len + 1) i)
      rw [Fin.addCases_right]
    rfl
  | .star, _, _, _, f₁, f₂ => by aesop_cat
  | _, _, .star, _, _, _ => rfl

@[reassoc (attr := simp)]
lemma φ₂_comp_associator (x y z : AugmentedSimplexCategory) :
    φ₂ _ _ ≫ (α_ x y z).hom = φ₂ _ _ ≫ φ₂ _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change φ₂' _ _ ≫ WithInitial.down _ = φ₂' _ _ ≫ φ₂' _ _
    ext i
    simp only [SimplexCategory.len_mk, MonoidalCategoryStruct.associator, associator, eqToIso.hom,
      SimplexCategory.comp_toOrderHom, eqToHom_toOrderHom, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
      Fin.castOrderIso_apply, Fin.coe_cast]
    haveI := φ₂'_eval (tensorObjOf x y) z i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    haveI := φ₂'_eval y z i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    generalize_proofs h h'
    haveI := φ₂'_eval x (tensorObjOf y z) <| Fin.cast h' <| i.natAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    simp +arith
  | .star, _, _ => by aesop_cat
  | _, .star, _ => by aesop_cat
  | _, _, .star => by aesop_cat

@[reassoc (attr := simp)]
lemma φ₁_comp_φ₁_comp_associator (x y z : AugmentedSimplexCategory) :
    φ₁ _ _ ≫ φ₁ _ _ ≫ (α_ x y z).hom = φ₁ _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change φ₁' _ _ ≫ φ₁' _ _ ≫ WithInitial.down _ = φ₁' _ _
    ext i
    simp only [SimplexCategory.len_mk, MonoidalCategoryStruct.associator, associator, eqToIso.hom,
      SimplexCategory.comp_toOrderHom, eqToHom_toOrderHom, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
      Fin.castOrderIso_apply, Fin.coe_cast]
    haveI := φ₁'_eval x y i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    haveI := φ₁'_eval x (tensorObjOf y z) i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    generalize_proofs h h'
    haveI := φ₁'_eval (tensorObjOf x y) z <| Fin.cast h <| i.castAdd (y.len + 1)
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    simp +arith
  | .star, _, _ => by aesop_cat
  | _, .star, _ => by aesop_cat
  | _, _, .star => by aesop_cat

@[reassoc (attr := simp)]
lemma φ₂_comp_φ₁_comp_associator (x y z : AugmentedSimplexCategory) :
    φ₂ _ _ ≫ φ₁ _ _ ≫ (α_ x y z).hom = φ₁ _ _ ≫ φ₂ _ _ :=
  match x, y, z with
  | .of x, .of y, .of z => by
    change φ₂' _ _ ≫ φ₁' _ _ ≫ WithInitial.down _ = φ₁' _ _ ≫ φ₂' _ _
    ext i
    simp only [SimplexCategory.len_mk, MonoidalCategoryStruct.associator, associator, eqToIso.hom,
      SimplexCategory.comp_toOrderHom, eqToHom_toOrderHom, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
      Fin.castOrderIso_apply, Fin.coe_cast]
    haveI := φ₁'_eval y z i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    haveI := φ₂'_eval x y i
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    generalize_proofs h h'
    haveI := φ₁'_eval (tensorObjOf x y) z <| Fin.cast h <| i.natAdd (x.len + 1)
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    haveI := φ₂'_eval x (tensorObjOf y z) <| Fin.cast h' <| i.castAdd (z.len + 1)
    simp only [SimplexCategory.len_mk] at this
    rw [this]
    simp +arith
  | .star, _, _ => by aesop_cat
  | _, .star, _ => by aesop_cat
  | _, _, .star => by aesop_cat

theorem tensor_comp {x₁ y₁ z₁ x₂ y₂ z₂ : AugmentedSimplexCategory}
    (f₁ : x₁ ⟶ y₁) (f₂ : x₂ ⟶ y₂) (g₁ : y₁ ⟶ z₁) (g₂ : y₂ ⟶ z₂) :
    (f₁ ≫ g₁) ⊗ (f₂ ≫ g₂) = (f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂) := by
  aesop_cat

theorem tensor_id (x y : AugmentedSimplexCategory) : (𝟙 x) ⊗ (𝟙 y) = 𝟙 (x ⊗ y) := by
  ext
  · simpa [φ₁, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensor_comp (𝟙 x) (WithInitial.starInitial.to y) (𝟙 x) (𝟙 y)).symm
  · simpa [φ₂, MonoidalCategoryStruct.whiskerLeft, MonoidalCategoryStruct.whiskerRight] using
      (tensor_comp (WithInitial.starInitial.to x) (𝟙 y) (𝟙 x) (𝟙 y)).symm

instance : MonoidalCategory AugmentedSimplexCategory :=
  MonoidalCategory.ofTensorHom
    (tensor_id := tensor_id)
    (tensor_comp := tensor_comp)
    (pentagon := fun w x y z ↦ by
      ext <;>
      simp [← id_tensorHom, ← tensorHom_id])

end AugmentedSimplexCategory
