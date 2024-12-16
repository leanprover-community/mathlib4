/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# The category ParallelMaps

Given a type `T`, we introduce a category with two objects `zero` and `one`,
such that `(zero ⟶ one) ≃ T`, and other morphisms are identities.

This category is used in order to show that it is possible to coequalize
a suitable family of morphisms in a `κ`-filtered category
(see `CategoryTheory.Presentable.IsCardinalFiltered`.)

-/

universe w v u u₀

namespace CategoryTheory

/-- Given a type `T`, which is the category with two objects `zero` and `one`,
such that `(zero ⟶ one) ≃ T`, and other morphisms are identities. -/
inductive ParallelMaps (T : Type u₀) : Type
  | zero
  | one

namespace ParallelMaps

variable {T : Type u₀}

/-- The type of morphisms in the category `ParallelMaps T`: identities, and morphisms
`zero ⟶ one` attached to any `t : T`. -/
inductive Hom : ParallelMaps T → ParallelMaps T → Type u₀
  | id (X : ParallelMaps T) : Hom X X
  | map (t : T) : Hom zero one

/-- The composition of morphisms in the category `ParallelMaps T`. -/
def Hom.comp : ∀ {X Y Z : ParallelMaps T}, Hom X Y → Hom Y Z → Hom X Z
  | _, _, _, id _, g => g
  | _, _, _, f, id _ => f

instance : Category (ParallelMaps T) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by rintro _ _ (_ | _); all_goals rfl
  comp_id := by rintro _ _ (_ | _); all_goals rfl
  assoc := by rintro _ _ _ _ (_ | _) (_ | _) (_ | _); all_goals rfl

/-- Constructor for functors from the category `ParallelMaps T`. -/
@[simps]
def mkFunctor {C : Type u} [Category.{v} C] {X Y : C} (f : T → (X ⟶ Y)) :
    ParallelMaps T ⥤ C where
  obj a := match a with
    | zero => X
    | one => Y
  map φ := match φ with
    | .id _ => 𝟙 _
    | .map t => f t
  map_comp := by
    rintro _ _ _ (_ | _) (_ | _) <;> simp <;> rfl

variable (T) in
/-- `Arrow (ParallelMaps T)` identify to the type obtained by adding two elements to `T`. -/
def arrowEquiv : Arrow (ParallelMaps T) ≃ Option (Option T) where
  toFun f := match f.left, f.right, f.hom with
    | zero, _, .id _ => none
    | one, _, .id _ => some none
    | zero, one, .map t => some (some t)
  invFun x := match x with
    | none => Arrow.mk (𝟙 zero)
    | some none => Arrow.mk (𝟙 one)
    | some (some t) => Arrow.mk (.map t)
  left_inv := by rintro ⟨(_ | _), _, (_ | _)⟩ <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

lemma hasCardinalLT {κ' : Cardinal.{w}} (hT : HasCardinalLT T κ') (hκ' : Cardinal.aleph0 ≤ κ') :
    HasCardinalLT (Arrow (ParallelMaps T)) κ' := by
  simpa only [hasCardinalLT_iff_of_equiv (arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ'] using hT

end ParallelMaps

end CategoryTheory
