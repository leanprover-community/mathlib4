/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Module objects in cartesian monoidal categories

In this file we study module objects in a cartesian monoidal category `C` action on
itself by `⊗`.

In particular, for a monoid object `M : C` action on `X : C`, we equip `Z ⟶ X` with a `M ⟶ X` action
for every `Z : C`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

open scoped MonObj

attribute [local simp] leftUnitor_hom

/-- Every object is a module over a monoid object via the trivial action. -/
@[reducible] def ModObj.trivialAction (M : C) [MonObj M] (X : C) :
    ModObj M X where
  smul := snd M X

attribute [local instance] ModObj.trivialAction in
/-- Every object is a module over a monoid object via the trivial action. -/
@[simps]
def Mod.trivialAction (M : Mon C) (X : C) : Mod C M.X where
  X := X

@[deprecated (since := "2026-04-21")]
alias Mod_.trivialAction := Mod.trivialAction

variable {M : C} [MonObj M] {X : C} [ModObj M X]

namespace Hom

/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal scalar multiplication. -/
@[to_additive (attr := simps! -isSimp)
/-- Morphisms `Y ⟶ M` act on morphisms `Y ⟶ X` via the internal additive action. -/]
instance (Y : C) : SMul (Y ⟶ M) (Y ⟶ X) where
  smul m x := lift m x ≫ γ[M, X]

/-- If `M` is a monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/
@[to_additive /-- If `M` is an additive monoid object acting on `X`, then morphisms into `M` act on
morphisms into `X`. -/]
instance mulAction (Z : C) : MulAction (Z ⟶ M) (Z ⟶ X) where
  one_smul x := by simp [one_def, smul_def, ← lift_whiskerRight]
  mul_smul m n x := by simp [mul_def, smul_def, ← lift_whiskerRight]

end Hom

variable {Y : C} [ModObj M Y]

lemma ModObj.comp_smul {Z Z' : C} (g : Z' ⟶ Z) (m : Z ⟶ M) (x : Z ⟶ X) :
    g ≫ (m • x) = (g ≫ m) • (g ≫ x) := by
  rw [Hom.smul_def, Hom.smul_def, comp_lift_assoc]

@[to_additive (attr := reassoc (attr := simp))]
lemma IsModHom.map_smul (f : X ⟶ Y) [IsModHom M f] {Z : C} (m : Z ⟶ M) (x : Z ⟶ X) :
    (m • x) ≫ f = m • x ≫ f := by
  simp [Hom.smul_def, Category.assoc, IsModHom.smul_hom]

/-- An `M`-equivariant morphism induces an equivariant function on hom types. -/
@[to_additive (attr := simps)
/-- A `φ`-equivariant morphism induces an equivariant morphism on hom types. -/]
def IsModHom.mulActionHom (f : X ⟶ Y) [IsModHom M f] (Z : C) :
    MulActionHom (id (α := Z ⟶ M)) (Z ⟶ X) (Z ⟶ Y) where
  toFun := (· ≫ f)
  map_smul' := map_smul f

namespace ModObj

variable (M X) in
/-- The morphism `(m, x) ↦ (m • x, x)`. -/
def leftSMul : M ⊗ X ⟶ X ⊗ X :=
  lift γ[M, X] (snd _ _)

@[reassoc (attr := simp)]
lemma leftSMul_fst : leftSMul M X ≫ fst _ _ = γ[M, X] := by
  simp [leftSMul]

@[reassoc (attr := simp)]
lemma leftSMul_snd : leftSMul M X ≫ snd _ _ = snd _ _ := by
  simp [leftSMul]

@[reassoc]
lemma lift_leftSMul (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) : lift m x ≫ leftSMul M X = lift (m • x) x := by
  ext <;> simp [Hom.smul_def]

lemma lift_leftSMul_eq_lift_iff (Z : C) (x y : Z ⟶ X) (m : Z ⟶ M) :
    lift m x ≫ leftSMul M X = lift y x ↔ m • x = y := by
  simp [Hom.smul_def, leftSMul, CartesianMonoidalCategory.hom_ext_iff]

open CartesianMonoidalCategory in
/-- The morphism `(m, x) ↦ (m • x, x)` is an isomorphism if and only if the induced
action is pointwise simply transitive. -/
lemma isIso_leftSMul_iff :
    IsIso (leftSMul M X) ↔ ∀ (Z : C) (x y : Z ⟶ X), ∃! (m : Z ⟶ M), m • x = y := by
  have H (Z : C) (x : Z ⟶ X) (m : Z ⟶ M) :
      lift m x ≫ leftSMul M X = lift (m • x) x := by
    ext <;> simp [Hom.smul_def]
  have h (Z : C) (f g : Z ⟶ X) (m : Z ⟶ M) (x : Z ⟶ X) :
      lift m x ≫ leftSMul M X = lift f g ↔ x = g ∧ m • x = f := by
    simp [← lift_leftSMul_eq_lift_iff, CartesianMonoidalCategory.hom_ext_iff]
    grind
  rw [isIso_iff_yoneda_map_bijective]
  congr! with Z
  rw [← Function.Bijective.of_comp_iff _ liftEquiv.bijective, Function.bijective_iff_existsUnique]
  simp only [liftEquiv.surjective.forall, liftEquiv_apply, Prod.forall, Function.comp_apply, h]
  rw [forall_comm]
  congr! 2 with f g
  exact Equiv.existsUnique_subtype_congr ⟨fun a ↦ ⟨a.val.fst, by grind⟩,
    fun a ↦ ⟨⟨a.val, f⟩, by grind⟩, by cat_disch, by cat_disch⟩

end ModObj

end CategoryTheory
