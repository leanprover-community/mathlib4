/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Shifted morphisms

Given a category `C` endowed with a shift by an additive monoid `M` and two
objects `X` and `Y` in `C`, we consider the types `ShiftedHom X Y m`
defined as `X ⟶ Y⟦m⟧` for all `m : M`, and the composition on these
shifted hom.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]

/-- In a category `C` equipped with a shift by an additive monoid,
this is the type of morphisms `X ⟶ (Y⟦m⟧)` for `m : M`. -/
abbrev ShiftedHom (X Y : C) (m : M) : Type _ := X ⟶ Y⟦m⟧

namespace ShiftedHom

variable {X Y Z T : C}

/-- The composition of `f : X ⟶ Y⟦a⟧` and `g : Y ⟶ Z⟦b⟧`, as a morphism `X ⟶ Z⟦c⟧`
when `b + a = c`. -/
noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom X Z c :=
  f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _

set_option backward.isDefEq.respectTransparency false in
lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    (α : ShiftedHom X Y a₁) (β : ShiftedHom Y Z a₂) (γ : ShiftedHom Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  simp only [comp, assoc, Functor.map_comp,
    shiftFunctorAdd'_assoc_inv_app a₃ a₂ a₁ a₂₃ a₁₂ a h₂₃ h₁₂ h,
    ← NatTrans.naturality_assoc, Functor.comp_map]

/-! In degree `0 : M`, shifted hom `ShiftedHom X Y 0` identify to morphisms `X ⟶ Y`.
We generalize this to `m₀ : M` such that `m₀ : 0` as it shall be convenient when we
apply this with `M := ℤ` and `m₀` the coercion of `0 : ℕ`. -/

/-- The element of `ShiftedHom X Y m₀` (when `m₀ = 0`) attached to a morphism `X ⟶ Y`. -/
noncomputable def mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) : ShiftedHom X Y m₀ :=
  f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(X ⟶ Y) ≃ ShiftedHom X Y m₀` when `m₀ = 0`. -/
@[simps apply]
noncomputable def homEquiv (m₀ : M) (hm₀ : m₀ = 0) : (X ⟶ Y) ≃ ShiftedHom X Y m₀ where
  toFun f := mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]

set_option backward.isDefEq.respectTransparency false in
lemma mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) :
    (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add_zero]) = f ≫ g := by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]
lemma mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a) :
    (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_zero]) = f := by
  simp [mk₀_comp]

set_option backward.isDefEq.respectTransparency false in
lemma comp_mk₀ {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) :
    f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zero_add]) = f ≫ g⟦a⟧' := by
  subst hm₀
  simp only [comp, shiftFunctorAdd'_zero_add_inv_app, mk₀, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp]
lemma comp_mk₀_id {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) :
    f.comp (mk₀ m₀ hm₀ (𝟙 Y)) (by rw [hm₀, zero_add]) = f := by
  simp [comp_mk₀]

@[simp]
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) {a b c : M} (h : b + a = c)
    (ha : a = 0) (hb : b = 0) :
    (mk₀ a ha f).comp (mk₀ b hb g) h = mk₀ c (by rw [← h, ha, hb, add_zero]) (f ≫ g) := by
  subst ha hb
  obtain rfl : c = 0 := by rw [← h, zero_add]
  rw [mk₀_comp, mk₀, mk₀, assoc]

@[simp]
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {a : M}
    (ha : a = 0) {d : M} (h : ShiftedHom Z T d) :
    (mk₀ a ha f).comp ((mk₀ a ha g).comp h
        (show _ = d by rw [ha, add_zero])) (show _ = d by rw [ha, add_zero]) =
      (mk₀ a ha (f ≫ g)).comp h (by rw [ha, add_zero]) := by
  subst ha
  rw [← comp_assoc, mk₀_comp_mk₀]
  all_goals simp

section Preadditive

variable [Preadditive C]

variable (X Y) in
@[simp]
lemma mk₀_zero (m₀ : M) (hm₀ : m₀ = 0) : mk₀ m₀ hm₀ (0 : X ⟶ Y) = 0 := by simp [mk₀]

@[simp]
lemma mk₀_add (m₀ : M) (hm₀ : m₀ = 0) (f g : X ⟶ Y) :
    mk₀ m₀ hm₀ (f + g) = mk₀ m₀ hm₀ f + mk₀ m₀ hm₀ g := by simp [mk₀]

@[simp]
lemma mk₀_neg (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    mk₀ m₀ hm₀ (-f) = -mk₀ m₀ hm₀ f := by simp [mk₀]

@[simp]
lemma comp_add [∀ (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  rw [comp, comp, comp, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

@[simp]
lemma add_comp
    {a b c : M} (α₁ α₂ : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  rw [comp, comp, comp, Preadditive.add_comp]

@[simp]
lemma comp_neg [∀ (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (-β) h = -α.comp β h := by
  rw [comp, comp, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]

@[simp]
lemma neg_comp
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (-α).comp β h = -α.comp β h := by
  rw [comp, comp, Preadditive.neg_comp]

variable (Z) in
@[simp]
lemma comp_zero [∀ (a : M), (shiftFunctor C a).PreservesZeroMorphisms]
    {a : M} (β : ShiftedHom X Y a) {b c : M} (h : b + a = c) :
    β.comp (0 : ShiftedHom Y Z b) h = 0 := by
  rw [comp, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

variable (X) in
@[simp]
lemma zero_comp (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c) :
    (0 : ShiftedHom X Y a).comp β h = 0 := by
  rw [comp, Limits.zero_comp]

end Preadditive

/-- The action on `ShiftedHom` of a functor which commutes with the shift. -/
def map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] :
    ShiftedHom (F.obj X) (F.obj Y) a :=
  F.map f ≫ (F.commShiftIso a).hom.app Y

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (F : C ⥤ D) [F.CommShift M] :
    (ShiftedHom.mk₀ m₀ hm₀ f).map F = .mk₀ _ hm₀ (F.map f) := by
  subst hm₀
  simp [map, mk₀, shiftFunctorZero', F.commShiftIso_zero M, ← Functor.map_comp_assoc]

@[simp]
lemma id_map {a : M} (f : ShiftedHom X Y a) : f.map (𝟭 C) = f := by
  simp [map]

lemma comp_map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
    (G : D ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f.map F).map G := by
  simp [map, Functor.commShiftIso_comp_hom_app]

set_option backward.isDefEq.respectTransparency false in
lemma map_naturality {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift τ M] :
    (f.map F).comp (mk₀ 0 rfl (τ.app Y)) (zero_add _) =
      (mk₀ 0 rfl (τ.app X)).comp (f.map G) (add_zero _) := by
  rw [comp_mk₀, mk₀_comp, map, map, Category.assoc, ← τ.naturality_assoc,
    τ.shift_app_comm a]

@[simp]
lemma map_naturality_1
    {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] :
    (mk₀ 0 rfl (e.inv.app X)).comp ((f.map F).comp
      (mk₀ 0 rfl (e.hom.app Y)) (zero_add _)) (add_zero _) = f.map G := by
  simp [map_naturality]

@[simp]
lemma map_naturality_2
    {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] :
    (mk₀ 0 rfl (e.hom.app X)).comp ((f.map G).comp
      (mk₀ 0 rfl (e.inv.app Y)) (zero_add _)) (add_zero _) = f.map F :=
  map_naturality_1 f e.symm

set_option backward.isDefEq.respectTransparency false in
lemma map_comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) (F : C ⥤ D) [F.CommShift M] :
    (f.comp g h).map F = (f.map F).comp (g.map F) h := by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc]
  erw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_map, F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id]

section Preadditive

variable [Preadditive C] [Preadditive D]

@[simp]
lemma map_add {a : M} (α₁ α₂ : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Additive] :
    (α₁ + α₂).map F = α₁.map F + α₂.map F := by
  simp [ShiftedHom.map, F.map_add]

@[simp]
lemma map_zero {a : M} (F : C ⥤ D) [F.CommShift M] [F.Additive] :
    (0 : ShiftedHom X Y a).map F = 0 := by
  simp [ShiftedHom.map]

end Preadditive

section Linear

variable {R : Type*} [Ring R] [Preadditive C] [Linear R C]

@[simp]
lemma comp_smul
    [∀ (a : M), Functor.Linear R (shiftFunctor C a)]
    (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (r • β) h = r • α.comp β h := by
  rw [comp, Functor.map_smul, comp, Linear.smul_comp, Linear.comp_smul]

@[simp]
lemma smul_comp
    (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (r • α).comp β h = r • α.comp β h := by
  rw [comp, comp, Linear.smul_comp]

@[simp]
lemma mk₀_smul (m₀ : M) (hm₀ : m₀ = 0) (r : R) {f : X ⟶ Y} :
    mk₀ m₀ hm₀ (r • f) = r • mk₀ m₀ hm₀ f := by
  simp [mk₀]

variable [Preadditive D] [Linear R D]

@[simp]
lemma map_smul (r : R) {a : M} (α : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Linear R] :
    (r • α).map F = r • (α.map F) := by
  simp [ShiftedHom.map, F.map_smul]

end Linear

end ShiftedHom

end CategoryTheory
