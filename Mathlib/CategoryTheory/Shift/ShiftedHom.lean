<<<<<<< HEAD
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.GradedHMul
import Mathlib.CategoryTheory.Linear.LinearFunctor

namespace CategoryTheory

open Category Preadditive

variable {C D : Type _} [Category C] [Category D]
  (M : Type _) [AddCommMonoid M] [HasShift C M] [HasShift D M]
  {R : Type _} [Semiring R]

def ShiftedHom (X Y : C) : GradedType M := fun (n : M) => X ⟶ (Y⟦n⟧)

instance [Preadditive C] (X Y : C) (n : M) : AddCommGroup (ShiftedHom M X Y n) := by
  dsimp only [ShiftedHom]
  infer_instance

instance [Preadditive C] [Linear R C] (X Y : C) (n : M) : Module R (ShiftedHom M X Y n) := by
  dsimp only [ShiftedHom]
  infer_instance

noncomputable instance (X Y Z : C ) :
    HasGradedHMul (ShiftedHom M X Y) (ShiftedHom M Y Z) (ShiftedHom M X Z) where
  γhmul' p q n h α β := α ≫ β⟦p⟧' ≫
    (shiftFunctorAdd' C q p n (by rw [add_comm q p, h])).inv.app _

namespace ShiftedHom

variable {X Y Z : C} (f : X ⟶ Y)
variable {M}

noncomputable def mk₀ (m₀ : M) (hm₀ : m₀ = 0) :
  ShiftedHom M X Y m₀ := f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

noncomputable instance : One (ShiftedHom M X X 0) := ⟨mk₀ (𝟙 X) (0 : M) rfl⟩

variable (X M)

lemma one_eq : (1 : ShiftedHom M X X 0) = mk₀ (𝟙 X) 0 rfl := rfl

variable {X M}

lemma γhmul_eq {p q : M} (α : ShiftedHom M X Y p) (β : ShiftedHom M Y Z q) (n : M)
    (hpq : p + q = n) :
    α •[hpq] β = α ≫ β⟦p⟧' ≫
      (shiftFunctorAdd' C q p n (by rw [add_comm q p, hpq])).inv.app _ := rfl

@[simp]
lemma mk₀_γhmul {n : M} (f : X ⟶ Y) (m₀ : M) (hm₀ : m₀ = 0) (β : ShiftedHom M Y Z n) :
    (mk₀ f m₀ hm₀) •[show m₀ + n = n by rw [hm₀, zero_add]] β = f ≫ β := by
  subst hm₀
  simp only [mk₀, shiftFunctorZero'_eq_shiftFunctorZero, γhmul_eq,
    shiftFunctorAdd'_add_zero_inv_app, NatTrans.naturality, Functor.id_obj,
    Functor.id_map, assoc, Iso.inv_hom_id_app_assoc]

@[simp]
lemma γhmul_mk₀ {n : M} (α : ShiftedHom M X Y n) (f : Y ⟶ Z) (m₀ : M) (hm₀ : m₀ = 0)  :
    α •[show n + m₀ = n by rw [hm₀, add_zero]] (mk₀ f m₀ hm₀) = α ≫ f⟦n⟧' := by
  subst hm₀
  simp only [mk₀, shiftFunctorZero'_eq_shiftFunctorZero, γhmul_eq,
    shiftFunctorAdd'_zero_add_inv_app, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp 1100]
lemma mk₀_comp (f : X ⟶ Y) (g : Y ⟶ Z) (m m' m'' : M) (hm : m = 0) (hm' : m' = 0)
  (hm'' : m + m' = m'' ) :
    mk₀ f m hm •[hm''] mk₀ g m' hm' = mk₀ (f ≫ g) m'' (by rw [← hm'', hm, hm', zero_add]) := by
  subst hm hm'
  obtain rfl : m'' = 0 := by rw [← hm'', zero_add]
  rw [mk₀_γhmul]
  simp [mk₀]

@[simp]
lemma mk₀_add [Preadditive C] (f₁ f₂ : X ⟶ Y) (m₀ : M) (hm₀ : m₀ = 0) :
    (mk₀ (f₁ + f₂) m₀ hm₀) = mk₀ f₁ m₀ hm₀ + mk₀ f₂ m₀ hm₀ := by
  simp [mk₀]

@[simp]
lemma one_γhmul {n : M} (β : ShiftedHom M X Y n) :
    (1 : ShiftedHom M X X 0) •[zero_add n] β = β := by simp [one_eq]

@[simp 1100]
lemma one_γhmul' {n : M} (m₀ : M) (hm₀ : m₀ = 0) (β : ShiftedHom M X Y n) :
    (mk₀ (𝟙 X) m₀ hm₀) •[show m₀ + n = n by rw [hm₀, zero_add]] β = β := by simp

@[simp]
lemma γhmul_one {n : M} (α : ShiftedHom M X Y n) :
    α •[add_zero n] (1 : ShiftedHom M Y Y 0) = α := by simp [one_eq]

@[simp 1100]
lemma γhmul_one' {n : M} (α : ShiftedHom M X Y n) (m₀ : M) (hm₀ : m₀ = 0) :
    α  •[show n + m₀ = n by rw [hm₀, add_zero]] (mk₀ (𝟙 Y) m₀ hm₀)= α := by simp

@[simp]
lemma γhmul_add [Preadditive C] [∀ (a : M), (shiftFunctor C a).Additive]
    {p q n : M} (α : ShiftedHom M X Y p) (β₁ β₂ : ShiftedHom M Y Z q)
    (hpq : p + q = n) :
    α •[hpq] (β₁ + β₂) = α •[hpq] β₁ + α •[hpq] β₂ := by
  rw [γhmul_eq, γhmul_eq, γhmul_eq, Functor.map_add, add_comp, comp_add]

@[simp]
lemma add_γhmul [Preadditive C]
    {p q n : M} (α₁ α₂ : ShiftedHom M X Y p) (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    (α₁ + α₂) •[hpq] β = α₁ •[hpq] β + α₂ •[hpq] β := by
  rw [γhmul_eq, γhmul_eq, γhmul_eq, add_comp]

@[simp]
lemma γhmul_smul [Preadditive C] [Linear R C] [∀ (a : M), (shiftFunctor C a).Additive]
    [∀ (a : M), (shiftFunctor C a).Linear R]
    {p q n : M} (α : ShiftedHom M X Y p) (x : R)
    (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    α •[hpq] (x • β) = x • (α •[hpq] β) := by
  rw [γhmul_eq, γhmul_eq, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

@[simp]
lemma γhmul_units_smul [Preadditive C] [Linear R C] [∀ (a : M), (shiftFunctor C a).Additive]
    [∀ (a : M), (shiftFunctor C a).Linear R]
    {p q n : M} (α : ShiftedHom M X Y p) (x : Rˣ)
    (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    α •[hpq] (x • β) = x • (α •[hpq] β) := by
  apply γhmul_smul

@[simp]
lemma smul_γhmul [Preadditive C] [Linear R C]
    {p q n : M} (x : R) (α : ShiftedHom M X Y p)
    (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    (x • α) •[hpq] β = x • (α •[hpq] β) := by
  rw [γhmul_eq, γhmul_eq, Linear.smul_comp]

@[simp]
lemma units_smul_γhmul [Preadditive C] [Linear R C]
    {p q n : M} (x : Rˣ) (α : ShiftedHom M X Y p)
    (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    (x • α) •[hpq] β = x • (α •[hpq] β) := by
  apply smul_γhmul

instance {X₁ X₂ X₃ X₄ : C} : IsAssocGradedHMul (ShiftedHom M X₁ X₂)
    (ShiftedHom M X₂ X₃) (ShiftedHom M X₃ X₄) (ShiftedHom M X₁ X₃) (ShiftedHom M X₂ X₄)
    (ShiftedHom M X₁ X₄) where
  γhmul_assoc a b c α β γ ab bc abc hab hbc habc := by
    simp only [γhmul_eq, assoc, Functor.map_comp]
    rw [shiftFunctorAdd'_assoc_inv_app c b a bc ab abc] ; rotate_left
    · rw [add_comm b a, hab]
    · rw [add_assoc, add_comm b a, hab, add_comm c, habc]
    dsimp
    rw [← NatTrans.naturality_assoc]
    rfl

lemma comp_mk₀_injective (f : Y ⟶ Z) {n : M} (α β : ShiftedHom M X Y n) [IsIso f]
    (h : α •[add_zero n] (mk₀ f (0 : M) rfl) = β •[add_zero n] (mk₀ f (0 : M) rfl)): α = β := by
  rw [← γhmul_one α, ← γhmul_one β, one_eq, ← IsIso.hom_inv_id f,
    ← mk₀_comp f (inv f) (0 : M) 0 0 rfl rfl (add_zero 0),
    ← γhmul_assoc_of_second_degree_eq_zero, ← γhmul_assoc_of_second_degree_eq_zero, h]

lemma mk₀_comp_injective (f : X ⟶ Y) {n : M} (α β : ShiftedHom M Y Z n) [IsIso f]
    (h : (mk₀ f (0 : M) rfl) •[zero_add n] α = (mk₀ f (0 : M) rfl) •[zero_add n] β) : α = β := by
  rw [← one_γhmul α, ← one_γhmul β, one_eq, ← IsIso.inv_hom_id f,
    ← mk₀_comp (inv f) f (0 : M) 0 0 rfl rfl (add_zero 0),
    γhmul_assoc_of_second_degree_eq_zero, γhmul_assoc_of_second_degree_eq_zero, h]

def map {X Y : C} {m : M} (x : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M] :
    ShiftedHom M (F.obj X) (F.obj Y) m :=
  F.map x ≫ (F.commShiftIso m).hom.app Y

lemma map_eq {X Y : C} {m : M} (x : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M] :
    x.map F = F.map x ≫ (F.commShiftIso m).hom.app Y := rfl

lemma map_add {X Y : C} {m : M} (x y : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M]
    [Preadditive C] [Preadditive D] [F.Additive] : (x + y).map F = x.map F + y.map F := by
  rw [map_eq, F.map_add, add_comp, map_eq, map_eq]

def map_zsmul (a : ℤ) {X Y : C} {m : M} (x : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M]
    [Preadditive C] [Preadditive D] [F.Additive] :
    (a • x).map F = a • (x.map F) := by
  rw [map_eq, map_eq, F.map_zsmul, Preadditive.zsmul_comp]

lemma map_comp {X Y Z : C} {p q r : M} (h : p + q = r)
    (α : ShiftedHom M X Y p) (β : ShiftedHom M Y Z q) (F : C ⥤ D) [F.CommShift M] :
    (α •[h] β).map F = (α.map F) •[h] (β.map F) := by
  have h' : q + p = r := by rw [add_comm q, h]
  simp only [γhmul_eq, map_eq, F.commShiftIso_add' h',
    Functor.CommShift.isoAdd'_hom_app, ← Functor.map_comp_assoc]
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.map_comp,
    Functor.commShiftIso_hom_naturality_assoc]

noncomputable def map' {X Y : C} {m : M} (x : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M]
    {X' Y' : D} (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') : ShiftedHom M X' Y' m :=
  (mk₀ e₁.inv (0 : M) rfl) •[zero_add m] (x.map F •[add_zero m] (mk₀ e₂.hom (0 : M) rfl))

lemma map'_eq {X Y : C} {m : M} (x : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M]
    {X' Y' : D} (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') :
    x.map' F e₁ e₂ = (mk₀ e₁.inv (0 : M) rfl) •[zero_add m]
      (x.map F •[add_zero m] (mk₀ e₂.hom (0 : M) rfl)) := rfl

lemma map'_zsmul (a : ℤ) {X Y : C} {m : M} (x : ShiftedHom M X Y m) (F : C ⥤ D) [F.CommShift M]
    [Preadditive C] [Preadditive D] [F.Additive]
    [∀ (a : M), (shiftFunctor D a).Additive]
    {X' Y' : D} (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') :
    (a • x).map' F e₁ e₂ = a • (x.map' F e₁ e₂) := by
  rw [map'_eq, map'_eq, map_zsmul, smul_γhmul, γhmul_smul]

lemma map'_comp {X Y Z : C} {p q r : M} (h : p + q = r)
    (α : ShiftedHom M X Y p) (β : ShiftedHom M Y Z q) (F : C ⥤ D) [F.CommShift M]
    {X' Y' Z' : D} (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') (e₃ : F.obj Z ≅ Z') :
    (α •[h] β).map' F e₁ e₃ = (α.map' F e₁ e₂) •[h] (β.map' F e₂ e₃) := by
  simp only [map'_eq, map_comp]
  rw [γhmul_assoc_of_first_degree_eq_zero,
    γhmul_assoc_of_second_degree_eq_zero,
    γhmul_assoc_of_third_degree_eq_zero]
  conv_rhs =>
    congr
    · skip
    · rw [← γhmul_assoc_of_first_degree_eq_zero]
  rw [mk₀_comp, e₂.hom_inv_id, ← one_eq, one_γhmul]

def mapEquiv (X Y : C) (m : M) (F : C ⥤ D) [F.CommShift M] [F.Full] [F.Faithful] :
    ShiftedHom M X Y m ≃ ShiftedHom M (F.obj X) (F.obj Y) m where
  toFun x := x.map F
  invFun y := F.preimage (y ≫ (F.commShiftIso m).inv.app Y)
  left_inv x := by simp [map]
  right_inv y := by simp [map]

def mapAddEquiv (X Y : C) (m : M)  (F : C ⥤ D) [F.CommShift M] [F.Full] [F.Faithful]
    [Preadditive C] [Preadditive D] [F.Additive] :
    ShiftedHom M X Y m ≃+ ShiftedHom M (F.obj X) (F.obj Y) m where
  toEquiv := mapEquiv X Y m F
  map_add' _ _ := map_add _ _ _

noncomputable def map'Equiv (F : C ⥤ D) {X Y : C} {X' Y' : D}
    (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') (m : M) [F.CommShift M] [F.Full] [F.Faithful] :
    ShiftedHom M X Y m ≃ ShiftedHom M X' Y' m where
  toFun x := x.map' F e₁ e₂
  invFun y := (mapEquiv X Y m F).symm ((mk₀ e₁.hom (0 : M) rfl) •[zero_add m] (y •[add_zero m] (mk₀ e₂.inv (0 : M) rfl)))
  left_inv x := by
    apply (mapEquiv X Y m F).injective
    rw [Equiv.apply_symm_apply]
    dsimp only
    rw [map'_eq]
    rw [γhmul_assoc_of_first_degree_eq_zero,
      γhmul_assoc_of_second_degree_eq_zero, mk₀_comp, e₂.hom_inv_id, ← one_eq, γhmul_one,
      ← γhmul_assoc_of_first_degree_eq_zero, mk₀_comp, e₁.hom_inv_id, ← one_eq, one_γhmul]
    rfl
  right_inv y := by
    dsimp
    rw [map'_eq]
    apply comp_mk₀_injective e₂.inv
    apply mk₀_comp_injective e₁.hom
    rw [γhmul_assoc_of_first_degree_eq_zero, γhmul_assoc_of_second_degree_eq_zero,
      mk₀_comp, e₂.hom_inv_id, ← one_eq, γhmul_one,
      ← γhmul_assoc_of_first_degree_eq_zero, mk₀_comp, e₁.hom_inv_id, ← one_eq, one_γhmul]
    apply (mapEquiv X Y m F).apply_symm_apply

noncomputable def map'AddEquiv (F : C ⥤ D) {X Y : C} {X' Y' : D}
    (e₁ : F.obj X ≅ X') (e₂ : F.obj Y ≅ Y') (m : M) [F.CommShift M] [F.Full] [F.Faithful]
    [Preadditive C] [Preadditive D] [F.Additive]
    [∀ (a : M), (shiftFunctor D a).Additive] :
    ShiftedHom M X Y m ≃+ ShiftedHom M X' Y' m where
  toEquiv := map'Equiv F e₁ e₂ m
  map_add' x y := by
    dsimp [map'Equiv]
    rw [map'_eq, map_add, add_γhmul, γhmul_add, map'_eq, map'_eq]
=======
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Shifted morphisms

Given a category `C` endowed with a shift by an additive monoid `M` and two
objects `X` and `Y` in `C`, we consider the types `ShiftedHom X Y m`
defined as `X ⟶ (Y⟦m⟧)` for all `m : M`, and the composition on these
shifted hom.

## TODO

* redefine Ext-groups in abelian categories using `ShiftedHom` in the derived category.
* study the `R`-module structures on `ShiftedHom` when `C` is `R`-linear

-/

namespace CategoryTheory

open Category

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]

/-- In a category `C` equipped with a shift by an additive monoid,
this is the type of morphisms `X ⟶ (Y⟦n⟧)` for `m : M`. -/
def ShiftedHom (X Y : C) (m : M) : Type _ := X ⟶ (Y⟦m⟧)

instance [Preadditive C] (X Y : C) (n : M) : AddCommGroup (ShiftedHom X Y n) := by
  dsimp only [ShiftedHom]
  infer_instance

namespace ShiftedHom

variable {X Y Z T : C}

/-- The composition of `f : X ⟶ Y⟦a⟧` and `g : Y ⟶ Z⟦b⟧`, as a morphism `X ⟶ Z⟦c⟧`
when `b + a = c`. -/
noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom X Z c :=
  f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _

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

/-- The bijection `(X ⟶ Y) ≃ ShiftedHom X Y m₀` when `m₀ = 0`. -/
@[simps apply]
noncomputable def homEquiv (m₀ : M) (hm₀ : m₀ = 0) : (X ⟶ Y) ≃ ShiftedHom X Y m₀ where
  toFun f := mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]

lemma mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) :
    (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add_zero]) = f ≫ g := by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]
lemma mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a) :
    (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_zero]) = f := by
  simp [mk₀_comp]

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

@[simp 1100]
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

@[simp]
lemma id_map {a : M} (f : ShiftedHom X Y a) : f.map (𝟭 C) = f := by
  simp [map, Functor.commShiftIso, Functor.CommShift.iso]

lemma comp_map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
    (G : D ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f.map F).map G := by
  simp [map, Functor.commShiftIso_comp_hom_app]

lemma map_comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) (F : C ⥤ D) [F.CommShift M] :
    (f.comp g h).map F = (f.map F).comp (g.map F) h := by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc]
  erw [← NatTrans.naturality_assoc]
  simp only [Functor.comp_map, F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id, assoc]
>>>>>>> origin/ext-change-of-universes

end ShiftedHom

end CategoryTheory
