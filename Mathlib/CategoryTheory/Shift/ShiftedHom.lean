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

end ShiftedHom

end CategoryTheory
