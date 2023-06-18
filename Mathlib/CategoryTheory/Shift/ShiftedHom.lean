import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.GradedType

namespace CategoryTheory

open Category Preadditive

variable {C : Type _} [Category C] (M : Type _) [AddCommMonoid M] [HasShift C M]

def ShiftedHom (X Y : C) : GradedType M := fun (n : M) => X ⟶ (Y⟦n⟧)

instance [Preadditive C] (X Y : C) (n : M) : AddCommGroup (ShiftedHom M X Y n) := by
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
lemma γhmul_zsmul [Preadditive C] [∀ (a : M), (shiftFunctor C a).Additive]
    {p q n : M} (α : ShiftedHom M X Y p) (x : ℤ)
    (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    α •[hpq] (x • β) = x • (α •[hpq] β) := by
  rw [γhmul_eq, γhmul_eq, Functor.map_zsmul, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul]

@[simp]
lemma zsmul_γhmul [Preadditive C]
    {p q n : M} (x : ℤ) (α : ShiftedHom M X Y p)
    (β : ShiftedHom M Y Z q) (hpq : p + q = n) :
    (x • α) •[hpq] β = x • (α •[hpq] β) := by
  rw [γhmul_eq, γhmul_eq, Preadditive.zsmul_comp]

instance {X₁ X₂ X₃ X₄ : C} : IsAssocGradedHMul (ShiftedHom M X₁ X₂)
    (ShiftedHom M X₂ X₃) (ShiftedHom M X₃ X₄) (ShiftedHom M X₁ X₃) (ShiftedHom M X₂ X₄)
    (ShiftedHom M X₁ X₄) where
  γhmul_assoc a b c α β γ ab bc abc hab hbc habc := by
    simp only [γhmul_eq, assoc, Functor.map_comp]
    rw [shiftFunctorAdd'_assoc_inv_app c b a bc ab abc] ; rotate_left
    . rw [add_comm b a, hab]
    . rw [add_assoc, add_comm b a, hab, add_comm c, habc]
    dsimp
    rw [← NatTrans.naturality_assoc]
    rfl

end ShiftedHom

end CategoryTheory
