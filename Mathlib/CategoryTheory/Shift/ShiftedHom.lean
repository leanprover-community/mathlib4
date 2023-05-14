import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Algebra.GradedType

namespace CategoryTheory

open Category

variable {C : Type _} [Category C] (M : Type _) [AddMonoid M] [HasShift C M]

def ShiftedHom (X Y : C) : GradedType M := fun (n : M) => X ⟶ (Y⟦n⟧)

-- note the order of the composition (this is motivated by signs conventions)

noncomputable instance (X Y Z : C ) :
    HasGradedHSMul (ShiftedHom M Y Z) (ShiftedHom M X Y) (ShiftedHom M X Z) where
  γhsmul' p q n h α β := β ≫ α⟦q⟧' ≫ (shiftFunctorAdd' C p q n h).inv.app _

namespace ShiftedHom

variable {X Y : C} (f : X ⟶ Y)

noncomputable def mk₀ : ShiftedHom M X Y 0 := f ≫ (shiftFunctorZero C M).inv.app Y

noncomputable instance : One (ShiftedHom M X X 0) := ⟨mk₀ M (𝟙 _)⟩

lemma one_eq (X : C) : (1 : ShiftedHom M X X 0) = (shiftFunctorZero C M).inv.app X :=
  id_comp _

variable {M}

lemma γhsmul_eq {p q : M} (α : ShiftedHom M Y Z p) (β : ShiftedHom M X Y q) (n : M)
  (hpq : p + q = n) :
  α •[hpq] β = β ≫ α⟦q⟧' ≫ (shiftFunctorAdd' C p q n hpq).inv.app _ := rfl

@[simp]
lemma one_γhsmul {n : M} (β : ShiftedHom M X Y n) :
    (1 : ShiftedHom M Y Y 0) •[zero_add n] β = β := by
  simp only [γhsmul_eq, one_eq, shiftFunctorAdd'_zero_add_inv_app, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, comp_id]

@[simp]
lemma γhsmul_one {n : M} (α : ShiftedHom M X Y n) :
    α •[add_zero n] (1 : ShiftedHom M X X 0) = α := by
  dsimp
  rw [γhsmul_eq]
  simp only [one_eq, shiftFunctorAdd'_add_zero_inv_app,
    NatTrans.naturality, Functor.id_obj, Functor.id_map, Iso.inv_hom_id_app_assoc]

instance {X₁ X₂ X₃ X₄ : C} : IsAssocGradedHSMul (ShiftedHom M X₃ X₄)
    (ShiftedHom M X₂ X₃) (ShiftedHom M X₁ X₂) (ShiftedHom M X₂ X₄) (ShiftedHom M X₁ X₃)
    (ShiftedHom M X₁ X₄) where
  γhsmul_assoc a b c α β γ ab bc abc hab hbc habc := by
    simp only [γhsmul_eq, assoc, Functor.map_comp,
      shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc (by rw [hab, habc])]
    dsimp
    rw [← NatTrans.naturality_assoc]
    rfl

end ShiftedHom

end CategoryTheory
