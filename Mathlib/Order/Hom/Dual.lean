/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Hom.Lattice

/-!
# Duals of order homomorphisms

-/

assert_not_exists HeytingAlgebra

open Function OrderDual

variable {F ι α β γ δ : Type*}

/-! ### Dual homs -/

namespace SupHom

variable [Max α] [Max β] [Max γ]

/-- Reinterpret a supremum homomorphism as an infimum homomorphism between the dual lattices. -/
@[simps]
protected def dual : SupHom α β ≃ InfHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_sup'⟩
  invFun f := ⟨f, f.map_inf'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem dual_id : SupHom.dual (SupHom.id α) = InfHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : SupHom β γ) (f : SupHom α β) :
    SupHom.dual (g.comp f) = (SupHom.dual g).comp (SupHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : SupHom.dual.symm (InfHom.id _) = SupHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : InfHom βᵒᵈ γᵒᵈ) (f : InfHom αᵒᵈ βᵒᵈ) :
    SupHom.dual.symm (g.comp f) =
      (SupHom.dual.symm g).comp (SupHom.dual.symm f) :=
  rfl

end SupHom

namespace InfHom

variable [Min α] [Min β] [Min γ]

/-- Reinterpret an infimum homomorphism as a supremum homomorphism between the dual lattices. -/
@[simps]
protected def dual : InfHom α β ≃ SupHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨f, f.map_inf'⟩
  invFun f := ⟨f, f.map_sup'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem dual_id : InfHom.dual (InfHom.id α) = SupHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : InfHom β γ) (f : InfHom α β) :
    InfHom.dual (g.comp f) = (InfHom.dual g).comp (InfHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : InfHom.dual.symm (SupHom.id _) = InfHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : SupHom βᵒᵈ γᵒᵈ) (f : SupHom αᵒᵈ βᵒᵈ) :
    InfHom.dual.symm (g.comp f) =
      (InfHom.dual.symm g).comp (InfHom.dual.symm f) :=
  rfl

end InfHom

namespace SupBotHom

variable [Max α] [Bot α] [Max β] [Bot β] [Max γ] [Bot γ]

/-- Reinterpret a finitary supremum homomorphism as a finitary infimum homomorphism between the dual
lattices. -/
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem dual_id : SupBotHom.dual (SupBotHom.id α) = InfTopHom.id _ := rfl

@[simp]
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) :
    SupBotHom.dual (g.comp f) = (SupBotHom.dual g).comp (SupBotHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) :
    SupBotHom.dual.symm (g.comp f) =
      (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f) :=
  rfl

end SupBotHom

namespace InfTopHom

variable [Min α] [Top α] [Min β] [Top β] [Min γ] [Top γ]

/-- Reinterpret a finitary infimum homomorphism as a finitary supremum homomorphism between the dual
lattices. -/
@[simps]
protected def dual : InfTopHom α β ≃ SupBotHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_top'⟩
  invFun f := ⟨InfHom.dual.symm f.toSupHom, f.map_bot'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem dual_id : InfTopHom.dual (InfTopHom.id α) = SupBotHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : InfTopHom β γ) (f : InfTopHom α β) :
    InfTopHom.dual (g.comp f) = (InfTopHom.dual g).comp (InfTopHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : InfTopHom.dual.symm (SupBotHom.id _) = InfTopHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : SupBotHom βᵒᵈ γᵒᵈ) (f : SupBotHom αᵒᵈ βᵒᵈ) :
    InfTopHom.dual.symm (g.comp f) =
      (InfTopHom.dual.symm g).comp (InfTopHom.dual.symm f) :=
  rfl

end InfTopHom

namespace LatticeHom

variable [Lattice α] [Lattice β] [Lattice γ]

/-- Reinterpret a lattice homomorphism as a lattice homomorphism between the dual lattices. -/
@[simps]
protected def dual : LatticeHom α β ≃ LatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨InfHom.dual f.toInfHom, f.map_sup'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_sup'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem dual_id : LatticeHom.dual (LatticeHom.id α) = LatticeHom.id _ := rfl

@[simp]
theorem dual_comp (g : LatticeHom β γ) (f : LatticeHom α β) :
    LatticeHom.dual (g.comp f) = (LatticeHom.dual g).comp (LatticeHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id : LatticeHom.dual.symm (LatticeHom.id _) = LatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : LatticeHom βᵒᵈ γᵒᵈ) (f : LatticeHom αᵒᵈ βᵒᵈ) :
    LatticeHom.dual.symm (g.comp f) =
      (LatticeHom.dual.symm g).comp (LatticeHom.dual.symm f) :=
  rfl

end LatticeHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps]
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem dual_id : BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLatticeHom.id _ :=
  rfl

@[simp]
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    BoundedLatticeHom.dual (g.comp f) =
      (BoundedLatticeHom.dual g).comp (BoundedLatticeHom.dual f) :=
  rfl

@[simp]
theorem symm_dual_id :
    BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl

@[simp]
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) =
      (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl

end BoundedLatticeHom
