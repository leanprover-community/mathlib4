import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Simple
import Mathlib.Order.JordanHolder
import Mathlib.RingTheory.SimpleModule.Basic

open CategoryTheory Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] (X Y : C) {x : Subobject X}

/-- An object is simple when it has only two subobjects, `⊥` and `⊤`. -/
@[mk_iff] class IsSimpleSubobject extends
  IsSimpleOrder (Subobject X)

theorem IsSimpleSubobject.congr (e : X ≅ Y) [IsSimpleSubobject X] : IsSimpleSubobject Y where
  __ := (Subobject.mapIsoToOrderIso e.symm).isSimpleOrder

theorem IsSimpleSubobject_iff_isAtom : IsSimpleSubobject (x : C) ↔ IsAtom x := by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom, isSimpleSubobject_iff]
  exact x.subobjectOrderIso.isSimpleOrder_iff

theorem IsSimpleSubobject_iff_isCoatom : IsSimpleSubobject (cokernel x.arrow) ↔ IsCoatom x := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom, isSimpleSubobject_iff]
  refine OrderIso.isSimpleOrder_iff ?_
  sorry

theorem covBy_iff_quot_is_simple' {A B : Subobject X} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleSubobject (cokernel (A.ofLE B hAB)) := sorry

#check Submodule.comapMkQRelIso

/-
Given `Y ⊆ X` correspondence `{ subobjects of X⧸Y } ↔ { subobjects of X containing Y }`
-/

noncomputable
def Subobject.image {X Y : C} (f : X ⟶ Y) : Subobject X ⟶ Subobject Y := by
  refine ↾?_
  intro X'
  exact Subobject.mk (Limits.image.ι (X'.arrow ≫ f))
  --have : (Subobject.exists f).obj X' = Subobject.mk (Limits.image.ι (X'.arrow ≫ f)) := sorry --true?

noncomputable
def Subobject.inverseImage {X Y : C} (f : X ⟶ Y) : Subobject Y ⟶ Subobject X :=
  ↾ fun Y' ↦ Subobject.mk (kernel.ι (f ≫ cokernel.π Y'.arrow))

noncomputable
def Subobject.temp_iso (Y : Subobject X) : Subobject (cokernel Y.arrow) ≃o Set.Ici Y where
  toFun p' := ⟨inverseImage (cokernel.π Y.arrow) p', by
    refine le_of_comm ?_ ?_
    · apply?
      sorry
    · sorry⟩
  invFun q := sorry
  left_inv p' := sorry
  right_inv := sorry
  map_rel_iff' := sorry

#check IsModularLattice

instance temp₀ (X : C) : IsModularLattice (Subobject X) where
  sup_inf_le_assoc_of_le := sorry

instance temp₁ (X : C) : JordanHolderLattice (Subobject X) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := inf_covBy_of_covBy_sup_of_covBy_sup_left
  Iso X Y := sorry
  iso_symm := sorry
  iso_trans := sorry
  second_iso {X} {Y} _ := sorry
