import Mathlib.CategoryTheory.GroupObjects.Basic
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Yoneda
open CategoryTheory Limits

namespace CategoryTheory.Functor
universe v u v₁ u₁
variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]

variable [HasFiniteProducts C] [HasFiniteProducts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F]

@[simps]
noncomputable def mapGroupObjectObj (G : GroupObject C) : GroupObject D where
  X := F.obj G.X
  one := (PreservesTerminal.iso F).inv ≫ F.map G.one
  mul := (PreservesLimitPair.iso F _ _).inv ≫ F.map G.mul
  inv := F.map G.inv
  one_mul := by
    rw [prod.map_comp_id]
    slice_lhs 2 3 =>
      rw [PreservesLimitPair.iso_inv, ← F.map_id, ← prodComparison_inv_natural]
    simp [← F.map_comp, inv_prodComparison_map_snd]
  mul_one := by
    rw [prod.map_id_comp]
    slice_lhs 2 3 =>
      rw [PreservesLimitPair.iso_inv, ← F.map_id, ← prodComparison_inv_natural]
    simp [← F.map_comp, inv_prodComparison_map_fst]
  mul_assoc := by
    rw [prod.map_comp_id, prod.map_id_comp]
    simp only [PreservesLimitPair.iso_inv]
    slice_lhs 2 3 =>
      rw [← F.map_id, ← prodComparison_inv_natural]
    slice_lhs 3 4 =>
      rw [← F.map_comp, G.mul_assoc]
    have := PreservesLimitsPair.iso.inv_comp_prod.associator G.X G.X G.X F
    simp only [PreservesLimitPair.iso_inv] at this
    simp only [F.map_comp]
    slice_lhs 1 3 =>
      rw [this]
    slice_rhs 3 4 =>
      rw [← F.map_id, ← prodComparison_inv_natural]
    simp only [Category.assoc]
    rfl
  mul_left_inv := by
    slice_lhs 1 2 =>
      rw [← F.map_id, PreservesLimitPair.iso.inv_comp_lift]
    rw [← F.map_comp, G.mul_left_inv]
    simp only [Functor.map_comp, PreservesTerminal.iso_inv]
    rw [← Category.assoc, default_comp_inv_terminalComparison]

@[simps]
def mapGroupObjectMap {X Y : GroupObject C}
    (f : X ⟶ Y) : F.mapGroupObjectObj X ⟶ F.mapGroupObjectObj Y  where
  hom := F.map f.hom
  one_hom := by simp [← F.map_comp]
  mul_hom := by
    simp only [mapGroupObjectObj_X, mapGroupObjectObj_mul, PreservesLimitPair.iso_inv,
      Category.assoc, IsIso.inv_comp_eq]
    rw [← F.map_comp]
    slice_rhs 2 3 =>
      rw [← prodComparison_inv_natural]
    simp
  inv_hom := by
    simp only [mapGroupObjectObj_X, mapGroupObjectObj_inv]
    rw [← F.map_comp, f.inv_hom, F.map_comp]

@[simps]
noncomputable def mapGroupObject : GroupObject C ⥤ GroupObject D where
  obj X := mapGroupObjectObj F X
  map f := mapGroupObjectMap F f
  map_id X := by ext; simp
  map_comp f g := by ext; simp

noncomputable abbrev groupYoneda : GroupObject C ⥤ GroupObject (Cᵒᵖ ⥤ Type v) :=
  mapGroupObject (yoneda (C := C))

end CategoryTheory.Functor
