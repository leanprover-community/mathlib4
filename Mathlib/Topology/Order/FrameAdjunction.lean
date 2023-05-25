import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Order.Category.FrmCat

open CategoryTheory Topology TopologicalSpace
universe u
variable (X : Type u)

-- pt functor on objects
@[reducible]
def pt_obj (L : Type _) [Order.Frame L] := FrameHom L Prop

-- unit
def open_of_element_hom (L : Type _) [Order.Frame L] : FrameHom L (Set (pt_obj L)) where
  toFun u :=  {x | x u}
  map_inf' a b := by simp; rfl
  map_top'     := by simp; rfl
  map_sSup' S  := by
    simp; sorry

-- pt L is a topological space
instance ptTop (L : Type _) [Order.Frame L] : TopologicalSpace (pt_obj L) where
  IsOpen := sorry
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

def pt : FrmCatᵒᵖ ⥤ TopCat where
  obj L := ⟨ FrameHom L.unop Prop, by infer_instance⟩
  map    := sorry
  map_id := sorry
  map_comp := sorry


def 𝒪 : TopCat ⥤ FrmCatᵒᵖ where
  obj X := ⟨Opens X, by infer_instance⟩
  map := sorry
  map_id := sorry
  map_comp := sorry

-- the final goal
theorem frame_top_adjunction : pt ⊣ 𝒪 := sorry


#check Adjunction.mkOfUnitCounit
