import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Order.Category.FrmCat

open CategoryTheory
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

-- this should be FrmCat.op but don't know syntax
def pt : FrmCat ⥤ TopCat where
  obj L := ⟨ FrameHom L Prop, by infer_instance⟩
  map    := sorry
  map_id := sorry
  map_comp := sorry

-- the final goal
theorem frame_top_adjunction : pt ⊣ 𝒪 := sorry
