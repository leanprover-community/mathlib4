import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.Basic
import Mathlib.Topology.Bases
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
  map_sSup' S  := by {
    simp only [map_sSup, sSup_Prop_eq, Set.mem_image, eq_iff_iff,
               Set.sSup_eq_sUnion, Set.sUnion_image]
    ext Z
    constructor
    . rintro ⟨p, ⟨x, hx, hp⟩, h⟩
      aesop_subst hp
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      exact ⟨x, hx, h⟩
    . rintro ⟨S', ⟨x, h⟩, hxZ⟩
      subst h
      use true
      simp only [iff_true, and_true]
      obtain ⟨S', h⟩ := hxZ
      simp only [Set.mem_range, exists_prop] at h
      obtain ⟨⟨hx, hS'⟩, hxZ⟩ := h
      subst hS'
      exact ⟨x, hx, hxZ⟩
  }

-- pt L is a topological space
instance ptTop (L : Type _) [Order.Frame L] : TopologicalSpace (pt_obj L) where
  IsOpen := Set.range fun u ↦ { x : pt_obj L | x u }
  isOpen_univ := ⟨⊤, by simp only [map_top]; exact rfl⟩
  isOpen_inter := by
    rintro s t ⟨u, hs⟩ ⟨v, ht⟩
    subst hs ht
    use u ⊓ v
    ext p
    simp only [ge_iff_le, map_inf, le_Prop_eq, inf_Prop_eq,
               Set.mem_setOf_eq, Set.mem_inter_iff]
  isOpen_sUnion := by
    intro U hU
    use (sSup { u | { x | x u } ∈ U })
    ext p
    simp only [map_sSup, sSup_Prop_eq, Set.mem_image, Set.mem_setOf_eq,
               eq_iff_iff, Set.mem_sUnion]
    constructor
    . rintro ⟨P, ⟨u, hu, hP⟩, h⟩
      aesop_subst hP
      exact ⟨{ x | x u }, hu, h⟩
    . rintro ⟨t, ht, hp⟩
      use true
      simp only [iff_true, and_true]
      obtain ⟨u, h⟩ := hU t ht
      subst h
      exact ⟨u, ht, hp⟩

@[reducible]
def pt_map {L L' : Type _} [Order.Frame L] [Order.Frame L']
  (f : FrameHom L' L) : C(pt_obj L, pt_obj L') where
  toFun := fun p ↦ p.comp f
  continuous_toFun := ⟨by
    rintro s ⟨u, hu⟩
    subst hu
    use f u
    ext p
    simp only [Set.mem_setOf_eq, Set.preimage_setOf_eq, FrameHom.comp_apply]⟩


def pt : FrmCatᵒᵖ ⥤ TopCat where
  obj L    := ⟨FrameHom L.unop Prop, by infer_instance⟩
  map f    := pt_map f.unop

set_option trace.Meta.synthInstance true in
def 𝒪 : TopCat ⥤ FrmCatᵒᵖ where
  obj X := ⟨Opens X.α, by infer_instance⟩
  map {X Y} f :=
  @Opposite.op
      (Bundled.mk (Opens ↑Y) (@Opens.instFrameOpens (↑Y) _)
       ⟶ (Bundled.mk (Opens ↑X) (@Opens.instFrameOpens (↑X) _)))
      (Opens.comap f)

set_option pp.explicit true
#print 𝒪

-- the final goal
theorem frame_top_adjunction : pt ⊣ 𝒪 := sorry


#check Adjunction.mkOfUnitCounit
