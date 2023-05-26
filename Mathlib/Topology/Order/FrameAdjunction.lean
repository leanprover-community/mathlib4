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

/- Definition of the functor `pt` --/

/- `points_of_frame L` is the type of points of a frame `L`, where a *point* of a frame is,
   by definition, a frame homomorphism to the frame `Prop`. -/
@[reducible]
def pt_obj (L : Type _) [Order.Frame L] := FrameHom L Prop

/- The frame homomorphism `open_of_element_hom` from a frame L to
   the frame `Set (points_of_frame L)`. -/
def open_of_element_hom (L : Type _) [Order.Frame L] : FrameHom L (Set (pt_obj L)) where
  toFun u :=  {x | x u}
  map_inf' a b := by simp; rfl
  map_top'     := by simp; rfl
  map_sSup' S  := by {
    simp
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

/- The topology on the set of points. -/
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

lemma open_in_pt_space_iff (L : Type _) [Order.Frame L] (U : Set (pt_obj L)) :
  IsOpen U ↔ ∃ u : L, U = {x : pt_obj L | x u} := by
  unfold IsOpen TopologicalSpace.IsOpen ptTop Set.range setOf; tauto

--the map from a frame L to the opens of the points of L
--probably could use a better name
def pt_open (L : Type _) [Order.Frame L] (l : L) : Opens (pt_obj L) where
  carrier := open_of_element_hom L l
  is_open' := by use l; rfl

/- The action of the functor `pt` on frame homomorphisms. -/
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

/- Definition of the functor `𝒪`. -/
def 𝒪 : TopCat ⥤ FrmCatᵒᵖ where
  obj X := ⟨Opens X.α, by infer_instance⟩
  map {X Y} f := by apply Opposite.op; exact Opens.comap f

-- TODO: is this in the library?
lemma elim_exists_prop (A : Prop → Prop) : (∃ p, (A p) ∧ p) ↔ (A True) := by aesop

def frame_point_of_space_point (X : Type _) [TopologicalSpace X] (x : X) : FrameHom (Opens X) Prop where
  toFun u := x ∈ u
  map_inf' a b := by simp; rfl
  map_top'     := by simp; rfl
  map_sSup' S  := by simp [elim_exists_prop, iff_true]

-- lemma inv_img_of_open (X : Type _) [τ : TopologicalSpace X] (U : Set (pt_obj (Opens X))) : frame_point_of_space_point X ⁻¹' U = U := sorry

/- The continuous function from a topological space `X` to `pt 𝒪 X`.-/
def neighborhoods (X : Type _) [τ : TopologicalSpace X] : ContinuousMap X (pt_obj (Opens X)) where
  toFun := frame_point_of_space_point X
  continuous_toFun := by
    rw [continuous_def]; intro U; rw[open_in_pt_space_iff]
    intro h
    cases' h with u hu
    rw [hu]
    have key : frame_point_of_space_point X ⁻¹' { x | x u } = u := by {
      ext x
      simp
      aesop_subst hu
      tauto
    }
    rw [key]
    exact u.2

def counit_app_cont (L : FrmCat) : FrameHom L (Opens (FrameHom L Prop)) where
  toFun := pt_open L
  map_inf' := sorry
  map_top' := sorry
  map_sSup' := sorry

def counit_app (L : FrmCatᵒᵖ) : (pt.comp 𝒪).obj L ⟶ L where
  unop := counit_app_cont L.unop

def counit : pt.comp 𝒪 ⟶ 𝟭 FrmCatᵒᵖ where
  app := counit_app
  naturality := sorry

def unit_frame_hom (X : TopCat) (x : X) : FrameHom (Opens ↑X) Prop where
  toFun U := x ∈ U
  map_inf' := sorry
  map_top' := sorry
  map_sSup' := sorry

def unit_app (X : TopCat) : X ⟶ (𝒪.comp pt).obj X where
  toFun x := unit_frame_hom X x
  continuous_toFun := sorry

def unit : 𝟭 TopCat ⟶ 𝒪.comp pt where
  app := unit_app --by dsimp; ⟨λ x => $ λ U => x ∈ U, by sorry⟩
  naturality := sorry

def unitCounit : Adjunction.CoreUnitCounit 𝒪 pt where
 unit := unit
 counit := counit
 left_triangle := sorry --aesop will automatically solve these
 right_triangle := sorry--if definitions are good enough

-- the final goal
theorem frame_top_adjunction : 𝒪 ⊣ pt := Adjunction.mkOfUnitCounit unitCounit
