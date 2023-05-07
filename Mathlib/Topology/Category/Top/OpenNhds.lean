/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.category.Top.open_nhds
! leanprover-community/mathlib commit 1ec4876214bf9f1ddfbf97ae4b0d777ebd5d6938
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Top.Opens

/-!
# The category of open neighborhoods of a point

Given an object `X` of the category `Top` of topological spaces and a point `x : X`, this file
builds the type `open_nhds x` of open neighborhoods of `x` in `X` and endows it with the partial
order given by inclusion and the corresponding category structure (as a full subcategory of the
poset category `set X`). This is used in `topology.sheaves.stalks` to build the stalk of a sheaf
at `x` as a limit over `open_nhds x`.

## Main declarations

Besides `open_nhds`, the main constructions here are:

* `inclusion (x : X)`: the obvious functor `open_nhds x ⥤ opens X`
* `functor_nhds`: An open map `f : X ⟶ Y` induces a functor `open_nhds x ⥤ open_nhds (f x)`
* `adjunction_nhds`: An open map `f : X ⟶ Y` induces an adjunction between `open_nhds x` and
                     `open_nhds (f x)`.
-/


open CategoryTheory

open TopologicalSpace

open Opposite

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

namespace TopologicalSpace

/-- The type of open neighbourhoods of a point `x` in a (bundled) topological space. -/
def OpenNhds (x : X) :=
  FullSubcategory fun U : Opens X => x ∈ U
#align topological_space.open_nhds TopologicalSpace.OpenNhds

namespace OpenNhds

instance (x : X) : PartialOrder (OpenNhds x)
    where
  le U V := U.1 ≤ V.1
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ i j := FullSubcategory.ext _ _ <| le_antisymm i j

instance (x : X) : Lattice (OpenNhds x) :=
  { OpenNhds.partialOrder x with
    inf := fun U V => ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩
    le_inf := fun U V W => @le_inf _ _ U.1.1 V.1.1 W.1.1
    inf_le_left := fun U V => @inf_le_left _ _ U.1.1 V.1.1
    inf_le_right := fun U V => @inf_le_right _ _ U.1.1 V.1.1
    sup := fun U V => ⟨U.1 ⊔ V.1, V.1.1.mem_union_left U.2⟩
    sup_le := fun U V W => @sup_le _ _ U.1.1 V.1.1 W.1.1
    le_sup_left := fun U V => @le_sup_left _ _ U.1.1 V.1.1
    le_sup_right := fun U V => @le_sup_right _ _ U.1.1 V.1.1 }

instance (x : X) : OrderTop (OpenNhds x)
    where
  top := ⟨⊤, trivial⟩
  le_top _ := le_top

instance (x : X) : Inhabited (OpenNhds x) :=
  ⟨⊤⟩

instance openNhdsCategory (x : X) : Category.{u} (OpenNhds x) :=
  by
  unfold open_nhds
  infer_instance
#align topological_space.open_nhds.open_nhds_category TopologicalSpace.OpenNhds.openNhdsCategory

instance opensNhdsHomHasCoeToFun {x : X} {U V : OpenNhds x} : CoeFun (U ⟶ V) fun _ => U.1 → V.1 :=
  ⟨fun f x => ⟨x, f.le x.2⟩⟩
#align topological_space.open_nhds.opens_nhds_hom_has_coe_to_fun TopologicalSpace.OpenNhds.opensNhdsHomHasCoeToFun

/-- The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def infLeLeft {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ U :=
  homOfLE inf_le_left
#align topological_space.open_nhds.inf_le_left TopologicalSpace.OpenNhds.infLeLeft

/-- The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def infLeRight {x : X} (U V : OpenNhds x) : U ⊓ V ⟶ V :=
  homOfLE inf_le_right
#align topological_space.open_nhds.inf_le_right TopologicalSpace.OpenNhds.infLeRight

/-- The inclusion functor from open neighbourhoods of `x`
to open sets in the ambient topological space. -/
def inclusion (x : X) : OpenNhds x ⥤ Opens X :=
  fullSubcategoryInclusion _
#align topological_space.open_nhds.inclusion TopologicalSpace.OpenNhds.inclusion

@[simp]
theorem inclusion_obj (x : X) (U) (p) : (inclusion x).obj ⟨U, p⟩ = U :=
  rfl
#align topological_space.open_nhds.inclusion_obj TopologicalSpace.OpenNhds.inclusion_obj

theorem openEmbedding {x : X} (U : OpenNhds x) : OpenEmbedding U.1.inclusion :=
  U.1.OpenEmbedding
#align topological_space.open_nhds.open_embedding TopologicalSpace.OpenNhds.openEmbedding

/-- The preimage functor from neighborhoods of `f x` to neighborhoods of `x`. -/
def map (x : X) : OpenNhds (f x) ⥤ OpenNhds x
    where
  obj U := ⟨(Opens.map f).obj U.1, U.2⟩
  map U V i := (Opens.map f).map i
#align topological_space.open_nhds.map TopologicalSpace.OpenNhds.map

@[simp]
theorem map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(Opens.map f).obj U, by tidy⟩ :=
  rfl
#align topological_space.open_nhds.map_obj TopologicalSpace.OpenNhds.map_obj

@[simp]
theorem map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U := by tidy
#align topological_space.open_nhds.map_id_obj TopologicalSpace.OpenNhds.map_id_obj

@[simp]
theorem map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
  rfl
#align topological_space.open_nhds.map_id_obj' TopologicalSpace.OpenNhds.map_id_obj'

@[simp]
theorem map_id_obj_unop (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U := by
  simp
#align topological_space.open_nhds.map_id_obj_unop TopologicalSpace.OpenNhds.map_id_obj_unop

@[simp]
theorem op_map_id_obj (x : X) (U : (OpenNhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U := by simp
#align topological_space.open_nhds.op_map_id_obj TopologicalSpace.OpenNhds.op_map_id_obj

/-- `opens.map f` and `open_nhds.map f` form a commuting square (up to natural isomorphism)
with the inclusion functors into `opens X`. -/
def inclusionMapIso (x : X) : inclusion (f x) ⋙ Opens.map f ≅ map f x ⋙ inclusion x :=
  NatIso.ofComponents (fun U => by constructor; exact 𝟙 _; exact 𝟙 _) (by tidy)
#align topological_space.open_nhds.inclusion_map_iso TopologicalSpace.OpenNhds.inclusionMapIso

@[simp]
theorem inclusionMapIso_hom (x : X) : (inclusionMapIso f x).Hom = 𝟙 _ :=
  rfl
#align topological_space.open_nhds.inclusion_map_iso_hom TopologicalSpace.OpenNhds.inclusionMapIso_hom

@[simp]
theorem inclusionMapIso_inv (x : X) : (inclusionMapIso f x).inv = 𝟙 _ :=
  rfl
#align topological_space.open_nhds.inclusion_map_iso_inv TopologicalSpace.OpenNhds.inclusionMapIso_inv

end OpenNhds

end TopologicalSpace

namespace IsOpenMap

open TopologicalSpace

variable {f}

/-- An open map `f : X ⟶ Y` induces a functor `open_nhds x ⥤ open_nhds (f x)`.
-/
@[simps]
def functorNhds (h : IsOpenMap f) (x : X) : OpenNhds x ⥤ OpenNhds (f x)
    where
  obj U := ⟨h.Functor.obj U.1, ⟨x, U.2, rfl⟩⟩
  map U V i := h.Functor.map i
#align is_open_map.functor_nhds IsOpenMap.functorNhds

/-- An open map `f : X ⟶ Y` induces an adjunction between `open_nhds x` and `open_nhds (f x)`.
-/
def adjunctionNhds (h : IsOpenMap f) (x : X) : IsOpenMap.functorNhds h x ⊣ OpenNhds.map f x :=
  Adjunction.mkOfUnitCounit
    { Unit := { app := fun U => homOfLE fun x hxU => ⟨x, hxU, rfl⟩ }
      counit := { app := fun V => homOfLE fun y ⟨x, hfxV, hxy⟩ => hxy ▸ hfxV } }
#align is_open_map.adjunction_nhds IsOpenMap.adjunctionNhds

end IsOpenMap

