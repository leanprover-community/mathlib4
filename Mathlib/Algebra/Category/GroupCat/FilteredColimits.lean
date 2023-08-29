/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.Algebra.Category.MonCat.FilteredColimits

#align_import algebra.category.Group.filtered_colimits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ GroupCat`.
We show that the colimit of `F ⋙ forget₂ GroupCat MonCat` (in `MonCat`) carries the structure of a
group,
thereby showing that the forgetful functor `forget₂ GroupCat MonCat` preserves filtered colimits.
In particular, this implies that `forget GroupCat` preserves filtered colimits.
Similarly for `AddGroupCat`, `CommGroupCat` and `AddCommGroupCat`.

-/

set_option linter.uppercaseLean3 false

universe v u

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace GroupCat.FilteredColimits

section

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

-- Mathlib3 used parameters here, mainly so we could have the abbreviations `G` and `G.mk` below,
-- without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GroupCat.{max v u})

/-- The colimit of `F ⋙ forget₂ GroupCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive
  "The colimit of `F ⋙ forget₂ AddGroupCat AddMonCat` in the category `AddMonCat`.
  In the following, we will show that this has the structure of an additive group."]
noncomputable abbrev G : MonCat :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ GroupCat MonCat.{max v u})
#align Group.filtered_colimits.G GroupCat.FilteredColimits.G
#align AddGroup.filtered_colimits.G AddGroupCat.FilteredColimits.G

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbrev G.mk : (Σ j, F.obj j) → G.{v, u} F :=
  Quot.mk (Types.Quot.Rel.{v, u} (F ⋙ forget GroupCat.{max v u}))
#align Group.filtered_colimits.G.mk GroupCat.FilteredColimits.G.mk
#align AddGroup.filtered_colimits.G.mk AddGroupCat.FilteredColimits.G.mk

@[to_additive]
theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    G.mk.{v, u} F x = G.mk F y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget GroupCat) x y h)
#align Group.filtered_colimits.G.mk_eq GroupCat.FilteredColimits.G.mk_eq
#align AddGroup.filtered_colimits.G.mk_eq AddGroupCat.FilteredColimits.G.mk_eq

/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive "The \"unlifted\" version of negation in the colimit."]
def colimitInvAux (x : Σ j, F.obj j) : G.{v, u} F :=
  G.mk F ⟨x.1, x.2⁻¹⟩
#align Group.filtered_colimits.colimit_inv_aux GroupCat.FilteredColimits.colimitInvAux
#align AddGroup.filtered_colimits.colimit_neg_aux AddGroupCat.FilteredColimits.colimitNegAux

@[to_additive]
theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel.{v, u} (F ⋙ forget GroupCat) x y) :
    colimitInvAux.{v, u} F x = colimitInvAux F y := by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [MonoidHom.map_inv, MonoidHom.map_inv, inv_inj]
  exact hfg
#align Group.filtered_colimits.colimit_inv_aux_eq_of_rel GroupCat.FilteredColimits.colimitInvAux_eq_of_rel
#align AddGroup.filtered_colimits.colimit_neg_aux_eq_of_rel AddGroupCat.FilteredColimits.colimitNegAux_eq_of_rel

/-- Taking inverses in the colimit. See also `colimitInvAux`. -/
@[to_additive "Negation in the colimit. See also `colimitNegAux`."]
instance colimitInv : Inv (G.{v, u} F) where
  inv x := by
    refine' Quot.lift (colimitInvAux.{v, u} F) _ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_quot_rel
    exact h
#align Group.filtered_colimits.colimit_has_inv GroupCat.FilteredColimits.colimitInv
#align AddGroup.filtered_colimits.colimit_has_neg AddGroupCat.FilteredColimits.colimitNeg

@[to_additive (attr := simp)]
theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩ :=
  rfl
#align Group.filtered_colimits.colimit_inv_mk_eq GroupCat.FilteredColimits.colimit_inv_mk_eq
#align AddGroup.filtered_colimits.colimit_neg_mk_eq AddGroupCat.FilteredColimits.colimit_neg_mk_eq

@[to_additive]
noncomputable instance colimitGroup : Group (G.{v, u} F) :=
  { colimitInv.{v, u} F, (G.{v, u} F).str with
    mul_left_inv := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      cases' x with j x
      erw [colimit_inv_mk_eq,
        colimit_mul_mk_eq (F ⋙ forget₂ GroupCat MonCat.{max v u}) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq (F ⋙ forget₂ GroupCat MonCat.{max v u}) j]
      dsimp
      erw [CategoryTheory.Functor.map_id, mul_left_inv] }
#align Group.filtered_colimits.colimit_group GroupCat.FilteredColimits.colimitGroup
#align AddGroup.filtered_colimits.colimit_add_group AddGroupCat.FilteredColimits.colimitAddGroup

/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive group giving the filtered colimit of a diagram."]
noncomputable def colimit : GroupCat.{max v u} :=
  GroupCat.of (G.{v, u} F)
#align Group.filtered_colimits.colimit GroupCat.FilteredColimits.colimit
#align AddGroup.filtered_colimits.colimit AddGroupCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit group. -/
@[to_additive "The cocone over the proposed colimit additive group."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι := { (MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ GroupCat MonCat.{max v u})).ι with }
#align Group.filtered_colimits.colimit_cocone GroupCat.FilteredColimits.colimitCocone
#align AddGroup.filtered_colimits.colimit_cocone AddGroupCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `GroupCat`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddGroup`."]
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc t :=
    MonCat.FilteredColimits.colimitDesc.{v, u} (F ⋙ forget₂ GroupCat MonCat.{max v u})
      ((forget₂ GroupCat MonCat).mapCocone t)
  fac t j :=
    FunLike.coe_injective <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget GroupCat)).fac
      ((forget GroupCat).mapCocone t) j
  uniq t _ h :=
    FunLike.coe_injective' <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget GroupCat)).uniq
      ((forget GroupCat).mapCocone t) _
        fun j => funext fun x => FunLike.congr_fun (h j) x
#align Group.filtered_colimits.colimit_cocone_is_colimit GroupCat.FilteredColimits.colimitCoconeIsColimit
#align AddGroup.filtered_colimits.colimit_cocone_is_colimit AddGroupCat.FilteredColimits.colimitCoconeIsColimit

@[to_additive forget₂AddMonPreservesFilteredColimits]
noncomputable instance forget₂MonPreservesFilteredColimits :
    PreservesFilteredColimits.{u} (forget₂ GroupCat.{u} MonCat.{u}) where
      preserves_filtered_colimits x hx1 _ :=
      letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩
#align Group.filtered_colimits.forget₂_Mon_preserves_filtered_colimits GroupCat.FilteredColimits.forget₂MonPreservesFilteredColimits
#align AddGroup.filtered_colimits.forget₂_AddMon_preserves_filtered_colimits AddGroupCat.FilteredColimits.forget₂AddMonPreservesFilteredColimits

@[to_additive]
noncomputable instance forgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget GroupCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ GroupCat MonCat) (forget MonCat.{u})
#align Group.filtered_colimits.forget_preserves_filtered_colimits GroupCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddGroup.filtered_colimits.forget_preserves_filtered_colimits AddGroupCat.FilteredColimits.forgetPreservesFilteredColimits

end

end GroupCat.FilteredColimits

namespace CommGroupCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommGroupCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommGroupCat GroupCat` in the category `GroupCat`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive
  "The colimit of `F ⋙ forget₂ AddCommGroupCat AddGroupCat` in the category `AddGroupCat`.
  In the following, we will show that this has the structure of a _commutative_ additive group."]
noncomputable abbrev G : GroupCat.{max v u} :=
  GroupCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGroupCat.{max v u} GroupCat.{max v u})
#align CommGroup.filtered_colimits.G CommGroupCat.FilteredColimits.G
#align AddCommGroup.filtered_colimits.G AddCommGroupCat.FilteredColimits.G

@[to_additive]
noncomputable instance colimitCommGroup : CommGroup.{max v u} (G.{v, u} F) :=
  { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGroupCat CommMonCat.{max v u}) with }
#align CommGroup.filtered_colimits.colimit_comm_group CommGroupCat.FilteredColimits.colimitCommGroup
#align AddCommGroup.filtered_colimits.colimit_add_comm_group AddCommGroupCat.FilteredColimits.colimitAddCommGroup

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative group giving the filtered colimit of a diagram."]
noncomputable def colimit : CommGroupCat :=
  CommGroupCat.of (G.{v, u} F)
#align CommGroup.filtered_colimits.colimit CommGroupCat.FilteredColimits.colimit
#align AddCommGroup.filtered_colimits.colimit AddCommGroupCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit commutative group. -/
@[to_additive "The cocone over the proposed colimit additive commutative group."]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (GroupCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommGroupCat GroupCat.{max v u})).ι with }
#align CommGroup.filtered_colimits.colimit_cocone CommGroupCat.FilteredColimits.colimitCocone
#align AddCommGroup.filtered_colimits.colimit_cocone AddCommGroupCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `CommGroupCat`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommGroup`."]
def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) where
  desc t :=
    (GroupCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
          (F ⋙ forget₂ CommGroupCat GroupCat.{max v u})).desc
      ((forget₂ CommGroupCat GroupCat.{max v u}).mapCocone t)
  fac t j :=
    FunLike.coe_injective <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommGroupCat)).fac
        ((forget CommGroupCat).mapCocone t) j
  uniq t _ h :=
    FunLike.coe_injective <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommGroupCat)).uniq
        ((forget CommGroupCat).mapCocone t) _ fun j => funext fun x => FunLike.congr_fun (h j) x
#align CommGroup.filtered_colimits.colimit_cocone_is_colimit CommGroupCat.FilteredColimits.colimitCoconeIsColimit
#align AddCommGroup.filtered_colimits.colimit_cocone_is_colimit AddCommGroupCat.FilteredColimits.colimitCoconeIsColimit

@[to_additive]
noncomputable instance forget₂GroupPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommGroupCat GroupCat.{u}) where
  preserves_filtered_colimits J hJ1 _ :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (GroupCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGroupCat GroupCat.{u})) }
#align CommGroup.filtered_colimits.forget₂_Group_preserves_filtered_colimits CommGroupCat.FilteredColimits.forget₂GroupPreservesFilteredColimits
#align AddCommGroup.filtered_colimits.forget₂_AddGroup_preserves_filtered_colimits AddCommGroupCat.FilteredColimits.forget₂AddGroupPreservesFilteredColimits

@[to_additive]
noncomputable instance forgetPreservesFilteredColimits :
    PreservesFilteredColimits (forget CommGroupCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommGroupCat GroupCat) (forget GroupCat.{u})
#align CommGroup.filtered_colimits.forget_preserves_filtered_colimits CommGroupCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddCommGroup.filtered_colimits.forget_preserves_filtered_colimits AddCommGroupCat.FilteredColimits.forgetPreservesFilteredColimits

end

end CommGroupCat.FilteredColimits
