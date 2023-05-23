/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

! This file was ported from Lean 3 source module algebra.category.Group.filtered_colimits
! leanprover-community/mathlib commit c43486ecf2a5a17479a32ce09e4818924145e90e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.Basic
import Mathbin.Algebra.Category.Mon.FilteredColimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ Group`.
We show that the colimit of `F ⋙ forget₂ Group Mon` (in `Mon`) carries the structure of a group,
thereby showing that the forgetful functor `forget₂ Group Mon` preserves filtered colimits. In
particular, this implies that `forget Group` preserves filtered colimits. Similarly for `AddGroup`,
`CommGroup` and `AddCommGroup`.

-/


universe v u

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max'

-- avoid name collision with `_root_.max`.
namespace GroupCat.FilteredColimits

section

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

-- We use parameters here, mainly so we can have the abbreviations `G` and `G.mk` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ GroupCat.{max v u})

/-- The colimit of `F ⋙ forget₂ Group Mon` in the category `Mon`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddGroup AddMon` in the category `AddMon`.\nIn the following, we will show that this has the structure of an additive group."]
abbrev g : MonCat :=
  MonCat.FilteredColimits.colimit (F ⋙ forget₂ GroupCat MonCat.{max v u})
#align Group.filtered_colimits.G GroupCat.FilteredColimits.g
#align AddGroup.filtered_colimits.G AddGroupCat.FilteredColimits.g

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive "The canonical projection into the colimit, as a quotient type."]
abbrev g.mk : (Σj, F.obj j) → G :=
  Quot.mk (Types.Quot.Rel (F ⋙ forget GroupCat))
#align Group.filtered_colimits.G.mk GroupCat.FilteredColimits.g.mk
#align AddGroup.filtered_colimits.G.mk AddGroupCat.FilteredColimits.g.mk

@[to_additive]
theorem g.mk_eq (x y : Σj, F.obj j)
    (h : ∃ (k : J)(f : x.1 ⟶ k)(g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : G.mk x = G.mk y :=
  Quot.EqvGen_sound (Types.FilteredColimit.eqvGen_quot_rel_of_rel (F ⋙ forget GroupCat) x y h)
#align Group.filtered_colimits.G.mk_eq GroupCat.FilteredColimits.g.mk_eq
#align AddGroup.filtered_colimits.G.mk_eq AddGroupCat.FilteredColimits.g.mk_eq

/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive "The \"unlifted\" version of negation in the colimit."]
def colimitInvAux (x : Σj, F.obj j) : G :=
  G.mk ⟨x.1, x.2⁻¹⟩
#align Group.filtered_colimits.colimit_inv_aux GroupCat.FilteredColimits.colimitInvAux
#align AddGroup.filtered_colimits.colimit_neg_aux AddGroupCat.FilteredColimits.colimitNegAux

@[to_additive]
theorem colimitInvAux_eq_of_rel (x y : Σj, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget GroupCat) x y) :
    colimit_inv_aux x = colimit_inv_aux y :=
  by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [MonoidHom.map_inv, MonoidHom.map_inv, inv_inj]
  exact hfg
#align Group.filtered_colimits.colimit_inv_aux_eq_of_rel GroupCat.FilteredColimits.colimitInvAux_eq_of_rel
#align AddGroup.filtered_colimits.colimit_neg_aux_eq_of_rel AddGroupCat.FilteredColimits.colimit_neg_aux_eq_of_rel

/-- Taking inverses in the colimit. See also `colimit_inv_aux`. -/
@[to_additive "Negation in the colimit. See also `colimit_neg_aux`."]
instance colimitHasInv : Inv G
    where inv x := by
    refine' Quot.lift (colimit_inv_aux F) _ x
    intro x y h
    apply colimit_inv_aux_eq_of_rel
    apply types.filtered_colimit.rel_of_quot_rel
    exact h
#align Group.filtered_colimits.colimit_has_inv GroupCat.FilteredColimits.colimitHasInv
#align AddGroup.filtered_colimits.colimit_has_neg AddGroupCat.FilteredColimits.colimitHasNeg

@[simp, to_additive]
theorem colimit_inv_mk_eq (x : Σj, F.obj j) : (G.mk x)⁻¹ = G.mk ⟨x.1, x.2⁻¹⟩ :=
  rfl
#align Group.filtered_colimits.colimit_inv_mk_eq GroupCat.FilteredColimits.colimit_inv_mk_eq
#align AddGroup.filtered_colimits.colimit_neg_mk_eq AddGroupCat.FilteredColimits.colimit_neg_mk_eq

@[to_additive]
instance colimitGroup : Group G :=
  { G.Monoid, colimit_has_inv with
    mul_left_inv := fun x => by
      apply Quot.inductionOn x; clear x; intro x
      cases' x with j x
      erw [colimit_inv_mk_eq,
        colimit_mul_mk_eq (F ⋙ forget₂ GroupCat MonCat.{max v u}) ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq (F ⋙ forget₂ GroupCat MonCat.{max v u}) j]
      dsimp
      simp only [CategoryTheory.Functor.map_id, id_apply, mul_left_inv] }
#align Group.filtered_colimits.colimit_group GroupCat.FilteredColimits.colimitGroup
#align AddGroup.filtered_colimits.colimit_add_group AddGroupCat.FilteredColimits.colimitAddGroup

/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive group giving the filtered colimit of a diagram."]
def colimit : GroupCat :=
  GroupCat.of G
#align Group.filtered_colimits.colimit GroupCat.FilteredColimits.colimit
#align AddGroup.filtered_colimits.colimit AddGroupCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit group. -/
@[to_additive "The cocone over the proposed colimit additive group."]
def colimitCocone : cocone F where
  pt := colimit
  ι := { (MonCat.FilteredColimits.colimitCocone (F ⋙ forget₂ GroupCat MonCat.{max v u})).ι with }
#align Group.filtered_colimits.colimit_cocone GroupCat.FilteredColimits.colimitCocone
#align AddGroup.filtered_colimits.colimit_cocone AddGroupCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `Group`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddGroup`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc t :=
    MonCat.FilteredColimits.colimitDesc (F ⋙ forget₂ GroupCat MonCat.{max v u})
      ((forget₂ GroupCat MonCat).mapCocone t)
  fac t j :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget GroupCat)).fac ((forget GroupCat).mapCocone t) j
  uniq t m h :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget GroupCat)).uniq ((forget GroupCat).mapCocone t) m
        fun j => funext fun x => MonoidHom.congr_fun (h j) x
#align Group.filtered_colimits.colimit_cocone_is_colimit GroupCat.FilteredColimits.colimitCoconeIsColimit
#align AddGroup.filtered_colimits.colimit_cocone_is_colimit AddGroupCat.FilteredColimits.colimitCoconeIsColimit

@[to_additive forget₂_AddMon_preserves_filtered_colimits]
instance forget₂MonPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ GroupCat MonCat.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ GroupCat MonCat.{u})) }
#align Group.filtered_colimits.forget₂_Mon_preserves_filtered_colimits GroupCat.FilteredColimits.forget₂MonPreservesFilteredColimits
#align AddGroup.filtered_colimits.forget₂_AddMon_preserves_filtered_colimits AddGroupCat.FilteredColimits.forget₂AddMonPreservesFilteredColimits

@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget GroupCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ GroupCat MonCat) (forget MonCat.{u})
#align Group.filtered_colimits.forget_preserves_filtered_colimits GroupCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddGroup.filtered_colimits.forget_preserves_filtered_colimits AddGroupCat.FilteredColimits.forgetPreservesFilteredColimits

end

end GroupCat.FilteredColimits

namespace CommGroupCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
parameter {J : Type v}[SmallCategory J][IsFiltered J](F : J ⥤ CommGroupCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommGroup Group` in the category `Group`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive
      "The colimit of `F ⋙ forget₂ AddCommGroup AddGroup` in the category `AddGroup`.\nIn the following, we will show that this has the structure of a _commutative_ additive group."]
abbrev g : GroupCat :=
  GroupCat.FilteredColimits.colimit (F ⋙ forget₂ CommGroupCat GroupCat.{max v u})
#align CommGroup.filtered_colimits.G CommGroupCat.FilteredColimits.g
#align AddCommGroup.filtered_colimits.G AddCommGroupCat.FilteredColimits.g

@[to_additive]
instance colimitCommGroup : CommGroup G :=
  { G.Group,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGroupCat CommMonCat.{max v u}) with }
#align CommGroup.filtered_colimits.colimit_comm_group CommGroupCat.FilteredColimits.colimitCommGroup
#align AddCommGroup.filtered_colimits.colimit_add_comm_group AddCommGroupCat.FilteredColimits.colimitAddCommGroup

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive "The bundled additive commutative group giving the filtered colimit of a diagram."]
def colimit : CommGroupCat :=
  CommGroupCat.of G
#align CommGroup.filtered_colimits.colimit CommGroupCat.FilteredColimits.colimit
#align AddCommGroup.filtered_colimits.colimit AddCommGroupCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit commutative group. -/
@[to_additive "The cocone over the proposed colimit additive commutative group."]
def colimitCocone : cocone F where
  pt := colimit
  ι :=
    {
      (GroupCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommGroupCat GroupCat.{max v u})).ι with }
#align CommGroup.filtered_colimits.colimit_cocone CommGroupCat.FilteredColimits.colimitCocone
#align AddCommGroup.filtered_colimits.colimit_cocone AddCommGroupCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `CommGroup`. -/
@[to_additive "The proposed colimit cocone is a colimit in `AddCommGroup`."]
def colimitCoconeIsColimit : IsColimit colimit_cocone
    where
  desc t :=
    (GroupCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ CommGroupCat GroupCat.{max v u})).desc
      ((forget₂ CommGroupCat GroupCat.{max v u}).mapCocone t)
  fac t j :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommGroupCat)).fac
        ((forget CommGroupCat).mapCocone t) j
  uniq t m h :=
    MonoidHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommGroupCat)).uniq
        ((forget CommGroupCat).mapCocone t) m fun j => funext fun x => MonoidHom.congr_fun (h j) x
#align CommGroup.filtered_colimits.colimit_cocone_is_colimit CommGroupCat.FilteredColimits.colimitCoconeIsColimit
#align AddCommGroup.filtered_colimits.colimit_cocone_is_colimit AddCommGroupCat.FilteredColimits.colimitCoconeIsColimit

@[to_additive forget₂_AddGroup_preserves_filtered_colimits]
instance forget₂GroupPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommGroupCat GroupCat.{u})
    where PreservesFilteredColimits J _ _ :=
    {
      PreservesColimit := fun F =>
        preserves_colimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (GroupCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommGroupCat GroupCat.{u})) }
#align CommGroup.filtered_colimits.forget₂_Group_preserves_filtered_colimits CommGroupCat.FilteredColimits.forget₂GroupPreservesFilteredColimits
#align AddCommGroup.filtered_colimits.forget₂_AddGroup_preserves_filtered_colimits AddCommGroupCat.FilteredColimits.forget₂AddGroupPreservesFilteredColimits

@[to_additive]
instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommGroupCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommGroupCat GroupCat) (forget GroupCat.{u})
#align CommGroup.filtered_colimits.forget_preserves_filtered_colimits CommGroupCat.FilteredColimits.forgetPreservesFilteredColimits
#align AddCommGroup.filtered_colimits.forget_preserves_filtered_colimits AddCommGroupCat.FilteredColimits.forgetPreservesFilteredColimits

end

end CommGroupCat.FilteredColimits

