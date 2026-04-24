/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# The forgetful functor from (commutative) (additive) groups preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ GrpCat`.
We show that the colimit of `F ⋙ forget₂ GrpCat MonCat` (in `MonCat`) carries the structure of a
group,
thereby showing that the forgetful functor `forget₂ GrpCat MonCat` preserves filtered colimits.
In particular, this implies that `forget GrpCat` preserves filtered colimits.
Similarly for `AddGrpCat`, `CommGrpCat` and `AddCommGrpCat`.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

namespace GrpCat.FilteredColimits

section

-- Mathlib3 used parameters here, mainly so we could have the abbreviations `G` and `G.mk` below,
-- without passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

/-- The colimit of `F ⋙ forget₂ GrpCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a group.
-/
@[to_additive
  /-- The colimit of `F ⋙ forget₂ AddGrpCat AddMonCat` in the category `AddMonCat`.
  In the following, we will show that this has the structure of an additive group. -/]
noncomputable abbrev G : MonCat :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ GrpCat MonCat.{max v u})

/-- The canonical projection into the colimit, as a quotient type. -/
@[to_additive /-- The canonical projection into the colimit, as a quotient type. -/]
abbrev G.mk : (Σ j, F.obj j) → G.{v, u} F :=
  fun x ↦ (F ⋙ forget GrpCat).ιColimitType x.1 x.2

@[to_additive]
theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    G.mk.{v, u} F x = G.mk F y :=
  Quot.eqvGen_sound <| Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget GrpCat) x y h

@[to_additive]
theorem colimit_one_eq (j : J) : (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩ :=
  MonCat.FilteredColimits.colimit_one_eq _ _

@[to_additive]
theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    G.mk.{v, u} F x * G.mk F y = G.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ :=
  MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

@[to_additive]
lemma colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    G.mk.{v, u} F ⟨j, x⟩ * G.mk.{v, u} F ⟨j, y⟩ = G.mk.{v, u} F ⟨j, x * y⟩ := by
  #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  `simpa using colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  have := colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  simpa using this

/-- The "unlifted" version of taking inverses in the colimit. -/
@[to_additive /-- The "unlifted" version of negation in the colimit. -/]
def colimitInvAux (x : Σ j, F.obj j) : G.{v, u} F :=
  G.mk F ⟨x.1, x.2⁻¹⟩

@[to_additive]
theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget GrpCat) x y) :
    colimitInvAux.{v, u} F x = colimitInvAux F y := by
  apply G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv, map_inv, inv_inj]
  exact hfg

/-- Taking inverses in the colimit. See also `colimitInvAux`. -/
@[to_additive /-- Negation in the colimit. See also `colimitNegAux`. -/]
instance colimitInv : Inv (G.{v, u} F) where
  inv x := by
    refine Quot.lift (colimitInvAux.{v, u} F) ?_ x
    intro x y h
    apply colimitInvAux_eq_of_rel
    apply Types.FilteredColimit.rel_of_colimitTypeRel
    exact h

@[to_additive (attr := simp)]
theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩ :=
  rfl

@[to_additive]
noncomputable instance colimitGroup : Group (G.{v, u} F) :=
  { colimitInv.{v, u} F, (G.{v, u} F).str with
    inv_mul_cancel := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      change (G.mk _ _)⁻¹ * G.mk _ _ = _
      obtain ⟨j, x⟩ := x
      simp [colimit_inv_mk_eq, colimit_mul_mk_eq F ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j),
        colimit_one_eq F j] }

/-- The bundled group giving the filtered colimit of a diagram. -/
@[to_additive /-- The bundled additive group giving the filtered colimit of a diagram. -/]
noncomputable def colimit : GrpCat.{max v u} :=
  GrpCat.of (G.{v, u} F)

/-- The cocone over the proposed colimit group. -/
@[to_additive /-- The cocone over the proposed colimit additive group. -/]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app J := GrpCat.ofHom ((MonCat.FilteredColimits.colimitCocone
    (F ⋙ forget₂ GrpCat MonCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ MonCat).map_injective
    ((MonCat.FilteredColimits.colimitCocone _).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `GrpCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddGroup`. -/]
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ _ MonCat)
    (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ GrpCat MonCat))

@[to_additive forget₂AddMon_preservesFilteredColimits]
noncomputable instance forget₂Mon_preservesFilteredColimits :
    PreservesFilteredColimits.{u} (forget₂ GrpCat.{u} MonCat.{u}) where
      preserves_filtered_colimits x hx1 _ :=
      letI : Category.{u, u} x := hx1
      ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit.{u, u} _)⟩

@[to_additive]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget GrpCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ GrpCat MonCat) (forget MonCat.{u})

end

end GrpCat.FilteredColimits

namespace CommGrpCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `G` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommGrpCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommGrpCat GrpCat` in the category `GrpCat`.
In the following, we will show that this has the structure of a _commutative_ group.
-/
@[to_additive
  /-- The colimit of `F ⋙ forget₂ AddCommGrpCat AddGrpCat` in the category `AddGrpCat`.
  In the following, we will show that this has the structure of a _commutative_ additive group. -/]
noncomputable abbrev G : GrpCat.{max v u} :=
  GrpCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommGrpCat.{max v u} GrpCat.{max v u})

@[to_additive]
noncomputable instance colimitCommGroup : CommGroup.{max v u} (G.{v, u} F) :=
  { (G F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommGrpCat CommMonCat.{max v u}) with }

/-- The bundled commutative group giving the filtered colimit of a diagram. -/
@[to_additive
/-- The bundled additive commutative group giving the filtered colimit of a diagram. -/]
noncomputable def colimit : CommGrpCat :=
  CommGrpCat.of (G.{v, u} F)

/-- The cocone over the proposed colimit commutative group. -/
@[to_additive /-- The cocone over the proposed colimit additive commutative group. -/]
noncomputable def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι.app J := CommGrpCat.ofHom
    ((GrpCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommGrpCat GrpCat)).ι.app J).hom
  ι.naturality _ _ f := (forget₂ _ GrpCat).map_injective
    ((GrpCat.FilteredColimits.colimitCocone _).ι.naturality f)

/-- The proposed colimit cocone is a colimit in `CommGrpCat`. -/
@[to_additive /-- The proposed colimit cocone is a colimit in `AddCommGroup`. -/]
noncomputable def colimitCoconeIsColimit : IsColimit (colimitCocone.{v, u} F) :=
  isColimitOfReflects (forget₂ _ GrpCat)
    (GrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommGrpCat GrpCat))

@[to_additive]
noncomputable instance forget₂Group_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommGrpCat GrpCat.{u}) where
  preserves_filtered_colimits J hJ1 _ :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimit_of_preserves_colimit_cocone (colimitCoconeIsColimit.{u, u} F)
          (GrpCat.FilteredColimits.colimitCoconeIsColimit.{u, u}
            (F ⋙ forget₂ CommGrpCat GrpCat.{u})) }

@[to_additive]
noncomputable instance forget_preservesFilteredColimits :
    PreservesFilteredColimits (forget CommGrpCat.{u}) :=
  Limits.comp_preservesFilteredColimits (forget₂ CommGrpCat GrpCat) (forget GrpCat.{u})

end

end CommGrpCat.FilteredColimits
