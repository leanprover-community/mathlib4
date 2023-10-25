/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.GroupCat.FilteredColimits

#align_import algebra.category.Ring.filtered_colimits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRing`.
We show that the colimit of `F ⋙ forget₂ SemiRing Mon` (in `Mon`) carries the structure of a
semiring, thereby showing that the forgetful functor `forget₂ SemiRing Mon` preserves filtered
colimits. In particular, this implies that `forget SemiRing` preserves filtered colimits.
Similarly for `CommSemiRing`, `Ring` and `CommRing`.

-/


universe v u w

noncomputable section

open Classical

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
variable {J : Type v} [Category.{w} J] (F : J ⥤ SemiRingCat.{u}) [UnivLE.{v, u}]

-- This instance is needed below in `colimit_semiring`, during the verification of the
-- semiring axioms.
instance semiringObj (j : J) :
    Semiring (((F ⋙ forget₂ SemiRingCat MonCat) ⋙ forget MonCat).obj j) :=
  show Semiring (F.obj j) by infer_instance
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.semiring_obj SemiRingCat.FilteredColimits.semiringObj

variable [IsFiltered J]

/-- The colimit of `F ⋙ forget₂ SemiRing Mon` in the category `Mon`.
In the following, we will show that this has the structure of a semiring.
-/
abbrev R : MonCat.{u} :=
  MonCat.FilteredColimits.colimit (F ⋙ forget₂ SemiRingCat MonCat.{u})
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.R SemiRingCat.FilteredColimits.R

instance colimitSemiring : Semiring.{u} <| (R F) :=
  { (R F).str,
    AddCommMonCat.FilteredColimits.colimitAddCommMonoid
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{u}) with
    mul_zero := fun x => by
      obtain ⟨⟨j, x : F.obj j⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [mul_zero x]
      rfl
    zero_mul := fun x => by
      obtain ⟨⟨j, x : F.obj j⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [zero_mul x]
      rfl
    left_distrib := fun x y z => by
      obtain ⟨⟨j₁, x : F.obj j₁⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ x
      obtain ⟨⟨j₂, y : F.obj j₂⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ y
      obtain ⟨⟨j₃, z : F.obj j₃⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ z
      let k := IsFiltered.max₃ j₁ j₂ j₃
      let f := IsFiltered.firstToMax₃ j₁ j₂ j₃
      let g := IsFiltered.secondToMax₃ j₁ j₂ j₃
      let h := IsFiltered.thirdToMax₃ j₁ j₂ j₃
      erw [colimit_add_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨k, _⟩ k f (𝟙 k),
        colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h,
        colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      simp only [CategoryTheory.Functor.map_id, id_apply]
      erw [left_distrib (F.map f x) (F.map g y) (F.map h z)]
      rfl
    right_distrib := fun x y z => by
      obtain ⟨⟨j₁, x : F.obj j₁⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ x
      obtain ⟨⟨j₂, y : F.obj j₂⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ y
      obtain ⟨⟨j₃, z : F.obj j₃⟩, rfl⟩ := MonCat.FilteredColimits.M.surjective_mk _ z
      let k := IsFiltered.max₃ j₁ j₂ j₃
      let f := IsFiltered.firstToMax₃ j₁ j₂ j₃
      let g := IsFiltered.secondToMax₃ j₁ j₂ j₃
      let h := IsFiltered.thirdToMax₃ j₁ j₂ j₃
      erw [colimit_add_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨k, _⟩ ⟨j₃, _⟩ k (𝟙 k) h,
        colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h, colimit_mul_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h,
        colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)]
      simp only [CategoryTheory.Functor.map_id, id_apply]
      erw [right_distrib (F.map f x) (F.map g y) (F.map h z)]
      rfl }
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.colimit_semiring SemiRingCat.FilteredColimits.colimitSemiring

/-- The bundled semiring giving the filtered colimit of a diagram. -/
def colimit : SemiRingCat.{u} :=
  SemiRingCat.of <| R F
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.colimit SemiRingCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit semiring. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { app := fun j =>
        { (MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCat.{u} MonCat)).ι.app j,
            (AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat)).ι.app j with }
      naturality := fun {_ _} f =>
        RingHom.coe_inj ((Types.colimitCocone (F ⋙ forget SemiRingCat)).ι.naturality f) }
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.colimit_cocone SemiRingCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `SemiRing`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone F where
  desc t :=
    { (MonCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ SemiRingCat MonCat)).desc
        ((forget₂ SemiRingCat MonCat).mapCocone t),
      (AddCommMonCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ SemiRingCat AddCommMonCat)).desc
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) with }
  fac t j :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget SemiRingCat)).fac
        ((forget SemiRingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget SemiRingCat)).uniq
        ((forget SemiRingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.colimit_cocone_is_colimit SemiRingCat.FilteredColimits.colimitCoconeIsColimit

instance forget₂MonPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ SemiRingCat MonCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.forget₂_Mon_preserves_filtered_colimits SemiRingCat.FilteredColimits.forget₂MonPreservesFilteredColimits

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget SemiRingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ SemiRingCat MonCat) (forget MonCat.{u})
set_option linter.uppercaseLean3 false in
#align SemiRing.filtered_colimits.forget_preserves_filtered_colimits SemiRingCat.FilteredColimits.forgetPreservesFilteredColimits

end

end SemiRingCat.FilteredColimits

namespace CommSemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [Category.{w} J] [IsFiltered J] (F : J ⥤ CommSemiRingCat.{u}) [UnivLE.{v, u}]

/-- The colimit of `F ⋙ forget₂ CommSemiRing SemiRing` in the category `SemiRing`.
In the following, we will show that this has the structure of a _commutative_ semiring.
-/
abbrev R : SemiRingCat.{u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat)
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.R CommSemiRingCat.FilteredColimits.R

instance colimitCommSemiring : CommSemiring.{u} <| R F :=
  { (R F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat) with }
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.colimit_comm_semiring CommSemiRingCat.FilteredColimits.colimitCommSemiring

/-- The bundled commutative semiring giving the filtered colimit of a diagram. -/
def colimit : CommSemiRingCat.{u} :=
  CommSemiRingCat.of <| R F
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.colimit CommSemiRingCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit commutative semiring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})).ι with }
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.colimit_cocone CommSemiRingCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `CommSemiRing`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone F where
  desc t :=
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat)).desc
      ((forget₂ CommSemiRingCat SemiRingCat).mapCocone t)
  fac t j :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommSemiRingCat)).fac
        ((forget CommSemiRingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommSemiRingCat)).uniq
        ((forget CommSemiRingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.colimit_cocone_is_colimit CommSemiRingCat.FilteredColimits.colimitCoconeIsColimit

instance forget₂SemiRingPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.forget₂_SemiRing_preserves_filtered_colimits CommSemiRingCat.FilteredColimits.forget₂SemiRingPreservesFilteredColimits

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommSemiRingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat)
    (forget SemiRingCat.{u})
set_option linter.uppercaseLean3 false in
#align CommSemiRing.filtered_colimits.forget_preserves_filtered_colimits CommSemiRingCat.FilteredColimits.forgetPreservesFilteredColimits

end

end CommSemiRingCat.FilteredColimits

namespace RingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [Category.{w} J] [IsFiltered J] (F : J ⥤ RingCat.{u}) [UnivLE.{v, u}]

/-- The colimit of `F ⋙ forget₂ Ring SemiRing` in the category `SemiRing`.
In the following, we will show that this has the structure of a ring.
-/
abbrev R : SemiRingCat.{u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ RingCat SemiRingCat.{u})
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.R RingCat.FilteredColimits.R

instance colimitRing : Ring.{u} <| R F :=
  { (R F).str,
    AddCommGroupCat.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGroupCat.{u}) with }
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.colimit_ring RingCat.FilteredColimits.colimitRing

/-- The bundled ring giving the filtered colimit of a diagram. -/
def colimit : RingCat.{u} :=
  RingCat.of <| R F
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.colimit RingCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit ring. -/
def colimitCocone : Cocone F where
  pt := colimit F
  ι :=
    { (SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat)).ι with }
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.colimit_cocone RingCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `Ring`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone F where
  desc t :=
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ RingCat SemiRingCat)).desc
      ((forget₂ RingCat SemiRingCat).mapCocone t)
  fac t j :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget RingCat)).fac
        ((forget RingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget RingCat)).uniq ((forget RingCat).mapCocone t) _
        fun j => funext fun x => RingHom.congr_fun (h j) x
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.colimit_cocone_is_colimit RingCat.FilteredColimits.colimitCoconeIsColimit

instance forget₂SemiRingPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ RingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.forget₂_SemiRing_preserves_filtered_colimits RingCat.FilteredColimits.forget₂SemiRingPreservesFilteredColimits

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget RingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{u})
set_option linter.uppercaseLean3 false in
#align Ring.filtered_colimits.forget_preserves_filtered_colimits RingCat.FilteredColimits.forgetPreservesFilteredColimits

end

end RingCat.FilteredColimits

namespace CommRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [Category.{w} J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) [UnivLE.{v, u}]

/-- The colimit of `F ⋙ forget₂ CommRing Ring` in the category `Ring`.
In the following, we will show that this has the structure of a _commutative_ ring.
-/
abbrev R : RingCat.{u} :=
  RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u})
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.R CommRingCat.FilteredColimits.R

instance colimitCommRing : CommRing.{u} <| R F :=
  { (R F).str,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u}) with }
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.colimit_comm_ring CommRingCat.FilteredColimits.colimitCommRing

/-- The bundled commutative ring giving the filtered colimit of a diagram. -/
def colimit : CommRingCat.{u} :=
  CommRingCat.of <| R F
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.colimit CommRingCat.FilteredColimits.colimit

/-- The cocone over the proposed colimit commutative ring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (RingCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommRingCat RingCat)).ι with }
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.colimit_cocone CommRingCat.FilteredColimits.colimitCocone

/-- The proposed colimit cocone is a colimit in `CommRing`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t :=
    (RingCat.FilteredColimits.colimitCoconeIsColimit
          (F ⋙ forget₂ CommRingCat RingCat)).desc
      ((forget₂ CommRingCat RingCat).mapCocone t)
  fac t j :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommRingCat)).fac
        ((forget CommRingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.colimitCoconeIsColimit (F ⋙ forget CommRingCat)).uniq
        ((forget CommRingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.colimit_cocone_is_colimit CommRingCat.FilteredColimits.colimitCoconeIsColimit

instance forget₂RingPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommRingCat RingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.forget₂_Ring_preserves_filtered_colimits CommRingCat.FilteredColimits.forget₂RingPreservesFilteredColimits

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommRingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})
set_option linter.uppercaseLean3 false in
#align CommRing.filtered_colimits.forget_preserves_filtered_colimits CommRingCat.FilteredColimits.forgetPreservesFilteredColimits

end

end CommRingCat.FilteredColimits
