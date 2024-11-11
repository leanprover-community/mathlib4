/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRingCatMax`.
We show that the colimit of `F ⋙ forget₂ SemiRingCatMax MonCat` (in `MonCat`)
carries the structure of a semiring, thereby showing that the forgetful functor
`forget₂ SemiRingCatMax MonCat` preserves filtered colimits.
In particular, this implies that `forget SemiRingCatMax` preserves filtered colimits.
Similarly for `CommSemiRingCat`, `RingCat` and `CommRingCat`.

-/


universe v u

noncomputable section

open CategoryTheory Limits

open IsFiltered renaming max → max' -- avoid name collision with `_root_.max`.

open AddMonCat.FilteredColimits (colimit_zero_eq colimit_add_mk_eq)

open MonCat.FilteredColimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCatMax.{v, u})

-- This instance is needed below in `colimitSemiring`, during the verification of the
-- semiring axioms.
instance semiringObj (j : J) :
    Semiring (((F ⋙ forget₂ SemiRingCatMax.{v, u} MonCat) ⋙ forget MonCat).obj j) :=
  show Semiring (F.obj j) by infer_instance

variable [IsFiltered J]

/-- The colimit of `F ⋙ forget₂ SemiRingCat MonCat` in the category `MonCat`.
In the following, we will show that this has the structure of a semiring.
-/
abbrev R : MonCatMax.{v, u} :=
  MonCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ SemiRingCatMax.{v, u} MonCatMax.{v, u})

instance colimitSemiring : Semiring.{max v u} <| R.{v, u} F :=
  { (R.{v, u} F).str,
    AddCommMonCat.FilteredColimits.colimitAddCommMonoid.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat.{max v u}) with
    mul_zero := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [mul_zero x]
      rfl
    zero_mul := fun x => by
      refine Quot.inductionOn x ?_; clear x; intro x
      obtain ⟨j, x⟩ := x
      erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)]
      rw [CategoryTheory.Functor.map_id]
      dsimp
      rw [zero_mul x]
      rfl
    left_distrib := fun x y z => by
      refine Quot.induction_on₃ x y z ?_; clear x y z; intro x y z
      obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, z⟩ := z
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
      refine Quot.induction_on₃ x y z ?_; clear x y z; intro x y z
      obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, z⟩ := z
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

/-- The bundled semiring giving the filtered colimit of a diagram. -/
def colimit : SemiRingCatMax.{v, u} :=
  SemiRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit semiring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { app := fun j =>
        { (MonCat.FilteredColimits.colimitCocone
            (F ⋙ forget₂ SemiRingCatMax.{v, u} MonCat)).ι.app j,
            (AddCommMonCat.FilteredColimits.colimitCocone
              (F ⋙ forget₂ SemiRingCatMax.{v, u} AddCommMonCat)).ι.app j with }
      naturality := fun {_ _} f =>
        RingHom.coe_inj ((Types.TypeMax.colimitCocone (F ⋙ forget SemiRingCat)).ι.naturality f) }

/-- The proposed colimit cocone is a colimit in `SemiRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t :=
    { (MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
            (F ⋙ forget₂ SemiRingCatMax.{v, u} MonCat)).desc
        ((forget₂ SemiRingCatMax.{v, u} MonCat).mapCocone t),
      (AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
            (F ⋙ forget₂ SemiRingCatMax.{v, u} AddCommMonCat)).desc
        ((forget₂ SemiRingCatMax.{v, u} AddCommMonCat).mapCocone t) with }
  fac t j :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget SemiRingCatMax.{v, u})).fac
        ((forget SemiRingCatMax.{v, u}).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget SemiRingCat)).uniq
        ((forget SemiRingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x

instance forget₂MonPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ SemiRingCat MonCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (MonCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ SemiRingCat MonCat.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget SemiRingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ SemiRingCat MonCat) (forget MonCat.{u})

end

end SemiRingCat.FilteredColimits

namespace CommSemiRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommSemiRingCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommSemiRingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a _commutative_ semiring.
-/
abbrev R : SemiRingCatMax.{v, u} :=
  SemiRingCat.FilteredColimits.colimit (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})

instance colimitCommSemiring : CommSemiring.{max v u} <| R.{v, u} F :=
  { (R F).str,
    CommMonCat.FilteredColimits.colimitCommMonoid
      (F ⋙ forget₂ CommSemiRingCat CommMonCat.{max v u}) with }

/-- The bundled commutative semiring giving the filtered colimit of a diagram. -/
def colimit : CommSemiRingCat.{max v u} :=
  CommSemiRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit commutative semiring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `CommSemiRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t :=
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
          (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{max v u})).desc
      ((forget₂ CommSemiRingCat SemiRingCat).mapCocone t)
  fac t j :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommSemiRingCat)).fac
        ((forget CommSemiRingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommSemiRingCat)).uniq
        ((forget CommSemiRingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x

instance forget₂SemiRingPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ CommSemiRingCat SemiRingCat.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommSemiRingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommSemiRingCat SemiRingCat)
    (forget SemiRingCat.{u})

end

end CommSemiRingCat.FilteredColimits

namespace RingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ RingCat.{max v u})

/-- The colimit of `F ⋙ forget₂ RingCat SemiRingCat` in the category `SemiRingCat`.
In the following, we will show that this has the structure of a ring.
-/
abbrev R : SemiRingCat.{max v u} :=
  SemiRingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ RingCat SemiRingCat.{max v u})

instance colimitRing : Ring.{max v u} <| R.{v, u} F :=
  { (R F).str,
    AddCommGrp.FilteredColimits.colimitAddCommGroup.{v, u}
      (F ⋙ forget₂ RingCat AddCommGrp.{max v u}) with }

/-- The bundled ring giving the filtered colimit of a diagram. -/
def colimit : RingCat.{max v u} :=
  RingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit ring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (SemiRingCat.FilteredColimits.colimitCocone
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `Ring`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t :=
    (SemiRingCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
          (F ⋙ forget₂ RingCat SemiRingCat.{max v u})).desc
      ((forget₂ RingCat SemiRingCat).mapCocone t)
  fac t j :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget RingCat)).fac
        ((forget RingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget RingCat)).uniq
        ((forget RingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x

instance forget₂SemiRingPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ RingCat SemiRingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (SemiRingCat.FilteredColimits.colimitCoconeIsColimit
            (F ⋙ forget₂ RingCat SemiRingCat.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget RingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ RingCat SemiRingCat) (forget SemiRingCat.{u})

end

end RingCat.FilteredColimits

namespace CommRingCat.FilteredColimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{max v u})

/-- The colimit of `F ⋙ forget₂ CommRingCat RingCat` in the category `RingCat`.
In the following, we will show that this has the structure of a _commutative_ ring.
-/
abbrev R : RingCat.{max v u} :=
  RingCat.FilteredColimits.colimit.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{max v u})

instance colimitCommRing : CommRing.{max v u} <| R.{v, u} F :=
  { (R.{v, u} F).str,
    CommSemiRingCat.FilteredColimits.colimitCommSemiring
      (F ⋙ forget₂ CommRingCat CommSemiRingCat.{max v u}) with }

/-- The bundled commutative ring giving the filtered colimit of a diagram. -/
def colimit : CommRingCat.{max v u} :=
  CommRingCat.of <| R.{v, u} F

/-- The cocone over the proposed colimit commutative ring. -/
def colimitCocone : Cocone F where
  pt := colimit.{v, u} F
  ι :=
    { (RingCat.FilteredColimits.colimitCocone (F ⋙ forget₂ CommRingCat RingCat.{max v u})).ι with }

/-- The proposed colimit cocone is a colimit in `CommRingCat`. -/
def colimitCoconeIsColimit : IsColimit <| colimitCocone.{v, u} F where
  desc t :=
    (RingCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
          (F ⋙ forget₂ CommRingCat RingCat.{max v u})).desc
      ((forget₂ CommRingCat RingCat).mapCocone t)
  fac t j :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit.{v, u} (F ⋙ forget CommRingCat)).fac
        ((forget CommRingCat).mapCocone t) j
  uniq t _ h :=
    RingHom.coe_inj <|
      (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget CommRingCat)).uniq
        ((forget CommRingCat).mapCocone t) _ fun j => funext fun x => RingHom.congr_fun (h j) x

instance forget₂RingPreservesFilteredColimits :
    PreservesFilteredColimits (forget₂ CommRingCat RingCat.{u}) where
  preserves_filtered_colimits {J hJ1 _} :=
    letI : Category J := hJ1
    { preservesColimit := fun {F} =>
        preservesColimitOfPreservesColimitCocone (colimitCoconeIsColimit.{u, u} F)
          (RingCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ CommRingCat RingCat.{u})) }

instance forgetPreservesFilteredColimits : PreservesFilteredColimits (forget CommRingCat.{u}) :=
  Limits.compPreservesFilteredColimits (forget₂ CommRingCat RingCat) (forget RingCat.{u})

end

end CommRingCat.FilteredColimits
