/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Algebra.limits
! leanprover-community/mathlib commit c43486ecf2a5a17479a32ce09e4818924145e90e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace AlgebraCat

variable {R : Type u} [CommRing R]

variable {J : Type v} [SmallCategory J]

instance semiringObj (F : J ⥤ AlgebraCatMax.{v, w} R) (j) :
    Semiring ((F ⋙ forget (AlgebraCat R)).obj j) := by change Semiring (F.obj j); infer_instance
#align Algebra.semiring_obj AlgebraCat.semiringObj

instance algebraObj (F : J ⥤ AlgebraCatMax.{v, w} R) (j) :
    Algebra R ((F ⋙ forget (AlgebraCat R)).obj j) := by change Algebra R (F.obj j); infer_instance
#align Algebra.algebra_obj AlgebraCat.algebraObj

/-- The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sectionsSubalgebra (F : J ⥤ AlgebraCatMax.{v, w} R) : Subalgebra R (∀ j, F.obj j) :=
  {
    SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{max v w} ⋙ forget₂ RingCat SemiRingCatMax.{v, w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).commutes r }
#align Algebra.sections_subalgebra AlgebraCat.sectionsSubalgebra

instance limitSemiring (F : J ⥤ AlgebraCatMax.{v, w} R) :
    Ring.{max v w} (Types.limitCone.{v, w} (F ⋙ forget (AlgebraCatMax.{v, w} R))).pt := by
  change Ring (sectionsSubalgebra F)
  infer_instance
#align Algebra.limit_semiring AlgebraCat.limitSemiring

instance limitAlgebra (F : J ⥤ AlgebraCatMax.{v, w} R) :
    Algebra R (Types.limitCone (F ⋙ forget (AlgebraCatMax.{v, w} R))).pt := by
  have :
    Algebra R (Types.limitCone (F ⋙ forget (AlgebraCatMax.{v, w} R))).pt =
      Algebra R (sectionsSubalgebra F) :=
    by rfl
  rw [this]
  infer_instance
#align Algebra.limit_algebra AlgebraCat.limitAlgebra

/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limitπAlgHom (F : J ⥤ AlgebraCatMax.{v, w} R) (j) :
    (Types.limitCone (F ⋙ forget (AlgebraCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgebraCatMax.{v, w} R)).obj j :=
  {
    SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{max v w} ⋙ forget₂ RingCat SemiRingCat.{max v w}) j with
    commutes' := fun _ => rfl }
#align Algebra.limit_π_alg_hom AlgebraCat.limitπAlgHom

namespace HasLimits

-- The next two definitions are used in the construction of `has_limits (Algebra R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.
/-- Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ AlgebraCatMax.{v, w} R) : Cone F where
  pt := AlgebraCat.of R (Types.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπAlgHom F
      naturality := fun _ _ f =>
        AlgHom.coe_fn_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align Algebra.has_limits.limit_cone AlgebraCat.HasLimits.limitCone

/-- Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ AlgebraCatMax.{v, w} R) : IsLimit (limitCone.{v, w} F) := by
  refine'
    IsLimit.ofFaithful (forget (AlgebraCat R)) (Types.limitConeIsLimit.{v, w} _) (fun s => { .. })
      (fun s => rfl)
  · simp only [forget_map_eq_coe, AlgHom.map_one, Functor.mapCone_π_app]; rfl
  · intro x y; simp only [forget_map_eq_coe, AlgHom.map_mul, functor.map_cone_π_app]; rfl
  · simp only [forget_map_eq_coe, AlgHom.map_zero, Functor.mapCone_π_app]; rfl
  · intro x y; simp only [forget_map_eq_coe, AlgHom.map_add, functor.map_cone_π_app]; rfl
  · intro r; ext j; exact (s.π.app j).commutes r
#align Algebra.has_limits.limit_cone_is_limit AlgebraCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

-- porting note: mathport translated this as `irreducible_def`, but as `HasLimitsOfSize`
-- is a `Prop`, declaring this as `irreducible` should presumably have no effect
/-- The category of R-algebras has all limits. -/
lemma hasLimitsOfSize : HasLimitsOfSize.{v, v} (AlgebraCatMax.{v, w} R) :=
  {
    has_limits_of_shape := fun _ _ =>
      {
        has_limit := fun F =>
          HasLimit.mk
            { cone := limitCone F
              isLimit := limitConeIsLimit F } } }
#align Algebra.has_limits_of_size AlgebraCat.hasLimitsOfSize

instance hasLimits : HasLimits (AlgebraCat.{w} R) :=
  AlgebraCat.hasLimitsOfSize.{w, w, u}
#align Algebra.has_limits AlgebraCat.hasLimits

/-- The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂RingPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ (AlgebraCatMax.{v, w} R) RingCatMax.{v, w})
    where preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun F =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (by apply RingCat.limitConeIsLimit.{v, w} (F ⋙ forget₂ (AlgebraCatMax.{v, w} R) RingCatMax.{v, w})) }
#align Algebra.forget₂_Ring_preserves_limits_of_size AlgebraCat.forget₂RingPreservesLimitsOfSize

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ (AlgebraCat R) RingCat.{w}) :=
  AlgebraCat.forget₂RingPreservesLimitsOfSize.{w, w}
#align Algebra.forget₂_Ring_preserves_limits AlgebraCat.forget₂RingPreservesLimits

/-- The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂ModulePreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ (AlgebraCatMax.{v, w} R) (ModuleCat.ModuleCatMax.{v, w} R))
    where preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun F =>
        preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (by
            apply
              ModuleCat.HasLimits.limitConeIsLimit
                (F ⋙ forget₂ (AlgebraCatMax.{v, w} R) (ModuleCat.ModuleCatMax.{v, w} R))) }
#align Algebra.forget₂_Module_preserves_limits_of_size AlgebraCat.forget₂ModulePreservesLimitsOfSize

instance forget₂ModulePreservesLimits :
    PreservesLimits (forget₂ (AlgebraCat R) (ModuleCat.{w} R)) :=
  AlgebraCat.forget₂ModulePreservesLimitsOfSize.{w, w}
#align Algebra.forget₂_Module_preserves_limits AlgebraCat.forget₂ModulePreservesLimits

/-- The forgetful functor from R-algebras to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget (AlgebraCatMax.{v, w} R))
    where preservesLimitsOfShape {J} 𝒥 :=
    {
      preservesLimit := fun F =>
       preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
          (Types.limitConeIsLimit (F ⋙ forget _)) }
#align Algebra.forget_preserves_limits_of_size AlgebraCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget (AlgebraCat.{w} R)) :=
  AlgebraCat.forgetPreservesLimitsOfSize.{w, w}
#align Algebra.forget_preserves_limits AlgebraCat.forgetPreservesLimits

end AlgebraCat

