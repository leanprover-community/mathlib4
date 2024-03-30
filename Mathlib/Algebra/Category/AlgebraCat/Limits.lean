/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits

#align_import algebra.category.Algebra.limits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory

open CategoryTheory.Limits

universe v w u t

-- `u` is determined by the ring, so can come later
noncomputable section

namespace AlgebraCat

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgebraCat.{w} R)

instance semiringObj (j) : Semiring ((F ⋙ forget (AlgebraCat R)).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)
#align Algebra.semiring_obj AlgebraCat.semiringObj

instance algebraObj (j) :
    Algebra R ((F ⋙ forget (AlgebraCat R)).obj j) :=
  inferInstanceAs <| Algebra R (F.obj j)
#align Algebra.algebra_obj AlgebraCat.algebraObj

/-- The flat sections of a functor into `AlgebraCat R` form a submodule of all sections.
-/
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).commutes r }
#align Algebra.sections_subalgebra AlgebraCat.sectionsSubalgebra

instance (F : J ⥤ AlgebraCat.{w} R) : Ring (F ⋙ forget _).sections :=
  inferInstanceAs <| Ring (sectionsSubalgebra F)

instance (F : J ⥤ AlgebraCat.{w} R) : Algebra R (F ⋙ forget _).sections :=
  inferInstanceAs <| Algebra R (sectionsSubalgebra F)

variable [Small.{w} (F ⋙ forget (AlgebraCat.{w} R)).sections]

instance : Small.{w} (sectionsSubalgebra F) :=
  inferInstanceAs <| Small.{w} (F ⋙ forget _).sections

instance limitSemiring :
    Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgebraCat.{w} R))).pt :=
  inferInstanceAs <| Ring (Shrink (sectionsSubalgebra F))
#align Algebra.limit_semiring AlgebraCat.limitSemiring

instance limitAlgebra :
    Algebra R (Types.Small.limitCone (F ⋙ forget (AlgebraCat.{w} R))).pt :=
  inferInstanceAs <| Algebra R (Shrink (sectionsSubalgebra F))
#align Algebra.limit_algebra AlgebraCat.limitAlgebra

/-- `limit.π (F ⋙ forget (AlgebraCat R)) j` as a `AlgHom`. -/
def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgebraCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgebraCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgebraCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget (AlgebraCat.{w} R))).π.app j
    commutes' := fun x => by
      simp only [Types.Small.limitCone_π_app, ← Shrink.algEquiv_apply _ R,
        Types.Small.limitCone_pt, AlgEquiv.commutes]
      rfl
    }
#align Algebra.limit_π_alg_hom AlgebraCat.limitπAlgHom

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (AlgebraCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `AlgebraCat R`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := AlgebraCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := limitπAlgHom F
      naturality := fun _ _ f =>
        AlgHom.coe_fn_injective ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }
#align Algebra.has_limits.limit_cone AlgebraCat.HasLimits.limitCone

/-- Witness that the limit cone in `AlgebraCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine
    IsLimit.ofFaithful (forget (AlgebraCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      -- Porting note: in mathlib3 the function term
      -- `fun v => ⟨fun j => ((forget (AlgebraCat R)).mapCone s).π.app j v`
      -- was provided by unification, and the last argument `(fun s => _)` was `(fun s => rfl)`.
      (fun s => { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
                  commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
      forget_map_eq_coe]
    erw [map_one]
    rfl
  · intro x y
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app]
    erw [← map_mul (MulEquiv.symm Shrink.mulEquiv)]
    apply congrArg
    ext j
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app,
      forget_map_eq_coe, map_mul]
    rfl
  · simp only [Functor.mapCone_π_app, forget_map_eq_coe]
    congr
    funext j
    simp only [map_zero, Pi.zero_apply]
  · intro x y
    simp only [Functor.mapCone_π_app]
    erw [← map_add (AddEquiv.symm Shrink.addEquiv)]
    apply congrArg
    ext j
    simp only [forget_map_eq_coe, map_add]
    rfl
  · intro r
    simp only [← Shrink.algEquiv_symm_apply _ R, limitCone, Equiv.algebraMap_def,
      Equiv.symm_symm]
    apply congrArg
    apply Subtype.ext
    ext j
    exact (s.π.app j).commutes r
#align Algebra.has_limits.limit_cone_is_limit AlgebraCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

-- Porting note: mathport translated this as `irreducible_def`, but as `HasLimitsOfSize`
-- is a `Prop`, declaring this as `irreducible` should presumably have no effect
/-- The category of R-algebras has all limits. -/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgebraCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }
#align Algebra.has_limits_of_size AlgebraCat.hasLimitsOfSize

instance hasLimits : HasLimits (AlgebraCat.{w} R) :=
  AlgebraCat.hasLimitsOfSize.{w, w, u}
#align Algebra.has_limits AlgebraCat.hasLimits

/-- The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂RingPreservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget₂ (AlgebraCat.{w} R) RingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimitOfPreservesLimitCone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgebraCat.{w} R) RingCat.{w})) }
#align Algebra.forget₂_Ring_preserves_limits_of_size AlgebraCat.forget₂RingPreservesLimitsOfSize

instance forget₂RingPreservesLimits : PreservesLimits (forget₂ (AlgebraCat R) RingCat.{w}) :=
  AlgebraCat.forget₂RingPreservesLimitsOfSize.{w, w}
#align Algebra.forget₂_Ring_preserves_limits AlgebraCat.forget₂RingPreservesLimits

/-- The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂ModulePreservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v}
    (forget₂ (AlgebraCat.{w} R) (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimitOfPreservesLimitCone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgebraCat.{w} R) (ModuleCat.{w} R))) }
#align Algebra.forget₂_Module_preserves_limits_of_size AlgebraCat.forget₂ModulePreservesLimitsOfSize

instance forget₂ModulePreservesLimits :
    PreservesLimits (forget₂ (AlgebraCat R) (ModuleCat.{w} R)) :=
  AlgebraCat.forget₂ModulePreservesLimitsOfSize.{w, w}
#align Algebra.forget₂_Module_preserves_limits AlgebraCat.forget₂ModulePreservesLimits

/-- The forgetful functor from R-algebras to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (AlgebraCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
       preservesLimitOfPreservesLimitCone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }
#align Algebra.forget_preserves_limits_of_size AlgebraCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget (AlgebraCat.{w} R)) :=
  AlgebraCat.forgetPreservesLimitsOfSize.{w, w}
#align Algebra.forget_preserves_limits AlgebraCat.forgetPreservesLimits

end AlgebraCat
