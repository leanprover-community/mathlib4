/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Category.AlgCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.Limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory Limits

universe v w u t

-- `u` is determined by the ring, so can come later
noncomputable section

namespace AlgCat

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgCat.{w} R)

instance semiringObj (j) : Semiring ((F ⋙ forget (AlgCat R)).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)

instance algebraObj (j) :
    Algebra R ((F ⋙ forget (AlgCat R)).obj j) :=
  inferInstanceAs <| Algebra R (F.obj j)

/-- The flat sections of a functor into `AlgCat R` form a submodule of all sections.
-/
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }

instance (F : J ⥤ AlgCat.{w} R) : Ring (F ⋙ forget _).sections :=
  inferInstanceAs <| Ring (sectionsSubalgebra F)

instance (F : J ⥤ AlgCat.{w} R) : Algebra R (F ⋙ forget _).sections :=
  inferInstanceAs <| Algebra R (sectionsSubalgebra F)

variable [Small.{w} (F ⋙ forget (AlgCat.{w} R)).sections]

instance : Small.{w} (sectionsSubalgebra F) :=
  inferInstanceAs <| Small.{w} (F ⋙ forget _).sections

instance limitSemiring :
    Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgCat.{w} R))).pt :=
  inferInstanceAs <| Ring (Shrink (sectionsSubalgebra F))

instance limitAlgebra :
    Algebra R (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).pt :=
  inferInstanceAs <| Algebra R (Shrink (sectionsSubalgebra F))

/-- `limit.π (F ⋙ forget (AlgCat R)) j` as a `AlgHom`. -/
def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).π.app j
    commutes' := fun x => by
      simp only [Types.Small.limitCone_π_app, ← Shrink.algEquiv_apply R,
        Types.Small.limitCone_pt, AlgEquiv.commutes]
      rfl
    }

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (AlgCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `AlgCat R`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext : 1
        exact AlgHom.coe_fn_injective ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `AlgCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine
    IsLimit.ofFaithful (forget (AlgCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp only [Functor.mapCone_π_app, forget_map, map_one, Pi.one_apply]
  · intro x y
    ext j
    simp only [Functor.comp_obj, forget_obj, Functor.mapCone_pt,
      Functor.mapCone_π_app, forget_map, Equiv.symm_apply_apply,
      Types.Small.limitCone_pt, equivShrink_symm_mul, EquivLike.coe_apply]
    apply map_mul
  · ext j
    simp only [Functor.comp_obj, forget_obj, Functor.mapCone_pt,
      Functor.mapCone_π_app, forget_map, Equiv.symm_apply_apply,
      equivShrink_symm_zero, EquivLike.coe_apply]
    apply map_zero
  · intro x y
    ext j
    simp only [Functor.comp_obj, forget_obj, Functor.mapCone_pt,
      Functor.mapCone_π_app, forget_map, Equiv.symm_apply_apply,
      Types.Small.limitCone_pt, equivShrink_symm_add, EquivLike.coe_apply]
    apply map_add
  · intro r
    simp only [Equiv.algebraMap_def, Equiv.symm_symm]
    apply congrArg
    apply Subtype.ext
    ext j
    exact (s.π.app j).hom.commutes r

end HasLimits

open HasLimits

/-- The category of R-algebras has all limits. -/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

instance hasLimits : HasLimits (AlgCat.{w} R) :=
  AlgCat.hasLimitsOfSize.{w, w, u}

/-- The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget₂ (AlgCat.{w} R) RingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgCat.{w} R) RingCat.{w})) }

instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ (AlgCat R) RingCat.{w}) :=
  AlgCat.forget₂Ring_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂Module_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v}
    (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) }

instance forget₂Module_preservesLimits :
    PreservesLimits (forget₂ (AlgCat R) (ModuleCat.{w} R)) :=
  AlgCat.forget₂Module_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to types preserves all limits.
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (AlgCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }

instance forget_preservesLimits : PreservesLimits (forget (AlgCat.{w} R)) :=
  AlgCat.forget_preservesLimitsOfSize.{w, w}

end AlgCat
