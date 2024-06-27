/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.DirectLimit

#align_import algebra.category.Module.limits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v w u t

-- `u` is determined by the ring, so can come later
noncomputable section

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

instance addCommGroupObj (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| AddCommGroup (F.obj j)
set_option linter.uppercaseLean3 false
#align Module.add_comm_group_obj ModuleCat.addCommGroupObj

instance moduleObj (j) :
    Module.{u, w} R ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| Module R (F.obj j)
#align Module.module_obj ModuleCat.moduleObj

/-- The flat sections of a functor into `ModuleCat R` form a submodule of all sections.
-/
def sectionsSubmodule : Submodule R (∀ j, F.obj j) :=
  { AddGrp.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrp.{w} ⋙
          forget₂ AddCommGrp AddGrp.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simp only [forget_map, Functor.comp_map, Pi.smul_apply, map_smul]
      dsimp [Functor.sections] at sh
      rw [sh f] }
#align Module.sections_submodule ModuleCat.sectionsSubmodule

instance : AddCommMonoid (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| AddCommMonoid (sectionsSubmodule F)

instance : Module R (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| Module R (sectionsSubmodule F)

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

instance : Small.{w} (sectionsSubmodule F) :=
  inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))

-- Adding the following instance speeds up `limitModule` noticeably,
-- by preventing a bad unfold of `limitAddCommGroup`.
instance limitAddCommMonoid :
    AddCommMonoid (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommMonoid (Shrink (sectionsSubmodule F))
#align Module.limit_add_comm_monoid ModuleCat.limitAddCommMonoid

instance limitAddCommGroup :
    AddCommGroup (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommGroup (Shrink.{w} (sectionsSubmodule F))
#align Module.limit_add_comm_group ModuleCat.limitAddCommGroup

instance limitModule :
    Module R (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| Module R (Shrink (sectionsSubmodule F))
#align Module.limit_module ModuleCat.limitModule

/-- `limit.π (F ⋙ forget (ModuleCat.{w} R)) j` as an `R`-linear map. -/
def limitπLinearMap (j) :
    (Types.Small.limitCone (F ⋙ forget (ModuleCat.{w} R))).pt →ₗ[R]
      (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by
    simp only [Types.Small.limitCone_π_app,
      ← Shrink.linearEquiv_apply (F ⋙ forget (ModuleCat R)).sections R, map_smul]
    simp only [Shrink.linearEquiv_apply]
    rfl
  map_add' _ _ := by
    simp only [Types.Small.limitCone_π_app, ← Equiv.addEquiv_apply, map_add]
    rfl
#align Module.limit_π_linear_map ModuleCat.limitπLinearMap

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (ModuleCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `ModuleCat R`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app := limitπLinearMap F
      naturality := fun _ _ f =>
        LinearMap.coe_injective ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }
#align Module.has_limits.limit_cone ModuleCat.HasLimits.limitCone

/-- Witness that the limit cone in `ModuleCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp only [Types.Small.limitConeIsLimit_lift, Functor.mapCone_π_app, forget_map, map_add]
    erw [← map_add (AddEquiv.symm Shrink.addEquiv)]
    rfl
  · intro r x
    simp only [Types.Small.limitConeIsLimit_lift, Functor.mapCone_π_app, forget_map, map_smul]
    erw [← map_smul (LinearEquiv.symm <| Shrink.linearEquiv _ _)]
    rfl
#align Module.has_limits.limit_cone_is_limit ModuleCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits

/-- If `(F ⋙ forget (ModuleCat R)).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F := HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, the category of `R`-modules has limits of shape `J`. -/
lemma hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where

-- Porting note: mathport translated this as `irreducible_def`, but as `HasLimitsOfSize`
-- is a `Prop`, declaring this as `irreducible` should presumably have no effect
/-- The category of R-modules has all limits. -/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := hasLimitsOfShape
#align Module.has_limits_of_size ModuleCat.hasLimitsOfSize

instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, u}
#align Module.has_limits ModuleCat.hasLimits

instance (priority := high) hasLimits' : HasLimits (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux :
    IsLimit ((forget₂ (ModuleCat R) AddCommGrp).mapCone (limitCone F)) :=
  letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrp) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrp.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrp.{w})
#align Module.forget₂_AddCommGroup_preserves_limits_aux ModuleCat.forget₂AddCommGroupPreservesLimitsAux

/-- The forgetful functor from R-modules to abelian groups preserves all limits. -/
instance forget₂AddCommGroupPreservesLimit :
    PreservesLimit F (forget₂ (ModuleCat R) AddCommGrp) :=
  preservesLimitOfPreservesLimitCone (limitConeIsLimit F)
    (forget₂AddCommGroupPreservesLimitsAux F)

instance forget₂AddCommGroupReflectsLimit :
    ReflectsLimit F (forget₂ (ModuleCat R) AddCommGrp) :=
  reflectsLimitOfReflectsIsomorphisms _ _

/-- The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (ModuleCat.{w} R) AddCommGrp.{w}) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }
#align Module.forget₂_AddCommGroup_preserves_limits_of_size ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize

instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGrp.{w}) :=
  ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize.{w, w}
#align Module.forget₂_AddCommGroup_preserves_limits ModuleCat.forget₂AddCommGroupPreservesLimits

/-- The forgetful functor from R-modules to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦ preservesLimitOfPreservesLimitCone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }
#align Module.forget_preserves_limits_of_size ModuleCat.forgetPreservesLimitsOfSize

instance forgetPreservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forgetPreservesLimitsOfSize.{w, w}
#align Module.forget_preserves_limits ModuleCat.forgetPreservesLimits

section DirectLimit

open Module

variable {ι : Type v}
variable [dec_ι : DecidableEq ι] [Preorder ι]
variable (G : ι → Type v)
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h => f i j h]

/-- The diagram (in the sense of `CategoryTheory`)
 of an unbundled `directLimit` of modules. -/
@[simps]
def directLimitDiagram : ι ⥤ ModuleCat R where
  obj i := ModuleCat.of R (G i)
  map hij := f _ _ hij.le
  map_id i := by
    apply LinearMap.ext
    intro x
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    apply LinearMap.ext
    intro x
    symm
    apply Module.DirectedSystem.map_map
#align Module.direct_limit_diagram ModuleCat.directLimitDiagram

variable [DecidableEq ι]

/-- The `Cocone` on `directLimitDiagram` corresponding to
the unbundled `directLimit` of modules.

In `directLimitIsColimit` we show that it is a colimit cocone. -/
@[simps]
def directLimitCocone : Cocone (directLimitDiagram G f) where
  pt := ModuleCat.of R <| DirectLimit G f
  ι :=
    { app := Module.DirectLimit.of R ι G f
      naturality := fun _ _ hij => by
        apply LinearMap.ext
        intro x
        exact DirectLimit.of_f }
#align Module.direct_limit_cocone ModuleCat.directLimitCocone

/-- The unbundled `directLimit` of modules is a colimit
in the sense of `CategoryTheory`. -/
@[simps]
def directLimitIsColimit [IsDirected ι (· ≤ ·)] : IsColimit (directLimitCocone G f) where
  desc s :=
    DirectLimit.lift R ι G f s.ι.app fun i j h x => by
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    apply LinearMap.ext
    intro x
    dsimp only [directLimitCocone, CategoryStruct.comp]
    rw [LinearMap.comp_apply]
    apply DirectLimit.lift_of
  uniq s m h := by
    have :
      s.ι.app = fun i =>
        LinearMap.comp m (DirectLimit.of R ι (fun i => G i) (fun i j H => f i j H) i) := by
      funext i
      rw [← h]
      rfl
    apply LinearMap.ext
    intro x
    simp only [this]
    apply Module.DirectLimit.lift_unique
#align Module.direct_limit_is_colimit ModuleCat.directLimitIsColimit

end DirectLimit

end ModuleCat
