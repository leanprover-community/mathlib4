/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Algebra.DirectLimit

#align_import algebra.category.Module.limits from "leanprover-community/mathlib"@"c43486ecf2a5a17479a32ce09e4818924145e90e"

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe v w u

-- `u` is determined by the ring, so can come last
noncomputable section

namespace ModuleCat

variable (R : Type u) [Ring R]

variable {J : Type v} [SmallCategory J]

variable {R}

instance addCommGroupObj (F : J ⥤ ModuleCatMax.{v, w, u} R) (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) := by
  change AddCommGroup (F.obj j)
  -- ⊢ AddCommGroup ↑(F.obj j)
  infer_instance
  -- 🎉 no goals
set_option linter.uppercaseLean3 false
#align Module.add_comm_group_obj ModuleCat.addCommGroupObj

instance moduleObj (F : J ⥤ ModuleCatMax.{v, w, u} R) (j) :
    Module.{u, max v w} R ((F ⋙ forget (ModuleCat R)).obj j) := by
  change Module R (F.obj j)
  -- ⊢ Module R ↑(F.obj j)
  infer_instance
  -- 🎉 no goals
#align Module.module_obj ModuleCat.moduleObj

/-- The flat sections of a functor into `ModuleCat R` form a submodule of all sections.
-/
def sectionsSubmodule (F : J ⥤ ModuleCatMax.{v, w, u} R) : Submodule R (∀ j, F.obj j) :=
  { AddGroupCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGroupCat.{max v w} ⋙
          forget₂ AddCommGroupCat AddGroupCat.{max v w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simp only [forget_map, Functor.comp_map, Pi.smul_apply, map_smul]
      -- ⊢ r • ↑(F.map f) (s j) = r • s j'
      dsimp [Functor.sections] at sh
      -- ⊢ r • ↑(F.map f) (s j) = r • s j'
      rw [sh f] }
      -- 🎉 no goals
#align Module.sections_submodule ModuleCat.sectionsSubmodule

-- Adding the following instance speeds up `limitModule` noticeably,
-- by preventing a bad unfold of `limitAddCommGroup`.
instance limitAddCommMonoid (F : J ⥤ ModuleCatMax.{v, w, u} R) :
    AddCommMonoid (Types.limitCone.{v, w} (F ⋙ forget (ModuleCatMax.{v, w, u} R))).pt :=
  show AddCommMonoid (sectionsSubmodule F) by infer_instance
                                              -- 🎉 no goals
#align Module.limit_add_comm_monoid ModuleCat.limitAddCommMonoid

instance limitAddCommGroup (F : J ⥤ ModuleCatMax.{v, w, u} R) :
    AddCommGroup (Types.limitCone.{v, w} (F ⋙ forget (ModuleCatMax.{v, w, u} R))).pt :=
  show AddCommGroup (sectionsSubmodule F) by infer_instance
                                             -- 🎉 no goals
#align Module.limit_add_comm_group ModuleCat.limitAddCommGroup

instance limitModule (F : J ⥤ ModuleCatMax.{v, w, u} R) :
    Module R (Types.limitCone.{v, w} (F ⋙ forget (ModuleCat.{max v w} R))).pt :=
  show Module R (sectionsSubmodule F) by infer_instance
                                         -- 🎉 no goals
#align Module.limit_module ModuleCat.limitModule

/-- `limit.π (F ⋙ forget Ring) j` as a `RingHom`. -/
def limitπLinearMap (F : J ⥤ ModuleCatMax.{v, w, u} R) (j) :
    (Types.limitCone (F ⋙ forget (ModuleCat.{max v w} R))).pt →ₗ[R] (F ⋙ forget (ModuleCat R)).obj j
    where
  toFun := (Types.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
#align Module.limit_π_linear_map ModuleCat.limitπLinearMap

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (ModuleCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `ModuleCat R`.
(Internal use only; use the limits API.)
-/
def limitCone (F : J ⥤ ModuleCatMax.{v, w, u} R) : Cone F where
  pt := ModuleCat.of R (Types.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app := limitπLinearMap F
      naturality := fun _ _ f =>
        LinearMap.coe_injective ((Types.limitCone (F ⋙ forget _)).π.naturality f) }
#align Module.has_limits.limit_cone ModuleCat.HasLimits.limitCone

/-- Witness that the limit cone in `ModuleCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit (F : J ⥤ ModuleCatMax.{v, w, u} R) : IsLimit (limitCone.{v, w} F) := by
  refine' IsLimit.ofFaithful (forget (ModuleCat R)) (Types.limitConeIsLimit.{v, w} _)
    (fun s => ⟨⟨(Types.limitConeIsLimit.{v, w} _).lift ((forget (ModuleCat R)).mapCone s), _⟩, _⟩)
    (fun s => rfl)
  all_goals
    intros
    dsimp [Types.limitConeIsLimit]
    simp
    rfl
#align Module.has_limits.limit_cone_is_limit ModuleCat.HasLimits.limitConeIsLimit

end HasLimits

open HasLimits


-- porting note: mathport translated this as `irreducible_def`, but as `HasLimitsOfSize`
-- is a `Prop`, declaring this as `irreducible` should presumably have no effect
/-- The category of R-modules has all limits. -/
lemma hasLimitsOfSize : HasLimitsOfSize.{v, v} (ModuleCatMax.{v, w, u} R) where
  has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } }
#align Module.has_limits_of_size ModuleCat.hasLimitsOfSize

instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, u}
#align Module.has_limits ModuleCat.hasLimits

instance (priority := high) hasLimits' : HasLimits (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroupPreservesLimitsAux (F : J ⥤ ModuleCatMax.{v, w, u} R) :
    IsLimit ((forget₂ (ModuleCat R) AddCommGroupCat).mapCone (limitCone F)) :=
  AddCommGroupCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCatMax.{v, w, u} R) _ : J ⥤ AddCommGroupCat.{max v w})
#align Module.forget₂_AddCommGroup_preserves_limits_aux ModuleCat.forget₂AddCommGroupPreservesLimitsAux

/-- The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v}
      (forget₂ (ModuleCatMax.{v, w, u} R) AddCommGroupCat.{max v w}) where
  preservesLimitsOfShape :=
    { preservesLimit := preservesLimitOfPreservesLimitCone (limitConeIsLimit _)
          (forget₂AddCommGroupPreservesLimitsAux _) }
#align Module.forget₂_AddCommGroup_preserves_limits_of_size ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize

instance forget₂AddCommGroupPreservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGroupCat.{w}) :=
  ModuleCat.forget₂AddCommGroupPreservesLimitsOfSize.{w, w}
#align Module.forget₂_AddCommGroup_preserves_limits ModuleCat.forget₂AddCommGroupPreservesLimits

/-- The forgetful functor from R-modules to types preserves all limits.
-/
instance forgetPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget (ModuleCatMax.{v, w, u} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := preservesLimitOfPreservesLimitCone (limitConeIsLimit _)
        (Types.limitConeIsLimit (_ ⋙ forget _)) }
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
    -- ⊢ ∀ (x : ↑({ obj := fun i => of R (G i), map := fun {X Y} hij => f X Y (_ : X  …
    intro x
    -- ⊢ ↑({ obj := fun i => of R (G i), map := fun {X Y} hij => f X Y (_ : X ≤ Y) }. …
    apply Module.DirectedSystem.map_self
    -- 🎉 no goals
  map_comp hij hjk := by
    apply LinearMap.ext
    -- ⊢ ∀ (x : ↑({ obj := fun i => of R (G i), map := fun {X Y} hij => f X Y (_ : X  …
    intro x
    -- ⊢ ↑({ obj := fun i => of R (G i), map := fun {X Y} hij => f X Y (_ : X ≤ Y) }. …
    symm
    -- ⊢ ↑({ obj := fun i => of R (G i), map := fun {X Y} hij => f X Y (_ : X ≤ Y) }. …
    apply Module.DirectedSystem.map_map
    -- 🎉 no goals
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
        -- ⊢ ∀ (x : ↑((directLimitDiagram G f).obj x✝¹)), ↑((directLimitDiagram G f).map  …
        intro x
        -- ⊢ ↑((directLimitDiagram G f).map hij ≫ DirectLimit.of R ι G f x✝) x = ↑(Direct …
        exact DirectLimit.of_f }
        -- 🎉 no goals
#align Module.direct_limit_cocone ModuleCat.directLimitCocone

/-- The unbundled `directLimit` of modules is a colimit
in the sense of `CategoryTheory`. -/
@[simps]
def directLimitIsColimit [Nonempty ι] [IsDirected ι (· ≤ ·)] : IsColimit (directLimitCocone G f)
    where
  desc s :=
    DirectLimit.lift R ι G f s.ι.app fun i j h x => by
      rw [← s.w (homOfLE h)]
      -- ⊢ ↑(NatTrans.app s.ι j) (↑(f i j h) x) = ↑((directLimitDiagram G f).map (homOf …
      rfl
      -- 🎉 no goals
  fac s i := by
    apply LinearMap.ext
    -- ⊢ ∀ (x : ↑((directLimitDiagram G f).obj i)), ↑(NatTrans.app (directLimitCocone …
    intro x
    -- ⊢ ↑(NatTrans.app (directLimitCocone G f).ι i ≫ (fun s => DirectLimit.lift R ι  …
    dsimp only [directLimitCocone, CategoryStruct.comp]
    -- ⊢ ↑(LinearMap.comp (DirectLimit.lift R ι G f s.ι.app (_ : ∀ (i j : ι) (h : i ≤ …
    rw [LinearMap.comp_apply]
    -- ⊢ ↑(DirectLimit.lift R ι G f s.ι.app (_ : ∀ (i j : ι) (h : i ≤ j) (x : G i), ↑ …
    apply DirectLimit.lift_of
    -- 🎉 no goals
  uniq s m h := by
    have :
      s.ι.app = fun i =>
        LinearMap.comp m (DirectLimit.of R ι (fun i => G i) (fun i j H => f i j H) i) := by
      funext i
      rw [← h]
      rfl
    apply LinearMap.ext
    -- ⊢ ∀ (x : ↑(directLimitCocone G f).pt), ↑m x = ↑((fun s => DirectLimit.lift R ι …
    intro x
    -- ⊢ ↑m x = ↑((fun s => DirectLimit.lift R ι G f s.ι.app (_ : ∀ (i j : ι) (h : i  …
    simp only [this]
    -- ⊢ ↑m x = ↑(DirectLimit.lift R ι G f (fun i => LinearMap.comp m (DirectLimit.of …
    apply Module.DirectLimit.lift_unique
    -- 🎉 no goals
#align Module.direct_limit_is_colimit ModuleCat.directLimitIsColimit

end DirectLimit

end ModuleCat
