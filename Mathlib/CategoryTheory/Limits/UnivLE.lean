/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.Limits.Final

set_option autoImplicit true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits.Types

variable {J : Type v} [Category J] {F : J ⥤ Type u}

namespace Initial

open CategoryTheory.Functor.Initial

variable {J' : Type u} [Category J'] (G : J' ⥤ J) [G.Initial]
/- We could work with [InitiallySmall.{u} J] and arbitrarily choose an initial functor G from
  a `u`-small category J', except that InitiallySmall requires J' to have morphisms in Type u
  as well, so that would not be good enough for the UnivLE version below which have no restriction
  on morphisms. -/

/-- Transfer `CategoryTheory.Limits.Types.limitCone` for `G ⋙ F` to a limit cone over `F`
  across an initial functor G. -/
noncomputable def limitCone (F : J ⥤ Type u) : Cone F :=
  extendCone.obj <| Types.limitCone.{u, u} (G ⋙ F)

/-- The transferred cone is a limit. -/
@[simps!]
noncomputable def limitConeIsLimit (F : J ⥤ Type u) : IsLimit (limitCone G F) :=
  (isLimitExtendConeEquiv G _).symm (Types.limitConeIsLimit _)

end Initial

namespace Small

variable [Small.{u} J]

/-- Specialize `CategoryTheory.Limits.Types.Initial.limitCone` to `Shrink.equivalence`. -/
@[simps!]
noncomputable def limitCone (F : J ⥤ Type u) : Cone F :=
  Initial.limitCone (Shrink.equivalence J).functor F

/-- The specialized cone is a limit. -/
@[simps!]
noncomputable def limitConeIsLimit (F : J ⥤ Type u) : IsLimit (limitCone.{v, u} F) :=
  Initial.limitConeIsLimit (Shrink.equivalence J).functor F

end Small

/-!
The results in this section have a `Small.{u} J` hypothesis,
but as they only use the constructions from the `CategoryTheory.Limits.Types.Small` namespace
in their definitions (rather than their statements),
we leave them in the main `CategoryTheory.Limits.Types` namespace.
-/
section Small

variable [Small.{u} J]

instance hasLimit (F : J ⥤ Type u) : HasLimit F :=
  HasLimit.mk
    { cone := Small.limitCone.{v, u} F
      isLimit := Small.limitConeIsLimit F }

/--
The category of types has all limits.

More specifically, when `UnivLE.{v, u}`, the category `Type u` has all `v`-small limits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance (priority := 1300) hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{v} (Type u) where
  has_limits_of_shape _ :=
    { has_limit := fun _ => inferInstance }
#align category_theory.limits.types.has_limits_of_size CategoryTheory.Limits.Types.hasLimitsOfSize

/-- The equivalence between the abstract limit of `F` in `TypeMax.{v, u}`
and the "concrete" definition as the sections of `F`.
-/
noncomputable def limitEquivSections (F : J ⥤ Type u) :
    (@limit _ _ _ _ F (hasLimit.{v, u} F) : Type u) ≃ F.sections :=
  isLimitEquivSections.{v, u} (limit.isLimit F)
#align category_theory.limits.types.limit_equiv_sections CategoryTheory.Limits.Types.limitEquivSections

@[simp]
theorem limitEquivSections_apply (F : J ⥤ Type u) (x : limit F) (j : J) :
    ((limitEquivSections.{v, u} F) x : ∀ j, F.obj j) j = limit.π F j x :=
  isLimitEquivSections_apply _ _ _
#align category_theory.limits.types.limit_equiv_sections_apply CategoryTheory.Limits.Types.limitEquivSections_apply

@[simp]
theorem limitEquivSections_symm_apply (F : J ⥤ Type u) (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections.{v, u} F).symm x) = (x : ∀ j, F.obj j) j :=
  isLimitEquivSections_symm_apply _ _ _
#align category_theory.limits.types.limit_equiv_sections_symm_apply CategoryTheory.Limits.Types.limitEquivSections_symm_apply

-- porting note : `limitEquivSections_symm_apply'` was removed because the linter
--   complains it is unnecessary
--@[simp]
--theorem limitEquivSections_symm_apply' (F : J ⥤ Type v) (x : F.sections) (j : J) :
--    limit.π F j ((limitEquivSections.{v, v} F).symm x) = (x : ∀ j, F.obj j) j :=
--  isLimitEquivSections_symm_apply _ _ _
--#align category_theory.limits.types.limit_equiv_sections_symm_apply' CategoryTheory.Limits.Types.limitEquivSections_symm_apply'

--porting note: removed @[ext]
/-- Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
noncomputable def Limit.mk (F : J ⥤ Type u) (x : ∀ j, F.obj j)
    (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') : (limit F : Type u) :=
  (limitEquivSections.{v, u} F).symm ⟨x, h _ _⟩
#align category_theory.limits.types.limit.mk CategoryTheory.Limits.Types.Limit.mk

@[simp]
theorem Limit.π_mk (F : J ⥤ Type u) (x : ∀ j, F.obj j)
    (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
      limit.π F j (Limit.mk.{v, u} F x h) = x j := by
  dsimp [Limit.mk]
  simp
#align category_theory.limits.types.limit.π_mk CategoryTheory.Limits.Types.Limit.π_mk

-- porting note : `Limit.π_mk'` was removed because the linter complains it is unnecessary
--@[simp]
--theorem Limit.π_mk' (F : J ⥤ Type v) (x : ∀ j, F.obj j)
--    (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
--    limit.π F j (Limit.mk.{v, v} F x h) = x j := by
--  dsimp [Limit.mk]
--  simp
--#align category_theory.limits.types.limit.π_mk' CategoryTheory.Limits.Types.Limit.π_mk'

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
@[ext]
theorem limit_ext (F : J ⥤ Type u) (x y : limit F)
    (w : ∀ j, limit.π F j x = limit.π F j y) : x = y := by
  apply (limitEquivSections.{v, u} F).injective
  ext j
  simp [w j]
#align category_theory.limits.types.limit_ext CategoryTheory.Limits.Types.limit_ext

@[ext]
theorem limit_ext' (F : J ⥤ Type v) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
    x = y :=
  limit_ext F x y w
#align category_theory.limits.types.limit_ext' CategoryTheory.Limits.Types.limit_ext'

theorem limit_ext_iff (F : J ⥤ Type u) (x y : limit F) :
    x = y ↔ ∀ j, limit.π F j x = limit.π F j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext _ _ _⟩
#align category_theory.limits.types.limit_ext_iff CategoryTheory.Limits.Types.limit_ext_iff

theorem limit_ext_iff' (F : J ⥤ Type v) (x y : limit F) :
    x = y ↔ ∀ j, limit.π F j x = limit.π F j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩
#align category_theory.limits.types.limit_ext_iff' CategoryTheory.Limits.Types.limit_ext_iff'

-- TODO: are there other limits lemmas that should have `_apply` versions?
-- Can we generate these like with `@[reassoc]`?
-- PROJECT: prove these for any concrete category where the forgetful functor preserves limits?
--porting note: @[simp] was removed because the linter said it was useless
--@[simp]
theorem Limit.w_apply {F : J ⥤ Type u} {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x
#align category_theory.limits.types.limit.w_apply CategoryTheory.Limits.Types.Limit.w_apply

--porting note: @[simp] was removed because the linter said it was useless
theorem Limit.lift_π_apply (F : J ⥤ Type u) (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x
#align category_theory.limits.types.limit.lift_π_apply CategoryTheory.Limits.Types.Limit.lift_π_apply

--porting note: @[simp] was removed because the linter said it was useless
theorem Limit.map_π_apply {F G : J ⥤ Type u} (α : F ⟶ G) (j : J) (x : limit F) :
    limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (limMap_π α j) x
#align category_theory.limits.types.limit.map_π_apply CategoryTheory.Limits.Types.Limit.map_π_apply

@[simp]
theorem Limit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x
#align category_theory.limits.types.limit.w_apply' CategoryTheory.Limits.Types.Limit.w_apply'

@[simp]
theorem Limit.lift_π_apply' (F : J ⥤ Type v) (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x
#align category_theory.limits.types.limit.lift_π_apply' CategoryTheory.Limits.Types.Limit.lift_π_apply'

@[simp]
theorem Limit.map_π_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x : limit F) :
    limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (limMap_π α j) x
#align category_theory.limits.types.limit.map_π_apply' CategoryTheory.Limits.Types.Limit.map_π_apply'

end Small

/-!
In this section we verify that instances are available as expected.
-/
section instances

example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (TypeMax.{w, v}) := inferInstance
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max v w) := inferInstance

example : HasLimitsOfSize.{0, 0, v, v+1} (Type v) := inferInstance
example : HasLimitsOfSize.{v, v, v, v+1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasLimitsOfSize.{v, v, u, u+1} (Type u) := inferInstance

end instances

end CategoryTheory.Limits.Types
