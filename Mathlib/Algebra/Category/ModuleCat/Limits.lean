/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.Shrink

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/


open CategoryTheory

open CategoryTheory.Limits

universe t v w u

-- `u` is determined by the ring, so can come later
noncomputable section

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

instance addCommGroupObj (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| AddCommGroup (F.obj j)

instance moduleObj (j) :
    Module.{u, w} R ((F ⋙ forget (ModuleCat R)).obj j) :=
  inferInstanceAs <| Module R (F.obj j)

/-- The flat sections of a functor into `ModuleCat R` form a submodule of all sections.
-/
def sectionsSubmodule : Submodule R (∀ j, F.obj j) :=
  { AddGrpCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{w} ⋙
          forget₂ AddCommGrpCat AddGrpCat.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simpa [Functor.sections, forget_map] using congr_arg (r • ·) (sh f) }

instance : AddCommMonoid (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| AddCommMonoid (sectionsSubmodule F)

instance : Module R (F ⋙ forget (ModuleCat R)).sections :=
  inferInstanceAs <| Module R (sectionsSubmodule F)

section

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

instance : Small.{w} (sectionsSubmodule F) :=
  inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))

-- Adding the following instance speeds up `limitModule` noticeably,
-- by preventing a bad unfold of `limitAddCommGroup`.
instance limitAddCommMonoid :
    AddCommMonoid (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommMonoid (Shrink (sectionsSubmodule F))

instance limitAddCommGroup :
    AddCommGroup (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| AddCommGroup (Shrink.{w} (sectionsSubmodule F))

instance limitModule :
    Module R (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
  inferInstanceAs <| Module R (Shrink (sectionsSubmodule F))

/-- `limit.π (F ⋙ forget (ModuleCat.{w} R)) j` as an `R`-linear map. -/
def limitπLinearMap (j) :
    (Types.Small.limitCone (F ⋙ forget (ModuleCat.{w} R))).pt →ₗ[R]
      (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by
    simp only [Types.Small.limitCone_π_app,
      ← Shrink.linearEquiv_apply R (F ⋙ forget (ModuleCat R)).sections, map_smul]
    simp only [Shrink.linearEquiv_apply]
    rfl
  map_add' _ _ := by
    simp only [Types.Small.limitCone_π_app, ← Equiv.addEquiv_apply, map_add]
    rfl

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
    { app := fun j => ofHom (limitπLinearMap F j)
      naturality := fun _ _ f => hom_ext <| LinearMap.coe_injective <|
        ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) }

/-- Witness that the limit cone in `ModuleCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limitConeIsLimit : IsLimit (limitCone.{t, v, w} F) := by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ofHom ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp only [Types.Small.limitConeIsLimit_lift, Functor.mapCone_π_app, forget_map, map_add]
    rw [← equivShrink_add]
    rfl
  · intro r x
    simp only [Types.Small.limitConeIsLimit_lift, Functor.mapCone_π_app, forget_map, map_smul]
    rw [← equivShrink_smul]
    rfl

end HasLimits

open HasLimits

/-- If `(F ⋙ forget (ModuleCat R)).sections` is `u`-small, `F` has a limit. -/
instance hasLimit : HasLimit F := HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, the category of `R`-modules has limits of shape `J`. -/
lemma hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where

/-- The category of R-modules has all limits. -/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := hasLimitsOfShape

instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, w, u}

instance (priority := high) hasLimits' : HasLimits (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u}

/-- An auxiliary declaration to speed up typechecking.
-/
def forget₂AddCommGroup_preservesLimitsAux :
    IsLimit ((forget₂ (ModuleCat R) AddCommGrpCat).mapCone (limitCone F)) :=
  letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrpCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrpCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrpCat.{w})

/-- The forgetful functor from R-modules to abelian groups preserves all limits. -/
instance forget₂AddCommGroup_preservesLimit :
    PreservesLimit F (forget₂ (ModuleCat R) AddCommGrpCat) :=
  preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (forget₂AddCommGroup_preservesLimitsAux F)

/-- The forgetful functor from R-modules to abelian groups preserves all limits.
-/
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }

instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGrpCat.{w}) :=
  ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-modules to types preserves all limits.
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦ preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }

instance forget_preservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forget_preservesLimitsOfSize.{w, w}

end

instance forget₂AddCommGroup_reflectsLimit :
    ReflectsLimit F (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where
  reflects {c} hc := ⟨by
    have : HasLimit (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) := ⟨_, hc⟩
    have : Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R))) := by
      simpa only [AddCommGrpCat.hasLimit_iff_small_sections] using this
    have := reflectsLimit_of_reflectsIsomorphisms F (forget₂ (ModuleCat R) AddCommGrpCat)
    exact isLimitOfReflects _ hc⟩

instance forget₂AddCommGroup_reflectsLimitOfShape :
    ReflectsLimitsOfShape J (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where

instance forget₂AddCommGroup_reflectsLimitOfSize :
    ReflectsLimitsOfSize.{t, v} (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where

section DirectLimit

open Module

variable {ι : Type v}
variable [DecidableEq ι] [Preorder ι]
variable (G : ι → Type v)
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) [DirectedSystem G fun i j h ↦ f i j h]

/-- The diagram (in the sense of `CategoryTheory`) of an unbundled `directLimit` of modules. -/
@[simps]
def directLimitDiagram : ι ⥤ ModuleCat R where
  obj i := ModuleCat.of R (G i)
  map hij := ofHom (f _ _ hij.le)
  map_id i := by
    ext
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    ext
    symm
    apply Module.DirectedSystem.map_map f

variable [DecidableEq ι]

/-- The `Cocone` on `directLimitDiagram` corresponding to
the unbundled `directLimit` of modules.

In `directLimitIsColimit` we show that it is a colimit cocone. -/
@[simps]
def directLimitCocone : Cocone (directLimitDiagram G f) where
  pt := ModuleCat.of R <| DirectLimit G f
  ι :=
    { app := fun x => ofHom (Module.DirectLimit.of R ι G f x)
      naturality := fun _ _ hij => by
        ext
        exact DirectLimit.of_f }

/-- The unbundled `directLimit` of modules is a colimit
in the sense of `CategoryTheory`. -/
@[simps]
def directLimitIsColimit : IsColimit (directLimitCocone G f) where
  desc s := ofHom <|
    Module.DirectLimit.lift R ι G f (fun i => (s.ι.app i).hom) fun i j h x => by
      simp only [Functor.const_obj_obj]
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    ext
    dsimp only [hom_comp, directLimitCocone, hom_ofHom, LinearMap.comp_apply]
    apply DirectLimit.lift_of
  uniq s m h := by
    have :
      s.ι.app = fun i =>
        (ofHom (DirectLimit.of R ι (fun i => G i) (fun i j H => f i j H) i)) ≫ m := by
      funext i
      rw [← h]
      rfl
    ext
    simp [this]

end DirectLimit

end ModuleCat
