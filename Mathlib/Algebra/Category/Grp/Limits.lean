/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Category.MonCat.ForgetCorepresentable
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

open CategoryTheory CategoryTheory.Limits

universe v u w

noncomputable section

variable {J : Type v} [Category.{w} J]

namespace GrpCat

variable (F : J ⥤ GrpCat.{u})

@[to_additive]
instance groupObj (j) : Group ((F ⋙ forget GrpCat).obj j) :=
  inferInstanceAs <| Group (F.obj j)

/-- The flat sections of a functor into `GrpCat` form a subgroup of all sections. -/
@[to_additive
/-- The flat sections of a functor into `AddGrpCat` form an additive subgroup of all sections. -/]
def sectionsSubgroup : Subgroup (∀ j, F.obj j) :=
  { MonCat.sectionsSubmonoid (F ⋙ forget₂ GrpCat MonCat) with
    carrier := (F ⋙ forget GrpCat).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).hom.map_inv (a j), ah f] }

@[to_additive]
instance sectionsGroup : Group (F ⋙ forget GrpCat.{u}).sections :=
  (sectionsSubgroup F).toGroup

/-- The projection from `Functor.sections` to a factor as a `MonoidHom`. -/
@[to_additive /-- The projection from `Functor.sections` to a factor as an `AddMonoidHom`. -/]
def sectionsπMonoidHom (j : J) : (F ⋙ forget GrpCat.{u}).sections →* F.obj j where
  toFun x := x.val j
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Small.{u} (Functor.sections (F ⋙ forget GrpCat))]

@[to_additive]
noncomputable instance limitGroup :
    Group (Types.Small.limitCone.{v, u} (F ⋙ forget GrpCat.{u})).pt :=
  inferInstanceAs <| Group (Shrink (F ⋙ forget GrpCat.{u}).sections)

@[to_additive]
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget GrpCat))

/-- We show that the forgetful functor `GrpCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `Group` instance available, and then reuse
the existing limit. -/
@[to_additive /-- We show that the forgetful functor `AddGrpCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddGroup` instance available, and then
reuse the existing limit. -/]
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ GrpCat.{u} MonCat.{u}) :=
  -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : (forget₂ GrpCat.{u} MonCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ GrpCat.{u} MonCat.{u}))
    fun c' t =>
      have : Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat)) := by
        have : HasLimit (F ⋙ forget₂ GrpCat MonCat) := ⟨_, t⟩
        apply Concrete.small_sections_of_hasLimit (F ⋙ forget₂ GrpCat MonCat)
      have : Small.{u} (Functor.sections (F ⋙ forget GrpCat)) := inferInstanceAs <| Small.{u}
        (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat))
      { liftedCone :=
          { pt := GrpCat.of (Types.Small.limitCone (F ⋙ forget GrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom (F ⋙ forget₂ GrpCat MonCat) j
                naturality i j h:= hom_ext <| congr_arg MonCat.Hom.hom <|
                  (MonCat.HasLimits.limitCone
                        (F ⋙ forget₂ GrpCat MonCat.{u})).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
        makesLimit :=
         IsLimit.ofFaithful (forget₂ GrpCat MonCat.{u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun _ => _) fun _ => rfl }

/-- A choice of limit cone for a functor into `GrpCat`.
(Generally, you'll just want to use `limit F`.) -/
@[to_additive /-- A choice of limit cone for a functor into `GrpCat`.
  (Generally, you'll just want to use `limit F`.) -/]
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ GrpCat.{u} MonCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/
@[to_additive /-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget GrpCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddGrpCat).sections` is `u`-small, `F` has a limit. -/]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

end

/-- A functor `F : J ⥤ GrpCat.{u}` has a limit iff `(F ⋙ forget GrpCat).sections` is
`u`-small. -/
@[to_additive /-- A functor `F : J ⥤ AddGrpCat.{u}` has a limit iff
`(F ⋙ forget AddGrpCat).sections` is `u`-small. -/]
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget GrpCat).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

/-- If `J` is `u`-small, `GrpCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddGrpCat.{u}` has limits of shape `J`. -/]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J GrpCat.{u} where
  has_limit _ := inferInstance

/-- The category of groups has all limits. -/
@[to_additive (relevant_arg := 100) /-- The category of additive groups has all limits. -/]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} GrpCat.{u} where
  has_limits_of_shape J _ := { }

@[to_additive]
instance hasLimits : HasLimits GrpCat.{u} :=
  GrpCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive (relevant_arg := 100) AddGrpCat.forget₂AddMonPreservesLimitsOfSize
/-- The forgetful functor from additive groups to additive monoids preserves all limits.

This means the underlying additive monoid of a limit can be computed as a limit in the category of
additive monoids. -/]
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ GrpCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J _} := { }

@[to_additive]
instance forget₂Mon_preservesLimits : PreservesLimits (forget₂ GrpCat.{u} MonCat.{u}) :=
  GrpCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `GrpCat.{u}` preserves limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddGrpCat.{u}` preserves limits
of shape `J`. -/]
instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget GrpCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive (relevant_arg := 100)
/-- The forgetful functor from additive groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/]
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget GrpCat.{u}) := inferInstance

@[to_additive]
instance forget_preservesLimits : PreservesLimits (forget GrpCat.{u}) :=
  GrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget GrpCat.{u}) := by
  set e : forget₂ GrpCat.{u} MonCat.{u} ⋙ forget MonCat.{u} ≅ forget GrpCat.{u} := Iso.refl _
  exact createsLimitOfNatIso e

@[to_additive]
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget GrpCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from groups to types creates all limits.
-/
@[to_additive (relevant_arg := 100)
/-- The forgetful functor from additive groups to types creates all limits. -/]
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget GrpCat.{u}) where
  CreatesLimitsOfShape := inferInstance
end GrpCat

namespace CommGrpCat

variable (F : J ⥤ CommGrpCat.{u})

@[to_additive]
instance commGroupObj (j) : CommGroup ((F ⋙ forget CommGrpCat).obj j) :=
  inferInstanceAs <| CommGroup (F.obj j)

@[to_additive]
noncomputable instance limitCommGroup
    [Small.{u} (Functor.sections (F ⋙ forget CommGrpCat))] :
    CommGroup (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrpCat.{u})).pt :=
  letI : CommGroup (F ⋙ forget CommGrpCat.{u}).sections :=
    @Subgroup.toCommGroup (∀ j, F.obj j) _
      (GrpCat.sectionsSubgroup (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))
  inferInstanceAs <| CommGroup (Shrink (F ⋙ forget CommGrpCat.{u}).sections)

@[to_additive]
instance : (forget₂ CommGrpCat.{u} GrpCat.{u}).ReflectsIsomorphisms :=
    reflectsIsomorphisms_forget₂ _ _

/-- We show that the forgetful functor `CommGrpCat ⥤ GrpCat` creates limits.

All we need to do is notice that the limit point has a `CommGroup` instance available,
and then reuse the existing limit.
-/
@[to_additive /-- We show that the forgetful functor `AddCommGrpCat ⥤ AddGrpCat` creates limits.

All we need to do is notice that the limit point has an `AddCommGroup` instance available,
and then reuse the existing limit. -/]
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ CommGrpCat GrpCat.{u}) :=
  createsLimitOfReflectsIso (fun c hc => by
    have : HasLimit _ := ⟨_, hc⟩
    have : Small.{u} (F ⋙ forget CommGrpCat).sections :=
      Concrete.small_sections_of_hasLimit (F ⋙ forget₂ CommGrpCat GrpCat)
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat) ⋙
      forget MonCat).sections := this
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).sections := this
    exact
      { liftedCone :=
          { pt := CommGrpCat.of (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGrpCat GrpCat.{u} ⋙ forget₂ GrpCat MonCat.{u}) j
                naturality i j h := hom_ext <| congr_arg MonCat.Hom.hom <|
                  (MonCat.HasLimits.limitCone _).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (GrpCat.limitConeIsLimit _) hc
        makesLimit :=
          IsLimit.ofFaithful (forget₂ _ GrpCat.{u} ⋙ forget₂ _ MonCat.{u})
            (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl })

section

variable [Small.{u} (Functor.sections (F ⋙ forget CommGrpCat))]

/-- A choice of limit cone for a functor into `CommGrpCat`.
(Generally, you'll just want to use `limit F`.) -/
@[to_additive
/-- A choice of limit cone for a functor into `AddCommGrpCat`.
(Generally, you'll just want to use `limit F`.) -/]
noncomputable def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGrpCat))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/
@[to_additive
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommGrpCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddCommGrpCat).sections` is `u`-small, `F` has a limit. -/]
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

end

/-- A functor `F : J ⥤ CommGrpCat.{u}` has a limit iff `(F ⋙ forget CommGrpCat).sections` is
`u`-small. -/
@[to_additive /-- A functor `F : J ⥤ AddCommGrpCat.{u}` has a limit iff
`(F ⋙ forget AddCommGrpCat).sections` is `u`-small. -/]
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget CommGrpCat).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

/-- If `J` is `u`-small, `CommGrpCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddCommGrpCat.{u}` has limits of shape `J`. -/]
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommGrpCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative groups has all limits. -/
@[to_additive (relevant_arg := 100)
/-- The category of additive commutative groups has all limits. -/]
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommGrpCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
instance hasLimits : HasLimits CommGrpCat.{u} :=
  CommGrpCat.hasLimitsOfSize.{u, u}

@[to_additive]
instance forget₂Group_preservesLimit :
    PreservesLimit F (forget₂ CommGrpCat.{u} GrpCat.{u}) where
  preserves {c} hc := ⟨by
    have : HasLimit (F ⋙ forget₂ CommGrpCat GrpCat) := by
      rw [GrpCat.hasLimit_iff_small_sections]
      change Small.{u} (F ⋙ forget CommGrpCat).sections
      rw [← CommGrpCat.hasLimit_iff_small_sections]
      exact ⟨_, hc⟩
    exact isLimitOfPreserves _ hc⟩

@[to_additive]
instance forget₂Group_preservesLimitsOfShape :
    PreservesLimitsOfShape J (forget₂ CommGrpCat.{u} GrpCat.{u}) where

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive (relevant_arg := 100)
/-- The forgetful functor from additive commutative groups to additive groups preserves all
limits. (That is, the underlying group could have been computed instead as limits in the
category of additive groups.) -/]
instance forget₂Group_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGrpCat.{u} GrpCat.{u}) where

@[to_additive]
instance forget₂Group_preservesLimits :
    PreservesLimits (forget₂ CommGrpCat GrpCat.{u}) :=
  CommGrpCat.forget₂Group_preservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking. -/
@[to_additive AddCommGrpCat.forget₂AddCommMon_preservesLimitsAux
/-- An auxiliary declaration to speed up typechecking. -/]
noncomputable def forget₂CommMon_preservesLimitsAux
    [Small.{u} (F ⋙ forget CommGrpCat).sections] :
    IsLimit ((forget₂ CommGrpCat.{u} CommMonCat.{u}).mapCone (limitCone.{v, u} F)) :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ CommMonCat) ⋙ forget CommMonCat)) :=
    inferInstanceAs <| Small (Functor.sections (F ⋙ forget CommGrpCat))
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGrpCat.{u} CommMonCat.{u})

/-- If `J` is `u`-small, the forgetful functor from `CommGrpCat.{u}` to `CommMonCat.{u}`
preserves limits of shape `J`. -/
@[to_additive AddCommGrpCat.forget₂AddCommMon_preservesLimitsOfShape
/-- If `J` is `u`-small, the forgetful functor from `AddCommGrpCat.{u}`
to `AddCommMonCat.{u}` preserves limits of shape `J`. -/]
instance forget₂CommMon_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget₂ CommGrpCat.{u} CommMonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
      (forget₂CommMon_preservesLimitsAux.{v, u} F)

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGrpCat.forget₂AddCommMon_preservesLimitsOfSize
/-- The forgetful functor from additive commutative groups to additive commutative monoids
preserves all limits. (That is, the underlying additive commutative monoids could have been
computed instead as limits in the category of additive commutative monoids.) -/]
instance forget₂CommMon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGrpCat CommMonCat.{u}) where
  preservesLimitsOfShape := { }

/-- If `J` is `u`-small, the forgetful functor from `CommGrpCat.{u}` preserves limits of
shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddCommGrpCat.{u}`
preserves limits of shape `J`. -/]
instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommGrpCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive
/-- The forgetful functor from additive commutative groups to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of
types.) -/]
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget CommGrpCat.{u}) := inferInstance

noncomputable instance _root_.AddCommGrpCat.forget_preservesLimits :
    PreservesLimits (forget AddCommGrpCat.{u}) :=
  AddCommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]
noncomputable instance forget_preservesLimits : PreservesLimits (forget CommGrpCat.{u}) :=
  CommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget CommGrpCat.{u}) := by
  set e : forget₂ CommGrpCat.{u} GrpCat.{u} ⋙ forget GrpCat.{u} ≅ forget CommGrpCat.{u} := .refl _
  exact createsLimitOfNatIso e

@[to_additive]
noncomputable instance forget_createsLimitsOfShape (J : Type v) [Category.{w} J] :
    CreatesLimitsOfShape J (forget CommGrpCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from commutative groups to types creates all limits.
-/
@[to_additive (relevant_arg := 100)
/-- The forgetful functor from additive commutative groups to types creates all limits. -/]
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget CommGrpCat.{u}) where
  CreatesLimitsOfShape := inferInstance

-- Verify we can form limits indexed over smaller categories.
example (f : ℕ → AddCommGrpCat) : HasProduct f := by infer_instance

end CommGrpCat

namespace AddCommGrpCat

/-- The categorical kernel of a morphism in `AddCommGrpCat`
agrees with the usual group-theoretical kernel.
-/
def kernelIsoKer {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    kernel f ≅ AddCommGrpCat.of f.hom.ker where
  hom := ofHom
    { toFun := fun g => ⟨kernel.ι f g, ConcreteCategory.congr_hom (kernel.condition f) g⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := fun g g' => by
        refine Subtype.ext ?_
        simp }
  inv := kernel.lift f (ofHom (AddSubgroup.subtype f.hom.ker)) <| by ext x; exact x.2
  hom_inv_id := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): it would be nice to do the next two steps by a single `ext`,
    -- but this will require thinking carefully about the relative priorities of `@[ext]` lemmas.
    refine equalizer.hom_ext ?_
    ext
    simp
  inv_hom_id := by
    apply AddCommGrpCat.ext
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    apply ConcreteCategory.congr_hom (kernel.lift_ι f _ _)

@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).hom ≫ ofHom (AddSubgroup.subtype f.hom.ker) = kernel.ι f := by ext; rfl

@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = ofHom (AddSubgroup.subtype f.hom.ker) := by
  simp [kernelIsoKer]

/-- The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `AddSubgroup.subtype` map.
-/
def kernelIsoKerOver {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGrpCat.of f.hom.ker)
      (ofHom (AddSubgroup.subtype f.hom.ker)) :=
  Over.isoMk (kernelIsoKer f)

end AddCommGrpCat
