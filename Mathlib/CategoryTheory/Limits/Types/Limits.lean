/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits in the category of types.

We show that the category of types has all limits, by providing the usual concrete models.

-/

universe u' v u w

namespace CategoryTheory.Limits.Types

section limit_characterization

variable {J : Type v} [Category.{w} J] {F : J ⥤ Type u}

/-- Given a section of a functor F into `Type*`,
  construct a cone over F with `PUnit` as the cone point. -/
def coneOfSection {s} (hs : s ∈ F.sections) : Cone F where
  pt := PUnit
  π :=
  { app := fun j _ ↦ s j,
    naturality := fun i j f ↦ by ext; exact (hs f).symm }

/-- Given a cone over a functor F into `Type*` and an element in the cone point,
  construct a section of F. -/
def sectionOfCone (c : Cone F) (x : c.pt) : F.sections :=
  ⟨fun j ↦ c.π.app j x, fun f ↦ congr_fun (c.π.naturality f).symm x⟩

theorem isLimit_iff (c : Cone F) :
    Nonempty (IsLimit c) ↔ ∀ s ∈ F.sections, ∃! x : c.pt, ∀ j, c.π.app j x = s j := by
  refine ⟨fun ⟨t⟩ s hs ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j ↦ congr_fun (t.fac cs j) ⟨⟩,
      fun x hx ↦ congr_fun (t.uniq cs (fun _ ↦ x) fun j ↦ funext fun _ ↦ hx j) ⟨⟩⟩
  · choose x hx using fun c y ↦ h _ (sectionOfCone c y).2
    exact ⟨x, fun c j ↦ funext fun y ↦ (hx c y).1 j,
      fun c f hf ↦ funext fun y ↦ (hx c y).2 (f y) (fun j ↦ congr_fun (hf j) y)⟩

theorem isLimit_iff_bijective_sectionOfCone (c : Cone F) :
    Nonempty (IsLimit c) ↔ (Types.sectionOfCone c).Bijective := by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]

/-- The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
  sections of `F`. -/
noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_fun (t.uniq (coneOfSection _) (fun _ ↦ x) fun _ ↦ rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j ↦ congr_fun (t.fac (coneOfSection s.2) j) ⟨⟩)

@[simp]
theorem isLimitEquivSections_apply {c : Cone F} (t : IsLimit c) (j : J)
    (x : c.pt) : (isLimitEquivSections t x : ∀ j, F.obj j) j = c.π.app j x := rfl

@[simp]
theorem isLimitEquivSections_symm_apply {c : Cone F} (t : IsLimit c)
    (x : F.sections) (j : J) :
    c.π.app j ((isLimitEquivSections t).symm x) = (x : ∀ j, F.obj j) j := by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
  rfl

end limit_characterization

variable {J : Type v} [Category.{w} J]

/-! We now provide two distinct implementations in the category of types.

The first, in the `CategoryTheory.Limits.Types.Small` namespace,
assumes `Small.{u} J` and constructs `J`-indexed limits in `Type u`.

The second, in the `CategoryTheory.Limits.Types.TypeMax` namespace
constructs limits for functors `F : J ⥤ Type max v u`, for `J : Type v`.
This construction is slightly nicer, as the limit is definitionally just `F.sections`,
rather than `Shrink F.sections`, which makes an arbitrary choice of `u`-small representative.

Hopefully we might be able to entirely remove the `TypeMax` constructions,
but for now they are useful glue for the later parts of the library.
-/

namespace Small

variable (F : J ⥤ Type u)

section

variable [Small.{u} F.sections]

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
noncomputable def limitCone : Cone F where
  pt := Shrink F.sections
  π :=
    { app := fun j u => ((equivShrink F.sections).symm u).val j
      naturality := fun j j' f => by
        funext x
        simp }

@[ext]
lemma limitCone_pt_ext {x y : (limitCone F).pt}
    (w : (equivShrink F.sections).symm x = (equivShrink F.sections).symm y) : x = y := by
  aesop

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) where
  lift s v := equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_fun (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using congr_fun (w j) x

end

end Small

theorem hasLimit_iff_small_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections :=
  ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isLimit_iff_bijective_sectionOfCone (limit.cone F)).mp ⟨limit.isLimit _⟩)).symm⟩⟩,
   fun _ => ⟨_, Small.limitConeIsLimit F⟩⟩

-- TODO: If `UnivLE` works out well, we will eventually want to deprecate these
-- definitions, and probably as a first step put them in namespace or otherwise rename them.
section TypeMax

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
noncomputable def limitCone (F : J ⥤ Type max v u) : Cone F where
  pt := F.sections
  π :=
    { app := fun j u => u.val j
      naturality := fun j j' f => by
        funext x
        simp }

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
noncomputable def limitConeIsLimit (F : J ⥤ Type max v u) : IsLimit (limitCone F) where
  lift s v :=
    { val := fun j => s.π.app j v
      property := fun f => congr_fun (Cone.w s f) _ }
  uniq := fun _ _ w => by
    funext x
    apply Subtype.ext
    funext j
    exact congr_fun (w j) x

end TypeMax


/-!
The results in this section have a `UnivLE.{v, u}` hypothesis,
but as they only use the constructions from the `CategoryTheory.Limits.Types.UnivLE` namespace
in their definitions (rather than their statements),
we leave them in the main `CategoryTheory.Limits.Types` namespace.
-/
section UnivLE

open UnivLE

instance hasLimit [Small.{u} J] (F : J ⥤ Type u) : HasLimit F :=
  (hasLimit_iff_small_sections F).mpr inferInstance

instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (Type u) where

/--
The category of types has all limits.

More specifically, when `UnivLE.{v, u}`, the category `Type u` has all `v`-small limits. -/
@[stacks 002U]
instance (priority := 1300) hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} (Type u) where
  has_limits_of_shape _ := { }

variable (F : J ⥤ Type u) [HasLimit F]

/-- The equivalence between the abstract limit of `F` in `Type max v u`
and the "concrete" definition as the sections of `F`.
-/
noncomputable def limitEquivSections : limit F ≃ F.sections :=
  isLimitEquivSections (limit.isLimit F)

@[simp]
theorem limitEquivSections_apply (x : limit F) (j : J) :
    ((limitEquivSections F) x : ∀ j, F.obj j) j = limit.π F j x :=
  isLimitEquivSections_apply _ _ _

@[simp]
theorem limitEquivSections_symm_apply (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections F).symm x) = (x : ∀ j, F.obj j) j :=
  isLimitEquivSections_symm_apply _ _ _

/-- The limit of a functor `F : J ⥤ Type _` is naturally isomorphic to `F.sections`. -/
noncomputable def limNatIsoSectionsFunctor :
    (lim : (J ⥤ Type max u v) ⥤ _) ≅ Functor.sectionsFunctor _ :=
  NatIso.ofComponents (fun _ ↦ (limitEquivSections _).toIso)
    fun f ↦ funext fun x ↦ Subtype.ext <| funext fun _ ↦ congrFun (limMap_π f _) x

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11182): removed @[ext]
/-- Construct a term of `limit F : Type u` from a family of terms `x : Π j, F.obj j`
which are "coherent": `∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j'`.
-/
noncomputable def Limit.mk (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') :
    limit F :=
  (limitEquivSections F).symm ⟨x, h _ _⟩

@[simp]
theorem Limit.π_mk (x : ∀ j, F.obj j) (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
    limit.π F j (Limit.mk F x h) = x j := by
  dsimp [Limit.mk]
  simp

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
@[ext]
theorem limit_ext (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) : x = y := by
  apply (limitEquivSections F).injective
  ext j
  simp [w j]

@[ext]
theorem limit_ext' (F : J ⥤ Type v) (x y : limit F) (w : ∀ j, limit.π F j x = limit.π F j y) :
    x = y :=
  limit_ext F x y w

theorem limit_ext_iff' (F : J ⥤ Type v) (x y : limit F) :
    x = y ↔ ∀ j, limit.π F j x = limit.π F j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩

-- TODO: are there other limits lemmas that should have `_apply` versions?
-- Can we generate these like with `@[reassoc]`?
-- PROJECT: prove these for any concrete category where the forgetful functor preserves limits?
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] was removed because the linter said it was useless
--@[simp]
variable {F} in
theorem Limit.w_apply {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] was removed because the linter said it was useless
theorem Limit.lift_π_apply (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] was removed because the linter said it was useless
theorem Limit.map_π_apply {F G : J ⥤ Type u} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
    (x : limit F) : limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (limMap_π α j) x

@[simp]
theorem Limit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : limit F} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  congr_fun (limit.w F f) x

@[simp]
theorem Limit.lift_π_apply' (F : J ⥤ Type v) (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  congr_fun (limit.lift_π s j) x

@[simp]
theorem Limit.map_π_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x : limit F) :
    limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  congr_fun (limMap_π α j) x

end UnivLE

/-!
In this section we verify that instances are available as expected.
-/
section instances

example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max w v) := inferInstance
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max v w) := inferInstance

example : HasLimitsOfSize.{0, 0, v, v+1} (Type v) := inferInstance
example : HasLimitsOfSize.{v, v, v, v+1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasLimitsOfSize.{v, v, u, u+1} (Type u) := inferInstance

end instances

end CategoryTheory.Limits.Types
