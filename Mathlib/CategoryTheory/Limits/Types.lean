/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.Data.TypeMax
import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Filtered.Basic

#align_import category_theory.limits.types from "leanprover-community/mathlib"@"4aa2a2e17940311e47007f087c9df229e7f12942"

/-!
# Limits in the category of types.

We show that the category of types has all (co)limits, by providing the usual concrete models.

We also give a characterisation of filtered colimits in `Type`, via
`colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj`.

Next, we prove the category of types has categorical images, and that these agree with the range of
a function.

Finally, we give the natural isomorphism between cones on `F` with cone point `X` and the type
`lim Hom(X, F·)`, and similarly the natural isomorphism between cocones on `F` with cocone point `X`
and the type `lim Hom(F·, X)`.

-/

set_option autoImplicit true


open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory.Limits

namespace Types

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

/-- The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
  sections of `F`. -/
noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_fun (t.uniq (coneOfSection _) (fun _ ↦ x) fun _ ↦ rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j ↦ congr_fun (t.fac (coneOfSection s.2) j) ⟨⟩)
#align category_theory.limits.types.is_limit_equiv_sections CategoryTheory.Limits.Types.isLimitEquivSections

@[simp]
theorem isLimitEquivSections_apply {c : Cone F} (t : IsLimit c) (j : J)
    (x : c.pt) : (isLimitEquivSections t x : ∀ j, F.obj j) j = c.π.app j x := rfl
#align category_theory.limits.types.is_limit_equiv_sections_apply CategoryTheory.Limits.Types.isLimitEquivSections_apply

@[simp]
theorem isLimitEquivSections_symm_apply {c : Cone F} (t : IsLimit c)
    (x : F.sections) (j : J) :
    c.π.app j ((isLimitEquivSections t).symm x) = (x : ∀ j, F.obj j) j := by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
#align category_theory.limits.types.is_limit_equiv_sections_symm_apply CategoryTheory.Limits.Types.isLimitEquivSections_symm_apply

end limit_characterization

variable {J : Type v} [Category.{w} J]

/-! We now provide two distinct implementations in the category of types.

The first, in the `CategoryTheory.Limits.Types.Small` namespace,
assumes `Small.{u} J` and constructs `J`-indexed limits in `Type u`.

The second, in the `CategoryTheory.Limits.Types.TypeMax` namespace
constructs limits for functors `F : J ⥤ TypeMax.{v, u}`, for `J : Type v`.
This construction is slightly nicer, as the limit is definitionally just `F.sections`,
rather than `Shrink F.sections`, which makes an arbitrary choice of `u`-small representative.

Hopefully we might be able to entirely remove the `TypeMax` constructions,
but for now they are useful glue for the later parts of the library.
-/

namespace Small

variable [Small.{u} J]

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
noncomputable def limitCone (F : J ⥤ Type u) : Cone F where
  pt := Shrink F.sections
  π :=
    { app := fun j u => ((equivShrink F.sections).symm u).val j
      naturality := fun j j' f => by
        funext x
        simp }

@[ext]
lemma limitCone_pt_ext (F : J ⥤ Type u) {x y : (limitCone F).pt}
    (w : (equivShrink F.sections).symm x = (equivShrink F.sections).symm y) : x = y := by
  aesop

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
noncomputable def limitConeIsLimit (F : J ⥤ Type u) : IsLimit (limitCone.{v, u} F) where
  lift s v := equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_fun (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using congr_fun (w j) x

end Small

-- TODO: If `UnivLE` works out well, we will eventually want to deprecate these
-- definitions, and probably as a first step put them in namespace or otherwise rename them.
section TypeMax

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
noncomputable def limitCone (F : J ⥤ TypeMax.{v, u}) : Cone F where
  pt := F.sections
  π :=
    { app := fun j u => u.val j
      naturality := fun j j' f => by
        funext x
        simp }
#align category_theory.limits.types.limit_cone CategoryTheory.Limits.Types.limitCone

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
noncomputable def limitConeIsLimit (F : J ⥤ TypeMax.{v, u}) : IsLimit (limitCone F) where
  lift s v :=
    { val := fun j => s.π.app j v
      property := fun f => congr_fun (Cone.w s f) _ }
  uniq := fun _ _ w => by
    funext x
    apply Subtype.ext
    funext j
    exact congr_fun (w j) x
#align category_theory.limits.types.limit_cone_is_limit CategoryTheory.Limits.Types.limitConeIsLimit

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
  HasLimit.mk
    { cone := Small.limitCone.{v, u} F
      isLimit := Small.limitConeIsLimit F }

/--
The category of types has all limits.

More specifically, when `UnivLE.{v, u}`, the category `Type u` has all `v`-small limits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance (priority := 1300) hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w', v} (Type u) where
  has_limits_of_shape _ := { }
#align category_theory.limits.types.has_limits_of_size CategoryTheory.Limits.Types.hasLimitsOfSize

variable [Small.{u} J]
/-- The equivalence between the abstract limit of `F` in `TypeMax.{v, u}`
and the "concrete" definition as the sections of `F`.
-/
noncomputable def limitEquivSections (F : J ⥤ Type u) :
    (@limit _ _ _ _ F (hasLimit F) : Type u) ≃ F.sections :=
  isLimitEquivSections (limit.isLimit F)
#align category_theory.limits.types.limit_equiv_sections CategoryTheory.Limits.Types.limitEquivSections

@[simp]
theorem limitEquivSections_apply (F : J ⥤ Type u) (x : limit F) (j : J) :
    ((limitEquivSections F) x : ∀ j, F.obj j) j = limit.π F j x :=
  isLimitEquivSections_apply _ _ _
#align category_theory.limits.types.limit_equiv_sections_apply CategoryTheory.Limits.Types.limitEquivSections_apply

@[simp]
theorem limitEquivSections_symm_apply (F : J ⥤ Type u) (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections F).symm x) = (x : ∀ j, F.obj j) j :=
  isLimitEquivSections_symm_apply _ _ _
#align category_theory.limits.types.limit_equiv_sections_symm_apply CategoryTheory.Limits.Types.limitEquivSections_symm_apply

-- Porting note: `limitEquivSections_symm_apply'` was removed because the linter
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
  (limitEquivSections F).symm ⟨x, h _ _⟩
#align category_theory.limits.types.limit.mk CategoryTheory.Limits.Types.Limit.mk

@[simp]
theorem Limit.π_mk (F : J ⥤ Type u) (x : ∀ j, F.obj j)
    (h : ∀ (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
      limit.π F j (Limit.mk F x h) = x j := by
  dsimp [Limit.mk]
  simp
#align category_theory.limits.types.limit.π_mk CategoryTheory.Limits.Types.Limit.π_mk

-- Porting note: `Limit.π_mk'` was removed because the linter complains it is unnecessary
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
  apply (limitEquivSections F).injective
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

end UnivLE

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

/--
The relation defining the quotient type which implements the colimit of a functor `F : J ⥤ Type u`.
See `CategoryTheory.Limits.Types.Quot`.
-/
def Quot.Rel (F : J ⥤ TypeMax.{v, u}) : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop := fun p p' =>
  ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2
#align category_theory.limits.types.quot.rel CategoryTheory.Limits.Types.Quot.Rel

-- porting note (#10927): removed @[nolint has_nonempty_instance]
/-- A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
def Quot (F : J ⥤ TypeMax.{v, u}) : TypeMax.{v, u} :=
  _root_.Quot (Quot.Rel F)
#align category_theory.limits.types.quot CategoryTheory.Limits.Types.Quot

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
def colimitCocone (F : J ⥤ TypeMax.{v, u}) : Cocone F where
  pt := Quot F
  ι :=
    { app := fun j x => Quot.mk _ ⟨j, x⟩
      naturality := fun _ _ f => funext fun _ => Eq.symm (Quot.sound ⟨f, rfl⟩) }
#align category_theory.limits.types.colimit_cocone CategoryTheory.Limits.Types.colimitCocone

--attribute [local elab_with_expected_type] Quot.lift

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
def colimitCoconeIsColimit (F : J ⥤ TypeMax.{v, u}) : IsColimit (colimitCocone F) where
  desc s :=
    Quot.lift (fun p : Σj, F.obj j => s.ι.app p.1 p.2) fun ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩ => by
      dsimp at hf
      rw [hf]
      exact (congr_fun (Cocone.w s f) x).symm
  uniq s m hm := by
    funext x
    induction' x using Quot.ind with x
    exact congr_fun (hm x.1) x.2
#align category_theory.limits.types.colimit_cocone_is_colimit CategoryTheory.Limits.Types.colimitCoconeIsColimit

namespace Small

variable [Small.{u} J]

/--
The relation defining the quotient type which implements the colimit of a functor `F : J ⥤ Type u`.
See `CategoryTheory.Limits.Types.Quot`.
-/
def Quot.Rel (F : J ⥤ Type u) :
    (Σ j, F.obj ((equivShrink.{u} J).symm j)) → (Σ j, F.obj ((equivShrink.{u} J).symm j)) → Prop :=
  fun p p' => ∃ f, p'.2 = F.map f p.2

/-- A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
def Quot (F : J ⥤ Type u) : Type u :=
  _root_.Quot (Quot.Rel F)

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
noncomputable def colimitCocone (F : J ⥤ Type u) : Cocone F where
  pt := Quot F
  ι :=
    { app := fun j x => Quot.mk _
        ⟨equivShrink J j, F.map (eqToHom (Equiv.symm_apply_apply _ _).symm) x⟩
      naturality := fun j j' f => funext fun x =>
        Eq.symm (Quot.sound ⟨eqToHom (by simp) ≫ f ≫ eqToHom (by simp), by simp⟩) }

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type u) : IsColimit (colimitCocone F) where
  desc s :=
    Quot.lift (fun p => s.ι.app _ p.2) <| by
      rintro ⟨j, x⟩ ⟨j', x'⟩ ⟨f, hf⟩
      dsimp at hf
      rw [hf]
      exact (congr_fun (Cocone.w s f) x).symm
  fac s j := by
    ext x
    let t : j ⟶ (equivShrink J).symm ((equivShrink J) j) := eqToHom (by simp)
    simpa using congrFun (s.ι.naturality t) x
  uniq s m hm := by
    ext x
    induction' x using Quot.ind with x
    dsimp only [id_eq, Functor.const_obj_obj, types_comp_apply, eq_mpr_eq_cast]
    rw [← congrFun (hm ((equivShrink J).symm x.1)) x.2]
    exact congrArg m (Quot.sound ⟨_, rfl⟩)

end Small

section UnivLE

instance hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F :=
  HasColimit.mk
    { cocone := Small.colimitCocone.{v, u} F
      isColimit := Small.colimitCoconeIsColimit F }

instance (priority := 1300) hasColimitsOfSize [UnivLE.{v, u}] : HasColimitsOfSize.{w', v} (Type u) where
  has_colimits_of_shape _ := { }

end UnivLE

section instances

example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (TypeMax.{w, v}) := inferInstance
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max v w) := inferInstance

example : HasColimitsOfSize.{0, 0, v, v+1} (Type v) := inferInstance
example : HasColimitsOfSize.{v, v, v, v+1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasColimitsOfSize.{v, v, u, u+1} (Type u) := inferInstance

end instances

/-- The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
noncomputable def colimitEquivQuot (F : J ⥤ TypeMax.{v, u}) : colimit F ≃ Quot F :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv
#align category_theory.limits.types.colimit_equiv_quot CategoryTheory.Limits.Types.colimitEquivQuot

@[simp]
theorem colimitEquivQuot_symm_apply (F : J ⥤ TypeMax.{v, u}) (j : J) (x : F.obj j) :
    (colimitEquivQuot F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  rfl
#align category_theory.limits.types.colimit_equiv_quot_symm_apply CategoryTheory.Limits.Types.colimitEquivQuot_symm_apply

@[simp]
theorem colimitEquivQuot_apply (F : J ⥤ TypeMax.{v, u}) (j : J) (x : F.obj j) :
    (colimitEquivQuot F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimitEquivQuot F).symm.injective
  simp
#align category_theory.limits.types.colimit_equiv_quot_apply CategoryTheory.Limits.Types.colimitEquivQuot_apply

--porting note: @[simp] was removed because the linter said it was useless
theorem Colimit.w_apply {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x
#align category_theory.limits.types.colimit.w_apply CategoryTheory.Limits.Types.Colimit.w_apply

--porting note: @[simp] was removed because the linter said it was useless
theorem Colimit.ι_desc_apply (F : J ⥤ TypeMax.{v, u}) (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
   congr_fun (colimit.ι_desc s j) x
#align category_theory.limits.types.colimit.ι_desc_apply CategoryTheory.Limits.Types.Colimit.ι_desc_apply

--porting note: @[simp] was removed because the linter said it was useless
theorem Colimit.ι_map_apply {F G : J ⥤ TypeMax.{v, u}} (α : F ⟶ G) (j : J) (x : F.obj j) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x
#align category_theory.limits.types.colimit.ι_map_apply CategoryTheory.Limits.Types.Colimit.ι_map_apply

@[simp]
theorem Colimit.w_apply' {F : J ⥤ Type v} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x
#align category_theory.limits.types.colimit.w_apply' CategoryTheory.Limits.Types.Colimit.w_apply'

@[simp]
theorem Colimit.ι_desc_apply' (F : J ⥤ Type v) (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_fun (colimit.ι_desc s j) x
#align category_theory.limits.types.colimit.ι_desc_apply' CategoryTheory.Limits.Types.Colimit.ι_desc_apply'

@[simp]
theorem Colimit.ι_map_apply' {F G : J ⥤ Type v} (α : F ⟶ G) (j : J) (x) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x
#align category_theory.limits.types.colimit.ι_map_apply' CategoryTheory.Limits.Types.Colimit.ι_map_apply'

theorem colimit_sound {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w, Colimit.w_apply]
#align category_theory.limits.types.colimit_sound CategoryTheory.Limits.Types.colimit_sound

theorem colimit_sound' {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w _ f, ← colimit.w _ f']
  rw [types_comp_apply, types_comp_apply, w]
#align category_theory.limits.types.colimit_sound' CategoryTheory.Limits.Types.colimit_sound'

theorem colimit_eq {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') :
      EqvGen (Quot.Rel F) ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using congr_arg (colimitEquivQuot.{v, u} F) w
#align category_theory.limits.types.colimit_eq CategoryTheory.Limits.Types.colimit_eq

theorem jointly_surjective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t)
    (x : t.pt) : ∃ j y, t.ι.app j y = x := by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (fun _ ↦ ULift.up True) ≠ (⟨· ≠ x⟩))
  · refine h.hom_ext fun j ↦ ?_
    ext y
    exact (true_iff _).mpr (hx j y)
  · exact fun he ↦ of_eq_true (congr_arg ULift.down <| congr_fun he x).symm rfl

theorem jointly_surjective (F : J ⥤ TypeMax.{v, u}) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := jointly_surjective_of_isColimit h x
#align category_theory.limits.types.jointly_surjective CategoryTheory.Limits.Types.jointly_surjective

/-- A variant of `jointly_surjective` for `x : colimit F`. -/
theorem jointly_surjective' {F : J ⥤ TypeMax.{v, u}} (x : colimit F) :
    ∃ j y, colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit F) x
#align category_theory.limits.types.jointly_surjective' CategoryTheory.Limits.Types.jointly_surjective'


namespace FilteredColimit

/- For filtered colimits of types, we can give an explicit description
  of the equivalence relation generated by the relation used to form
  the colimit.  -/
variable (F : J ⥤ TypeMax.{v, u})

/-- An alternative relation on `Σ j, F.obj j`,
which generates the same equivalence relation as we use to define the colimit in `Type` above,
but that is more convenient when working with filtered colimits.

Elements in `F.obj j` and `F.obj j'` are equivalent if there is some `k : J` to the right
where their images are equal.
-/
protected def Rel (x y : Σ j, F.obj j) : Prop :=
  ∃ (k : _) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2
#align category_theory.limits.types.filtered_colimit.rel CategoryTheory.Limits.Types.FilteredColimit.Rel

theorem rel_of_quot_rel (x y : Σ j, F.obj j) :
    Quot.Rel F x y → FilteredColimit.Rel.{v, u} F x y :=
  fun ⟨f, h⟩ => ⟨y.1, f, 𝟙 y.1, by rw [← h, FunctorToTypes.map_id_apply]⟩
#align category_theory.limits.types.filtered_colimit.rel_of_quot_rel CategoryTheory.Limits.Types.FilteredColimit.rel_of_quot_rel

theorem eqvGen_quot_rel_of_rel (x y : Σ j, F.obj j) :
    FilteredColimit.Rel.{v, u} F x y → EqvGen (Quot.Rel F) x y := fun ⟨k, f, g, h⟩ => by
  refine' EqvGen.trans _ ⟨k, F.map f x.2⟩ _ _ _
  · exact (EqvGen.rel _ _ ⟨f, rfl⟩)
  · exact (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨g, h⟩))
#align category_theory.limits.types.filtered_colimit.eqv_gen_quot_rel_of_rel CategoryTheory.Limits.Types.FilteredColimit.eqvGen_quot_rel_of_rel

--attribute [local elab_without_expected_type] nat_trans.app

/-- Recognizing filtered colimits of types. -/
noncomputable def isColimitOf (t : Cocone F) (hsurj : ∀ x : t.pt, ∃ i xi, x = t.ι.app i xi)
    (hinj :
      ∀ i j xi xj,
        t.ι.app i xi = t.ι.app j xj → ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj) :
    IsColimit t := by
  -- Strategy: Prove that the map from "the" colimit of F (defined above) to t.X
  -- is a bijection.
  apply IsColimit.ofIsoColimit (colimit.isColimit F)
  refine' Cocones.ext (Equiv.toIso (Equiv.ofBijective _ _)) _
  · exact colimit.desc F t
  · constructor
    · show Function.Injective _
      intro a b h
      rcases jointly_surjective F (colimit.isColimit F) a with ⟨i, xi, rfl⟩
      rcases jointly_surjective F (colimit.isColimit F) b with ⟨j, xj, rfl⟩
      replace h : (colimit.ι F i ≫ colimit.desc F t) xi = (colimit.ι F j ≫ colimit.desc F t) xj := h
      rw [colimit.ι_desc, colimit.ι_desc] at h
      rcases hinj i j xi xj h with ⟨k, f, g, h'⟩
      change colimit.ι F i xi = colimit.ι F j xj
      rw [← colimit.w F f, ← colimit.w F g]
      change colimit.ι F k (F.map f xi) = colimit.ι F k (F.map g xj)
      rw [h']
    · show Function.Surjective _
      intro x
      rcases hsurj x with ⟨i, xi, rfl⟩
      use colimit.ι F i xi
      apply Colimit.ι_desc_apply
  · intro j
    apply colimit.ι_desc
#align category_theory.limits.types.filtered_colimit.is_colimit_of CategoryTheory.Limits.Types.FilteredColimit.isColimitOf

variable [IsFilteredOrEmpty J]

protected theorem rel_equiv : _root_.Equivalence (FilteredColimit.Rel.{v, u} F) where
  refl x := ⟨x.1, 𝟙 x.1, 𝟙 x.1, rfl⟩
  symm := fun ⟨k, f, g, h⟩ => ⟨k, g, f, h.symm⟩
  trans {x y z} := fun ⟨k, f, g, h⟩ ⟨k', f', g', h'⟩ =>
    let ⟨l, fl, gl, _⟩ := IsFilteredOrEmpty.cocone_objs k k'
    let ⟨m, n, hn⟩ := IsFilteredOrEmpty.cocone_maps (g ≫ fl) (f' ≫ gl)
    ⟨m, f ≫ fl ≫ n, g' ≫ gl ≫ n,
      calc
        F.map (f ≫ fl ≫ n) x.2 = F.map (fl ≫ n) (F.map f x.2) := by simp
        _ = F.map (fl ≫ n) (F.map g y.2) := by rw [h]
        _ = F.map ((g ≫ fl) ≫ n) y.2 := by simp
        _ = F.map ((f' ≫ gl) ≫ n) y.2 := by rw [hn]
        _ = F.map (gl ≫ n) (F.map f' y.2) := by simp
        _ = F.map (gl ≫ n) (F.map g' z.2) := by rw [h']
        _ = F.map (g' ≫ gl ≫ n) z.2 := by simp⟩
#align category_theory.limits.types.filtered_colimit.rel_equiv CategoryTheory.Limits.Types.FilteredColimit.rel_equiv

protected theorem rel_eq_eqvGen_quot_rel :
    FilteredColimit.Rel.{v, u} F = EqvGen (Quot.Rel F) := by
  ext ⟨j, x⟩ ⟨j', y⟩
  constructor
  · apply eqvGen_quot_rel_of_rel
  · rw [← (FilteredColimit.rel_equiv F).eqvGen_iff]
    exact EqvGen.mono (rel_of_quot_rel F)
#align category_theory.limits.types.filtered_colimit.rel_eq_eqv_gen_quot_rel CategoryTheory.Limits.Types.FilteredColimit.rel_eq_eqvGen_quot_rel

theorem colimit_eq_iff_aux {i j : J} {xi : F.obj i} {xj : F.obj j} :
    (colimitCocone.{v, u} F).ι.app i xi = (colimitCocone.{v, u} F).ι.app j xj ↔
      FilteredColimit.Rel.{v, u} F ⟨i, xi⟩ ⟨j, xj⟩ := by
  change Quot.mk _ _ = Quot.mk _ _ ↔ _
  rw [Quot.eq, FilteredColimit.rel_eq_eqvGen_quot_rel]
#align category_theory.limits.types.filtered_colimit.colimit_eq_iff_aux CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff_aux

theorem isColimit_eq_iff {t : Cocone F} (ht : IsColimit t) {i j : J} {xi : F.obj i} {xj : F.obj j} :
    t.ι.app i xi = t.ι.app j xj ↔ ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj := by
  let t' := colimitCocone.{v, u} F
  let e : t' ≅ t := IsColimit.uniqueUpToIso (colimitCoconeIsColimit F) ht
  let e' : t'.pt ≅ t.pt := (Cocones.forget _).mapIso e
  refine' Iff.trans _ (colimit_eq_iff_aux F)
  exact @Equiv.apply_eq_iff_eq _ _ e'.toEquiv ((colimitCocone.{v, u} F).ι.app i xi)
    ((colimitCocone.{v, u} F).ι.app j xj)
#align category_theory.limits.types.filtered_colimit.is_colimit_eq_iff CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff

theorem colimit_eq_iff {i j : J} {xi : F.obj i} {xj : F.obj j} :
    colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj :=
  isColimit_eq_iff _ (colimit.isColimit F)
#align category_theory.limits.types.filtered_colimit.colimit_eq_iff CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff

end FilteredColimit

variable {α β : Type u} (f : α ⟶ β)

section

-- implementation of `HasImage`
/-- the image of a morphism in Type is just `Set.range f` -/
def Image : Type u :=
  Set.range f
#align category_theory.limits.types.image CategoryTheory.Limits.Types.Image

instance [Inhabited α] : Inhabited (Image f) where default := ⟨f default, ⟨_, rfl⟩⟩

/-- the inclusion of `Image f` into the target -/
def Image.ι : Image f ⟶ β :=
  Subtype.val
#align category_theory.limits.types.image.ι CategoryTheory.Limits.Types.Image.ι

instance : Mono (Image.ι f) :=
  (mono_iff_injective _).2 Subtype.val_injective

variable {f}

/-- the universal property for the image factorisation -/
noncomputable def Image.lift (F' : MonoFactorisation f) : Image f ⟶ F'.I :=
  (fun x => F'.e (Classical.indefiniteDescription _ x.2).1 : Image f → F'.I)
#align category_theory.limits.types.image.lift CategoryTheory.Limits.Types.Image.lift

theorem Image.lift_fac (F' : MonoFactorisation f) : Image.lift F' ≫ F'.m = Image.ι f := by
  funext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl
#align category_theory.limits.types.image.lift_fac CategoryTheory.Limits.Types.Image.lift_fac

end

/-- the factorisation of any morphism in Type through a mono. -/
def monoFactorisation : MonoFactorisation f where
  I := Image f
  m := Image.ι f
  e := Set.rangeFactorization f
#align category_theory.limits.types.mono_factorisation CategoryTheory.Limits.Types.monoFactorisation

/-- the factorisation through a mono has the universal property of the image. -/
noncomputable def isImage : IsImage (monoFactorisation f) where
  lift := Image.lift
  lift_fac := Image.lift_fac
#align category_theory.limits.types.is_image CategoryTheory.Limits.Types.isImage

instance : HasImage f :=
  HasImage.mk ⟨_, isImage f⟩

instance : HasImages (Type u) where
  has_image := by infer_instance

instance : HasImageMaps (Type u) where
  has_image_map {f g} st :=
    HasImageMap.transport st (monoFactorisation f.hom) (isImage g.hom)
      (fun x => ⟨st.right x.1, ⟨st.left (Classical.choose x.2), by
        have p := st.w
        replace p := congr_fun p (Classical.choose x.2)
        simp only [Functor.id_obj, Functor.id_map, types_comp_apply] at p
        erw [p, Classical.choose_spec x.2]⟩⟩) rfl

end Types

open Functor Opposite

variable {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]

/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`. -/
@[simps]
noncomputable def limitCompCoyonedaIsoCone (F : J ⥤ C) (X : C) :
    limit (F ⋙ coyoneda.obj (op X)) ≅ ((const J).obj X ⟶ F) where
  hom := fun x => ⟨fun j => limit.π (F ⋙ coyoneda.obj (op X)) j x,
    fun j j' f => by simpa using (congrFun (limit.w (F ⋙ coyoneda.obj (op X)) f) x).symm⟩
  inv := fun ι => Types.Limit.mk _ (fun j => ι.app j)
    fun j j' f => by simpa using (ι.naturality f).symm

/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `X`. -/
@[simps!]
noncomputable def coyonedaCompLimIsoCones (F : J ⥤ C) :
    coyoneda ⋙ (whiskeringLeft _ _ _).obj F ⋙ lim ≅ F.cones :=
  NatIso.ofComponents (fun X => limitCompCoyonedaIsoCone F X.unop)

variable (J) (C) in
/-- A cone on `F` with cone point `X` is the same as an element of `lim Hom(X, F·)`,
    naturally in `F` and `X`. -/
@[simps!]
noncomputable def whiskeringLimYonedaIsoCones : whiskeringLeft _ _ _ ⋙
    (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj coyoneda ≅ cones J C :=
  NatIso.ofComponents coyonedaCompLimIsoCones

/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`. -/
@[simps]
noncomputable def limitCompYonedaIsoCocone (F : J ⥤ C) (X : C) :
    limit (F.op ⋙ yoneda.obj X) ≅ (F ⟶ (const J).obj X) where
  hom := fun x => ⟨fun j => limit.π (F.op ⋙ yoneda.obj X) (Opposite.op j) x,
    fun j j' f => by simpa using congrFun (limit.w (F.op ⋙ yoneda.obj X) f.op) x⟩
  inv := fun ι => Types.Limit.mk _ (fun j => ι.app j.unop) (by simp)

/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
    naturally in `X`. -/
@[simps!]
noncomputable def yonedaCompLimIsoCocones (F : J ⥤ C) :
    yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙ lim ≅ F.cocones :=
  NatIso.ofComponents (limitCompYonedaIsoCocone F)

variable (J) (C) in
/-- A cocone on `F` with cocone point `X` is the same as an element of `lim Hom(F·, X)`,
    naturally in `F` and `X`. -/
@[simps!]
noncomputable def opHomCompWhiskeringLimYonedaIsoCocones : opHom _ _ ⋙ whiskeringLeft _ _ _ ⋙
      (whiskeringRight _ _ _).obj lim ⋙ (whiskeringLeft _ _ _).obj yoneda ≅ cocones J C :=
  NatIso.ofComponents (fun F => yonedaCompLimIsoCocones F.unop)

end CategoryTheory.Limits
