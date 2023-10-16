/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.Data.TypeMax
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Filtered.Basic

#align_import category_theory.limits.types from "leanprover-community/mathlib"@"4aa2a2e17940311e47007f087c9df229e7f12942"

/-!
# Limits in the category of types.

We show that the category of types has all (co)limits, by providing the usual concrete models.

We also give a characterisation of filtered colimits in `Type`, via
`colimit.ι F i xi = colimit.ι F j xj ↔ ∃ k (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj`.

Finally, we prove the category of types has categorical images,
and that these agree with the range of a function.
-/

set_option autoImplicit true


open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits.Types

section limit_characterization

variable {J : Type v} [Category J] {F : J ⥤ Type u}

/-- Given a section of a functor F into `Type*`,
  construct a cone over F with `PUnit` as the cone point. -/
def cone_of_section {s} (hs : s ∈ F.sections) : Cone F where
  pt := PUnit
  π :=
  { app := fun j _ ↦ s j,
    naturality := fun i j f ↦ by ext; exact (hs f).symm }

/-- Given a cone over a functor F into `Type*` and an element in the cone point,
  construct a section of F. -/
def section_of_cone (c : Cone F) (x : c.pt) : F.sections :=
  ⟨fun j ↦ c.π.app j x, fun f ↦ congr_fun (c.π.naturality f).symm x⟩

theorem isLimit_iff (c : Cone F) :
    Nonempty (IsLimit c) ↔ ∀ s ∈ F.sections, ∃! x : c.pt, ∀ i, c.π.app i x = s i := by
  refine ⟨fun ⟨t⟩ s hs ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · let cs := cone_of_section hs
    exact ⟨t.lift cs ⟨⟩, fun j ↦ congr_fun (t.fac cs j) ⟨⟩,
      fun x hx ↦ congr_fun (t.uniq cs (fun _ ↦ x) fun j ↦ funext fun _ ↦ hx j) ⟨⟩⟩
  · choose x hx using fun c y ↦ h _ (section_of_cone c y).2
    exact ⟨x, fun c j ↦ funext fun y ↦ (hx c y).1 j,
      fun c f hf ↦ funext fun y ↦ (hx c y).2 (f y) (fun j ↦ congr_fun (hf j) y)⟩

/-- The equivalence between a limiting cone of `F` in `Type u` and the "concrete" definition as the
sections of `F`.
-/
noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := section_of_cone c
  invFun s := t.lift (cone_of_section s.2) ⟨⟩
  left_inv x := (congr_fun (t.uniq (cone_of_section _) (fun _ ↦ x) fun _ ↦ rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j ↦ congr_fun (t.fac (cone_of_section s.2) j) ⟨⟩)
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

variable {J : Type v} [Category J]

/-! We now provide three related implementations in the category of types.

The first, in the `TypeMax` section
constructs limits for functors `F : J ⥤ TypeMax.{v, u}`, for `J : Type v`.

The second, in the `CategoryTheory.Limits.Types.Initial` namespace
constructs limits for functors `F : J ⥤ Type u` for `J` that admits an initial functor
from another indexing category `J' : Type u`, and is defined in terms of the first
using `CategoryTheory.Functor.Initial.isLimitWhiskerEquiv`.

The third, in the `CategoryTheory.Limits.Types.Small` namespace,
assumes `UnivLE.{v, u}` and constructs `v`-small limits in `Type u`,
and is defined by specializing the second to the equivalence `Shrink.{u} J ≌ J`
which is initial.

-/

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
noncomputable def limitConeIsLimit (F : J ⥤ TypeMax.{v, u}) : IsLimit (limitCone.{v, u} F) where
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

/--
The relation defining the quotient type which implements the colimit of a functor `F : J ⥤ Type u`.
See `CategoryTheory.Limits.Types.Quot`.
-/
def Quot.Rel (F : J ⥤ TypeMax.{v, u}) : (Σ j, F.obj j) → (Σ j, F.obj j) → Prop := fun p p' =>
  ∃ f : p.1 ⟶ p'.1, p'.2 = F.map f p.2
#align category_theory.limits.types.quot.rel CategoryTheory.Limits.Types.Quot.Rel

-- porting note: removed @[nolint has_nonempty_instance]
/-- A quotient type implementing the colimit of a functor `F : J ⥤ Type u`,
as pairs `⟨j, x⟩` where `x : F.obj j`, modulo the equivalence relation generated by
`⟨j, x⟩ ~ ⟨j', x'⟩` whenever there is a morphism `f : j ⟶ j'` so `F.map f x = x'`.
-/
def Quot (F : J ⥤ TypeMax.{v, u}) : TypeMax.{v, u} :=
  _root_.Quot (Quot.Rel.{v, u} F)
#align category_theory.limits.types.quot CategoryTheory.Limits.Types.Quot

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
def colimitCocone (F : J ⥤ TypeMax.{v, u}) : Cocone F where
  pt := Quot.{v, u} F
  ι :=
    { app := fun j x => Quot.mk _ ⟨j, x⟩
      naturality := fun _ _ f => funext fun _ => Eq.symm (Quot.sound ⟨f, rfl⟩) }
#align category_theory.limits.types.colimit_cocone CategoryTheory.Limits.Types.colimitCocone

--attribute [local elab_with_expected_type] Quot.lift

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
def colimitCoconeIsColimit (F : J ⥤ TypeMax.{v, u}) : IsColimit (colimitCocone.{v, u} F) where
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

/-- The category of types has all colimits.

See <https://stacks.math.columbia.edu/tag/002U>.
-/
instance hasColimitsOfSize : HasColimitsOfSize.{v} TypeMax.{v, u} where
  has_colimits_of_shape _ :=
    { has_colimit := fun F =>
        HasColimit.mk
          { cocone := colimitCocone.{v, u} F
            isColimit := colimitCoconeIsColimit F } }
#align category_theory.limits.types.has_colimits_of_size CategoryTheory.Limits.Types.hasColimitsOfSize

instance : HasColimits (Type u) :=
  Types.hasColimitsOfSize.{u, u}

instance hasColimit (F : J ⥤ TypeMax.{v, u}) : HasColimit F :=
  (Types.hasColimitsOfSize.{v, u}.has_colimits_of_shape J).has_colimit F

instance hasColimit' (F : J ⥤ Type v) : HasColimit F :=
  hasColimit.{v, v} F

/-- The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
noncomputable def colimitEquivQuot (F : J ⥤ TypeMax.{v, u}) : colimit F ≃ Quot.{v, u} F :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv
#align category_theory.limits.types.colimit_equiv_quot CategoryTheory.Limits.Types.colimitEquivQuot

@[simp]
theorem colimitEquivQuot_symm_apply (F : J ⥤ TypeMax.{v, u}) (j : J) (x : F.obj j) :
    (colimitEquivQuot.{v, u} F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  rfl
#align category_theory.limits.types.colimit_equiv_quot_symm_apply CategoryTheory.Limits.Types.colimitEquivQuot_symm_apply

@[simp]
theorem colimitEquivQuot_apply (F : J ⥤ TypeMax.{v, u}) (j : J) (x : F.obj j) :
    (colimitEquivQuot.{v, u} F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
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
    colim.{v, v}.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x
#align category_theory.limits.types.colimit.ι_map_apply CategoryTheory.Limits.Types.Colimit.ι_map_apply

@[simp]
theorem Colimit.w_apply' {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x
#align category_theory.limits.types.colimit.w_apply' CategoryTheory.Limits.Types.Colimit.w_apply'

@[simp]
theorem Colimit.ι_desc_apply' (F : J ⥤ TypeMax.{v, u}) (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_fun (colimit.ι_desc s j) x
#align category_theory.limits.types.colimit.ι_desc_apply' CategoryTheory.Limits.Types.Colimit.ι_desc_apply'

@[simp]
theorem Colimit.ι_map_apply' {F G : J ⥤ TypeMax.{v, u}} (α : F ⟶ G) (j : J) (x) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x
#align category_theory.limits.types.colimit.ι_map_apply' CategoryTheory.Limits.Types.Colimit.ι_map_apply'

theorem colimit_sound {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w, Colimit.w_apply.{v, u}]
#align category_theory.limits.types.colimit_sound CategoryTheory.Limits.Types.colimit_sound

theorem colimit_sound' {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w _ f, ← colimit.w _ f']
  rw [types_comp_apply, types_comp_apply, w]
#align category_theory.limits.types.colimit_sound' CategoryTheory.Limits.Types.colimit_sound'

theorem colimit_eq {F : J ⥤ TypeMax.{v, u}} {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') :
      EqvGen (Quot.Rel.{v, u} F) ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using congr_arg (colimitEquivQuot.{v, u} F) w
#align category_theory.limits.types.colimit_eq CategoryTheory.Limits.Types.colimit_eq

theorem jointly_surjective (F : J ⥤ TypeMax.{v, u}) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := by
  suffices (fun x : t.pt => ULift.up (∃ j y, t.ι.app j y = x)) = fun _ => ULift.up.{max v u} True by
    have := congr_fun this x
    simpa using congr_arg ULift.down this
  refine' h.hom_ext _
  intro j
  funext y
  simp only [Functor.const_obj_obj, types_comp_apply, ULift.up_inj, eq_iff_iff, iff_true]
  exact ⟨j, y, rfl⟩
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
    Quot.Rel.{v, u} F x y → FilteredColimit.Rel.{v, u} F x y :=
  fun ⟨f, h⟩ => ⟨y.1, f, 𝟙 y.1, by rw [← h, FunctorToTypes.map_id_apply]⟩
#align category_theory.limits.types.filtered_colimit.rel_of_quot_rel CategoryTheory.Limits.Types.FilteredColimit.rel_of_quot_rel

theorem eqvGen_quot_rel_of_rel (x y : Σ j, F.obj j) :
    FilteredColimit.Rel.{v, u} F x y → EqvGen (Quot.Rel.{v, u} F) x y := fun ⟨k, f, g, h⟩ => by
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
      apply Colimit.ι_desc_apply.{v, u}
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
    FilteredColimit.Rel.{v, u} F = EqvGen (Quot.Rel.{v, u} F) := by
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

end CategoryTheory.Limits.Types
