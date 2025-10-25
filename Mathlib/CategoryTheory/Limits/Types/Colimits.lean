/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
import Mathlib.Logic.UnivLE
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types.ColimitType

/-!
# Colimits in the category of types

We show that the category of types has all colimits, by providing the usual concrete models.

-/

universe u' v u w

namespace CategoryTheory

open Limits

variable {J : Type v} [Category.{w} J]

namespace Functor

instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (F.ColimitType) :=
  small_of_surjective Quot.mk_surjective

variable (F : J ⥤ Type u)

/-- If `F : J ⥤ Type u`, then the data of a "type-theoretic" cocone of `F`
with a point in `Type u` is the same as the data of a cocone (in a categorical sense). -/
@[simps]
def coconeTypesEquiv : CoconeTypes.{u} F ≃ Cocone F where
  toFun c :=
    { pt := c.pt
      ι := { app j := c.ι j } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality := c.w }
  left_inv _ := rfl
  right_inv _ := rfl

variable {F}

lemma CoconeTypes.isColimit_iff (c : CoconeTypes.{u} F) :
    c.IsColimit ↔ Nonempty (Limits.IsColimit (F.coconeTypesEquiv c)) := by
  constructor
  · intro hc
    exact
     ⟨{ desc s := hc.desc (F.coconeTypesEquiv.symm s)
        fac s j := hc.fac (F.coconeTypesEquiv.symm s) j
        uniq s m hm := hc.funext (fun j ↦ by
          rw [hc.fac]
          exact hm j )}⟩
  · rintro ⟨hc⟩
    classical
    refine ⟨⟨fun x y h ↦ ?_, fun x ↦ ?_⟩⟩
    · let f (z : F.ColimitType) : ULift.{u} Bool := ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      have : (hc.desc (F.coconeTypesEquiv (F.coconeTypes.postcomp f))).comp
          (F.descColimitType c) = f := by
        ext z
        obtain ⟨j, z, rfl⟩ := F.ιColimitType_jointly_surjective z
        exact congr_fun (hc.fac _ j) z
      simp only [← this, coconeTypesEquiv_apply_pt, Function.comp_apply, h]
    · let f₁ : c.pt ⟶ ULift.{u} Bool := fun _ => ULift.up true
      let f₂ : c.pt ⟶ ULift.{u} Bool := fun x => ULift.up (∃ a, F.descColimitType c a = x)
      suffices f₁ = f₂ by simpa [f₁, f₂] using congrFun this x
      refine hc.hom_ext fun j => funext fun x => ?_
      simpa [f₁, f₂] using ⟨F.ιColimitType j x, by simp⟩

end Functor

namespace Limits.Types

theorem isColimit_iff_coconeTypesIsColimit {F : J ⥤ Type u} (c : Cocone F) :
    Nonempty (IsColimit c) ↔ (F.coconeTypesEquiv.symm c).IsColimit := by
  simp only [Functor.CoconeTypes.isColimit_iff, Equiv.apply_symm_apply]

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
noncomputable abbrev colimitCocone (F : J ⥤ Type u) [Small.{u} F.ColimitType] : Cocone F :=
  F.coconeTypesEquiv (F.coconeTypes.postcomp (equivShrink.{u} F.ColimitType))

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type u) [Small.{u} F.ColimitType] :
    IsColimit (colimitCocone F) :=
  Nonempty.some ((isColimit_iff_coconeTypesIsColimit _).2
    (F.isColimit_coconeTypes.of_equiv (equivShrink.{u} F.ColimitType) (by aesop)))

theorem hasColimit_iff_small_colimitType (F : J ⥤ Type u) :
    HasColimit F ↔ Small.{u} F.ColimitType :=
  ⟨fun _ ↦ small_of_injective
      ((isColimit_iff_coconeTypesIsColimit _).1 ⟨colimit.isColimit F⟩).bijective.1,
    fun _ ↦ ⟨_, colimitCoconeIsColimit F⟩⟩

@[deprecated (since := "2025-06-22")] alias hasColimit_iff_small_quot :=
  hasColimit_iff_small_colimitType

theorem small_colimitType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] :
    Small.{u} F.ColimitType :=
  (hasColimit_iff_small_colimitType F).mp inferInstance

@[deprecated (since := "2025-06-22")] alias small_quot_of_hasColimit :=
  small_colimitType_of_hasColimit

instance hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F :=
  (hasColimit_iff_small_colimitType F).mpr inferInstance

instance hasColimitsOfShape [Small.{u} J] : HasColimitsOfShape J (Type u) where

/-- The category of types has all colimits. -/
@[stacks 002U]
instance (priority := 1300) hasColimitsOfSize [UnivLE.{v, u}] :
    HasColimitsOfSize.{w, v} (Type u) where

section instances

example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max w v) := inferInstance
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type max v w) := inferInstance

example : HasColimitsOfSize.{0, 0, v, v + 1} (Type v) := inferInstance
example : HasColimitsOfSize.{v, v, v, v + 1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasColimitsOfSize.{v, v, u, u + 1} (Type u) := inferInstance

end instances

namespace TypeMax

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
abbrev colimitCocone (F : J ⥤ Type max v u) : Cocone F :=
  F.coconeTypesEquiv F.coconeTypes

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type max v u) :
    IsColimit (colimitCocone F) :=
  (F.coconeTypes.isColimit_iff.1 F.isColimit_coconeTypes).some

end TypeMax

variable (F : J ⥤ Type u) [HasColimit F]

attribute [local instance] small_colimitType_of_hasColimit

/-- The equivalence between the abstract colimit of `F` in `Type u`
and the "concrete" definition as a quotient.
-/
noncomputable def colimitEquivColimitType : colimit F ≃ F.ColimitType :=
  (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm

@[simp]
theorem colimitEquivColimitType_symm_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  congrFun (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x

@[simp]
theorem colimitEquivColimitType_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimitEquivColimitType F).symm.injective
  simp

variable (J) in
/-- `Quot` is functorial, so long as the universe levels work out. -/
@[simps]
noncomputable def _root_.CategoryTheory.Functor.quotFunctor [Small.{u} J] :
    (J ⥤ Type u) ⥤ Type max u v where
  obj F := Quot F
  map {F G} η x := by
    refine Quot.map (Sigma.map id η.app)
      (fun ⟨j, x⟩ ⟨j', y⟩ ⟨(f : j ⟶ j'), (hf : y = F.map f x)⟩ ↦ ?h) x
    subst hf
    simp only [Sigma.map, id_eq]
    simp_rw [← types_comp_apply, η.naturality, types_comp_apply]
    exact ⟨f, rfl⟩

  map_id F := by
    ext ⟨j, x⟩
    simp [Sigma.map, Quot.map]
  map_comp {F G H} η ϑ := by
    ext ⟨j, x⟩
    simp [Sigma.map, Quot.map]


/-- `colimitEquivQuot` is natural in `F`. -/
@[simps!]
noncomputable def colimIsoQuotFunctor :
    colim (J := J) (C := Type max v u) ≅ Functor.quotFunctor J :=
  NatIso.ofComponents (Types.colimitEquivQuot · |>.toIso) fun {F G} η ↦ by
    apply colimit.hom_ext
    intro j
    ext x
    simp_rw [← Category.assoc, colimit.ι_map]
    simp [Sigma.map, Quot.map]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11119): @[simp] was removed because the linter said it was useless
variable {F} in
@[simp]
theorem Colimit.w_apply {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x :=
  congr_fun (colimit.w F f) x

@[simp]
theorem Colimit.ι_desc_apply (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_fun (colimit.ι_desc s j) x

@[simp]
theorem Colimit.ι_map_apply {F G : J ⥤ Type u} [HasColimitsOfShape J (Type u)] (α : F ⟶ G) (j : J)
    (x : F.obj j) : colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_fun (colimit.ι_map α j) x

-- These were variations of the aliased lemmas with different universe variables.
-- It appears those are now strictly more powerful.
@[deprecated (since := "2025-08-22")] alias Colimit.w_apply' := Colimit.w_apply
@[deprecated (since := "2025-08-22")] alias Colimit.ι_desc_apply' := Colimit.ι_desc_apply
@[deprecated (since := "2025-08-22")] alias Colimit.ι_map_apply' := Colimit.ι_map_apply

variable {F} in
theorem colimit_sound {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w, Colimit.w_apply]

variable {F} in
theorem colimit_sound' {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w _ f, ← colimit.w _ f']
  rw [types_comp_apply, types_comp_apply, w]

variable {F} in
theorem colimit_eq {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') :
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using congr_arg (colimitEquivColimitType F) w

theorem jointly_surjective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t)
    (x : t.pt) : ∃ j y, t.ι.app j y = x := by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (fun _ ↦ ULift.up True) ≠ (⟨· ≠ x⟩))
  · refine h.hom_ext fun j ↦ ?_
    ext y
    exact (true_iff _).mpr (hx j y)
  · exact fun he ↦ of_eq_true (congr_arg ULift.down <| congr_fun he x).symm rfl

theorem jointly_surjective (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x := jointly_surjective_of_isColimit h x

variable {F} in
/-- A variant of `jointly_surjective` for `x : colimit F`. -/
theorem jointly_surjective' (x : colimit F) :
    ∃ j y, colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit F) x

/-- If a colimit is nonempty, also its index category is nonempty. -/
theorem nonempty_of_nonempty_colimit {F : J ⥤ Type u} [HasColimit F] :
    Nonempty (colimit F) → Nonempty J :=
  Nonempty.map <| Sigma.fst ∘ Quot.out ∘ (colimitEquivColimitType F).toFun

@[deprecated (since := "2025-06-22")] alias Quot.Rel := Functor.ColimitTypeRel
@[deprecated (since := "2025-06-22")] alias Quot := Functor.ColimitType
@[deprecated (since := "2025-06-22")] alias Quot.ι := Functor.ιColimitType
@[deprecated (since := "2025-06-22")] alias Quot.jointly_surjective :=
  Functor.ιColimitType_jointly_surjective
@[deprecated (since := "2025-06-22")] alias Quot.desc := Functor.descColimitType
@[deprecated (since := "2025-06-22")] alias Quot.ι_desc := Functor.descColimitType_comp_ι
@[deprecated (since := "2025-06-22")] alias Quot.map_ι := Functor.ιColimitType_map
@[deprecated (since := "2025-06-22")] alias isColimit_iff_bijective_desc :=
  isColimit_iff_coconeTypesIsColimit
@[deprecated (since := "2025-06-22")] alias colimitEquivQuot := colimitEquivColimitType
@[deprecated (since := "2025-06-22")] alias colimitEquivQuot_symm_apply :=
  colimitEquivColimitType_symm_apply
@[deprecated (since := "2025-06-22")] alias colimitEquivQuot_apply :=
  colimitEquivColimitType_apply

end CategoryTheory.Limits.Types
