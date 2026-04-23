/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Batteries.Tactic.Init
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ULift
import Mathlib.Init
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.StacksAttribute
import Mathlib.Util.CompileInductive

/-!
# Colimits in the category of types

We show that the category of types has all colimits, by providing the usual concrete models.

-/

@[expose] public section

universe u' v u w

namespace CategoryTheory

open Limits ConcreteCategory

variable {J : Type v} [Category.{w} J]

namespace Functor

instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (F.ColimitType) :=
  small_of_surjective Quot.mk_surjective

variable (F : J ⥤ Type u)

/-- If `F : J ⥤ Type u`, then the data of a "type-theoretic" cocone of `F`
with a point in `Type u` is the same as the data of a cocone (in a categorical sense). -/
@[simps apply_pt symm_apply_pt apply_ι_app symm_apply_ι]
def coconeTypesEquiv : CoconeTypes.{u} F ≃ Cocone F where
  toFun c :=
    { pt := c.pt
      ι := { app j := TypeCat.ofHom (c.ι j) } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x }
  left_inv _ := rfl
  right_inv _ := rfl

variable {F}

set_option backward.isDefEq.respectTransparency false in
lemma CoconeTypes.isColimit_iff (c : CoconeTypes.{u} F) :
    c.IsColimit ↔ Nonempty (Limits.IsColimit (F.coconeTypesEquiv c)) := by
  constructor
  · intro hc
    exact
     ⟨{ desc s := TypeCat.ofHom (fun x => hc.desc (F.coconeTypesEquiv.symm s) x)
        fac s j := by
          ext x
          exact congr_fun (hc.fac (F.coconeTypesEquiv.symm s) j) x
        uniq s m hm := by
          ext x
          exact congr_fun (hc.funext fun j ↦ funext fun y ↦ by simp [← hm j]) x }⟩
  · rintro ⟨hc⟩
    classical
    refine ⟨⟨fun x y h ↦ ?_, fun x ↦ ?_⟩⟩
    · let f (z : F.ColimitType) : ULift.{u} Bool := ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      suffices ∀ z, hc.desc (F.coconeTypesEquiv (F.coconeTypes.postcomp f))
          (F.descColimitType c z) = f z by rw [← this x, h, ← this y]
      intro z
      obtain ⟨j, z, rfl⟩ := F.ιColimitType_jointly_surjective z
      exact ConcreteCategory.congr_hom (hc.fac _ j) z
    · let f₁ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        TypeCat.ofHom (fun _ => ULift.up true)
      let f₂ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        TypeCat.ofHom (fun x => ULift.up (∃ a, F.descColimitType c a = x))
      suffices f₁ = f₂ by
        have := ConcreteCategory.congr_hom this x
        simpa [f₁, f₂] using this
      refine hc.hom_ext fun j => ?_
      ext x
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

theorem small_colimitType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] :
    Small.{u} F.ColimitType :=
  (hasColimit_iff_small_colimitType F).mp inferInstance

instance hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F :=
  (hasColimit_iff_small_colimitType F).mpr inferInstance

instance hasColimitsOfShape [Small.{u} J] : HasColimitsOfShape J (Type u) where

/-- The category of types has all colimits. -/
@[stacks 002U]
instance (priority := 1300) hasColimitsOfSize [UnivLE.{v, u}] :
    HasColimitsOfSize.{w, v} (Type u) where

section instances

example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max w v)) :=
  inferInstance
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max v w)) :=
  inferInstance

example : HasColimitsOfSize.{0, 0, v, v + 1} (Type v) := inferInstance
example : HasColimitsOfSize.{v, v, v, v + 1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasColimitsOfSize.{v, v, u, u + 1} (Type u) := inferInstance

end instances

namespace TypeMax

/-- (internal implementation) the colimit cocone of a functor,
implemented as a quotient of a sigma type
-/
abbrev colimitCocone (F : J ⥤ Type (max v u)) : Cocone F :=
  F.coconeTypesEquiv F.coconeTypes

/-- (internal implementation) the fact that the proposed colimit cocone is the colimit -/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type (max v u)) :
    IsColimit (colimitCocone F) :=
  (F.coconeTypes.isColimit_iff.1 F.isColimit_coconeTypes).some

end TypeMax

variable (F : J ⥤ Type u) [HasColimit F]

attribute [local instance] small_colimitType_of_hasColimit

/-- The equivalence between the abstract colimit of `F` in `TypeCat u`
and the "concrete" definition as a quotient.
-/
noncomputable def colimitEquivColimitType : (colimit F : Type u) ≃ F.ColimitType :=
  (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm

@[simp]
theorem colimitEquivColimitType_symm_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  congr_hom (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x

@[simp]
theorem colimitEquivColimitType_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimitEquivColimitType F).symm.injective
  simp

-- We don’t want to add `simp` to the original lemmas here
attribute [elementwise] colimit.w colimit.ι_desc colimit.ι_map
attribute [simp] colimit.w_apply colimit.ι_desc_apply colimit.ι_map_apply

variable {F} in
@[deprecated colimit.w_apply (since := "2026-03-06")]
theorem Colimit.w_apply {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x := by
  rw [← comp_apply]
  exact congr_hom (colimit.w F f) x

@[deprecated colimit.ι_desc_apply (since := "2026-03-06")]
theorem Colimit.ι_desc_apply (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_hom (colimit.ι_desc s j) x

@[deprecated colimit.ι_map_apply (since := "2026-03-06")]
theorem Colimit.ι_map_apply {F G : J ⥤ Type u} [HasColimitsOfShape J (Type u)]
    (α : F ⟶ G) (j : J) (x : F.obj j) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_hom (colimit.ι_map α j) x

-- These were variations of the aliased lemmas with different universe variables.
-- It appears those are now strictly more powerful.
variable {F} in
theorem colimit_sound {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w, colimit.w_apply]

variable {F} in
theorem colimit_sound' {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w_apply _ f, ← colimit.w_apply _ f', w]

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
  apply (_ : (TypeCat.ofHom (fun _ ↦ ULift.up True) :
      t.pt ⟶ (ULift.{u} Prop)) ≠
    (TypeCat.ofHom (fun y ↦ ULift.up (y ≠ x))))
  · refine h.hom_ext fun j ↦ ?_
    ext y
    simp only [Functor.const_obj_obj, TypeCat.Fun.toFun_apply, comp_apply, hom_ofHom,
      TypeCat.Fun.coe_mk, ne_eq, true_iff]
    exact hx j y
  · intro he
    have := ConcreteCategory.congr_hom he x
    dsimp at this
    exact of_eq_true (congrArg ULift.down this).symm rfl

theorem jointly_surjective (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    ∃ (j : J) (y : F.obj j), t.ι.app j y = x := jointly_surjective_of_isColimit h x

variable {F} in
/-- A variant of `jointly_surjective` for `x : colimit F`. -/
theorem jointly_surjective' (x : colimit F) :
    ∃ (j : J) (y : F.obj j), colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit F) x

/-- If a colimit is nonempty, also its index category is nonempty. -/
theorem nonempty_of_nonempty_colimit {F : J ⥤ Type u} [HasColimit F] :
    Nonempty (colimit F) → Nonempty J :=
  Nonempty.map <| Sigma.fst ∘ Quot.out ∘ (colimitEquivColimitType F).toFun

end CategoryTheory.Limits.Types
