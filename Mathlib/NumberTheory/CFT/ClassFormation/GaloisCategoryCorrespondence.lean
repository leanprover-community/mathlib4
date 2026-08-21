/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryAut

/-!
# ...

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

namespace CategoryTheory

open Limits PreGaloisCategory

variable {C : Type*} [Category* C]

namespace SingleObj

variable {X : C} (H : Subgroup (Aut X))

abbrev HasQuotient {X : C} (H : Subgroup (Aut X)) :=
  HasColimit (SingleObj.functor ((Aut.toEnd X).comp H.subtype))

variable [HasQuotient H]

noncomputable def quotient : C :=
  colimit (SingleObj.functor ((Aut.toEnd X).comp H.subtype))

namespace quotient

noncomputable def π : X ⟶ quotient H :=
  colimit.ι (SingleObj.functor ((Aut.toEnd X).comp H.subtype))
    (Quiver.SingleObj.star _)

variable {H} in
@[reassoc (attr := simp)]
lemma w (h : H) : h.val.hom ≫ π H = π H :=
  colimit.w (SingleObj.functor ((Aut.toEnd X).comp H.subtype)) (Quiver.SingleObj.toHom h)

variable {H} in
@[reassoc (attr := simp)]
lemma w' (h : H) : h.val.inv ≫ π H = π H := w (h⁻¹)

set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible]
noncomputable def cocone :
    Cocone (SingleObj.functor ((Aut.toEnd X).comp H.subtype)) where
  pt := SingleObj.quotient H
  ι := SingleObj.natTrans (SingleObj.quotient.π H) (fun h ↦ by simp [Aut.unitsEndEquivAut])

noncomputable def isColimit : IsColimit (cocone H) :=
  colimit.isColimit (SingleObj.functor ((Aut.toEnd X).comp H.subtype))

instance {X : C} (H : Subgroup (Aut X)) [SingleObj.HasQuotient H] :
    Epi (SingleObj.quotient.π H) where
  left_cancellation _ _ h := (isColimit H).hom_ext (fun _ ↦ h)

end quotient

end SingleObj

namespace GaloisCategory

variable [GaloisCategory C]

instance {X : C} [PreGaloisCategory.IsConnected X] (H : Subgroup (Aut X)) :
    SingleObj.HasQuotient H := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} H
  have := hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm (C := C)
  infer_instance

instance {X : C} [PreGaloisCategory.IsConnected X] (H : Subgroup (Aut X)) :
    PreGaloisCategory.IsConnected (SingleObj.quotient H) :=
  PreGaloisCategory.IsConnected.of_epi (SingleObj.quotient.π H)

instance {X : C} [IsGalois X] (H : Subgroup (Aut X)) :
    IsGaloisCover (SingleObj.quotient.π H) := by
  rw [isGaloisCover_def]
  sorry

section

variable {Y X : C} {f : Y ⟶ X}
  [PreGaloisCategory.IsConnected X] [PreGaloisCategory.IsConnected Y]
  (H : Subgroup (Aut (Over.mk f)))

noncomputable abbrev overQuotient : Over X := SingleObj.quotient H

noncomputable abbrev overQuotientπ : Y ⟶ (overQuotient H).left :=
  (SingleObj.quotient.π H).left

instance : PreGaloisCategory.IsConnected (overQuotient H).left := by
  rw [← isConnected_over_iff]
  infer_instance

instance [IsGaloisCover f] : IsGaloisCover (overQuotientπ H) :=
  (isGalois_iff_of_isEquivalence
    (Over.iteratedSliceEquiv (overQuotient H)).functor
      (Over.mk (Y := Over.mk f) (Over.homMk (overQuotientπ H)))).2 (by
        change IsGaloisCover (SingleObj.quotient.π H)
        infer_instance)

@[simp]
lemma range_overMap_overQuotientπ :
    (Aut.overMap (overQuotientπ H) (overQuotient H).hom f).range = H := by
  sorry

end

lemma exists_of_subgroup
    {Y X : C} {f : Y ⟶ X} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] [IsGaloisCover f] (H : Subgroup (Aut (Over.mk f))) :
    ∃ (Z : C) (_ : PreGaloisCategory.IsConnected Z) (a : Y ⟶ Z) (b : Z ⟶ X) (fac : a ≫ b = f)
      (_ : IsGaloisCover a), (Aut.overMap a b f).range = H :=
  ⟨(overQuotient H).left, inferInstance, overQuotientπ H, (overQuotient H).hom,
    by simp, inferInstance, by simp⟩

lemma isGaloisCover_iff_normal
    {Z Y X : C} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X) [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    IsGaloisCover g ↔ (Aut.overMap f g fg).range.Normal := sorry

lemma exists_of_normal_subgroup
    {Y X : C} {f : Y ⟶ X} [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    [IsGaloisCover f] (H : Subgroup (Aut (Over.mk f))) [H.Normal] :
    ∃ (Z : C) (_ :PreGaloisCategory.IsConnected Z) (a : Y ⟶ Z) (b : Z ⟶ X) (fac : a ≫ b = f)
      (_ : IsGaloisCover a) (_ : IsGaloisCover b), (Aut.overMap a b f).range = H := by
  obtain ⟨Z, _, a, b, fac, _, h⟩ := exists_of_subgroup H
  refine ⟨Z, inferInstance, a, b, fac, inferInstance, ?_, h⟩
  rw [isGaloisCover_iff_normal a b f, h]
  infer_instance

end GaloisCategory

end CategoryTheory
