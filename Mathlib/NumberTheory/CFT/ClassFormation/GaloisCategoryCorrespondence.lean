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

universe w

namespace CategoryTheory

open Limits PreGaloisCategory

variable {C : Type*} [Category* C]

namespace Limits.SingleObj

variable {G X : Type*} [Group G] {φ : G →* End X}

lemma eq_iff_of_coconeTypesIsColimit {c : (SingleObj.functor φ).CoconeTypes}
    (hc : c.IsColimit) {x y : X} :
    c.ι (SingleObj.star _) x = c.ι (SingleObj.star _) y ↔
      ∃ (σ : G), φ σ x = y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have :
      (SingleObj.functor φ).ιColimitType (SingleObj.star _) x =
        (SingleObj.functor φ).ιColimitType (SingleObj.star _) y :=
      hc.equiv.injective (by simpa)
    exact Quotient.exact (congr_arg (colimitTypeRelEquivOrbitRelQuotient _) this.symm)
  · rintro ⟨σ, rfl⟩
    exact (c.ι_naturality_apply _ _).symm

lemma eq_iff_of_isColimit {c : Cocone (SingleObj.functor φ)}
    (hc : IsColimit c) {x y : X} :
    c.ι.app (SingleObj.star _) x = c.ι.app (SingleObj.star _) y ↔
      ∃ (g : G), φ g x = y :=
  eq_iff_of_coconeTypesIsColimit
    ((Types.isColimit_iff_coconeTypesIsColimit _).1 ⟨hc⟩)

end Limits.SingleObj

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

@[simps]
noncomputable def autMap : H →* Aut (Over.mk (SingleObj.quotient.π H)) where
  toFun σ := Over.isoMk σ.val
  map_one' := rfl
  map_mul' _ _ := rfl

lemma injective_autMap : Function.Injective (autMap H) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← le_bot_iff]
  intro σ hσ
  simp only [MonoidHom.mem_ker, autMap_apply] at hσ
  simp only [Subgroup.mem_bot]
  ext
  exact (Over.forget _).congr_map (congr_arg Iso.hom hσ)

end quotient

end SingleObj

namespace GaloisCategory

variable [GaloisCategory C]

section

variable {X : C} [PreGaloisCategory.IsConnected X] (H : Subgroup (Aut X))

instance : SingleObj.HasQuotient H := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} H
  have := hasColimitsOfShape_of_equivalence (C := C) e.toSingleObjEquiv.symm
  infer_instance

instance : PreGaloisCategory.IsConnected (SingleObj.quotient H) :=
  PreGaloisCategory.IsConnected.of_epi (SingleObj.quotient.π H)

lemma map_quotientπ_eq_iff (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (x y : F.obj X) :
    F.map (SingleObj.quotient.π H) x = F.map (SingleObj.quotient.π H) y ↔
      ∃ σ ∈ H, F.map σ.hom x = y := by
  have : PreservesColimitsOfShape (SingleObj H) (forget FintypeCat.{w}) := by
    obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} H
    exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm _
  let iso : SingleObj.functor ((Aut.toEnd X).comp H.subtype) ⋙ F ⋙ forget _ ≅
    SingleObj.functor
      (((MonoidHom.comp (Functor.mapEnd _ (forget _))
        (Aut.toEnd (F.obj X))).comp (Functor.mapAut X F)).comp H.subtype) :=
    SingleObj.natIso (Iso.refl _) (by cat_disch)
  simpa [iso] using! SingleObj.eq_iff_of_isColimit ((IsColimit.precomposeInvEquiv iso _).2
    ((isColimitOfPreserves (F ⋙ forget _) (SingleObj.quotient.isColimit H))))

lemma surjective_quotientAutMap : Function.Surjective (SingleObj.quotient.autMap H) := by
  let F := getFiberFunctor C
  let x : F.obj X := Classical.arbitrary _
  intro σ
  obtain ⟨h, mem, eq⟩ := (map_quotientπ_eq_iff H F x (F.map σ.hom.left x)).1 (by
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, dsimp% σ.hom.w])
  refine ⟨⟨h, mem⟩, ?_⟩
  ext : 2
  have : PreGaloisCategory.IsConnected (Over.mk (SingleObj.quotient.π H)).left := by
    dsimp
    infer_instance
  exact GaloisCategory.hom_ext_of_isConnected F x (by simpa)

lemma bijective_quotientAutMap : Function.Bijective (SingleObj.quotient.autMap H) :=
  ⟨SingleObj.quotient.injective_autMap _, surjective_quotientAutMap H⟩

@[simps! apply]
noncomputable def quotientAutMulEquiv :
    H ≃* Aut (Over.mk (SingleObj.quotient.π H)) :=
  .ofBijective _ (bijective_quotientAutMap H)

end

instance {X : C} [IsGalois X] (H : Subgroup (Aut X)) :
    IsGaloisCover (SingleObj.quotient.π H) := by
  let F := getFiberFunctor C
  let s : F.obj (SingleObj.quotient H) := Classical.arbitrary _
  rw [isGaloisCover_def, isGalois_iff_pretransitive (fiberFunctorOver F _ s)]
  refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨σ, hσ, hσ'⟩ := (map_quotientπ_eq_iff H F x y).1 (by
    simp only [Over.mk_left, Over.mk_hom, Set.mem_preimage, Set.mem_singleton_iff] at hx hy
    rw [hx, hy])
  exact ⟨SingleObj.quotient.autMap H ⟨σ, hσ⟩, Subtype.ext_iff.2 hσ'⟩

-- to be moved
def Aut.overForget {Y X : C} (f : Y ⟶ X) :
    Aut (Over.mk f) →* Aut Y :=
  Functor.mapAut _ (Over.forget X)

omit [GaloisCategory C] in
lemma Aut.overMap_comp_overOverEquiv
    {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X) (fac : f ≫ g = fg := by cat_disch) :
    (Aut.overMap f g fg fac).comp (Aut.overOverEquiv f g fg fac) =
      Aut.overForget (Y := Over.mk fg) (X := Over.mk g) (Over.homMk f) := rfl

lemma isGalois_iff_normal
    {Y X : C} [PreGaloisCategory.IsGalois Y] [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) :
    IsGalois X ↔ (Aut.overForget f).range.Normal := sorry

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

@[simps!]
noncomputable def overQuotientπAutMulEquiv :
    Aut (Over.mk (overQuotientπ H)) ≃* Aut (Over.mk (SingleObj.quotient.π H)) :=
  (Aut.overOverEquiv (overQuotientπ H) (overQuotient H).hom f).symm

lemma autOverMap_overQuotientπ_eq :
    Aut.overMap (overQuotientπ H) (overQuotient H).hom f =
    H.subtype.comp (MonoidHom.comp (quotientAutMulEquiv H).symm.toMonoidHom
      (overQuotientπAutMulEquiv H).toMonoidHom) := by
  ext σ : 1
  obtain ⟨σ, rfl⟩ := (overQuotientπAutMulEquiv H).symm.surjective σ
  obtain ⟨σ, rfl⟩ := (quotientAutMulEquiv H).surjective σ
  dsimp [-quotientAutMulEquiv_apply]
  simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  rfl

@[simp]
lemma range_overMap_overQuotientπ :
    (Aut.overMap (overQuotientπ H) (overQuotient H).hom f).range = H := by
  rw [autOverMap_overQuotientπ_eq]
  ext σ
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.mem_range, MonoidHom.coe_comp,
    Subgroup.coe_subtype, MonoidHom.coe_coe, Function.comp_apply]
  refine ⟨?_, fun hσ ↦ ?_⟩
  · rintro ⟨σ, rfl⟩
    simp
  · exact ⟨(overQuotientπAutMulEquiv H).symm ((quotientAutMulEquiv H) ⟨σ, hσ⟩),
      by simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]⟩

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
    IsGaloisCover g ↔ (Aut.overMap f g fg).range.Normal := by
  simp [isGalois_iff_normal (Y := Over.mk fg) (X := Over.mk g) (Over.homMk f),
    ← Aut.overMap_comp_overOverEquiv f g fg, MonoidHom.range_comp, ← MonoidHom.range_eq_map]

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
