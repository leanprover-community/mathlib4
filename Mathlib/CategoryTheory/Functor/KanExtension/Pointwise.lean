/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan extension. Given two functors
`L : C ⥤ D` and `F : C ⥤ H`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
the point of which is `E.right.obj Y`, and the type `E.IsPointwiseLeftKanExtensionAt Y`
which expresses that `E.coconeAt Y` is colimit. When this holds for all `Y : D`,
we may say that `E` is a pointwise left Kan extension (`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show it is a pointwise Kan extension.

A dual API for pointwise right Kan extension is also formalized.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H] (L : C ⥤ D) (F : C ⥤ H)

/-- The condition that a functor `F` has a pointwise left Kan extension along `L` at `Y`.
It means that the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
has a colimit. -/
abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

/-- The condition that a functor `F` has a pointwise left Kan extension along `L`: it means
that it has a pointwise left Kan extension at any object. -/
abbrev HasPointwiseLeftKanExtension := ∀ (Y : D), HasPointwiseLeftKanExtensionAt L F Y

/-- The condition that a functor `F` has a pointwise right Kan extension along `L` at `Y`.
It means that the functor `StructuredArrow.proj Y L ⋙ F : StructuredArrow Y L ⥤ H`
has a limit. -/
abbrev HasPointwiseRightKanExtensionAt (Y : D) :=
  HasLimit (StructuredArrow.proj Y L ⋙ F)

/-- The condition that a functor `F` has a pointwise right Kan extension along `L`: it means
that it has a pointwise right Kan extension at any object. -/
abbrev HasPointwiseRightKanExtension := ∀ (Y : D), HasPointwiseRightKanExtensionAt L F Y

namespace LeftExtension

variable {F L}
variable (E : LeftExtension L F)

/-- The cocone for `CostructuredArrow.proj L Y ⋙ F` attached to `E : LeftExtension L F`.
The point of this cocone is `E.right.obj Y` -/
@[simps]
def coconeAt (Y : D) : Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := E.right.obj Y
  ι :=
    { app := fun g => E.hom.app g.left ≫ E.right.map g.hom
      naturality := fun g₁ g₂ φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        simp only [assoc, NatTrans.naturality_assoc, Functor.comp_map,
          Functor.map_comp, comp_id] }

variable (L F) in
/-- The cocones for `CostructuredArrow.proj L Y ⋙ F`, as a functor from `LeftExtension L F`. -/
@[simps]
def coconeAtFunctor (Y : D) :
    LeftExtension L F ⥤ Cocone (CostructuredArrow.proj L Y ⋙ F) where
  obj E := E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp)

/-- A left extension `E : LeftExtension L F` is a pointwise left Kan extension at `Y` when
`E.coconeAt Y` is a colimit cocone. -/
def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)

variable {E} in
lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
    {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y) :
    HasPointwiseLeftKanExtensionAt L F Y := ⟨_, h⟩

lemma IsPointwiseLeftKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseLeftKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

/-- A left extension `E : LeftExtension L F` is a pointwise left Kan extension when
it is a pointwise left Kan extension at any object. -/
abbrev IsPointwiseLeftKanExtension := ∀ (Y : D), E.IsPointwiseLeftKanExtensionAt Y

variable {E E'}

/-- If two left extensions `E` and `E'` are isomorphic, `E` is a pointwise
left Kan extension at `Y` iff `E'` is. -/
def isPointwiseLeftKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E'.IsPointwiseLeftKanExtensionAt Y :=
  IsColimit.equivIsoColimit ((coconeAtFunctor L F Y).mapIso e)

/-- If two left extensions `E` and `E'` are isomorphic, `E` is a pointwise
left Kan extension iff `E'` is. -/
def isPointwiseLeftKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseLeftKanExtension ≃ E'.IsPointwiseLeftKanExtension where
  toFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by aesop
  right_inv h := by aesop

variable (h : E.IsPointwiseLeftKanExtension)

lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension :
    HasPointwiseLeftKanExtension L F :=
  fun Y => (h Y).hasPointwiseLeftKanExtensionAt

/-- The (unique) morphism from a pointwise left Kan extension. -/
def IsPointwiseLeftKanExtension.homFrom (G : LeftExtension L F) : E ⟶ G :=
  StructuredArrow.homMk
    { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
      naturality := fun Y₁ Y₂ φ => (h Y₁).hom_ext (fun X => by
        rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
        simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X)) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _)))

lemma IsPointwiseLeftKanExtension.hom_ext (h : E.IsPointwiseLeftKanExtension)
    {G : LeftExtension L F} {f₁ f₂ : E ⟶ G} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (StructuredArrow.w f₁) X.left
  have eq₂ := congr_app (StructuredArrow.w f₂) X.left
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, NatTrans.naturality]
  rw [reassoc_of% eq₁, reassoc_of% eq₂]

/-- A pointwise left Kan extension is universal, i.e. it is a left Kan extension. -/
def IsPointwiseLeftKanExtension.isUniversal : E.IsUniversal :=
  IsInitial.ofUniqueHom h.homFrom (fun _ _ => h.hom_ext)

lemma IsPointwiseLeftKanExtension.isLeftKanExtension :
    E.right.IsLeftKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩

lemma IsPointwiseLeftKanExtension.hasLeftKanExtension :
    HasLeftKanExtension L F :=
  have := h.isLeftKanExtension
  HasLeftKanExtension.mk E.right E.hom

lemma IsPointwiseLeftKanExtension.isIso_hom [L.Full] [L.Faithful] :
    IsIso (E.hom) :=
  have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

end LeftExtension

namespace RightExtension

variable {F L}
variable (E E' : RightExtension L F)

/-- The cone for `StructuredArrow.proj Y L ⋙ F` attached to `E : RightExtension L F`.
The point of this cone is `E.left.obj Y` -/
@[simps]
def coneAt (Y : D) : Cone (StructuredArrow.proj Y L ⋙ F) where
  pt := E.left.obj Y
  π :=
    { app := fun g ↦ E.left.map g.hom ≫ E.hom.app g.right
      naturality := fun g₁ g₂ φ ↦ by
        dsimp
        rw [assoc, id_comp, ← StructuredArrow.w φ, Functor.map_comp, assoc]
        congr 1
        apply E.hom.naturality }

variable (L F) in
/-- The cones for `StructuredArrow.proj Y L ⋙ F`, as a functor from `RightExtension L F`. -/
@[simps]
def coneAtFunctor (Y : D) :
    RightExtension L F ⥤ Cone (StructuredArrow.proj Y L ⋙ F) where
  obj E := E.coneAt Y
  map {E E'} φ := ConeMorphism.mk (φ.left.app Y) (fun G ↦ by
    dsimp
    rw [← CostructuredArrow.w φ]
    simp)

/-- A right extension `E : RightExtension L F` is a pointwise right Kan extension at `Y` when
`E.coneAt Y` is a limit cone. -/
def IsPointwiseRightKanExtensionAt (Y : D) := IsLimit (E.coneAt Y)

variable {E} in
lemma IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt
    {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y) :
    HasPointwiseRightKanExtensionAt L F Y := ⟨_, h⟩

lemma IsPointwiseRightKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseRightKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_π_app_of_isInitial _ StructuredArrow.mkIdInitial

/-- A right extension `E : RightExtension L F` is a pointwise right Kan extension when
it is a pointwise right Kan extension at any object. -/
abbrev IsPointwiseRightKanExtension := ∀ (Y : D), E.IsPointwiseRightKanExtensionAt Y

variable {E E'}

/-- If two right extensions `E` and `E'` are isomorphic, `E` is a pointwise
right Kan extension at `Y` iff `E'` is. -/
def isPointwiseRightKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseRightKanExtensionAt Y ≃ E'.IsPointwiseRightKanExtensionAt Y :=
  IsLimit.equivIsoLimit ((coneAtFunctor L F Y).mapIso e)

/-- If two right extensions `E` and `E'` are isomorphic, `E` is a pointwise
right Kan extension iff `E'` is. -/
def isPointwiseRightKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseRightKanExtension ≃ E'.IsPointwiseRightKanExtension where
  toFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseRightKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by aesop
  right_inv h := by aesop

variable (h : E.IsPointwiseRightKanExtension)

lemma IsPointwiseRightKanExtension.hasPointwiseRightKanExtension :
    HasPointwiseRightKanExtension L F :=
  fun Y => (h Y).hasPointwiseRightKanExtensionAt

/-- The (unique) morphism to a pointwise right Kan extension. -/
def IsPointwiseRightKanExtension.homTo (G : RightExtension L F) : G ⟶ E :=
  CostructuredArrow.homMk
    { app := fun Y ↦ (h Y).lift (RightExtension.coneAt G Y)
      naturality := fun Y₁ Y₂ φ ↦ (h Y₂).hom_ext (fun X ↦ by
        rw [assoc, (h Y₂).fac (coneAt G Y₂) X]
        simpa using ((h Y₁).fac (coneAt G Y₁) ((StructuredArrow.map φ).obj X)).symm) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (RightExtension.coneAt G _) (StructuredArrow.mk (𝟙 _)) )

lemma IsPointwiseRightKanExtension.hom_ext (h : E.IsPointwiseRightKanExtension)
    {G : RightExtension L F} {f₁ f₂ : G ⟶ E} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (CostructuredArrow.w f₁) X.right
  have eq₂ := congr_app (CostructuredArrow.w f₂) X.right
  dsimp at eq₁ eq₂ ⊢
  simp only [assoc, ← NatTrans.naturality_assoc, eq₁, eq₂]

/-- A pointwise right Kan extension is universal, i.e. it is a right Kan extension. -/
def IsPointwiseRightKanExtension.isUniversal : E.IsUniversal :=
  IsTerminal.ofUniqueHom h.homTo (fun _ _ => h.hom_ext)

lemma IsPointwiseRightKanExtension.isRightKanExtension :
    E.left.IsRightKanExtension E.hom where
  nonempty_isUniversal := ⟨h.isUniversal⟩

lemma IsPointwiseRightKanExtension.hasRightKanExtension :
    HasRightKanExtension L F :=
  have := h.isRightKanExtension
  HasRightKanExtension.mk E.left E.hom

lemma IsPointwiseRightKanExtension.isIso_hom [L.Full] [L.Faithful] :
    IsIso (E.hom) :=
  have := fun X => (h (L.obj X)).isIso_hom_app
  NatIso.isIso_of_isIso_app ..

end RightExtension

section

variable [HasPointwiseLeftKanExtension L F]

/-- The constructed pointwise left Kan extension when `HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
noncomputable def pointwiseLeftKanExtension : D ⥤ H where
  obj Y := colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F))
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            simpa using colimit.w (CostructuredArrow.proj L Y₂ ⋙ F)
              ((CostructuredArrow.map f).map φ) })
  map_id Y := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, comp_id]
    congr
    apply CostructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := colimit.hom_ext (fun j => by
    dsimp
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj]
    congr 1
    apply CostructuredArrow.map_comp)

/-- The unit of the constructed pointwise left Kan extension when
`HasPointwiseLeftKanExtension L F` holds. -/
@[simps]
noncomputable def pointwiseLeftKanExtensionUnit : F ⟶ L ⋙ pointwiseLeftKanExtension L F where
  app X := colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F)
    (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_obj, pointwiseLeftKanExtension_obj, comp_map,
      pointwiseLeftKanExtension_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact colimit.w (CostructuredArrow.proj L (L.obj X₂) ⋙ F) φ

/-- The functor `pointwiseLeftKanExtension L F` is a pointwise left Kan
extension of `F` along `L`. -/
noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp, ← CostructuredArrow.eq_mk]))

/-- The functor `pointwiseLeftKanExtension L F` is a left Kan extension of `F` along `L`. -/
noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsUniversal :=
  (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F).isUniversal

instance : (pointwiseLeftKanExtension L F).IsLeftKanExtension
    (pointwiseLeftKanExtensionUnit L F) where
  nonempty_isUniversal := ⟨pointwiseLeftKanExtensionIsUniversal L F⟩

instance : HasLeftKanExtension L F :=
  HasLeftKanExtension.mk _ (pointwiseLeftKanExtensionUnit L F)

variable {F L}

/-- If `F` admits a pointwise left Kan extension along `L`, then any left Kan extension of `F`
along `L` is a pointwise left Kan extension. -/
noncomputable def isPointwiseLeftKanExtensionOfIsLeftKanExtension (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (pointwiseLeftKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsLeftKanExtension α))
    (pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L F)

end

section

variable [HasPointwiseRightKanExtension L F]

/-- The constructed pointwise right Kan extension
when `HasPointwiseRightKanExtension L F` holds. -/
@[simps]
noncomputable def pointwiseRightKanExtension : D ⥤ H where
  obj Y := limit (StructuredArrow.proj Y L ⋙ F)
  map {Y₁ Y₂} f := limit.lift (StructuredArrow.proj Y₂ L ⋙ F)
      (Cone.mk (limit (StructuredArrow.proj Y₁ L ⋙ F))
        { app := fun g ↦ limit.π (StructuredArrow.proj Y₁ L ⋙ F)
            ((StructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ ↦ by
            simpa using (limit.w (StructuredArrow.proj Y₁ L ⋙ F)
              ((StructuredArrow.map f).map φ)).symm })
  map_id Y := limit.hom_ext (fun j => by
    dsimp
    simp only [limit.lift_π, id_comp]
    congr
    apply StructuredArrow.map_id)
  map_comp {Y₁ Y₂ Y₃} f f' := limit.hom_ext (fun j => by
    dsimp
    simp only [limit.lift_π, assoc]
    congr 1
    apply StructuredArrow.map_comp)

/-- The counit of the constructed pointwise right Kan extension when
`HasPointwiseRightKanExtension L F` holds. -/
@[simps]
noncomputable def pointwiseRightKanExtensionCounit :
    L ⋙ pointwiseRightKanExtension L F ⟶ F where
  app X := limit.π (StructuredArrow.proj (L.obj X) L ⋙ F)
    (StructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f := by
    simp only [comp_obj, pointwiseRightKanExtension_obj, comp_map,
      pointwiseRightKanExtension_map, limit.lift_π, StructuredArrow.map_mk]
    rw [comp_id]
    let φ : StructuredArrow.mk (𝟙 (L.obj X₁)) ⟶ StructuredArrow.mk (L.map f) :=
      StructuredArrow.homMk f
    exact (limit.w (StructuredArrow.proj (L.obj X₁) L ⋙ F) φ).symm

/-- The functor `pointwiseRightKanExtension L F` is a pointwise right Kan
extension of `F` along `L`. -/
noncomputable def pointwiseRightKanExtensionIsPointwiseRightKanExtension :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsPointwiseRightKanExtension :=
  fun X => IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [limit.lift_π, StructuredArrow.map_mk, id_comp]
    congr
    rw [comp_id, ← StructuredArrow.eq_mk]))

/-- The functor `pointwiseRightKanExtension L F` is a right Kan extension of `F` along `L`. -/
noncomputable def pointwiseRightKanExtensionIsUniversal :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsUniversal :=
  (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F).isUniversal

instance : (pointwiseRightKanExtension L F).IsRightKanExtension
    (pointwiseRightKanExtensionCounit L F) where
  nonempty_isUniversal := ⟨pointwiseRightKanExtensionIsUniversal L F⟩

instance : HasRightKanExtension L F :=
  HasRightKanExtension.mk _ (pointwiseRightKanExtensionCounit L F)

variable {F L}

/-- If `F` admits a pointwise right Kan extension along `L`, then any right Kan extension of `F`
along `L` is a pointwise right Kan extension. -/
noncomputable def isPointwiseRightKanExtensionOfIsRightKanExtension (F' : D ⥤ H) (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] :
    (RightExtension.mk _ α).IsPointwiseRightKanExtension :=
  RightExtension.isPointwiseRightKanExtensionEquivOfIso
    (IsLimit.conePointUniqueUpToIso (pointwiseRightKanExtensionIsUniversal L F)
      (F'.isUniversalOfIsRightKanExtension α))
    (pointwiseRightKanExtensionIsPointwiseRightKanExtension L F)

end

end Functor

end CategoryTheory
