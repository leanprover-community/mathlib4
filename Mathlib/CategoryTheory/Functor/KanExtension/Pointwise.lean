/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Pointwise Kan extensions

In this file, we define the notion of pointwise (left) Kan extension. Given two functors
`L : C ⥤ D` and `F : C ⥤ H`, and `E : LeftExtension L F`, we introduce a cocone
`E.coconeAt Y` for the functor `CostructuredArrow.proj L Y ⋙ F : CostructuredArrow L Y ⥤ H`
the point of which is `E.right.obj Y`, and the type `E.IsPointwiseLeftKanExtensionAt Y`
which expresses that `E.coconeAt Y` is a colimit. When this holds for all `Y : D`,
we may say that `E` is a pointwise left Kan extension (`E.IsPointwiseLeftKanExtension`).

Conversely, when `CostructuredArrow.proj L Y ⋙ F` has a colimit, we say that
`F` has a pointwise left Kan extension at `Y : D` (`HasPointwiseLeftKanExtensionAt L F Y`),
and if this holds for all `Y : D`, we construct a functor
`pointwiseLeftKanExtension L F : D ⥤ H` and show it is a pointwise Kan extension.

A dual API for pointwise right Kan extension is also formalized.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type*} [Category* C] [Category* D] [Category* D'] [Category* H]
  (L : C ⥤ D) (L' : C ⥤ D') (F : C ⥤ H)

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

lemma hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseLeftKanExtensionAt L F Y₁ ↔
      HasPointwiseLeftKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseLeftKanExtensionAt L F Y₁],
      HasPointwiseLeftKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ CostructuredArrow.proj L Y₁ ⋙ F)
  infer_instance

lemma hasPointwiseRightKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    HasPointwiseRightKanExtensionAt L F Y₁ ↔
      HasPointwiseRightKanExtensionAt L F Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [HasPointwiseRightKanExtensionAt L F Y₁],
      HasPointwiseRightKanExtensionAt L F Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasLimit ((StructuredArrow.mapIso e.symm).functor ⋙ StructuredArrow.proj Y₁ L ⋙ F)
  infer_instance

variable {L} in
/-- `HasPointwiseLeftKanExtensionAt` is invariant when we replace `L` by an equivalent functor. -/
lemma hasPointwiseLeftKanExtensionAt_iff_of_natIso {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseLeftKanExtensionAt L F Y],
      HasPointwiseLeftKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLeftIso _ e.symm
  let e' : CostructuredArrow.proj L' Y ⋙ F ≅
    Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F := Iso.refl _
  exact hasColimit_of_iso e'

variable {L} in
/-- `HasPointwiseRightKanExtensionAt` is invariant when we replace `L` by an equivalent functor. -/
lemma hasPointwiseRightKanExtensionAt_iff_of_natIso {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [HasPointwiseRightKanExtensionAt L F Y],
      HasPointwiseRightKanExtensionAt L' F Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : StructuredArrow Y L' ≌ StructuredArrow Y L := Comma.mapRightIso _ e.symm
  let e' : StructuredArrow.proj Y L' ⋙ F ≅
    Φ.functor ⋙ StructuredArrow.proj Y L ⋙ F := Iso.refl _
  exact hasLimit_of_iso e'.symm

lemma hasPointwiseLeftKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseLeftKanExtensionAt L F Y] :
    HasPointwiseLeftKanExtensionAt L' F Y' := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_natIso F eL,
    hasPointwiseLeftKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inferInstance : HasPointwiseLeftKanExtensionAt L F Y)
  exact hasColimit_of_equivalence_comp (asEquivalence Φ)

lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseLeftKanExtensionAt L F Y ↔
      HasPointwiseLeftKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseLeftKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

lemma hasPointwiseRightKanExtensionAt_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [HasPointwiseRightKanExtensionAt L F Y] :
    HasPointwiseRightKanExtensionAt L' F Y' := by
  rw [← hasPointwiseRightKanExtensionAt_iff_of_natIso F eL,
    hasPointwiseRightKanExtensionAt_iff_of_iso _ F e.symm]
  let Φ := StructuredArrow.post Y L E.functor
  have : HasLimit ((asEquivalence Φ).functor ⋙
    StructuredArrow.proj (E.functor.obj Y) (L ⋙ E.functor) ⋙ F) :=
    (inferInstance : HasPointwiseRightKanExtensionAt L F Y)
  exact hasLimit_of_equivalence_comp (asEquivalence Φ)

lemma hasPointwiseRightKanExtensionAt_iff_of_equivalence
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    HasPointwiseRightKanExtensionAt L F Y ↔
      HasPointwiseRightKanExtensionAt L' F Y' := by
  constructor
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L L' F E eL Y Y' e
  · intro
    exact hasPointwiseRightKanExtensionAt_of_equivalence L' L F E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

namespace LeftExtension

variable {F L}
variable (E : LeftExtension L F)

set_option backward.isDefEq.respectTransparency false in
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
        simp only [NatTrans.naturality_assoc, Functor.comp_map,
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

instance (Y : D) : Subsingleton (E.IsPointwiseLeftKanExtensionAt Y) :=
  inferInstanceAs (Subsingleton (IsColimit _))

variable {E} in
lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt
    {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y) :
    HasPointwiseLeftKanExtensionAt L F Y := ⟨_, h⟩

lemma IsPointwiseLeftKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseLeftKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_ι_app_of_isTerminal _ CostructuredArrow.mkIdTerminal

/-- The condition of being a pointwise left Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
def isPointwiseLeftKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseLeftKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y' :=
  IsColimit.ofIsoColimit (hY.whiskerEquivalence (CostructuredArrow.mapIso e.symm))
    (Cocone.ext (E.right.mapIso e))

/-- The condition of being a pointwise left Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
def isPointwiseLeftKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E.IsPointwiseLeftKanExtensionAt Y' where
  toFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

namespace IsPointwiseLeftKanExtensionAt

variable {E} {Y : D} (h : E.IsPointwiseLeftKanExtensionAt Y)

include h in
lemma hom_ext' {T : H} {f g : E.right.obj Y ⟶ T}
    (hfg : ∀ ⦃X : C⦄ (φ : L.obj X ⟶ Y),
      E.hom.app X ≫ E.right.map φ ≫ f = E.hom.app X ≫ E.right.map φ ≫ g) : f = g :=
  h.hom_ext (fun j ↦ by simpa using hfg j.hom)

@[reassoc]
lemma comp_homEquiv_symm {Z : H}
    (φ : CostructuredArrow.proj L Y ⋙ F ⟶ (Functor.const _).obj Z)
    (g : CostructuredArrow L Y) :
    E.hom.app g.left ≫ E.right.map g.hom ≫ h.homEquiv.symm φ = φ.app g := by
  simpa using h.ι_app_homEquiv_symm φ g

variable [HasColimit (CostructuredArrow.proj L Y ⋙ F)]

/-- A pointwise left Kan extension of `F` along `L` applied to an object `Y` is isomorphic to
`colimit (CostructuredArrow.proj L Y ⋙ F)`. -/
noncomputable def isoColimit :
    E.right.obj Y ≅ colimit (CostructuredArrow.proj L Y ⋙ F) :=
  h.coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc (attr := simp)]
lemma ι_isoColimit_inv (g : CostructuredArrow L Y) :
    colimit.ι _ g ≫ h.isoColimit.inv = E.hom.app g.left ≫ E.right.map g.hom :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

@[reassoc (attr := simp)]
lemma ι_isoColimit_hom (g : CostructuredArrow L Y) :
    E.hom.app g.left ≫ E.right.map g.hom ≫ h.isoColimit.hom =
      colimit.ι (CostructuredArrow.proj L Y ⋙ F) g := by
  simpa using h.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) g

end IsPointwiseLeftKanExtensionAt

/-- Given `E : Functor.LeftExtension L F`, this is the property of objects where
`E` is a pointwise left Kan extension. -/
def isPointwiseLeftKanExtensionAt : ObjectProperty D :=
  fun Y ↦ Nonempty (E.IsPointwiseLeftKanExtensionAt Y)

instance : E.isPointwiseLeftKanExtensionAt.IsClosedUnderIsomorphisms where
  of_iso e h := ⟨E.isPointwiseLeftKanExtensionAtOfIso' h.some e⟩

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
  left_inv h := by simp
  right_inv h := by simp

variable (h : E.IsPointwiseLeftKanExtension)
include h

lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension :
    HasPointwiseLeftKanExtension L F :=
  fun Y => (h Y).hasPointwiseLeftKanExtensionAt

set_option backward.isDefEq.respectTransparency false in
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

lemma IsPointwiseLeftKanExtension.hom_ext
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

instance (Y : D) : Subsingleton (E.IsPointwiseRightKanExtensionAt Y) :=
  inferInstanceAs (Subsingleton (IsLimit _))

variable {E} in
lemma IsPointwiseRightKanExtensionAt.hasPointwiseRightKanExtensionAt
    {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y) :
    HasPointwiseRightKanExtensionAt L F Y := ⟨_, h⟩

lemma IsPointwiseRightKanExtensionAt.isIso_hom_app
    {X : C} (h : E.IsPointwiseRightKanExtensionAt (L.obj X)) [L.Full] [L.Faithful] :
    IsIso (E.hom.app X) := by
  simpa using h.isIso_π_app_of_isInitial _ StructuredArrow.mkIdInitial

/-- The condition of being a pointwise right Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
def isPointwiseRightKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseRightKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseRightKanExtensionAt Y' :=
  IsLimit.ofIsoLimit (hY.whiskerEquivalence (StructuredArrow.mapIso e.symm))
    (Cone.ext (E.left.mapIso e))

/-- The condition of being a pointwise right Kan extension at an object `Y` is
unchanged by replacing `Y` by an isomorphic object `Y'`. -/
def isPointwiseRightKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseRightKanExtensionAt Y ≃ E.IsPointwiseRightKanExtensionAt Y' where
  toFun h := E.isPointwiseRightKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseRightKanExtensionAtOfIso' h e.symm
  left_inv h := by subsingleton
  right_inv h := by subsingleton

namespace IsPointwiseRightKanExtensionAt

variable {E} {Y : D} (h : E.IsPointwiseRightKanExtensionAt Y)

include h in
lemma hom_ext' {T : H} {f g : T ⟶ E.left.obj Y}
    (hfg : ∀ ⦃X : C⦄ (φ : Y ⟶ L.obj X),
      f ≫ E.left.map φ ≫ E.hom.app X = g ≫ E.left.map φ ≫ E.hom.app X) : f = g :=
  h.hom_ext (fun j ↦ hfg j.hom)

variable [HasLimit (StructuredArrow.proj Y L ⋙ F)]

/-- A pointwise right Kan extension of `F` along `L` applied to an object `Y` is isomorphic to
`limit (StructuredArrow.proj Y L ⋙ F)`. -/
noncomputable def isoLimit :
    E.left.obj Y ≅ limit (StructuredArrow.proj Y L ⋙ F) :=
  h.conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
lemma isoLimit_hom_π (g : StructuredArrow Y L) :
    h.isoLimit.hom ≫ limit.π _ g = E.left.map g.hom ≫ E.hom.app g.right :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]
lemma isoLimit_inv_π (g : StructuredArrow Y L) :
    h.isoLimit.inv ≫ E.left.map g.hom ≫ E.hom.app g.right =
      limit.π (StructuredArrow.proj Y L ⋙ F) g := by
  simpa using h.conePointUniqueUpToIso_inv_comp (limit.isLimit _) g

end IsPointwiseRightKanExtensionAt

/-- Given `E : Functor.RightExtension L F`, this is the property of objects where
`E` is a pointwise right Kan extension. -/
def isPointwiseRightKanExtensionAt : ObjectProperty D :=
  fun Y ↦ Nonempty (E.IsPointwiseRightKanExtensionAt Y)

instance : E.isPointwiseRightKanExtensionAt.IsClosedUnderIsomorphisms where
  of_iso e h := ⟨E.isPointwiseRightKanExtensionAtOfIso' h.some e⟩

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
  left_inv h := by simp
  right_inv h := by simp

variable (h : E.IsPointwiseRightKanExtension)
include h

lemma IsPointwiseRightKanExtension.hasPointwiseRightKanExtension :
    HasPointwiseRightKanExtension L F :=
  fun Y => (h Y).hasPointwiseRightKanExtensionAt

set_option backward.isDefEq.respectTransparency false in
/-- The (unique) morphism to a pointwise right Kan extension. -/
def IsPointwiseRightKanExtension.homTo (G : RightExtension L F) : G ⟶ E :=
  CostructuredArrow.homMk
    { app := fun Y ↦ (h Y).lift (RightExtension.coneAt G Y)
      naturality := fun Y₁ Y₂ φ ↦ (h Y₂).hom_ext (fun X ↦ by
        rw [assoc, (h Y₂).fac (coneAt G Y₂) X]
        simpa using ((h Y₁).fac (coneAt G Y₁) ((StructuredArrow.map φ).obj X)).symm) }
    (by
      ext X
      simpa using (h (L.obj X)).fac (RightExtension.coneAt G _) (StructuredArrow.mk (𝟙 _)))

lemma IsPointwiseRightKanExtension.hom_ext
    {G : RightExtension L F} {f₁ f₂ : G ⟶ E} : f₁ = f₂ := by
  ext Y
  apply (h Y).hom_ext
  intro X
  have eq₁ := congr_app (CostructuredArrow.w f₁) X.right
  have eq₂ := congr_app (CostructuredArrow.w f₂) X.right
  dsimp at eq₁ eq₂ ⊢
  simp only [← NatTrans.naturality_assoc, eq₁, eq₂]

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
/-- The functor `pointwiseLeftKanExtension L F` is a pointwise left Kan
extension of `F` along `L`. -/
noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (LeftExtension.mk _ (pointwiseLeftKanExtensionUnit L F)).IsPointwiseLeftKanExtension :=
  fun X => IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext (Iso.refl _) (fun j => by
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

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary cocone used in the lemma `pointwiseLeftKanExtension_desc_app` -/
@[simps]
def costructuredArrowMapCocone (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) :
    Cocone (CostructuredArrow.proj L Y ⋙ F) where
  pt := G.obj Y
  ι := {
    app := fun f ↦ α.app f.left ≫ G.map f.hom
    naturality := by simp [← G.map_comp] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pointwiseLeftKanExtension_desc_app (G : D ⥤ H) (α : F ⟶ L ⋙ G) (Y : D) :
    ((pointwiseLeftKanExtension L F).descOfIsLeftKanExtension (pointwiseLeftKanExtensionUnit L F)
      G α |>.app Y) = colimit.desc _ (costructuredArrowMapCocone L F G α Y) := by
  let β : L.pointwiseLeftKanExtension F ⟶ G :=
    { app := fun Y ↦ colimit.desc _ (costructuredArrowMapCocone L F G α Y) }
  have h : (pointwiseLeftKanExtension L F).descOfIsLeftKanExtension
      (pointwiseLeftKanExtensionUnit L F) G α = β := by
    apply hom_ext_of_isLeftKanExtension (α := pointwiseLeftKanExtensionUnit L F)
    aesop
  exact NatTrans.congr_app h Y

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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
/-- The functor `pointwiseRightKanExtension L F` is a pointwise right Kan
extension of `F` along `L`. -/
noncomputable def pointwiseRightKanExtensionIsPointwiseRightKanExtension :
    (RightExtension.mk _ (pointwiseRightKanExtensionCounit L F)).IsPointwiseRightKanExtension :=
  fun X => IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (Iso.refl _) (fun j => by
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

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary cone used in the lemma `pointwiseRightKanExtension_lift_app` -/
@[simps]
def structuredArrowMapCone (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) :
    Cone (StructuredArrow.proj Y L ⋙ F) where
  pt := G.obj Y
  π := {
    app := fun f ↦ G.map f.hom ≫ α.app f.right
    naturality := by simp [← α.naturality, ← G.map_comp_assoc] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pointwiseRightKanExtension_lift_app (G : D ⥤ H) (α : L ⋙ G ⟶ F) (Y : D) :
    ((pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α |>.app Y) =
        limit.lift _ (structuredArrowMapCone L F G α Y) := by
  let β : G ⟶ L.pointwiseRightKanExtension F :=
    { app := fun Y ↦ limit.lift _ (structuredArrowMapCone L F G α Y) }
  have h : (pointwiseRightKanExtension L F).liftOfIsRightKanExtension
      (pointwiseRightKanExtensionCounit L F) G α = β := by
    apply hom_ext_of_isRightKanExtension (α := pointwiseRightKanExtensionCounit L F)
    aesop
  exact NatTrans.congr_app h Y

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
