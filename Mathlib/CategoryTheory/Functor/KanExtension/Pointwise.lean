import Mathlib.CategoryTheory.Functor.KanExtension.Basic

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type _} [Category C] [Category D] [Category D'] [Category H]
  (F : C ⥤ H) (L : C ⥤ D)

abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

abbrev HasPointwiseLeftKanExtension := ∀ (Y : D), F.HasPointwiseLeftKanExtensionAt L Y

lemma hasPointwiseLeftKanExtensionAt_iff_of_iso {Y₁ Y₂ : D} (e : Y₁ ≅ Y₂) :
    F.HasPointwiseLeftKanExtensionAt L Y₁ ↔
      F.HasPointwiseLeftKanExtensionAt L Y₂ := by
  revert Y₁ Y₂ e
  suffices ∀ ⦃Y₁ Y₂ : D⦄ (_ : Y₁ ≅ Y₂) [F.HasPointwiseLeftKanExtensionAt L Y₁],
      F.HasPointwiseLeftKanExtensionAt L Y₂ from
    fun Y₁ Y₂ e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro Y₁ Y₂ e _
  change HasColimit ((CostructuredArrow.mapIso e.symm).functor ⋙ CostructuredArrow.proj L Y₁ ⋙ F)
  infer_instance

variable {L}

lemma hasPointwiseLeftKanExtensionAt_iff_of_iso' {L' : C ⥤ D} (e : L ≅ L') (Y : D) :
    F.HasPointwiseLeftKanExtensionAt L Y ↔
      F.HasPointwiseLeftKanExtensionAt L' Y := by
  revert L L' e
  suffices ∀ ⦃L L' : C ⥤ D⦄ (_ : L ≅ L') [F.HasPointwiseLeftKanExtensionAt L Y],
      F.HasPointwiseLeftKanExtensionAt L' Y from
    fun L L' e => ⟨fun _ => this e, fun _ => this e.symm⟩
  intro L L' e _
  let Φ : CostructuredArrow L' Y ≌ CostructuredArrow L Y := Comma.mapLeftIso _ e.symm
  have : HasColimit (Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F) := inferInstance
  let e' : CostructuredArrow.proj L' Y ⋙ F ≅
    Φ.functor ⋙ CostructuredArrow.proj L Y ⋙ F := Iso.refl _
  exact hasColimitOfIso e'

variable (L)

lemma hasPointwiseLeftKanExtensionAt_of_equivalence (L' : C ⥤ D')
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y')
    [F.HasPointwiseLeftKanExtensionAt L Y] :
    F.HasPointwiseLeftKanExtensionAt L' Y' := by
  rw [← F.hasPointwiseLeftKanExtensionAt_iff_of_iso' eL,
    F.hasPointwiseLeftKanExtensionAt_iff_of_iso _ e.symm]
  let Φ := CostructuredArrow.post L E.functor Y
  have : IsEquivalence Φ := CostructuredArrow.isEquivalencePost _ _ _
  have : HasColimit ((asEquivalence Φ).functor ⋙
    CostructuredArrow.proj (L ⋙ E.functor) (E.functor.obj Y) ⋙ F) :=
    (inferInstance : F.HasPointwiseLeftKanExtensionAt L Y)
  exact hasColimit_of_equivalence_comp (asEquivalence Φ)

lemma hasPointwiseLeftKanExtensionAt_iff_of_equivalence (L' : C ⥤ D')
    (E : D ≌ D') (eL : L ⋙ E.functor ≅ L') (Y : D) (Y' : D') (e : E.functor.obj Y ≅ Y') :
    F.HasPointwiseLeftKanExtensionAt L Y ↔
      F.HasPointwiseLeftKanExtensionAt L' Y' := by
  constructor
  · intro
    exact F.hasPointwiseLeftKanExtensionAt_of_equivalence L L' E eL Y Y' e
  · intro
    exact F.hasPointwiseLeftKanExtensionAt_of_equivalence L' L E.symm
      (isoWhiskerRight eL.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft L E.unitIso.symm ≪≫ L.rightUnitor) Y' Y
      (E.inverse.mapIso e.symm ≪≫ E.unitIso.symm.app Y)

namespace LeftExtension

variable {F L} (E E' : LeftExtension L F)

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

@[simps!]
def coconeAtIso {Y Y' : D} (e : Y ≅ Y') :
    (E.coconeAt Y').whisker (CostructuredArrow.mapIso e).functor ≅ E.coconeAt Y :=
  Cocones.ext (E.right.mapIso e.symm) (fun j => by
    dsimp
    simp only [assoc, ← map_comp, e.hom_inv_id, comp_id])

variable (L F)

@[simps]
def coconeAtFunctor (Y : D) : LeftExtension L F ⥤ Cocone (CostructuredArrow.proj L Y ⋙ F) where
  obj E := E.coconeAt Y
  map {E E'} φ := CoconeMorphism.mk (φ.right.app Y) (fun G => by
    dsimp
    rw [← StructuredArrow.w φ]
    simp only [assoc, NatTrans.naturality, const_obj_obj, whiskeringLeft_obj_obj, whiskeringLeft_obj_map,
      NatTrans.comp_app, comp_obj, whiskerLeft_app])

variable {L F}

def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)

lemma IsPointwiseLeftKanExtensionAt.hasPointwiseLeftKanExtensionAt {E : LeftExtension L F} {Y : D}
    (h : E.IsPointwiseLeftKanExtensionAt Y) : F.HasPointwiseLeftKanExtensionAt L Y := ⟨_, h⟩

abbrev IsPointwiseLeftKanExtension := ∀ (Y : D), E.IsPointwiseLeftKanExtensionAt Y

lemma IsPointwiseLeftKanExtension.hasPointwiseLeftKanExtension {E : LeftExtension L F}
    (h : E.IsPointwiseLeftKanExtension) : F.HasPointwiseLeftKanExtension L := by
  intro Y
  exact (h Y).hasPointwiseLeftKanExtensionAt

variable {E E'}

lemma isPointwiseLeftKanExtensionAtEquivOfIso (e : E ≅ E') (Y : D) :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E'.IsPointwiseLeftKanExtensionAt Y where
  toFun h := IsColimit.ofIsoColimit h ((coconeAtFunctor F L Y).mapIso e)
  invFun h := IsColimit.ofIsoColimit h ((coconeAtFunctor F L Y).mapIso e.symm)
  left_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim
  right_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim

lemma isPointwiseLeftKanExtensionEquivOfIso (e : E ≅ E') :
    E.IsPointwiseLeftKanExtension ≃ E'.IsPointwiseLeftKanExtension where
  toFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y) (h Y)
  invFun h := fun Y => (isPointwiseLeftKanExtensionAtEquivOfIso e Y).symm (h Y)
  left_inv h := by
    aesop_cat
    funext
  right_inv h := by
    aesop
    funext

def isPointwiseLeftKanExtensionAtOfIso'
    {Y : D} (hY : E.IsPointwiseLeftKanExtensionAt Y) {Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y' :=
  IsColimit.ofIsoColimit (hY.whiskerEquivalence _) (E.coconeAtIso e.symm)

def isPointwiseLeftKanExtensionAtEquivOfIso' {Y Y' : D} (e : Y ≅ Y') :
    E.IsPointwiseLeftKanExtensionAt Y ≃ E.IsPointwiseLeftKanExtensionAt Y' where
  toFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e
  invFun h := E.isPointwiseLeftKanExtensionAtOfIso' h e.symm
  left_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim
  right_inv h := by
    dsimp only [IsPointwiseLeftKanExtensionAt]
    apply Subsingleton.elim

variable (E E')

def isUniversalOfPointwise (h : E.IsPointwiseLeftKanExtension) :
    E.IsUniversal :=
  IsInitial.ofUniqueHom (fun G => StructuredArrow.homMk
        { app := fun Y => (h Y).desc (LeftExtension.coconeAt G Y)
          naturality := fun Y₁ Y₂ φ => by
            apply (h Y₁).hom_ext
            intro X
            rw [(h Y₁).fac_assoc (coconeAt G Y₁) X]
            simpa using (h Y₂).fac (coconeAt G Y₂) ((CostructuredArrow.map φ).obj X) }
      (by
        ext X
        simpa using (h (L.obj X)).fac (LeftExtension.coconeAt G _) (CostructuredArrow.mk (𝟙 _))))
    (fun G => by
      suffices ∀ (m₁ m₂ : E ⟶ G), m₁ = m₂ by intros; apply this
      intro m₁ m₂
      ext Y
      apply (h Y).hom_ext
      intro X
      have eq₁ := congr_app (StructuredArrow.w m₁) X.left
      have eq₂ := congr_app (StructuredArrow.w m₂) X.left
      dsimp at eq₁ eq₂ ⊢
      simp only [assoc, NatTrans.naturality]
      rw [reassoc_of% eq₁, reassoc_of% eq₂])

end LeftExtension

section

variable [F.HasPointwiseLeftKanExtension L]

@[simps]
noncomputable def pointwiseLeftKanExtensionFunctor : D ⥤ H where
  obj Y := colimit (CostructuredArrow.proj L Y ⋙ F)
  map {Y₁ Y₂} f :=
    colimit.desc (CostructuredArrow.proj L Y₁ ⋙ F)
      (Cocone.mk (colimit (CostructuredArrow.proj L Y₂ ⋙ F)) (
        { app := fun g => colimit.ι (CostructuredArrow.proj L Y₂ ⋙ F)
            ((CostructuredArrow.map f).obj g)
          naturality := fun g₁ g₂ φ => by
            dsimp
            simp only [comp_id]
            exact colimit.w (CostructuredArrow.proj L Y₂ ⋙ F) ((CostructuredArrow.map f).map φ) }))
  map_id Y := by
    apply colimit.hom_ext
    intro j
    dsimp
    simp only [colimit.ι_desc, comp_id]
    congr
    apply CostructuredArrow.map_id
  map_comp {Y₁ Y₂ Y₃} f f' := by
    apply colimit.hom_ext
    intro j
    dsimp
    simp only [colimit.ι_desc, colimit.ι_desc_assoc, comp_obj, CostructuredArrow.proj_obj]
    congr 1
    apply CostructuredArrow.map_comp

@[simps]
noncomputable def pointwiseLeftKanExtensionNatTrans : F ⟶ L ⋙ F.pointwiseLeftKanExtensionFunctor L where
  app X := colimit.ι (CostructuredArrow.proj L (L.obj X) ⋙ F) (CostructuredArrow.mk (𝟙 (L.obj X)))
  naturality {X₁ X₂} f:= by
    simp only [comp_obj, pointwiseLeftKanExtensionFunctor_obj, comp_map,
      pointwiseLeftKanExtensionFunctor_map, colimit.ι_desc, CostructuredArrow.map_mk]
    rw [id_comp]
    let φ : CostructuredArrow.mk (L.map f) ⟶ CostructuredArrow.mk (𝟙 (L.obj X₂)) :=
      CostructuredArrow.homMk f
    exact colimit.w (CostructuredArrow.proj L (L.obj X₂) ⋙ F) φ


@[simps! right hom]
noncomputable def pointwiseLeftKanExtension : LeftExtension L F :=
  StructuredArrow.mk (F.pointwiseLeftKanExtensionNatTrans L)

noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtension :
    (F.pointwiseLeftKanExtension L).IsPointwiseLeftKanExtension := fun X =>
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp]
    rfl))

noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (F.pointwiseLeftKanExtension L).IsUniversal :=
  (F.pointwiseLeftKanExtension L).isUniversalOfPointwise
    (F.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L)

instance : (F.pointwiseLeftKanExtensionFunctor L).IsLeftKanExtension
    (F.pointwiseLeftKanExtensionNatTrans L) where
  nonempty_isUniversal := ⟨F.pointwiseLeftKanExtensionIsUniversal L⟩

instance : HasLeftKanExtension L F :=
  HasLeftKanExtension.mk' _ (F.pointwiseLeftKanExtensionNatTrans L)

variable {F L}

noncomputable def isPointwiseLeftKanExtensionOfIsLeftKanExtension (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension :=
  LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
    (IsColimit.coconePointUniqueUpToIso (F.pointwiseLeftKanExtensionIsUniversal L)
      (F'.leftKanExtensionUniversal α))
    (F.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension L)

end

end Functor

end CategoryTheory
