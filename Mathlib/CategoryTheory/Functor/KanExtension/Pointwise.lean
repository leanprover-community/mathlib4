import Mathlib.CategoryTheory.Functor.KanExtension

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D H : Type _} [Category C] [Category D] [Category H]
  (F : C ⥤ H) (L : C ⥤ D)

abbrev HasPointwiseLeftKanExtensionAt (Y : D) :=
  HasColimit (CostructuredArrow.proj L Y ⋙ F)

namespace LeftExtension

variable {F L} (E : LeftExtension L F)

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

def IsPointwiseLeftKanExtensionAt (Y : D) := IsColimit (E.coconeAt Y)

def isUniversalOfPointwise (h : ∀ (Y : D), E.IsPointwiseLeftKanExtensionAt Y) :
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

variable [∀ (Y : D), F.HasPointwiseLeftKanExtensionAt L Y]

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

noncomputable def pointwiseLeftKanExtensionIsPointwiseLeftKanExtensionAt (X : D) :
    (F.pointwiseLeftKanExtension L).IsPointwiseLeftKanExtensionAt X :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (fun j => by
    dsimp
    simp only [comp_id, colimit.ι_desc, CostructuredArrow.map_mk]
    congr 1
    rw [id_comp]
    rfl))

noncomputable def pointwiseLeftKanExtensionIsUniversal :
    (F.pointwiseLeftKanExtension L).IsUniversal :=
  (F.pointwiseLeftKanExtension L).isUniversalOfPointwise
    (F.pointwiseLeftKanExtensionIsPointwiseLeftKanExtensionAt L)

instance : (F.pointwiseLeftKanExtensionFunctor L).IsLeftKanExtension
    (F.pointwiseLeftKanExtensionNatTrans L) where
  nonempty_isUniversal := ⟨F.pointwiseLeftKanExtensionIsUniversal L⟩

end

end Functor

end CategoryTheory
