/-import Mathlib.CategoryTheory.Functor.KanExtension.Basic

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Functor

variable {C : Type u₁} {D : Type u₂} {H : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H] [Category.{v₄} D']
  (L : C ⥤ H) (F : C ⥤ D) (ι : D ⥤ D')

@[simps]
def leftExtensionPostcomp : LeftExtension L F ⥤ LeftExtension L (F ⋙ ι) where
  obj G := LeftExtension.mk (G.right ⋙ ι) (whiskerRight G.hom ι)
  map {G₁ G₂} φ := StructuredArrow.homMk (whiskerRight φ.right ι) (by
    ext X
    dsimp
    rw [← ι.map_comp]
    congr 1
    simpa using congr_app φ.w.symm X)

instance [Faithful ι] : Faithful (leftExtensionPostcomp L F ι) where
  map_injective {G₁ G₂} φ₁ φ₂ h := by
    ext X
    apply ι.map_injective
    simpa using congr_app (congr_map (StructuredArrow.proj _ _) h) X

-- should be moved
noncomputable instance [Full ι] [Faithful ι] : Full ((whiskeringRight H D D').obj ι) :=
  fullOfSurjective _ (fun F₁ F₂ ψ => by
    let φ : F₁ ⟶ F₂ :=
      { app := fun X => ι.preimage (ψ.app X)
        naturality := fun X₁ X₂ f => ι.map_injective (by
          dsimp
          simp only [map_comp, image_preimage]
          exact ψ.naturality f) }
    exact ⟨φ, by aesop_cat⟩)

noncomputable instance [Full ι] [Faithful ι] : Full (leftExtensionPostcomp L F ι) :=
  fullOfSurjective _ (fun G₁ G₂ ψ => by
    obtain ⟨φ, hφ⟩ := ((whiskeringRight H D D').obj ι).map_surjective ψ.right
    refine' ⟨StructuredArrow.homMk φ _, _⟩
    · apply ((whiskeringRight C D D').obj ι).map_injective
      have eq := ψ.w
      simp only [leftExtensionPostcomp_obj, const_obj_obj, whiskeringLeft_obj_obj, LeftExtension.mk_right,
        StructuredArrow.left_eq_id, Discrete.functor_map_id, LeftExtension.mk_hom, Category.id_comp,
        whiskeringLeft_obj_map] at eq
      simp only [Functor.map_comp, const_obj_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj, whiskeringRight_obj_map,
        whiskeringLeft_obj_map]
      rw [eq, ← hφ]
      ext
      simp
    · ext1
      exact hφ)

class IsAbsoluteLeftKanExtension (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F')
    extends IsLeftKanExtension F' α : Prop where
  universal' : ∀ (J : Type max u₂ u₃ v₂ v₃) [SmallCategory J] (K : D ⥤ J),
    (F' ⋙ K).IsLeftKanExtension (whiskerRight α K)

/-lemma universalLeftKanExtension_aux (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F')
  {J : Type u₅} [Category.{v₅} J]
  (K : D ⥤ J) (G : LeftExtension L (F ⋙ K)) :
  ∃ (J' : Type max u₂ u₃ v₂ v₃) (hJ' : SmallCategory J') (ι : J' ⥤ J)
    (K' : D ⥤ J') (eK' : K ≅ K' ⋙ ι) (G' : H ⥤ J') (α' : F ⋙ K' ⟶ L ⋙ G')
      (eG : G.right ≅ G' ⋙ ι), G.hom ≫ whiskerLeft L eG.hom =
        whiskerLeft F eK'.hom ≫ whiskerRight α' ι := sorry

instance (F' : H ⥤ D) {L : C ⥤ H} {F : C ⥤ D} (α : F ⟶ L ⋙ F')
  [F'.IsAbsoluteLeftKanExtension α] {J : Type u₅} [Category.{v₅} J] (K : D ⥤ J) :
    (F' ⋙ K).IsLeftKanExtension (whiskerRight α K) :=
  ⟨⟨@Limits.IsInitial.ofUnique _ _ _ (fun (G : LeftExtension L (F ⋙ K)) => Nonempty.some (by
    obtain ⟨J', _, ι, K', eK', G', α', eG, w⟩ := universalLeftKanExtension_aux F' α K G
    have : (F' ⋙ K').IsLeftKanExtension (whiskerRight α K') :=
      IsAbsoluteLeftKanExtension.universal' _ _
    have : Inhabited (LeftExtension.mk (F' ⋙ K) (whiskerRight α K) ⟶ G) := by
      exact ⟨StructuredArrow.homMk (whiskerLeft F' eK'.hom ≫
        whiskerRight (leftKanExtensionDesc (F' ⋙ K') (whiskerRight α K') G' α') ι ≫ eG.inv)
        (by
          ext X
          dsimp
          simp only [NatTrans.naturality_assoc, comp_obj, comp_map, ← ι.map_comp_assoc]
          erw [leftKanExtension_fac_app (F' ⋙ K') (whiskerRight α K') G' α' X]
          have h := congr_app w X
          dsimp at h
          erw [← reassoc_of% h]
          simp)⟩
    have : Subsingleton (LeftExtension.mk (F' ⋙ K) (whiskerRight α K) ⟶ G) := sorry
    exact Nonempty.intro (Unique.mk' _)))⟩⟩-/

end Functor

end CategoryTheory
-/
