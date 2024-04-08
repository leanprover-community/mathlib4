import Mathlib.CategoryTheory.Comma.StructuredArrow

namespace CategoryTheory

open Category

namespace Comma

variable {C₁ C₂ D C₁' C₂' D' : Type*} [Category C₁] [Category C₂] [Category D]
  [Category C₁'] [Category C₂'] [Category D']

variable {L : C₁ ⥤ D} {R : C₂ ⥤ D} {L' : C₁' ⥤ D'} {R' : C₂' ⥤ D'}
  {F₁ : C₁ ⥤ C₁'} {F₂ : C₂ ⥤ C₂'} {F : D ⥤ D'}
  (α : F₁ ⋙ L' ⟶ L ⋙ F)
  (β : R ⋙ F ⟶ F₂ ⋙ R')

@[simps!]
def map : Comma L R ⥤ Comma L' R' where
  obj X :=
    { left := F₁.obj X.left
      right := F₂.obj X.right
      hom := α.app X.left ≫ F.map X.hom ≫ β.app X.right }
  map {X Y} φ :=
    { left := F₁.map φ.left
      right := F₂.map φ.right
      w := by
        dsimp
        rw [assoc, assoc]
        erw [α.naturality_assoc, ← β.naturality]
        dsimp
        rw [← F.map_comp_assoc, ← F.map_comp_assoc, φ.w] }

instance faithful_map [Faithful F₁] [Faithful F₂] : Faithful (map α β) where
  map_injective {X Y} f g h := by
    ext
    · exact F₁.map_injective (congr_arg CommaMorphism.left h)
    · exact F₂.map_injective (congr_arg CommaMorphism.right h)

instance fullMap [Faithful F] [Full F₁] [Full F₂] [IsIso α] [IsIso β] : Full (map α β) where
  preimage {X Y} φ :=
    { left := F₁.preimage φ.left
      right := F₂.preimage φ.right
      w := F.map_injective (by
        rw [← cancel_mono (β.app _), ← cancel_epi (α.app _), F.map_comp, F.map_comp,
          assoc, assoc]
        erw [← α.naturality_assoc, β.naturality]
        dsimp
        rw [F₁.image_preimage, F₂.image_preimage]
        simpa using φ.w) }

instance essSurj_map [EssSurj F₁] [EssSurj F₂] [Full F] [IsIso α] [IsIso β] :
    EssSurj (map α β) where
  mem_essImage X :=
    ⟨{  left := F₁.objPreimage X.left
        right := F₂.objPreimage X.right
        hom := F.preimage ((inv α).app _ ≫ L'.map (F₁.objObjPreimageIso X.left).hom ≫
          X.hom ≫ R'.map (F₂.objObjPreimageIso X.right).inv ≫ (inv β).app _) },
            ⟨isoMk (F₁.objObjPreimageIso X.left) (F₂.objObjPreimageIso X.right) (by
              dsimp
              simp only [NatIso.isIso_inv_app, Functor.comp_obj, Functor.image_preimage, assoc,
                IsIso.inv_hom_id, comp_id, IsIso.hom_inv_id_assoc]
              rw [← R'.map_comp, Iso.inv_hom_id, R'.map_id, comp_id])⟩⟩

noncomputable instance isEquivalenceMap
    [Faithful F₁] [Faithful F₂] [Faithful F] [Full F₁] [Full F₂]
    [EssSurj F₁] [EssSurj F₂] [Full F] [IsIso α] [IsIso β] :
    IsEquivalence (map α β) := by
  apply Equivalence.ofFullyFaithfullyEssSurj

end Comma

namespace StructuredArrow

variable {C D C' D' : Type*} [Category C] [Category D]
  [Category C'] [Category D']

variable {L : D} {R : C ⥤ D} {L' : D'} {R' : C' ⥤ D'}
  {F : C ⥤ C'} {G : D ⥤ D'}
  (α : L' ⟶ G.obj L)
  (β : R ⋙ G ⟶ F ⋙ R')

@[simps!]
def map₂ : StructuredArrow L R ⥤ StructuredArrow L' R' :=
  Comma.map (F₁ := 𝟭 (Discrete PUnit)) (Discrete.natTrans (fun _ => α)) β

instance faithful_map₂ [Faithful F] : Faithful (map₂ α β) := by
  apply Comma.faithful_map

instance {I : Type*} {F G : Discrete I ⥤ C} (f : ∀ i, F.obj i ⟶ G.obj i)
    [∀ i, IsIso (f i)] :
    IsIso (Discrete.natTrans f) := by
  change IsIso (Discrete.natIso (fun i => asIso (f i))).hom
  infer_instance

instance fullMap₂ [Faithful G] [Full F] [IsIso α] [IsIso β] : Full (map₂ α β) := by
  apply Comma.fullMap

instance essSurj_map₂ [EssSurj F] [Full G] [IsIso α] [IsIso β] : EssSurj (map₂ α β) := by
  apply Comma.essSurj_map

noncomputable instance isEquivalenceMap₂
    [Faithful F] [Faithful G] [EssSurj F] [Full F] [Full G] [IsIso α] [IsIso β] :
    IsEquivalence (map₂ α β) := by
  apply Comma.isEquivalenceMap

end StructuredArrow

end CategoryTheory
