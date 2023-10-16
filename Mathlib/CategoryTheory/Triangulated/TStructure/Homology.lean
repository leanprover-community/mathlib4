import Mathlib.CategoryTheory.Triangulated.TStructure.TExact

namespace CategoryTheory

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]
  (i : C ⥤ D) [Full i] [Faithful i]

def preimageNatTrans {F₁ F₂ : H ⥤ C} (τ : F₁ ⋙ i ⟶ F₂ ⋙ i) : F₁ ⟶ F₂ where
  app X := i.preimage (τ.app X)
  naturality {X Y} f := i.map_injective (by
    simp only [map_comp, image_preimage]
    exact τ.naturality f)

@[simp]
lemma image_preimageNatTrans {F₁ F₂ : H ⥤ C} (τ : F₁ ⋙ i ⟶ F₂ ⋙ i) (X : H) :
    i.map ((i.preimageNatTrans τ).app X) = τ.app X := by
  simp [preimageNatTrans]

@[simp]
lemma preimageNatTrans_id (F : H ⥤ C) : i.preimageNatTrans (𝟙 (F ⋙ i)) = 𝟙 F := by
  ext X
  apply i.map_injective
  simp

@[reassoc (attr := simp)]
lemma preimageNatTrans_comp {F₁ F₂ F₃ : H ⥤ C} (τ : F₁ ⋙ i ⟶ F₂ ⋙ i) (τ' : F₂ ⋙ i ⟶ F₃ ⋙ i) :
    i.preimageNatTrans τ ≫ i.preimageNatTrans τ' = i.preimageNatTrans (τ ≫ τ') := by
  ext X
  apply i.map_injective
  simp

@[simps]
def preimageNatIso {F₁ F₂ : H ⥤ C} (e : F₁ ⋙ i ≅ F₂ ⋙ i) : F₁ ≅ F₂ where
  hom := i.preimageNatTrans e.hom
  inv := i.preimageNatTrans e.inv

end Functor

open Limits

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C) [t.HasHeart] [IsTriangulated C]

class HasHomology₀ where
  homology₀ : C ⥤ t.Heart
  iso : homology₀ ⋙ t.ιHeart ≅ t.truncGELE 0 0

variable [IsTriangulated C]

lemma truncLE₀GE₀_mem_heart (X : C) :
    (t.truncLEGE 0 0).obj X ∈ t.heart := by
  rw [t.mem_heart_iff]
  dsimp [truncLEGE]
  constructor
  · infer_instance
  · infer_instance

lemma truncGE₀LE₀_mem_heart (X : C) :
    (t.truncGELE 0 0).obj X ∈ t.heart := by
  rw [t.mem_heart_iff]
  constructor <;> infer_instance

noncomputable def hasHomology₀ : t.HasHomology₀ where
  homology₀ := t.liftHeart (t.truncGELE 0 0) t.truncGE₀LE₀_mem_heart
  iso := t.liftHeartιHeart _ _

variable [ht : t.HasHomology₀]

def homology₀ : C ⥤ t.Heart := ht.homology₀

def homology₀ιHeart : t.homology₀ ⋙ t.ιHeart ≅ t.truncGELE 0 0 := ht.iso

end TStructure

namespace Subcategory

variable (S : Subcategory C) (t : TStructure C)
  [S.HasInducedTStructure t] [t.HasHeart]

instance : S.ι.TExact (S.tStructure t) t where
  rightTExact := ⟨fun _ _ ⟨hX⟩ => ⟨hX⟩⟩
  leftTExact := ⟨fun _ _ ⟨hX⟩ => ⟨hX⟩⟩

class ContainsHeart : Prop where
  subset : t.heart ⊆ S.set

variable [hS : S.ContainsHeart t]

instance : (S.tStructure t).HasHeart where
  H := t.Heart
  ι := FullSubcategory.lift _ t.ιHeart (fun X => hS.subset (t.ιHeart_obj_mem X))
  additive_ι := ⟨fun {X Y f g} => S.ι.map_injective (by simp)⟩
  fullι := { preimage := fun f => t.ιHeart.preimage f }
  faithful_ι := ⟨fun {X Y} f g h => t.ιHeart.map_injective h⟩
  hι := by
    ext X
    constructor
    · rintro ⟨Y, ⟨e⟩⟩
      exact t.heart.mem_of_iso ((fullSubcategoryInclusion _).mapIso e)
        (t.ιHeart_obj_mem Y)
    · intro hX
      exact ⟨_, ⟨(fullSubcategoryInclusion _).preimageIso (t.ιHeartObjHeartMkIso _ hX)⟩⟩

def ιHeartIso : (S.tStructure t).ιHeart ⋙ S.ι ≅ t.ιHeart := Iso.refl _

variable [t.HasHomology₀]

noncomputable instance : (S.tStructure t).HasHomology₀ where
  homology₀ := S.ι ⋙ t.homology₀
  iso := S.ι.preimageNatIso (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (S.ιHeartIso t) ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ t.homology₀ιHeart ≪≫
      (S.ι.truncGELEIso (S.tStructure t) t 0 0).symm)

noncomputable instance [t.homology₀.ShiftSequence ℤ] :
    (S.tStructure t).homology₀.ShiftSequence ℤ :=
  (inferInstance : (S.ι ⋙ t.homology₀).ShiftSequence ℤ)

instance : t.plus.ContainsHeart t where
  subset _ hX := ⟨0, ⟨hX.2⟩⟩

instance : t.minus.ContainsHeart t where
  subset _ hX := ⟨0, ⟨hX.1⟩⟩

end Subcategory

namespace TStructure

variable (t : TStructure C) [IsTriangulated C]

abbrev tPlus := t.plus.tStructure t
abbrev tMinus := t.minus.tStructure t

end TStructure

end Triangulated

end CategoryTheory
