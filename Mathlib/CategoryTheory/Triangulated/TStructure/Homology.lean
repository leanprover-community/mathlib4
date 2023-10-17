import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Limits.FullSubcategory

namespace CategoryTheory

open Limits Pretriangulated ZeroObject

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

noncomputable def isEquivalenceFullSubcategoryLift (S : Set D) (hi : i.essImage = S) :
    IsEquivalence (FullSubcategory.lift S i
      (fun X => by rw [← hi]; exact obj_mem_essImage i X)) := by
  let F := FullSubcategory.lift S i
      (fun X => by rw [← hi]; exact obj_mem_essImage i X)
  have : Full F := fullOfSurjective _ (fun X Y f => ⟨i.preimage f, by simp⟩)
  have : Faithful F := ⟨fun {X Y} f g h => i.map_injective h⟩
  have : EssSurj F := ⟨by
    rintro ⟨X, hX⟩
    rw [← hi] at hX
    obtain ⟨Y, ⟨e⟩⟩ := hX
    exact ⟨Y, ⟨(fullSubcategoryInclusion S).preimageIso e⟩⟩⟩
  apply Equivalence.ofFullyFaithfullyEssSurj

end Functor

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

section

lemma zero_mem_heart : 0 ∈ t.heart := by
  rw [t.mem_heart_iff]
  constructor <;> infer_instance

lemma prod_mem_heart (X₁ X₂ : C) (hX₁ : X₁ ∈ t.heart) (hX₂ : X₂ ∈ t.heart) :
    (X₁ ⨯ X₂) ∈ t.heart := by
  rw [t.mem_heart_iff]
  constructor
  · exact t.isLE₂ _ (binaryProductTriangle_distinguished X₁ X₂) 0 ⟨hX₁.1⟩ ⟨hX₂.1⟩
  · exact t.isGE₂ _ (binaryProductTriangle_distinguished X₁ X₂) 0 ⟨hX₁.2⟩ ⟨hX₂.2⟩

instance : HasTerminal (FullSubcategory t.heart) := by
  let Z : FullSubcategory t.heart := ⟨0, t.zero_mem_heart⟩
  have : ∀ X, Inhabited (X ⟶ Z) := fun X => ⟨0⟩
  have : ∀ X, Unique (X ⟶ Z) := fun X =>
    { uniq := fun f => (fullSubcategoryInclusion t.heart).map_injective ((isZero_zero C).eq_of_tgt _ _) }
  exact hasTerminal_of_unique Z

instance : HasBinaryProducts (FullSubcategory t.heart) := by
  apply hasLimitsOfShape_of_closed_under_limits
  intro F c hc H
  exact t.heart.mem_of_iso
    (limit.isoLimitCone ⟨_, (IsLimit.postcomposeHomEquiv (diagramIsoPair F) _).symm hc⟩)
    (prod_mem_heart t _ _ (H _) (H _))

instance : HasFiniteProducts (FullSubcategory t.heart) := hasFiniteProducts_of_has_binary_and_terminal

variable [t.HasHeart]

noncomputable def heartEquivalenceFullsubcategory :
    t.Heart ≌ FullSubcategory t.heart :=
  have := t.ιHeart.isEquivalenceFullSubcategoryLift t.heart (by
    ext X
    rw [t.mem_essImage_ιHeart_iff])
  @Functor.asEquivalence _ _ _ _ _ this

instance : HasFiniteProducts t.Heart where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence
      t.heartEquivalenceFullsubcategory.functor

instance (X : C) (n : ℤ) [t.IsGE X 0] : t.IsGE (X⟦n⟧) (-n) :=
  t.isGE_shift X 0 n (-n) (by linarith)

instance (X : C) (n : ℤ) [t.IsGE X 0] : t.IsGE (X⟦-n⟧) n :=
  t.isGE_shift X 0 (-n) n (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X 0] : t.IsLE (X⟦n⟧) (-n) :=
  t.isLE_shift X 0 n (-n) (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X 0] : t.IsLE (X⟦-n⟧) n :=
  t.isLE_shift X 0 (-n) n (by linarith)

instance (X : C) [t.IsLE X 0] : t.IsLE X 1 :=
  t.isLE_of_LE X 0 1 (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X n] : t.IsLE (X⟦(1 : ℤ)⟧) n :=
  have := t.isLE_shift X n 1 (n - 1) (by linarith)
  t.isLE_of_LE (X⟦(1 : ℤ)⟧) (n - 1) n (by linarith)

instance (X : C) [t.IsGE X 0] : t.IsGE X (-1) :=
  t.isGE_of_GE X (-1) 0 (by linarith)

instance (X : C) (n : ℤ) [t.IsLE X n] : t.IsLE (X⟦n⟧) 0 :=
  t.isLE_shift X n n 0 (add_zero n)

instance (X : C) (n : ℤ) [t.IsGE X n] : t.IsGE (X⟦n⟧) 0 :=
  t.isGE_shift X n n 0 (add_zero n)

section

variable {X₁ X₂ : t.Heart} {X₃ : C} {f₁ : X₁ ⟶ X₂} {f₂ : t.ιHeart.obj X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f₁) f₂ f₃ ∈ distTriang C)

lemma cocone_heart_isLE_zero : t.IsLE X₃ 0 :=
  t.isLE₂ _ (rot_of_dist_triangle _ hT) 0 (by dsimp; infer_instance)
    (by dsimp; infer_instance)

lemma cocone_heart_isGE_neg_one : t.IsGE X₃ (-1) :=
  t.isGE₂ _ (rot_of_dist_triangle _ hT) (-1)
    (by dsimp; infer_instance) (by dsimp; infer_instance)

end

lemma exists_distinguished_triangle_of_isLE_zero_of_isGE_neg_one
    (X : C) [t.IsLE X 0] [t.IsGE X (-1)] :
    ∃ (K Q : t.Heart) (α : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ⟶ X) (β : X ⟶ t.ιHeart.obj Q)
      (γ : t.ιHeart.obj Q ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang C := by
  have hK : ((t.truncLE (-1)).obj X)⟦(-1 : ℤ)⟧ ∈ t.heart := by
    rw [t.mem_heart_iff]
    constructor <;> dsimp <;> infer_instance
  have hQ : (t.truncGE 0).obj X ∈ t.heart := by
    rw [t.mem_heart_iff]
    constructor <;> infer_instance
  have e₁ := (shiftFunctor C (1 : ℤ)).mapIso (t.ιHeartObjHeartMkIso _ hK) ≪≫
    (shiftEquiv C (1 : ℤ)).counitIso.app _
  have e₃ := t.ιHeartObjHeartMkIso _ hQ
  refine' ⟨t.heartMk _ hK, t.heartMk _ hQ, e₁.hom ≫ (t.truncLEι (-1)).app X,
    (t.truncGEπ 0).app X ≫ e₃.inv,
    e₃.hom ≫ (t.truncGEδLE (-1) 0 (by linarith)).app X ≫ e₁.inv⟦(1 : ℤ)⟧', _⟩
  refine' isomorphic_distinguished _ (t.triangleLEGE_distinguished (-1) 0 (by linarith) X) _ _
  refine' Triangle.isoMk _ _ e₁ (Iso.refl _) e₃ _ _ _
  · dsimp
    simp
  · dsimp
    simp
  · dsimp
    simp only [Category.assoc, Iso.cancel_iso_hom_left, ← Functor.map_comp,
      e₁.inv_hom_id, Functor.id_obj, Functor.map_id, Category.comp_id]

lemma admissibleMorphism_heart {X₁ X₂ : t.Heart} (f : X₁ ⟶ X₂) :
    AbelianSubcategory.admissibleMorphism t.ιHeart f := by
  intro X₃ f₂ f₃ hT
  have := t.cocone_heart_isLE_zero hT
  have := t.cocone_heart_isGE_neg_one hT
  exact t.exists_distinguished_triangle_of_isLE_zero_of_isGE_neg_one X₃

lemma abelian_heart [t.HasHomology₀] : Abelian t.Heart := by
  apply AbelianSubcategory.abelian t.ιHeart
  · intro X Y n f hn
    exact t.zero f 0 (-n) (by linarith)
  · apply admissibleMorphism_heart

end

noncomputable instance [t.HasHeart] : Abelian t.Heart := by
  have := t.hasHomology₀
  apply abelian_heart

end TStructure

end Triangulated

end CategoryTheory
