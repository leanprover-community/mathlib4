import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.ULift
import Mathlib.Algebra.Homology.ShortComplex.ShortComplexFour

universe v v'

open CategoryTheory Category Limits Pretriangulated Preadditive ZeroObject

namespace CategoryTheory

namespace Limits

namespace CokernelCofork

variable {C : Type*} [Category C] [Preadditive C]

def nonempty_isColimit_iff_preadditiveYoneda {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f) :
    Nonempty (IsColimit c) ↔ ∀ (A : C), ((ShortComplex.mk _ _ c.condition).op.map (preadditiveYoneda.obj A)).Exact ∧
      Mono (((ShortComplex.mk _ _ c.condition).op.map (preadditiveYoneda.obj A)).f) := by
  simp_rw [ShortComplex.ab_exact_iff, AddCommGroupCat.mono_iff_injective]
  constructor
  · intro ⟨h⟩ A
    constructor
    · rintro (x₂ : Y ⟶ A) (hx₂ : f ≫ x₂ = 0)
      exact ⟨_, (CokernelCofork.IsColimit.desc' h x₂ hx₂).2⟩
    · rintro (x₁ : c.pt ⟶ A) (x₁' : c.pt ⟶ A) (h₁ : c.π ≫ x₁ = c.π ≫ x₁')
      exact Cofork.IsColimit.hom_ext h h₁
  · rintro h
    exact ⟨Cofork.IsColimit.mk _
      (fun s => ((h _).1 s.π (CokernelCofork.condition s)).choose)
      (fun s => ((h _).1 s.π (CokernelCofork.condition s)).choose_spec)
      (fun s m hm => (h _).2
        (hm.trans ((h _).1 s.π (CokernelCofork.condition s)).choose_spec.symm))⟩

end CokernelCofork

namespace KernelFork

variable {C : Type*} [Category C] [Preadditive C]

def nonempty_isLimit_iff_preadditiveCoyoneda {X Y : C} {f : X ⟶ Y} (c : KernelFork f) :
    Nonempty (IsLimit c) ↔ ∀ (A : C), ((ShortComplex.mk _ _ c.condition).map (preadditiveCoyoneda.obj (Opposite.op A))).Exact ∧
      Mono (((ShortComplex.mk _ _ c.condition).map (preadditiveCoyoneda.obj (Opposite.op A))).f) := by
  simp_rw [ShortComplex.ab_exact_iff, AddCommGroupCat.mono_iff_injective]
  constructor
  · intro ⟨h⟩ A
    constructor
    · rintro (x₂ : A ⟶ X) (hx₂ : x₂ ≫ f = 0)
      exact ⟨_, (KernelFork.IsLimit.lift' h x₂ hx₂).2⟩
    · rintro (x₁ : A ⟶ c.pt) (x₁' : A ⟶ c.pt) (h₁ : x₁ ≫ c.ι = x₁' ≫ c.ι)
      exact Fork.IsLimit.hom_ext h h₁
  · rintro h
    exact ⟨Fork.IsLimit.mk _
      (fun s => ((h _).1 s.ι (KernelFork.condition s)).choose)
      (fun s => ((h _).1 s.ι (KernelFork.condition s)).choose_spec)
      (fun s m hm => (h _).2 (hm.trans ((h _).1 s.ι (KernelFork.condition s)).choose_spec.symm))⟩

end KernelFork

end Limits

namespace ShortComplex

variable {C : Type*} [Category C]

variable [Preadditive C]

lemma exact_and_epi_g_iff (S : ShortComplex C) [Balanced C] [S.HasHomology] :
    (S.Exact ∧ Epi S.g) ↔
      Nonempty (IsColimit (CokernelCofork.ofπ _ S.zero)) := by
  constructor
  · rintro ⟨hS, _⟩
    exact ⟨hS.gIsCokernel⟩
  · intro ⟨h⟩
    exact ⟨S.exact_of_g_is_cokernel h, ⟨fun _ _ => Cofork.IsColimit.hom_ext h⟩⟩

lemma exact_and_mono_f_iff (S : ShortComplex C) [Balanced C] [S.HasHomology] :
    (S.Exact ∧ Mono S.f) ↔
      Nonempty (IsLimit (KernelFork.ofι _ S.zero)) := by
  constructor
  · rintro ⟨hS, _⟩
    exact ⟨hS.fIsKernel⟩
  · intro ⟨h⟩
    exact ⟨S.exact_of_f_is_kernel h, ⟨fun _ _ => Fork.IsLimit.hom_ext h⟩⟩

lemma exact_and_epi_g_iff_preadditiveYoneda (S : ShortComplex C) [Balanced C] [S.HasHomology] :
    (S.Exact ∧ Epi S.g) ↔
      ∀ (A : C), (S.op.map (preadditiveYoneda.obj A)).Exact ∧
        Mono (S.op.map (preadditiveYoneda.obj A)).f := by
  rw [exact_and_epi_g_iff, CokernelCofork.nonempty_isColimit_iff_preadditiveYoneda]
  rfl

lemma exact_and_mono_f_iff_preadditiveCoyoneda (S : ShortComplex C) [Balanced C] [S.HasHomology] :
    (S.Exact ∧ Mono S.f) ↔
      ∀ (A : C), (S.map (preadditiveCoyoneda.obj (Opposite.op A))).Exact ∧
        Mono (S.map (preadditiveCoyoneda.obj (Opposite.op A))).f := by
  rw [exact_and_mono_f_iff, KernelFork.nonempty_isLimit_iff_preadditiveCoyoneda]
  rfl

end ShortComplex


namespace Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

lemma preadditiveYoneda_map_distinguished (A : C) (T : Triangle C) (hT : T ∈ distTriang C) :
    ((ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj A)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro (x₂ : T.obj₂ ⟶ A) (hx₂ : T.mor₁ ≫ x₂ = 0)
  obtain ⟨x₃, hx₃⟩ := T.yoneda_exact₂ hT x₂ hx₂
  exact ⟨x₃, hx₃.symm⟩

instance (A : Cᵒᵖ) : (preadditiveCoyoneda.obj A).IsHomological where
  exact T hT := by
    rw [ShortComplex.ab_exact_iff]
    intro (x₂ : A.unop ⟶ T.obj₂) (hx₂ : x₂ ≫ T.mor₂ = 0)
    obtain ⟨x₁, hx₁⟩ := T.coyoneda_exact₂ hT x₂ hx₂
    exact ⟨x₁, hx₁.symm⟩

end Pretriangulated

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

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
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

instance (X : C) : t.IsLE ((t.truncLT 0).obj X) (-1) :=
  t.isLE_of_iso ((t.truncLEIsoTruncLT (-1) 0 (by linarith)).app X) (-1)

section

variable {X₁ X₂ : t.Heart} {X₃ : C} {f₁ : X₁ ⟶ X₂} {f₂ : t.ιHeart.obj X₂ ⟶ X₃}
    {f₃ : X₃ ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (t.ιHeart.map f₁) f₂ f₃ ∈ distTriang C)

lemma cocone_heart_isLE_zero : t.IsLE X₃ 0 :=
  t.isLE₂ _ (rot_of_distTriang _ hT) 0 (by dsimp; infer_instance)
    (by dsimp; infer_instance)

lemma cocone_heart_isGE_neg_one : t.IsGE X₃ (-1) :=
  t.isGE₂ _ (rot_of_distTriang _ hT) (-1)
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

noncomputable instance : Abelian t.Heart := by
  apply AbelianSubcategory.abelian t.ιHeart
  · intro X Y n f hn
    exact t.zero f 0 (-n) (by linarith)
  · apply admissibleMorphism_heart

end

section

variable [TStructure.HasHeart.{_, _, _, v'} t] [t.HasHomology₀]

section

variable (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) [t.IsLE T.obj₁ n]

@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def truncLETriangle  :
    Triangle C :=
  Triangle.mk ((t.truncLE n).map T.mor₁)
    ((t.truncLE n).map T.mor₂)
    ((t.truncLEι n).app T.obj₃ ≫ T.mor₃ ≫ (asIso ((t.truncLEι n).app T.obj₁)).inv⟦(1 : ℤ)⟧')

instance : t.IsLE (t.truncLETriangle T n).obj₁ n := by dsimp; infer_instance
instance : t.IsLE (t.truncLETriangle T n).obj₂ n := by dsimp; infer_instance
instance : t.IsLE (t.truncLETriangle T n).obj₃ n := by dsimp; infer_instance

lemma truncLETriangle_distinguished :
    t.truncLETriangle T n ∈ distTriang C := by
  let a : T.obj₁ ⟶ (t.truncLE n).obj T.obj₂ :=
    (asIso ((t.truncLEι n).app T.obj₁)).inv ≫ (t.truncLE n).map T.mor₁
  let b := (t.truncLEι n).app T.obj₂
  have comm : a ≫ b = T.mor₁ := by simp
  obtain ⟨Z, f₂, f₃, h₁⟩ := distinguished_cocone_triangle a
  have h₂ := (t.triangleLEGT_distinguished n T.obj₂)
  have H := someOctahedron comm h₁ h₂ hT
  have : t.IsLE Z n := t.isLE₂ _ (rot_of_distTriang _ h₁) n
      (by dsimp; infer_instance) (by dsimp; infer_instance)
  obtain ⟨e, he : e.hom.hom₂ = 𝟙 _⟩ :=
    t.triangle_iso_exists n (n + 1) (by linarith) _ _
      (t.triangleLEGE_distinguished n (n + 1) rfl T.obj₃) H.mem (Iso.refl _)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
  have he' : e.inv.hom₂ = 𝟙 _ := by
    rw [← cancel_mono e.hom.hom₂, ← comp_hom₂, e.inv_hom_id, id_hom₂, he, comp_id]
  have he₁' : (truncLE t n).map T.mor₂ = f₂ ≫ e.inv.hom₁ := by
    apply to_truncLE_obj_ext
    have eq₁ := e.inv.comm₁
    have eq₂ := H.comm₁
    dsimp at eq₁ eq₂ ⊢
    simp only [NatTrans.naturality, Functor.id_map, ← eq₂, assoc, ← eq₁,
      he', Triangle.mk_obj₂, comp_id]
  have he₁ : (truncLE t n).map T.mor₂ ≫ e.hom.hom₁ = f₂ := by
    rw [he₁', assoc, ← comp_hom₁, e.inv_hom_id, id_hom₁]
    simp only [Triangle.mk_obj₁, comp_id]
  have he₂ : (t.truncLETriangle T n).mor₃ ≫
    (shiftFunctor C 1).map ((truncLEι t n).app T.obj₁) = e.hom.hom₁ ≫ f₃ := by
    have eq₁ := H.comm₂
    have eq₂ := e.hom.comm₁
    dsimp at eq₁ eq₂
    dsimp [truncLETriangle]
    erw [he, comp_id] at eq₂
    rw [assoc, assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      Functor.map_id, comp_id, eq₂, assoc, eq₁]
  refine' isomorphic_distinguished _ h₁ _ _
  exact Triangle.isoMk _ _ (asIso ((t.truncLEι n).app T.obj₁))
    (Iso.refl _) (Triangle.π₁.mapIso e) (by simp) (by simp [he₁]) he₂

end

section

variable (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) [t.IsGE T.obj₃ n]

@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def truncGETriangle  :
    Triangle C :=
  Triangle.mk ((t.truncGE n).map T.mor₁) ((t.truncGE n).map T.mor₂)
    ((asIso ((t.truncGEπ n).app T.obj₃)).inv ≫ T.mor₃ ≫ ((t.truncGEπ n).app T.obj₁)⟦(1 : ℤ)⟧')

instance : t.IsGE (t.truncGETriangle T n).obj₁ n := by dsimp; infer_instance
instance : t.IsGE (t.truncGETriangle T n).obj₂ n := by dsimp; infer_instance
instance : t.IsGE (t.truncGETriangle T n).obj₃ n := by dsimp; infer_instance

instance (X : C) [t.IsGE X n] : t.IsGE (X⟦(-1 : ℤ)⟧) n := by
  have : t.IsGE (X⟦(-1 : ℤ)⟧) (n + 1) :=
    t.isGE_shift X n (-1) (n + 1) (by linarith)
  exact t.isGE_of_GE _ n (n + 1) (by linarith)

lemma truncGETriangle_distinguished :
    t.truncGETriangle T n ∈ distTriang C := by
  have := hT
  let a := (t.truncGEπ n).app T.obj₂
  let b : (t.truncGE n).obj T.obj₂ ⟶ T.obj₃ :=
    (t.truncGE n).map T.mor₂ ≫ (asIso ((t.truncGEπ n).app T.obj₃)).inv
  have comm : a ≫ b = T.mor₂ := by simp
  have h₁ := rot_of_distTriang _ (t.triangleLEGE_distinguished (n-1) n (by linarith) T.obj₂)
  obtain ⟨Z, f₁, f₃, h₂⟩ := distinguished_cocone_triangle₁ b
  have H := someOctahedron comm h₁ (rot_of_distTriang _ h₂) (rot_of_distTriang _ hT)
  obtain ⟨m₁, hm₁⟩ : ∃ (m₁ : (t.truncLE (n-1)).obj T.obj₂ ⟶ T.obj₁),
    (shiftFunctor C (1 : ℤ)).map m₁ = H.m₁ := ⟨(shiftFunctor C (1 : ℤ)).preimage H.m₁, by simp⟩
  obtain ⟨m₃, hm₃⟩ : ∃ (m₃ : T.obj₁ ⟶ Z), (shiftFunctor C (1 : ℤ)).map m₃ = H.m₃ :=
    ⟨(shiftFunctor C (1 : ℤ)).preimage H.m₃, by simp⟩
  let T' := Triangle.mk m₁ m₃ (f₁ ≫ (t.truncGEδLE (n-1) n (by linarith)).app T.obj₂)
  have Hmem' : T' ∈ distTriang C := by
    rw [← T'.shift_distinguished_iff 1]
    refine' isomorphic_distinguished _ H.mem _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) (-(Iso.refl _)) (Iso.refl _) _ _ _
    · dsimp
      simp [hm₁]
    · dsimp
      simp [hm₃]
    · dsimp
      simp
  have : t.IsGE Z n := t.isGE₂ _ (inv_rot_of_distTriang _ h₂) n
    (by dsimp; infer_instance) (by dsimp; infer_instance)
  obtain ⟨e, he : _ = 𝟙 _⟩ :=
    t.triangle_iso_exists (n-1) n (by linarith) _ _
      (t.triangleLEGE_distinguished (n - 1) n (by linarith) T.obj₁)
      Hmem' (Iso.refl _) (by dsimp; infer_instance) (by dsimp; infer_instance)
      (by dsimp; infer_instance) (by dsimp; infer_instance)
  refine' isomorphic_distinguished _ h₂ _ _
  refine' Triangle.isoMk _ _ (Triangle.π₃.mapIso e) (Iso.refl _)
    (asIso ((t.truncGEπ n).app T.obj₃)).symm _ _ _
  · dsimp
    simp only [comp_id]
    have eq₁ := e.hom.comm₂
    have eq₂ := H.comm₄
    dsimp at eq₁ eq₂
    simp only [neg_comp, comp_neg, neg_inj] at eq₂
    apply from_truncGE_obj_ext
    rw [reassoc_of% eq₁, he]
    dsimp
    rw [id_comp, ← NatTrans.naturality]
    dsimp
    apply (shiftFunctor C (1 : ℤ)).map_injective
    simpa only [Functor.map_comp, hm₃] using eq₂
  · dsimp
    simp
  · dsimp [truncGETriangle]
    simp only [assoc, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc]
    have eq₁ := H.comm₃
    have eq₂ := e.hom.comm₂
    dsimp at eq₁ eq₂
    rw [← eq₁, ← Functor.map_comp, eq₂, he]
    dsimp
    rw [id_comp, hm₃]

end

noncomputable def toHomology₀ (X : C) [t.IsLE X 0] : X ⟶ t.ιHeart.obj ((t.homology₀).obj X) :=
  inv ((t.truncLEι 0).app X) ≫ (t.truncGEπ 0).app _ ≫ t.homology₀ιHeart.inv.app X

@[reassoc (attr := simp)]
lemma toHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsLE X 0] [t.IsLE Y 0] :
    t.toHomology₀ X ≫ t.ιHeart.map (t.homology₀.map f) = f ≫ t.toHomology₀ Y := by
  dsimp [toHomology₀]
  rw [← cancel_epi ((t.truncLEι 0).app X), assoc, assoc, IsIso.hom_inv_id_assoc]
  erw [← NatTrans.naturality, ← NatTrans.naturality_assoc,
    ← NatTrans.naturality_assoc, IsIso.hom_inv_id_assoc]
  rfl

instance (A X : C) [t.IsLE X 0] [t.IsGE A 0] :
    IsIso ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) := by
  have : Mono ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) :=
    (preadditiveYoneda_map_distinguished A _ (rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X))).mono_g (by
      apply IsZero.eq_of_src
      apply AddCommGroupCat.isZero
      intro (x : ((t.truncLT 0).obj X)⟦(1 : ℤ)⟧ ⟶ A)
      have : t.IsLE (((t.truncLT 0).obj X)⟦(1 : ℤ)⟧) (-1) :=
        t.isLE_shift ((t.truncLT 0).obj X) 0 1 (-1) (by linarith)
      exact t.zero x (-1) 0 (by linarith))
  have : Epi ((preadditiveYoneda.obj A).map ((t.truncGEπ 0).app X).op) :=
    (preadditiveYoneda_map_distinguished A _ (t.triangleLTGE_distinguished 0 X)).epi_f (by
      apply IsZero.eq_of_tgt
      apply AddCommGroupCat.isZero
      intro (x : (t.truncLT 0).obj X ⟶ A)
      exact t.zero x (-1) 0 (by linarith))
  apply isIso_of_mono_of_epi

instance (A X : C) [t.IsLE X 0] [t.IsGE A 0]:
    IsIso ((preadditiveYoneda.obj A).map (t.toHomology₀ X).op) := by
  dsimp only [toHomology₀]
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

noncomputable def fromHomology₀ (X : C) [t.IsGE X 0] :
    t.ιHeart.obj (t.homology₀.obj X) ⟶ X :=
  t.homology₀ιHeart.hom.app X ≫ (t.truncGELEIsoLEGE 0 0).hom.app X ≫ (t.truncLEι 0).app _ ≫
    inv ((t.truncGEπ 0).app X)

@[reassoc (attr := simp)]
lemma fromHomology₀_naturality {X Y : C} (f : X ⟶ Y) [t.IsGE X 0] [t.IsGE Y 0] :
    t.ιHeart.map (t.homology₀.map f) ≫ t.fromHomology₀ Y = t.fromHomology₀ X ≫ f := by
  dsimp [fromHomology₀]
  rw [← cancel_mono ((t.truncGEπ 0).app Y), assoc, assoc, assoc, assoc, assoc, assoc,
    assoc, assoc, IsIso.inv_hom_id, comp_id]
  erw [t.homology₀ιHeart.hom.naturality_assoc f, NatTrans.naturality_assoc,
    (t.truncGEπ 0).naturality, IsIso.inv_hom_id_assoc]
  dsimp [truncLEGE]
  rw [NatTrans.naturality]
  rfl

instance (A X : C) [t.IsGE X 0] [t.IsLE A 0] :
    IsIso ((preadditiveCoyoneda.obj (Opposite.op A)).map ((t.truncLEι 0).app X)) := by
  have : Mono ((preadditiveCoyoneda.obj (Opposite.op A)).map ((t.truncLEι 0).app X)) :=
    ((preadditiveCoyoneda.obj (Opposite.op A)).map_distinguished_exact _
      (inv_rot_of_distTriang _ (t.triangleLEGE_distinguished 0 1 (by linarith) X))).mono_g (by
        apply IsZero.eq_of_src
        apply AddCommGroupCat.isZero
        intro (x : A ⟶ (((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧))
        have : t.IsGE (((t.truncGE 1).obj X)⟦(-1 : ℤ)⟧) 1 :=
          t.isGE_shift ((t.truncGE 1).obj X) 0 (-1) 1 (by linarith)
        exact t.zero x 0 1 (by linarith))
  have : Epi ((preadditiveCoyoneda.obj (Opposite.op A)).map ((t.truncLEι 0).app X)) :=
    ((preadditiveCoyoneda.obj (Opposite.op A)).map_distinguished_exact _
      (t.triangleLEGE_distinguished 0 1 (by linarith) X)).epi_f (by
        apply IsZero.eq_of_tgt
        apply AddCommGroupCat.isZero
        intro (x : A ⟶ (t.truncGE 1).obj X)
        exact t.zero x 0 1 (by linarith))
  apply isIso_of_mono_of_epi

instance (A X : C) [t.IsGE X 0] [t.IsLE A 0] :
    IsIso ((preadditiveCoyoneda.obj (Opposite.op A)).map (t.fromHomology₀ X)) := by
  dsimp only [fromHomology₀]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

instance : t.homology₀.Additive := by
  have := Functor.additive_of_iso t.homology₀ιHeart.symm
  refine' ⟨fun {X Y f g} => t.ιHeart.map_injective _⟩
  erw [(t.homology₀ ⋙ t.ιHeart).map_add]
  simp

lemma isIso_homology₀_iff_isIso_truncGE₀LE₀_map {X Y : C} (f : X ⟶ Y) :
    IsIso (t.homology₀.map f) ↔ IsIso ((t.truncGELE 0 0).map f) := by
  have : IsIso (t.homology₀.map f) ↔  IsIso (t.ιHeart.map (t.homology₀.map f)) := by
    constructor
    · intro h
      infer_instance
    · intro h
      apply isIso_of_reflects_iso  _ t.ιHeart
  rw [this]
  exact NatIso.isIso_map_iff t.homology₀ιHeart f

lemma isIso_homology₀_iff_isIso_truncLE₀GE₀_map {X Y : C} (f : X ⟶ Y) :
    IsIso (t.homology₀.map f) ↔ IsIso ((t.truncLEGE 0 0).map f) := by
  rw [isIso_homology₀_iff_isIso_truncGE₀LE₀_map]
  exact NatIso.isIso_map_iff (t.truncGELEIsoLEGE 0 0) f

instance (X : C) : IsIso (t.homology₀.map ((truncLEι t 0).app X)) := by
  rw [isIso_homology₀_iff_isIso_truncGE₀LE₀_map]
  dsimp [truncGELE]
  infer_instance

instance (X : C) : IsIso (t.homology₀.map ((truncGEπ t 0).app X)) := by
  rw [isIso_homology₀_iff_isIso_truncLE₀GE₀_map]
  dsimp [truncLEGE]
  infer_instance

namespace IsHomologicalAux

variable {T : Triangle C} (hT : T ∈ distTriang C)

@[simps!]
noncomputable def shortComplex :=
  (ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).map t.homology₀

@[simps]
def ιHeartAddEquiv (X Y : t.Heart) : (X ⟶ Y) ≃+ (t.ιHeart.obj X ⟶ t.ιHeart.obj Y) where
  toFun f := t.ιHeart.map f
  invFun g := t.ιHeart.preimage g
  left_inv f := by simp
  right_inv g := by simp
  map_add' := by aesop_cat

noncomputable def addEquivFromHomology₀OfIsLE (X : C) [t.IsLE X 0] (A : t.Heart) :
    (t.homology₀.obj X ⟶ A) ≃+ (X ⟶ t.ιHeart.obj A)  :=
  (ιHeartAddEquiv _ _ _).trans
    (asIso ((preadditiveYoneda.obj
      (t.ιHeart.obj A)).map (t.toHomology₀ _).op)).addCommGroupIsoToAddEquiv

lemma addEquivFromHomology₀OfIsLE_naturality {X Y : C} (f : X ⟶ Y)
    [t.IsLE X 0] [t.IsLE Y 0] (A : t.Heart) (y : t.homology₀.obj Y ⟶ A) :
    f ≫ addEquivFromHomology₀OfIsLE t Y A y =
      addEquivFromHomology₀OfIsLE t X A (t.homology₀.map f ≫ y) := by
  change f ≫ t.toHomology₀ Y ≫ t.ιHeart.map y =
    t.toHomology₀ X ≫ t.ιHeart.map (t.homology₀.map f ≫ y)
  simp only [Functor.map_comp, toHomology₀_naturality_assoc]

lemma case₁ [t.IsLE T.obj₁ 0] [t.IsLE T.obj₂ 0] [t.IsLE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  rw [ShortComplex.exact_and_epi_g_iff_preadditiveYoneda]
  intro A
  let S := (shortComplex t hT).op.map (preadditiveYoneda.obj A)
  let S' := (ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj (t.ιHeart.obj A))
  refine' (ShortComplex.exact_and_mono_f_iff_of_addEquiv S S'
    (addEquivFromHomology₀OfIsLE t T.obj₃ A) (addEquivFromHomology₀OfIsLE t T.obj₂ A)
    (addEquivFromHomology₀OfIsLE t T.obj₁ A) (addEquivFromHomology₀OfIsLE_naturality t T.mor₂ A)
    (addEquivFromHomology₀OfIsLE_naturality t T.mor₁ A)).2 _
  refine' ⟨preadditiveYoneda_map_distinguished (t.ιHeart.obj A) _ hT,
    (preadditiveYoneda_map_distinguished (t.ιHeart.obj A) _ (rot_of_distTriang _ hT)).mono_g _⟩
  apply IsZero.eq_of_src
  apply AddCommGroupCat.isZero
  intro (x : T.obj₁⟦(1 : ℤ)⟧ ⟶ t.ιHeart.obj A)
  exact t.zero x (-1) 0 (by linarith)

lemma case₂ (h₁ : t.IsLE T.obj₁ 0) :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  have h' := case₁ t (t.truncLETriangle_distinguished T hT 0)
  refine' (ShortComplex.exact_and_epi_g_iff_of_iso _).1 h'
  refine' ShortComplex.isoMk
    (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₁)))
    (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₂)))
    (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₃))) _ _
  all_goals
    dsimp
    simp only [← Functor.map_comp, NatTrans.naturality, Functor.id_obj, Functor.id_map]

noncomputable def addEquivToHomology₀OfIsGE (X : C) [t.IsGE X 0] (A : t.Heart) :
    (A ⟶ t.homology₀.obj X) ≃+ (t.ιHeart.obj A ⟶ X) := by
  exact (ιHeartAddEquiv _ _ _).trans
    (asIso ((preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A))).map (t.fromHomology₀ X))).addCommGroupIsoToAddEquiv

lemma addEquivToHomology₀OfIsGE_naturality {X Y : C} (f : X ⟶ Y)
    [t.IsGE X 0] [t.IsGE Y 0] (A : t.Heart) (x : A ⟶ t.homology₀.obj X) :
    addEquivToHomology₀OfIsGE t X A x ≫ f =
      addEquivToHomology₀OfIsGE t Y A (x ≫ t.homology₀.map f) := by
  change (t.ιHeart.map x ≫ t.fromHomology₀ X) ≫ f =
    t.ιHeart.map (x ≫ t.homology₀.map f) ≫ t.fromHomology₀ Y
  simp only [assoc, Functor.map_comp, fromHomology₀_naturality]

lemma case₁' [t.IsGE T.obj₁ 0] [t.IsGE T.obj₂ 0] [t.IsGE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Mono (shortComplex t hT).f := by
  rw [ShortComplex.exact_and_mono_f_iff_preadditiveCoyoneda]
  intro A
  let S := (shortComplex t hT).map (preadditiveCoyoneda.obj (Opposite.op A))
  let S' := (ShortComplex.mk _ _ (comp_distTriang_mor_zero₁₂ T hT)).map (preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A)))
  refine' (ShortComplex.exact_and_mono_f_iff_of_addEquiv S S'
    (addEquivToHomology₀OfIsGE t T.obj₁ A) (addEquivToHomology₀OfIsGE t T.obj₂ A)
    (addEquivToHomology₀OfIsGE t T.obj₃ A)
    (addEquivToHomology₀OfIsGE_naturality t T.mor₁ A)
    (addEquivToHomology₀OfIsGE_naturality t T.mor₂ A)).2 _
  refine' ⟨(preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A))).map_distinguished_exact _ hT,
    ((preadditiveCoyoneda.obj (Opposite.op (t.ιHeart.obj A))).map_distinguished_exact _ (inv_rot_of_distTriang _ hT)).mono_g _⟩
  apply IsZero.eq_of_src
  apply AddCommGroupCat.isZero
  intro (x : t.ιHeart.obj A ⟶ T.obj₃⟦-1⟧)
  have : t.IsGE (T.obj₃⟦(-1 : ℤ)⟧) 1 := t.isGE_shift T.obj₃ 0 (-1) 1 (by linarith)
  exact t.zero x 0 1 (by linarith)

lemma case₂' (h₃ : t.IsGE T.obj₃ 0) :
    (shortComplex t hT).Exact ∧ Mono (shortComplex t hT).f := by
  have h' := case₁' t (t.truncGETriangle_distinguished T hT 0)
  refine' (ShortComplex.exact_and_mono_f_iff_of_iso _).2 h'
  refine' ShortComplex.isoMk
    (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₁)))
    (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₂)))
    (asIso (t.homology₀.map ((t.truncGEπ 0).app T.obj₃))) _ _
  all_goals
    dsimp
    simp only [← Functor.map_comp, ← NatTrans.naturality, Functor.id_map]

end IsHomologicalAux

open IsHomologicalAux
instance : t.homology₀.IsHomological where
  exact T hT := by
    have h₁ := t.triangleLEGE_distinguished 0 1 (by linarith) T.obj₁
    obtain ⟨U, f, g, h₃⟩ := distinguished_cocone_triangle ((t.truncLEι 0).app T.obj₁ ≫ T.mor₁)
    have H := someOctahedron rfl h₁ hT h₃
    have ex₁ := case₂ t h₃ (by dsimp; infer_instance)
    have ex₂ := case₂' t (rot_of_distTriang _ H.mem) (by dsimp; infer_instance)
    dsimp [Triangle.rotate] at ex₂
    have := ex₁.2
    have : Mono (shortComplex t (rot_of_distTriang _ H.mem)).f := ex₂.2
    have ex₃ := ShortComplex₄.connectShortComplex_exact (shortComplex t h₃)
      (shortComplex t (rot_of_distTriang _ H.mem)) (Iso.refl _)
        (t.homology₀.map T.mor₂) (by
          dsimp [shortComplex, ShortComplex.map]
          rw [id_comp, ← Functor.map_comp, H.comm₃]) ex₁.1 ex₂.1
    refine' ShortComplex.exact_of_iso _ ex₃.exact₂
    refine' ShortComplex.isoMk (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₁)))
        (Iso.refl _) (Iso.refl _) _ _
    all_goals
      dsimp; simp

variable [t.homology₀.ShiftSequence ℤ]

def homology (n : ℤ) : C ⥤ t.Heart := t.homology₀.shift n

instance (n : ℤ) : (t.homology n).Additive := by
  dsimp [homology]
  infer_instance

variable (T : Triangle C) (hT : T ∈ distTriang C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

def homologyδ : (t.homology n₀).obj T.obj₃ ⟶ (t.homology n₁).obj T.obj₁ :=
  t.homology₀.shiftMap T.mor₃ n₀ n₁ (by linarith)

@[reassoc (attr := simp)]
lemma homologyδ_comp : t.homologyδ T n₀ n₁ h ≫ (t.homology n₁).map T.mor₁ = 0 :=
  t.homology₀.homology_sequence_δ_comp _ hT _ _ h

@[reassoc (attr := simp)]
lemma comp_homologyδ : (t.homology n₀).map T.mor₂ ≫ t.homologyδ T n₀ n₁ h = 0 :=
  t.homology₀.comp_homology_sequence_δ _ hT _ _ h

lemma homology_exact₁ :
    (ShortComplex.mk _ _ (t.homologyδ_comp T hT n₀ n₁ h)).Exact :=
  t.homology₀.homology_sequence_exact₁ _ hT _ _ h

lemma homology_exact₂ (n : ℤ) :
    (ShortComplex.mk ((t.homology n).map T.mor₁) ((t.homology n).map T.mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])).Exact :=
  t.homology₀.homology_sequence_exact₂ _ hT _

lemma homology_exact₃ :
    (ShortComplex.mk _ _ (t.comp_homologyδ T hT n₀ n₁ h)).Exact :=
  t.homology₀.homology_sequence_exact₃ _ hT _ _ h

lemma isZero_homology₀_of_isGE_one (X : C) [t.IsGE X 1] :
    IsZero ((t.homology₀).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply t.ιHeart.map_injective
  rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero]
  refine' IsZero.of_iso _ (t.homology₀ιHeart.app X)
  dsimp [truncGELE]
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id]
  have : IsZero ((t.truncLE 0).obj X) := by
    rw [← t.isGE_iff_isZero_truncLE_obj 0 1 (by linarith)]
    infer_instance
  rw [IsZero.iff_id_eq_zero] at this
  rw [this, Functor.map_zero]

lemma isZero_homology_of_isGE (X : C) (q n : ℤ) (hn₁ : q < n) [t.IsGE X n] :
    IsZero ((t.homology q).obj X) := by
  have : t.IsGE (X⟦q⟧) (n - q) := t.isGE_shift X n q (n - q) (by linarith)
  have : t.IsGE (X⟦q⟧) 1 := t.isGE_of_GE (X⟦q⟧) 1 (n - q) (by linarith)
  exact IsZero.of_iso (t.isZero_homology₀_of_isGE_one (X⟦q⟧))
    (((t.homology₀.shiftIso q 0 q (by linarith)).app X).symm.trans
    ((t.homology₀.isoShiftZero ℤ).app (X⟦q⟧)))

lemma isZero_homology₀_of_isLE_neg_one (X : C) [t.IsLE X (-1)] :
    IsZero ((t.homology₀).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply t.ιHeart.map_injective
  rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero]
  refine' IsZero.of_iso _ ((t.homology₀ιHeart ≪≫ t.truncGELEIsoLEGE 0 0).app X)
  dsimp [truncLEGE]
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id]
  have : IsZero ((t.truncGE 0).obj X) := by
    rw [← t.isLE_iff_isZero_truncGE_obj (-1) 0 (by linarith)]
    infer_instance
  rw [IsZero.iff_id_eq_zero] at this
  rw [this, Functor.map_zero]

lemma isZero_homology_of_isLE (X : C) (q n : ℤ) (hn₁ : n < q) [t.IsLE X n] :
    IsZero ((t.homology q).obj X) := by
  have : t.IsLE (X⟦q⟧) (n - q) := t.isLE_shift X n q (n - q) (by linarith)
  have : t.IsLE (X⟦q⟧) (-1) := t.isLE_of_LE (X⟦q⟧) (n - q) (-1) (by linarith)
  exact IsZero.of_iso (t.isZero_homology₀_of_isLE_neg_one (X⟦q⟧))
    (((t.homology₀.shiftIso q 0 q (by linarith)).app X).symm.trans
    ((t.homology₀.isoShiftZero ℤ).app (X⟦q⟧)))

lemma isGE₁_iff_isGE₀_and_isZero_homology₀ (X : C) :
    t.IsGE X 1 ↔ t.IsGE X 0 ∧ (IsZero (t.homology₀.obj X)) := by
  constructor
  · intro _
    constructor
    · exact t.isGE_of_GE X 0 1 (by linarith)
    · apply isZero_homology₀_of_isGE_one
  · rintro ⟨_, hX⟩
    rw [t.isGE_iff_isZero_truncLE_obj 0 1 (by linarith)]
    rw [IsZero.iff_id_eq_zero] at hX
    replace hX := t.ιHeart.congr_map hX
    rw [Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero] at hX
    refine' IsZero.of_iso hX _
    exact asIso ((t.truncLE 0).map ((t.truncGEπ 0).app X)) ≪≫
      (t.homology₀ιHeart ≪≫ t.truncGELEIsoLEGE 0 0).symm.app X

lemma isGE_succ_iff_isGE_and_isZero_homology (X : C) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    t.IsGE X n₁ ↔ t.IsGE X n₀ ∧ (IsZero ((t.homology n₀).obj X)) := by
  have eq₁ : t.IsGE (X⟦n₀⟧) 1 ↔ t.IsGE X n₁ := t.isGE_shift_iff _ _ _ _ hn₁
  have eq₂ : t.IsGE (X⟦n₀⟧) 0 ↔ t.IsGE X n₀ := t.isGE_shift_iff _ _ _ _ (by linarith)
  have e : (t.homology n₀).obj X ≅ t.homology₀.obj (X⟦n₀⟧) :=
    (t.homology₀.shiftIso n₀ 0 n₀ (add_zero n₀)).symm.app _ ≪≫
      (t.homology₀.isoShiftZero ℤ ).app _
  have eq₃ : IsZero ((t.homology n₀).obj X) ↔ IsZero (t.homology₀.obj (X⟦n₀⟧)) :=
    ⟨fun h => IsZero.of_iso h e.symm, fun h => IsZero.of_iso h e⟩
  rw [← eq₁, ←eq₂, eq₃]
  exact t.isGE₁_iff_isGE₀_and_isZero_homology₀ _

lemma isIso_whiskerLeft_ιHeart_truncLEι (b : ℤ) (hb : 0 ≤ b) :
    IsIso (whiskerLeft t.ιHeart (t.truncLEι b)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  dsimp
  rw [← t.isLE_iff_isIso_truncLEι_app]
  exact t.isLE_of_LE _ 0 _ hb

lemma isIso_whiskerLeft_ιHeart_truncGEπ (a : ℤ) (ha : a ≤ 0) :
    IsIso (whiskerLeft t.ιHeart (t.truncGEπ a)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  dsimp
  rw [← t.isGE_iff_isIso_truncGEπ_app]
  exact t.isGE_of_GE _ _ 0 ha

noncomputable def ιHeartTruncLE (b : ℤ) (hb : 0 ≤ b): t.ιHeart ⋙ t.truncLE b ≅ t.ιHeart :=
  have := t.isIso_whiskerLeft_ιHeart_truncLEι b hb
  asIso (whiskerLeft t.ιHeart (t.truncLEι b))

noncomputable def ιHeartTruncGE (a : ℤ) (ha : a ≤ 0): t.ιHeart ⋙ t.truncGE a ≅ t.ιHeart :=
  have := t.isIso_whiskerLeft_ιHeart_truncGEπ a ha
  (asIso (whiskerLeft t.ιHeart (t.truncGEπ a))).symm

noncomputable def ιHeartTruncGELE (a b : ℤ) (ha : a ≤ 0) (hb : 0 ≤ b) :
    t.ιHeart ⋙ t.truncGELE a b ≅ t.ιHeart :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (t.ιHeartTruncLE b hb) (t.truncGE a) ≪≫ t.ιHeartTruncGE a ha

noncomputable def ιHeartHomology₀ : t.ιHeart ⋙ t.homology₀ ≅ 𝟭 _ :=
  t.ιHeart.preimageNatIso (Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ t.homology₀ιHeart ≪≫
    t.ιHeartTruncGELE 0 0 (by rfl) (by rfl) ≪≫ (Functor.leftUnitor _).symm)

noncomputable def ιHeartHomology_zero : t.ιHeart ⋙ t.homology 0 ≅ 𝟭 _ :=
  isoWhiskerLeft _ (t.homology₀.isoShiftZero ℤ) ≪≫ t.ιHeartHomology₀

instance {A B : t.Heart} (f : A ⟶ B) [Mono f] (n : ℤ) :
    Mono ((t.homology n).map (t.ιHeart.map f)) := by
  by_cases h : n = 0
  · subst h
    exact ((MorphismProperty.RespectsIso.monomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso t.ιHeartHomology_zero).app (Arrow.mk f))).2
      (inferInstance : Mono f)
  · constructor
    intros
    apply IsZero.eq_of_tgt
    by_cases h' : 0 < n
    · exact t.isZero_homology_of_isLE _ _ 0 h'
    · simp only [not_lt] at h'
      obtain h'' : n < 0 := by
        obtain h' | rfl := h'.lt_or_eq
        · linarith
        · exfalso
          exact h rfl
      apply t.isZero_homology_of_isGE _ _ 0 h''

end

section

variable [t.HasHeart]

lemma shortExact_of_distTriang {X₁ X₂ X₃ : t.Heart} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} (δ : t.ιHeart.obj X₃ ⟶ (t.ιHeart.obj X₁)⟦(1 : ℤ)⟧)
    (h : Triangle.mk (t.ιHeart.map f) (t.ιHeart.map g) δ ∈ distTriang C) :
    (ShortComplex.mk f g (t.ιHeart.map_injective
    (by
      rw [Functor.map_comp, Functor.map_zero]
      exact comp_distTriang_mor_zero₁₂ _ h))).ShortExact := by
  have : t.HasHomology₀ := t.hasHomology₀
  have : t.homology₀.ShiftSequence ℤ := Functor.ShiftSequence.tautological _ _
  have w : f ≫ g = 0 := t.ιHeart.map_injective (by
    simpa only [Functor.map_comp, Functor.map_zero]
      using comp_distTriang_mor_zero₁₂ _ h)
  let S := (ShortComplex.mk _ _ w).map (t.ιHeart ⋙ t.homology 0)
  have : Mono S.f := (t.homology_exact₁ _ h (-1) 0 (by linarith)).mono_g (by
    apply IsZero.eq_of_src
    dsimp
    exact t.isZero_homology_of_isGE _ (-1) 0 (by linarith))
  have : Epi S.g := (t.homology_exact₃ _ h 0 1 (by linarith)).epi_f (by
    apply IsZero.eq_of_tgt
    dsimp
    exact t.isZero_homology_of_isLE _ 1 0 (by linarith))
  have hS : S.ShortExact := { exact := t.homology_exact₂ _ h 0 }
  refine' ShortComplex.shortExact_of_iso _ hS
  exact ShortComplex.isoMk (t.ιHeartHomology_zero.app X₁) (t.ιHeartHomology_zero.app X₂)
    (t.ιHeartHomology_zero.app X₃) (t.ιHeartHomology_zero.hom.naturality f).symm
    (t.ιHeartHomology_zero.hom.naturality g).symm

variable (S : ShortComplex t.Heart) (hS : S.ShortExact)

lemma exists_distTriang_of_shortExact :
    ∃ (δ : t.ιHeart.obj S.X₃ ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧),
      Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ ∈ distTriang C := by
  have : t.HasHomology₀ := t.hasHomology₀
  have : t.homology₀.ShiftSequence ℤ := Functor.ShiftSequence.tautological _ _
  have := hS
  obtain ⟨Z, f₂, f₃, h⟩ := distinguished_cocone_triangle (t.ιHeart.map S.f)
  have := t.cocone_heart_isLE_zero h
  have : t.IsGE Z 0 := by
    rw [t.isGE_succ_iff_isGE_and_isZero_homology Z (-1) 0 (by linarith)]
    constructor
    · exact t.cocone_heart_isGE_neg_one h
    · apply (t.homology_exact₃ _ h (-1) 0 (by linarith)).isZero_X₂
      · apply IsZero.eq_of_src
        dsimp
        apply t.isZero_homology_of_isGE _ _ 0 (by linarith)
      · apply (t.homology_exact₁ _ h (-1) 0 (by linarith)).mono_g_iff.1
        have := hS.mono_f
        dsimp
        infer_instance
  have hZ : Z ∈ t.heart := by
    rw [mem_heart_iff]
    constructor <;> infer_instance
  let Y := t.heartMk _ hZ
  let g' : S.X₂ ⟶ Y := t.ιHeart.preimage (f₂ ≫ (t.ιHeartObjHeartMkIso _ hZ).inv)
  let δ' : t.ιHeart.obj Y ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧ :=
    (t.ιHeartObjHeartMkIso _ hZ).hom ≫ f₃
  have h' : Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map g') δ' ∈ distTriang C := by
    refine' isomorphic_distinguished _ h _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (t.ιHeartObjHeartMkIso _ hZ) _ _ _
    all_goals simp
  obtain ⟨e, he⟩ : ∃ (e : S.X₃ ≅ Y), S.g ≫ e.hom = g' := by
    have h₁ := hS.gIsCokernel
    have h₂ := (t.shortExact_of_distTriang _ h').gIsCokernel
    exact ⟨IsColimit.coconePointUniqueUpToIso h₁ h₂,
      IsColimit.comp_coconePointUniqueUpToIso_hom h₁ h₂ WalkingParallelPair.one⟩
  refine' ⟨t.ιHeart.map e.hom ≫ δ', isomorphic_distinguished _ h' _ _⟩
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (t.ιHeart.mapIso e) _ _ _
  · dsimp
    simp
  · dsimp
    simp only [Functor.image_preimage, id_comp, ← Functor.map_comp, he]
  · dsimp
    simp

noncomputable def heartShortExactδ : t.ιHeart.obj S.X₃ ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧ :=
  (t.exists_distTriang_of_shortExact S hS).choose

@[simps!]
noncomputable def heartShortExactTriangle : Triangle C :=
  Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) (t.heartShortExactδ S hS)

lemma heartShortExactTriangle_distinguished :
    t.heartShortExactTriangle S hS ∈ distTriang C :=
  (t.exists_distTriang_of_shortExact S hS).choose_spec

lemma heartShortExactδ_unique (δ : t.ιHeart.obj S.X₃ ⟶ (t.ιHeart.obj S.X₁)⟦(1 : ℤ)⟧)
    (hδ : Triangle.mk (t.ιHeart.map S.f) (t.ιHeart.map S.g) δ ∈ distTriang C) :
    δ = t.heartShortExactδ S hS := by
  obtain ⟨α, h₁, h₂⟩ := complete_distinguished_triangle_morphism₁ _ _
    (t.heartShortExactTriangle_distinguished S hS) hδ (𝟙 _) (𝟙 _) (by simp)
  obtain ⟨β, rfl⟩ := t.ιHeart.map_surjective α
  dsimp at h₁ h₂
  obtain rfl : β = 𝟙 _ := by
    have := hS.mono_f
    rw [← cancel_mono S.f]
    apply t.ιHeart.map_injective
    simpa using h₁.symm
  simpa using h₂.symm

def mapHeartShortExactTriangle {S₁ S₂ : ShortComplex t.Heart} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) :
    t.heartShortExactTriangle S₁ hS₁ ⟶ t.heartShortExactTriangle S₂ hS₂ where
  hom₁ := t.ιHeart.map φ.τ₁
  hom₂ := t.ιHeart.map φ.τ₂
  hom₃ := t.ιHeart.map φ.τ₃
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp, φ.comm₁₂]
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, φ.comm₂₃]
  comm₃ := by
    dsimp
    obtain ⟨α, h₁, h₂⟩ := complete_distinguished_triangle_morphism₁ _ _
      (t.heartShortExactTriangle_distinguished S₁ hS₁)
      (t.heartShortExactTriangle_distinguished S₂ hS₂)
      (t.ιHeart.map φ.τ₂) (t.ιHeart.map φ.τ₃) (by
        dsimp
        simp only [← Functor.map_comp, φ.comm₂₃])
    obtain ⟨β, rfl⟩ := t.ιHeart.map_surjective α
    dsimp at h₁ h₂
    obtain rfl : β = φ.τ₁ := by
      have := hS₂.mono_f
      rw [← cancel_mono S₂.f]
      apply t.ιHeart.map_injective
      simp only [φ.comm₁₂, Functor.map_comp, h₁]
    exact h₂

end

section

variable [t.HasHeart] [t.HasHomology₀] [(homology₀ t).ShiftSequence  ℤ]

/-def homology'ιHeart'IsoHomoloyιHeart (q : ℤ) :
    t.homology' q ⋙ t.ιHeart' ≅ t.homology q ⋙ t.ιHeart := by
  refine' _ ≪≫ isoWhiskerLeft _ t.homology₀ιHeart.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft _ (t.homology₀.isoShiftZero ℤ).symm ≪≫ t.homology₀.shiftIso q 0 q (by simp)) _
  dsimp [homology']
  sorry-/

variable (X : C) (q q' : ℤ) (hqq' : q + 1 = q')

/-noncomputable def shiftSpectralObjectω₁IsoHomologyιHeart :
    ((spectralObject t X).ω₁ ⋙ shiftFunctor C q).obj
        (ComposableArrows.mk₁ (homOfLE (by simp; linarith) : ℤt.mk q ⟶ ℤt.mk q')) ≅
      (t.homology q ⋙ ιHeart t).obj X :=
  t.shiftSpectralObjectω₁IsoHomologyιHeart' X q q' hqq' ≪≫
    (t.homology'ιHeart'IsoHomoloyιHeart q).app X-/

end

end TStructure

end Triangulated

end CategoryTheory
