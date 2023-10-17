import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.ShortComplex.Ab

universe v v'

open CategoryTheory Category Limits Pretriangulated Preadditive ZeroObject

namespace AddCommGroupCat

lemma isZero (X : AddCommGroupCat) (hX : ∀ (x : X), x = 0) :
    CategoryTheory.Limits.IsZero X := by
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  ext x
  exact hX x

@[simps]
def uliftFunctor : AddCommGroupCat.{v'} ⥤ AddCommGroupCat.{max v v'} where
  obj G := AddCommGroupCat.of (ULift.{v, v'} G.α)
  map f := AddCommGroupCat.ofHom (AddMonoidHom.mk' (uliftFunctor.map f) (by
    rintro ⟨a⟩ ⟨b⟩
    dsimp
    rw [map_add]
    rfl))

@[simps!]
def addEquivULiftFunctorObj (X : AddCommGroupCat.{v'}) :
    uliftFunctor.{v, v'}.obj X ≃+ X :=
  AddEquiv.mk' Equiv.ulift (fun _ _ => rfl)

instance : uliftFunctor.{v, v'}.Additive where

instance : Faithful uliftFunctor.{v, v'} where
  map_injective {G₁ G₂} f g h := by
    ext x
    change (uliftFunctor.{v, v'}.map f ⟨x⟩).down = (uliftFunctor.{v, v'}.map g ⟨x⟩).down
    rw [h]

instance : Full uliftFunctor.{v, v'} where
  preimage {X Y} f := AddMonoidHom.mk' (fun x => (f ⟨x⟩).down) (by
    rintro a b
    dsimp
    erw [f.map_add ⟨a⟩ ⟨b⟩]
    rfl)

lemma _root_.CategoryTheory.ShortComplex.ab_exact_iff_ulift
    (S : ShortComplex (AddCommGroupCat.{v'})) :
    (S.map (uliftFunctor.{v, v'})).Exact ↔ S.Exact := by
  simp only [ShortComplex.ab_exact_iff]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂⟩ (congr_arg ULift.up.{v, v'} hx₂)
    exact ⟨x₁.down, congr_arg ULift.down hx₁⟩
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h x₂.down (congr_arg ULift.down.{v, v'} hx₂)
    exact ⟨ULift.up x₁, congr_arg ULift.up hx₁⟩

def ShortComplexIso (S : ShortComplex AddCommGroupCat.{v}) (S' : ShortComplex AddCommGroupCat.{v'}) :=
  S.map (uliftFunctor.{v', v}) ≅ S'.map (uliftFunctor.{v, v'})

@[simps!]
def _root_.AddEquiv.toIsoULift {A : AddCommGroupCat.{v}} {B : AddCommGroupCat.{v'}} (e : A ≃+ B) :
    uliftFunctor.{v', v}.obj A ≅ uliftFunctor.{v, v'}.obj B :=
  AddEquiv.toAddCommGroupCatIso ((addEquivULiftFunctorObj.{v', v} A).trans
    (e.trans (addEquivULiftFunctorObj.{v, v'} B).symm))

section

variable
  (S : ShortComplex AddCommGroupCat.{v}) (S' : ShortComplex AddCommGroupCat.{v'})
  (e₁ : S.X₁ ≃+ S'.X₁) (e₂ : S.X₂ ≃+ S'.X₂) (e₃ : S.X₃ ≃+ S'.X₃)
  (commf : ∀ (x₁ : S.X₁), S'.f (e₁ x₁) = e₂ (S.f x₁))
  (commg : ∀ (x₂ : S.X₂), S'.g (e₂ x₂) = e₃ (S.g x₂))

def ShortComplexIso.mk : S.map (uliftFunctor.{v', v}) ≅ S'.map (uliftFunctor.{v, v'}) :=
  ShortComplex.isoMk e₁.toIsoULift e₂.toIsoULift e₃.toIsoULift (by
    ext x₁
    exact Equiv.ulift.injective (commf x₁.down)) (by
    ext x₂
    exact Equiv.ulift.injective (commg x₂.down))

lemma _root_.ShortComplex.ab_exact_iff_of_addEquiv :
    S.Exact ↔ S'.Exact := by
  rw [← ShortComplex.ab_exact_iff_ulift.{v', v} S,
    ← ShortComplex.ab_exact_iff_ulift.{v, v'} S']
  exact ShortComplex.exact_iff_of_iso (ShortComplexIso.mk S S' e₁ e₂ e₃ commf commg)

end

end AddCommGroupCat

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

lemma exact_and_mono_f_iff_of_iso [HasZeroMorphisms C] {S T : ShortComplex C} (e : S ≅ T) :
    (S.Exact ∧ Mono S.f) ↔ (T.Exact ∧ Mono T.f) := by
  have : Mono S.f ↔ Mono T.f :=
    MorphismProperty.RespectsIso.arrow_mk_iso_iff
      (MorphismProperty.RespectsIso.monomorphisms C)
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e, this]

lemma exact_and_epi_g_iff_of_iso [HasZeroMorphisms C] {S T : ShortComplex C} (e : S ≅ T) :
    (S.Exact ∧ Epi S.g) ↔ (T.Exact ∧ Epi T.g) := by
  have : Epi S.g ↔ Epi T.g :=
    MorphismProperty.RespectsIso.arrow_mk_iso_iff
      (MorphismProperty.RespectsIso.epimorphisms C)
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e, this]

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
    ((ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj A)).Exact := by
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

noncomputable instance : Abelian t.Heart := by
  apply AbelianSubcategory.abelian t.ιHeart
  · intro X Y n f hn
    exact t.zero f 0 (-n) (by linarith)
  · apply admissibleMorphism_heart

end

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
  have : t.IsLE Z n := t.isLE₂ _ (rot_of_dist_triangle _ h₁) n
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
  have h₁ := rot_of_dist_triangle _ (t.triangleLEGE_distinguished (n-1) n (by linarith) T.obj₂)
  obtain ⟨Z, f₁, f₃, h₂⟩ := distinguished_cocone_triangle₁ b
  have H := someOctahedron comm h₁ (rot_of_dist_triangle _ h₂) (rot_of_dist_triangle _ hT)
  obtain ⟨m₁, hm₁⟩ : ∃ (m₁ : (t.truncLE (n-1)).obj T.obj₂ ⟶ T.obj₁),
    (shiftFunctor C (1 : ℤ)).map m₁ = H.m₁ := ⟨(shiftFunctor C (1 : ℤ)).preimage H.m₁, by simp⟩
  obtain ⟨m₃, hm₃⟩ : ∃ (m₃ : T.obj₁ ⟶ Z), (shiftFunctor C (1 : ℤ)).map m₃ = H.m₃ :=
    ⟨(shiftFunctor C (1 : ℤ)).preimage H.m₃, by simp⟩
  let T' := Triangle.mk m₁ m₃ (f₁ ≫ (t.truncGEδLE (n-1) n (by linarith)).app T.obj₂)
  have Hmem' : T' ∈ distTriang C := by
    rw [← T'.shift_distinguished_iff 1]
    refine' isomorphic_distinguished _ H.mem _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) (mulIso (-1) (Iso.refl _)) (Iso.refl _) _ _ _
    · dsimp
      simp [hm₁]
    · dsimp
      simp [hm₃]
    · dsimp
      simp
  have : t.IsGE Z n := t.isGE₂ _ (inv_rot_of_dist_triangle _ h₂) n
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
    (preadditiveYoneda_map_distinguished A _ (rot_of_dist_triangle _ (t.triangleLTGE_distinguished 0 X))).mono_g (by
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
      (inv_rot_of_dist_triangle _ (t.triangleLEGE_distinguished 0 1 (by linarith) X))).mono_g (by
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

instance (A X : C) [t.IsGE X 0] [t.IsLE A 0]:
    IsIso ((preadditiveCoyoneda.obj (Opposite.op A)).map (t.fromHomology₀ X)) := by
  dsimp only [fromHomology₀]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

instance : t.homology₀.Additive := by
  have := Functor.additive_of_iso t.homology₀ιHeart.symm
  refine' ⟨fun {X Y f g} => t.ιHeart.map_injective _⟩
  erw [(t.homology₀ ⋙ t.ιHeart).map_add]
  simp

namespace IsHomologicalAux

variable {T : Triangle C} (hT : T ∈ distTriang C)

@[simps!]
noncomputable def shortComplex :=
  (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).map t.homology₀

/-lemma case₁ [t.IsLE T.obj₁ 0] [t.IsLE T.obj₂ 0] [t.IsLE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  sorry
  --let S := fun A => (shortComplex t hT).op.map (preadditiveYoneda.obj A)
  --let S' := fun A => (ShortComplex.mk _ _ (comp_dist_triangle_mor_zero₁₂ T hT)).op.map (preadditiveYoneda.obj A)
  --suffices ∀ A, (S A).Exact ∧ Mono (S A).f by
  --  simpa only [ShortComplex.exact_and_epi_g_iff_preadditiveYoneda] using this
  --intro A

lemma case₂ (h₁ : t.IsLE T.obj₁ 0) :
    (shortComplex t hT).Exact ∧ Epi (shortComplex t hT).g := by
  sorry

lemma case₁' [t.IsGE T.obj₁ 0] [t.IsGE T.obj₂ 0] [t.IsGE T.obj₃ 0] :
    (shortComplex t hT).Exact ∧ Mono (shortComplex t hT).f := by
  sorry

lemma case₂' (h₃ : t.IsGE T.obj₃ 0) :
    (shortComplex t hT).Exact ∧ Mono (shortComplex t hT).f := by
  sorry-/

end IsHomologicalAux

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

/-open IsHomologicalAux
instance : t.homology₀.IsHomological where
  exact T hT := by
    have h₁ := t.triangleLEGE_distinguished 0 1 (by linarith) T.obj₁
    obtain ⟨U, f, g, h₃⟩ := distinguished_cocone_triangle ((t.truncLEι 0).app T.obj₁ ≫ T.mor₁)
    have H := someOctahedron rfl h₁ hT h₃
    have ex₁ := case₂ t h₃ (by dsimp; infer_instance)
    have ex₂ := case₂' t (rot_of_dist_triangle _ H.mem) (by dsimp; infer_instance)
    dsimp [Triangle.rotate] at ex₂
    have := ex₁.2
    have : Mono (shortComplex t (rot_of_dist_triangle _ H.mem)).f := ex₂.2
    have ex₃ := ShortComplex₄.connectShortComplex_exact (shortComplex t h₃)
      (shortComplex t (rot_of_dist_triangle _ H.mem)) (Iso.refl _)
        (t.homology₀.map T.mor₂) (by
          dsimp [shortComplex, ShortComplex.map]
          rw [id_comp, ← Functor.map_comp, H.comm₃]) ex₁.1 ex₂.1
    refine' ShortComplex.exact_of_iso _ ex₃.exact₂
    refine' ShortComplex.isoMk (asIso (t.homology₀.map ((t.truncLEι 0).app T.obj₁)))
        (Iso.refl _) (Iso.refl _) _ _
    all_goals
      dsimp; simp-/

end TStructure

end Triangulated

end CategoryTheory
